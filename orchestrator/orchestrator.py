"""Core orchestration logic for proof attempts."""

import asyncio
import json
import socket
import subprocess
import sys
import uuid
from collections import deque, Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

from .models import ProofStatus, ProofStatusResponse
from .config import get_settings

# Store for running/completed proof jobs
_proof_jobs: dict[str, "ProofJob"] = {}


@dataclass
class ProofJob:
    """Represents a proof attempt job."""
    job_id: str
    theorem: str
    lean_file: str
    status: ProofStatus = ProofStatus.PENDING
    steps_taken: int = 0
    queue_size: int = 0
    solution: Optional[list[str]] = None
    error: Optional[str] = None
    stuck_on: Optional[list[str]] = None
    task: Optional[asyncio.Task] = None


class LeanClient:
    """Client for communicating with the Lean bridge server."""

    def __init__(self, socket_file: Path):
        self.socket_file = socket_file

    def is_available(self) -> bool:
        """Check if the Lean bridge server is running."""
        try:
            with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as s:
                s.connect(str(self.socket_file))
            return True
        except (FileNotFoundError, ConnectionRefusedError):
            return False

    def send_request(self, req: dict) -> dict:
        """Send a request to the Lean bridge and get response."""
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
            sock.connect(str(self.socket_file))
            sock.sendall(json.dumps(req).encode())
            data = ""
            while True:
                chunk = sock.recv(65536).decode()
                if not chunk:
                    break
                data += chunk
            return json.loads(data)


class ProofNode:
    """Node in the proof search tree."""

    def __init__(self, state_id: int, goals: list[str], history: list[tuple[str, int]] | None = None):
        self.state_id = state_id
        self.goals = goals
        self.history = history if history else []

    def is_solved(self) -> bool:
        return len(self.goals) == 0

    def goal_hash(self) -> str:
        return str(self.goals)


# Default tactics for proof search
DEFAULT_TACTICS = [
    "intro h",
    "simp",
    "ring",
    "assumption",
    "constructor",
    "rfl",
    "exact?",
    "decide",
    "norm_num",
    "linarith",
    "omega",
    "aesop",
]


async def run_proof_search(job: ProofJob, max_steps: int = 600, tactics: list[str] | None = None):
    """
    Run BFS proof search for a theorem.

    This is the async wrapper around the proof search logic.
    """
    settings = get_settings()
    client = LeanClient(settings.socket_file)

    if not client.is_available():
        job.status = ProofStatus.FAILED
        job.error = "Lean bridge server not running. Start with: python lean_bridge.py server <file>"
        return

    job.status = ProofStatus.RUNNING
    tactic_list = tactics if tactics else DEFAULT_TACTICS.copy()
    tactic_stats = Counter()
    tactic_attempts = Counter()
    visited: set[str] = set()
    queue: deque[ProofNode] = deque()

    # Load memory if available
    if settings.memory_file.exists():
        try:
            with open(settings.memory_file, 'r') as f:
                data = json.load(f)
                past_stats = data.get("tactic_success_counts", {})
                tactic_list.sort(key=lambda t: past_stats.get(t, 0), reverse=True)
        except Exception:
            pass

    # Initialize proof
    try:
        res = client.send_request({"command": "cmd", "cmd": job.theorem})
    except Exception as e:
        job.status = ProofStatus.FAILED
        job.error = f"Failed to connect to Lean bridge: {e}"
        return

    if "sorries" not in res.get("response", {}):
        job.status = ProofStatus.FAILED
        job.error = f"Failed to initialize proof: {res}"
        return

    initial_id = res["response"]["sorries"][0]["proofState"]
    root = ProofNode(initial_id, [res["response"]["sorries"][0]["goal"]])
    queue.append(root)
    visited.add(root.goal_hash())

    step_count = 0
    while queue:
        if step_count >= max_steps:
            job.status = ProofStatus.TIMEOUT
            job.stuck_on = [queue[i].goals[0] for i in range(min(3, len(queue)))]
            _save_memory(settings.memory_file, "max_steps_reached", tactic_stats, tactic_attempts, job.stuck_on)
            return

        node = queue.popleft()
        step_count += 1
        job.steps_taken = step_count
        job.queue_size = len(queue)

        # Yield control periodically
        if step_count % 10 == 0:
            await asyncio.sleep(0)

        for tactic in tactic_list:
            # Skip intro if not relevant
            if tactic.startswith("intro") and "->" not in node.goals[0] and "let" not in node.goals[0]:
                continue

            tactic_attempts[tactic] += 1

            try:
                res = client.send_request({
                    "command": "tactic",
                    "tactic": tactic,
                    "proof_state": node.state_id
                })
            except Exception:
                continue

            if res["status"] == "success":
                tactic_stats[tactic] += 1
                new_goals = res.get("goals", [])
                new_id = res["new_state_id"]
                new_history = node.history + [(tactic, new_id)]
                child = ProofNode(new_id, new_goals, new_history)

                if child.is_solved():
                    job.status = ProofStatus.SOLVED
                    job.solution = [t for t, _ in new_history]
                    _save_memory(settings.memory_file, "solved", tactic_stats, tactic_attempts, [])
                    return

                if child.goal_hash() in visited:
                    continue

                if len(queue) < settings.default_max_queue_size:
                    visited.add(child.goal_hash())
                    queue.append(child)

    job.status = ProofStatus.FAILED
    job.error = "Search space exhausted"
    job.stuck_on = []
    _save_memory(settings.memory_file, "exhausted", tactic_stats, tactic_attempts, [])


def _save_memory(memory_file: Path, reason: str, stats: Counter, attempts: Counter, stuck: list[str]):
    """Save learning memory to file."""
    report = {
        "last_run_reason": reason,
        "tactic_success_counts": dict(stats),
        "tactic_failure_counts": {k: attempts[k] - stats[k] for k in attempts},
        "stuck_on_goals": stuck
    }
    with open(memory_file, 'w') as f:
        json.dump(report, f, indent=2)


def start_proof_attempt(
    theorem: str,
    lean_file: str = "EnergyIncrement.lean",
    max_steps: int = 600,
    tactics: list[str] | None = None
) -> str:
    """
    Start an async proof attempt.

    Returns the job ID that can be used to check status.
    """
    job_id = str(uuid.uuid4())[:8]
    job = ProofJob(
        job_id=job_id,
        theorem=theorem,
        lean_file=lean_file
    )
    _proof_jobs[job_id] = job

    # Create async task
    loop = asyncio.get_event_loop()
    task = loop.create_task(run_proof_search(job, max_steps, tactics))
    job.task = task

    return job_id


def get_proof_status(job_id: str) -> ProofStatusResponse | None:
    """Get the status of a proof job."""
    job = _proof_jobs.get(job_id)
    if not job:
        return None

    return ProofStatusResponse(
        job_id=job.job_id,
        status=job.status,
        steps_taken=job.steps_taken,
        queue_size=job.queue_size,
        solution=job.solution,
        error=job.error,
        stuck_on=job.stuck_on
    )


def list_proof_jobs() -> list[ProofStatusResponse]:
    """List all proof jobs."""
    return [get_proof_status(job_id) for job_id in _proof_jobs if get_proof_status(job_id)]


def check_lean_bridge_available() -> bool:
    """Check if the Lean bridge server is running."""
    settings = get_settings()
    client = LeanClient(settings.socket_file)
    return client.is_available()
