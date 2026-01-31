import socket
import json
import os
from collections import deque, Counter

# --- CONFIGURATION ---
SOCKET_FILE = ".lean_bridge.sock"
MEMORY_FILE = "agent_memory.json"  # Where we save our learnings

# SAFETY LIMITS
MAX_STEPS = 600        
MAX_QUEUE_SIZE = 2000  

# BASE TACTIC LIBRARY
# We will dynamically re-order this list based on what works best!
BASE_TACTICS = [
    "intro B₁ B₂",
    "intro h",
    "dsimp [SmithReduction.rowOp]",
    "rw [if_pos rfl]",
    "simp",
    "ring",
    "assumption",
    "constructor",
    "rfl"
]

class LeanClient:
    def connect(self):
        try:
            with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as s:
                s.connect(SOCKET_FILE)
            return True
        except (FileNotFoundError, ConnectionRefusedError):
            return False

    def send_req(self, req):
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
            sock.connect(SOCKET_FILE)
            sock.sendall(json.dumps(req).encode())
            data = ""
            while True:
                chunk = sock.recv(65536).decode()
                if not chunk: break
                data += chunk
            return json.loads(data)

class ProofNode:
    def __init__(self, state_id, goals, history=None):
        self.state_id = state_id
        self.goals = goals
        self.history = history if history else []

    def is_solved(self):
        return len(self.goals) == 0

    def goal_hash(self):
        return str(self.goals)

class ProofSearch:
    def __init__(self, theorem_cmd):
        self.client = LeanClient()
        self.theorem_cmd = theorem_cmd
        self.visited = set()
        self.queue = deque()
        
        # LEARNING METRICS
        self.tactic_stats = Counter()  # Tracks successful uses
        self.tactic_attempts = Counter() # Tracks total attempts
        self.tactics = BASE_TACTICS.copy() # We will sort this later

    def load_memory(self):
        """Loads past knowledge to optimize the current run."""
        if os.path.exists(MEMORY_FILE):
            try:
                with open(MEMORY_FILE, 'r') as f:
                    data = json.load(f)
                    past_stats = data.get("tactic_success_counts", {})
                    
                    # Sort our library: Tactics with high success counts go FIRST
                    # This speeds up the search drastically on re-runs.
                    self.tactics.sort(key=lambda t: past_stats.get(t, 0), reverse=True)
                    
                    print(f"[*] Loaded Memory. Best tactic from last run: {self.tactics[0]}")
            except Exception as e:
                print(f"[!] Failed to load memory: {e}")

    def save_memory(self, reason):
        """Saves a report of what worked and what the agent was stuck on."""
        print(f"\n[*] Saving Agent Report to '{MEMORY_FILE}'...")
        
        # 1. Capture the 'Frontier' (What the agent was looking at when it stopped)
        # We take a sample of up to 3 unsolved goals from the queue
        stuck_on = []
        for i in range(min(3, len(self.queue))):
            stuck_on.append(self.queue[i].goals[0])

        report = {
            "last_run_reason": reason,
            "tactic_success_counts": self.tactic_stats,
            "tactic_failure_counts": {k: self.tactic_attempts[k] - self.tactic_stats[k] for k in self.tactic_attempts},
            "stuck_on_goals": stuck_on
        }

        with open(MEMORY_FILE, 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"[*] Report Saved. Open '{MEMORY_FILE}' to see what the agent was stuck on.")

    def run(self):
        print(f"[*] Connecting to Lean Bridge...")
        if not self.client.connect():
            print("[!] Could not connect. Is 'python lean_bridge.py server <file>' running?")
            return

        # LOAD INTELLIGENCE
        self.load_memory()

        print(f"[*] Initializing Proof...")
        res = self.client.send_req({"command": "cmd", "cmd": self.theorem_cmd})
        
        # --- DEBUG BLOCK ADDED HERE ---
        if "sorries" not in res.get("response", {}):
            print("\n[DEBUG] Initialization Error Response:")
            print(json.dumps(res, indent=2))
            print("[!] Failed to initialize.")
            return
        # -----------------------------

        initial_id = res["response"]["sorries"][0]["proofState"]
        root = ProofNode(initial_id, [res["response"]["sorries"][0]["goal"]])
        self.queue.append(root)
        self.visited.add(root.goal_hash())
        
        print(f"[*] Search started. Max Steps={MAX_STEPS}")
        print("-" * 60)

        step_count = 0
        while self.queue:
            # SAFETY CUTOFF
            if step_count >= MAX_STEPS:
                print(f"\n[STOP] Limit reached ({MAX_STEPS} steps).")
                self.save_memory("max_steps_reached")
                return

            node = self.queue.popleft()
            step_count += 1
            
            # Print minimal status
            if step_count % 10 == 0:
                print(f"[Step {step_count}] Q: {len(self.queue)} | Best Tactic: {self.tactics[0]}")

            # Try tactics in the ORDER of their past success
            for tactic in self.tactics:
                # Heuristic: skip 'intro' if not relevant
                if tactic.startswith("intro") and "→" not in node.goals[0] and "let" not in node.goals[0]:
                    continue

                self.tactic_attempts[tactic] += 1 # Log attempt
                
                res = self.client.send_req({
                    "command": "tactic",
                    "tactic": tactic,
                    "proof_state": node.state_id
                })

                if res["status"] == "success":
                    # SUCCESS! Log it.
                    self.tactic_stats[tactic] += 1
                    
                    new_goals = res.get("goals", [])
                    new_id = res["new_state_id"]
                    new_history = node.history + [(tactic, new_id)]
                    child = ProofNode(new_id, new_goals, new_history)

                    if child.is_solved():
                        print(f"\n[!!!] PROOF FOUND! [!!!]")
                        print("Solution Path:")
                        for t, sid in new_history:
                            print(f"  -> {t} (State {sid})")
                        self.save_memory("solved") # Save the winning stats!
                        return

                    if child.goal_hash() in self.visited:
                        continue
                    
                    # Queue Cap
                    if len(self.queue) < MAX_QUEUE_SIZE:
                        self.visited.add(child.goal_hash())
                        self.queue.append(child)

        print("\n[!] Search exhausted.")
        self.save_memory("exhausted")

if __name__ == "__main__":
    THEOREM = "example (R : Type) [CommRing R] [IsDomain R] [GCDMonoid R] (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n R) (i₁ i₂ : m) (j : n) (x y : R) (hxy : x * A i₁ j + y * A i₂ j = GCDMonoid.gcd (A i₁ j) (A i₂ j)) : let B₁ := SmithReduction.rowOp A i₁ i₂ x; let B₂ := SmithReduction.rowOp B₁ i₂ i₁ (-y); B₂ i₁ j = GCDMonoid.gcd (A i₁ j) (A i₂ j) := by sorry"
    
    agent = ProofSearch(THEOREM)
    agent.run()
