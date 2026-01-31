"""FastAPI server for the Proof-to-Publication Orchestrator."""

import asyncio
from contextlib import asynccontextmanager

from fastapi import FastAPI, HTTPException, BackgroundTasks
from fastapi.middleware.cors import CORSMiddleware

from . import __version__
from .models import (
    ScanRequest, ScanResponse,
    ProofStartRequest, ProofStartResponse, ProofStatusResponse, ProofListResponse,
    PaperGenerateRequest, PaperGenerateResponse,
    ReviewerFindRequest, ReviewerFindResponse,
    EmailDraftRequest, EmailDraftResponse,
    HealthResponse, ProofStatus
)
from .scanner import scan_proof_candidates
from .orchestrator import (
    start_proof_attempt, get_proof_status, list_proof_jobs,
    check_lean_bridge_available, run_proof_search, ProofJob
)
from .paper_generator import generate_paper
from .reviewer_finder import find_reviewers_async
from .email_drafter import draft_email


# Store for background proof tasks
_background_jobs: dict[str, ProofJob] = {}


@asynccontextmanager
async def lifespan(app: FastAPI):
    """Application lifespan handler."""
    yield


app = FastAPI(
    title="Proof-to-Publication Orchestrator",
    description="Turnkey pipeline for Lean theorem proving and paper generation",
    version=__version__,
    lifespan=lifespan
)

# CORS for web access
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)


@app.get("/health", response_model=HealthResponse)
async def health_check():
    """Check server health and Lean bridge availability."""
    return HealthResponse(
        status="healthy",
        version=__version__,
        lean_bridge_available=check_lean_bridge_available()
    )


@app.post("/candidates", response_model=ScanResponse)
async def scan_candidates(request: ScanRequest):
    """Scan for theorems/lemmas with sorry that can be proven."""
    candidates, files_scanned = scan_proof_candidates(
        source=request.source,
        pattern=request.pattern
    )
    return ScanResponse(
        candidates=candidates,
        total_count=len(candidates),
        files_scanned=files_scanned
    )


@app.post("/proof/start", response_model=ProofStartResponse)
async def start_proof(request: ProofStartRequest, background_tasks: BackgroundTasks):
    """Start an async proof attempt."""
    if not check_lean_bridge_available():
        raise HTTPException(
            status_code=503,
            detail="Lean bridge server not running. Start with: python lean_bridge.py server <file>"
        )

    # Create job
    import uuid
    job_id = str(uuid.uuid4())[:8]
    job = ProofJob(
        job_id=job_id,
        theorem=request.theorem,
        lean_file=request.lean_file
    )
    _background_jobs[job_id] = job

    # Start background task
    async def run_proof():
        await run_proof_search(job, request.max_steps, request.tactics)

    background_tasks.add_task(run_proof)

    return ProofStartResponse(
        job_id=job_id,
        status=ProofStatus.PENDING,
        message=f"Proof attempt started. Check status at /proof/status/{job_id}"
    )


@app.get("/proof/status/{job_id}", response_model=ProofStatusResponse)
async def proof_status(job_id: str):
    """Check the status of a proof attempt."""
    job = _background_jobs.get(job_id)
    if not job:
        raise HTTPException(status_code=404, detail=f"Job {job_id} not found")

    return ProofStatusResponse(
        job_id=job.job_id,
        status=job.status,
        steps_taken=job.steps_taken,
        queue_size=job.queue_size,
        solution=job.solution,
        error=job.error,
        stuck_on=job.stuck_on
    )


@app.get("/proof/list", response_model=ProofListResponse)
async def list_proofs():
    """List all proof attempts."""
    jobs = [
        ProofStatusResponse(
            job_id=job.job_id,
            status=job.status,
            steps_taken=job.steps_taken,
            queue_size=job.queue_size,
            solution=job.solution,
            error=job.error,
            stuck_on=job.stuck_on
        )
        for job in _background_jobs.values()
    ]
    return ProofListResponse(jobs=jobs)


@app.post("/paper/generate", response_model=PaperGenerateResponse)
async def generate_paper_endpoint(request: PaperGenerateRequest):
    """Generate a LaTeX paper from proven theorems."""
    try:
        latex_content, pdf_path = await generate_paper(
            title=request.title,
            theorem_names=request.theorems,
            abstract_hint=request.abstract_hint,
            authors=request.authors,
            template=request.template
        )
        return PaperGenerateResponse(
            latex_content=latex_content,
            pdf_path=pdf_path,
            success=True,
            message="Paper generated successfully"
        )
    except ValueError as e:
        return PaperGenerateResponse(
            latex_content="",
            pdf_path=None,
            success=False,
            message=str(e)
        )
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@app.post("/reviewers/find", response_model=ReviewerFindResponse)
async def find_reviewers_endpoint(request: ReviewerFindRequest):
    """Find academic experts based on research keywords."""
    return await find_reviewers_async(
        keywords=request.keywords,
        max_results=request.max_results,
        categories=request.categories
    )


@app.post("/emails/draft", response_model=EmailDraftResponse)
async def draft_email_endpoint(request: EmailDraftRequest):
    """Draft a personalized outreach email to a reviewer."""
    return await draft_email(
        reviewer=request.reviewer,
        paper_title=request.paper_title,
        paper_abstract=request.paper_abstract,
        sender_name=request.sender_name,
        sender_affiliation=request.sender_affiliation
    )


def main():
    """Run the server."""
    import uvicorn
    from .config import get_settings

    settings = get_settings()
    uvicorn.run(
        "orchestrator.server:app",
        host="0.0.0.0",
        port=settings.port,
        reload=True
    )


if __name__ == "__main__":
    main()
