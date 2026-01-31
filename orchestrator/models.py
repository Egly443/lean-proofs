"""Pydantic models for API request/response schemas."""

from pydantic import BaseModel, Field
from typing import Optional
from enum import Enum


class ProofStatus(str, Enum):
    PENDING = "pending"
    RUNNING = "running"
    SOLVED = "solved"
    FAILED = "failed"
    TIMEOUT = "timeout"


class TheoremCandidate(BaseModel):
    """A theorem or lemma that can be proven."""
    name: str
    statement: str
    file_path: str
    line_number: int
    has_sorry: bool = True


class ScanRequest(BaseModel):
    """Request to scan for proof candidates."""
    source: str = Field(default="local", description="Source: 'local' or file path")
    pattern: Optional[str] = Field(default=None, description="Glob pattern for .lean files")


class ScanResponse(BaseModel):
    """Response containing discovered theorems."""
    candidates: list[TheoremCandidate]
    total_count: int
    files_scanned: int


class ProofStartRequest(BaseModel):
    """Request to start a proof attempt."""
    theorem: str = Field(..., description="Full theorem statement ending with ':= by sorry'")
    lean_file: str = Field(default="EnergyIncrement.lean", description="Lean file for context")
    max_steps: int = Field(default=600, description="Maximum search steps")
    tactics: Optional[list[str]] = Field(default=None, description="Custom tactic list")


class ProofStartResponse(BaseModel):
    """Response when proof attempt is started."""
    job_id: str
    status: ProofStatus
    message: str


class ProofStatusResponse(BaseModel):
    """Status of a running or completed proof."""
    job_id: str
    status: ProofStatus
    steps_taken: int = 0
    queue_size: int = 0
    solution: Optional[list[str]] = None
    error: Optional[str] = None
    stuck_on: Optional[list[str]] = None


class ProofListResponse(BaseModel):
    """List of all proof jobs."""
    jobs: list[ProofStatusResponse]


class PaperGenerateRequest(BaseModel):
    """Request to generate a LaTeX paper."""
    title: str
    theorems: list[str] = Field(..., description="List of theorem names to include")
    abstract_hint: Optional[str] = Field(default=None, description="Guidance for abstract")
    authors: list[str] = Field(default_factory=list)
    template: str = Field(default="ejc", description="Template name: 'ejc' or 'arxiv'")


class PaperGenerateResponse(BaseModel):
    """Response with generated paper."""
    latex_content: str
    pdf_path: Optional[str] = None
    success: bool
    message: str


class ReviewerFindRequest(BaseModel):
    """Request to find academic reviewers."""
    keywords: list[str] = Field(..., description="Research keywords")
    max_results: int = Field(default=10, description="Maximum reviewers to return")
    categories: list[str] = Field(default_factory=lambda: ["math.CO", "cs.DM"])


class Reviewer(BaseModel):
    """An academic reviewer/expert."""
    name: str
    affiliation: Optional[str] = None
    email: Optional[str] = None
    relevant_papers: list[str] = Field(default_factory=list)
    arxiv_ids: list[str] = Field(default_factory=list)


class ReviewerFindResponse(BaseModel):
    """Response with found reviewers."""
    reviewers: list[Reviewer]
    query_used: str


class EmailDraftRequest(BaseModel):
    """Request to draft outreach emails."""
    reviewer: Reviewer
    paper_title: str
    paper_abstract: str
    sender_name: str
    sender_affiliation: Optional[str] = None


class EmailDraftResponse(BaseModel):
    """Response with drafted email."""
    subject: str
    body: str
    reviewer_name: str


class HealthResponse(BaseModel):
    """Health check response."""
    status: str
    version: str
    lean_bridge_available: bool
