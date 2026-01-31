"""Scan Lean files for theorems and lemmas with sorry."""

import re
from pathlib import Path

from .models import TheoremCandidate
from .config import get_settings


# Pattern to match theorem/lemma declarations
THEOREM_PATTERN = re.compile(
    r'^(theorem|lemma)\s+(\w+)\s*'  # keyword and name
    r'((?:\([^)]*\)|\{[^}]*\}|\[[^\]]*\]|\s)*)'  # parameters
    r':\s*'  # colon
    r'(.*?)'  # type/statement (non-greedy)
    r':=',  # assignment
    re.MULTILINE | re.DOTALL
)

# Pattern to detect sorry in proof body
SORRY_PATTERN = re.compile(r'\bsorry\b')


def scan_lean_file(file_path: Path) -> list[TheoremCandidate]:
    """Scan a single Lean file for theorems/lemmas with sorry."""
    candidates = []

    try:
        content = file_path.read_text()
    except Exception:
        return candidates

    lines = content.split('\n')
    line_starts = [0]
    for line in lines:
        line_starts.append(line_starts[-1] + len(line) + 1)

    def get_line_number(pos: int) -> int:
        for i, start in enumerate(line_starts):
            if start > pos:
                return i
        return len(lines)

    # Find all theorem/lemma declarations
    for match in re.finditer(r'^(theorem|lemma)\s+(\w+)', content, re.MULTILINE):
        keyword = match.group(1)
        name = match.group(2)
        start_pos = match.start()
        line_number = get_line_number(start_pos)

        # Extract the full declaration (up to next theorem/lemma or end)
        end_pos = len(content)
        next_match = re.search(r'^(theorem|lemma|def|structure|class|instance)\s+\w+',
                               content[match.end():], re.MULTILINE)
        if next_match:
            end_pos = match.end() + next_match.start()

        declaration = content[start_pos:end_pos]

        # Check if it contains sorry
        has_sorry = bool(SORRY_PATTERN.search(declaration))

        # Extract just the statement (before :=)
        stmt_match = re.match(
            r'(theorem|lemma)\s+\w+\s*((?:\([^)]*\)|\{[^}]*\}|\[[^\]]*\]|\s)*):\s*(.*?)\s*:=',
            declaration,
            re.DOTALL
        )
        if stmt_match:
            params = stmt_match.group(2).strip()
            type_sig = stmt_match.group(3).strip()
            statement = f"{keyword} {name} {params}: {type_sig}"
        else:
            # Fallback: use first few lines
            statement = declaration[:200].replace('\n', ' ').strip()
            if len(declaration) > 200:
                statement += "..."

        candidates.append(TheoremCandidate(
            name=name,
            statement=statement,
            file_path=str(file_path),
            line_number=line_number,
            has_sorry=has_sorry
        ))

    return candidates


def scan_proof_candidates(
    source: str = "local",
    pattern: str | None = None
) -> tuple[list[TheoremCandidate], int]:
    """
    Scan for proof candidates.

    Args:
        source: "local" to scan current directory, or a specific file path
        pattern: Glob pattern for .lean files (default: "*.lean")

    Returns:
        Tuple of (candidates with sorry, total files scanned)
    """
    settings = get_settings()

    if pattern is None:
        pattern = "*.lean"

    if source == "local":
        base_dir = settings.lean_files_dir
    else:
        path = Path(source)
        if path.is_file():
            candidates = scan_lean_file(path)
            sorry_candidates = [c for c in candidates if c.has_sorry]
            return sorry_candidates, 1
        base_dir = path

    # Scan all matching files
    all_candidates = []
    files_scanned = 0

    for lean_file in base_dir.glob(pattern):
        if lean_file.is_file():
            files_scanned += 1
            all_candidates.extend(scan_lean_file(lean_file))

    # Also check subdirectories
    for lean_file in base_dir.glob(f"**/{pattern}"):
        if lean_file.is_file() and lean_file not in base_dir.glob(pattern):
            files_scanned += 1
            all_candidates.extend(scan_lean_file(lean_file))

    # Filter to only those with sorry
    sorry_candidates = [c for c in all_candidates if c.has_sorry]

    return sorry_candidates, files_scanned
