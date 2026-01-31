"""Generate LaTeX papers from proven theorems."""

import subprocess
from pathlib import Path
from typing import Optional

from jinja2 import Template
import anthropic

from .config import get_settings
from .scanner import scan_lean_file, TheoremCandidate


# Load EJC template
TEMPLATE_DIR = Path(__file__).parent / "templates"


def load_template(name: str = "ejc") -> str:
    """Load a LaTeX template by name."""
    template_path = TEMPLATE_DIR / f"{name}_template.tex"
    if not template_path.exists():
        template_path = TEMPLATE_DIR / "ejc_template.tex"
    return template_path.read_text()


def extract_theorems_from_files(
    theorem_names: list[str],
    search_dir: Path | None = None
) -> list[TheoremCandidate]:
    """Extract specific theorems from Lean files."""
    settings = get_settings()
    search_dir = search_dir or settings.lean_files_dir

    all_theorems: list[TheoremCandidate] = []
    for lean_file in search_dir.glob("**/*.lean"):
        all_theorems.extend(scan_lean_file(lean_file))

    # Filter to requested theorems
    requested = set(theorem_names)
    return [t for t in all_theorems if t.name in requested]


async def generate_paper_content(
    title: str,
    theorems: list[TheoremCandidate],
    abstract_hint: str | None = None,
    authors: list[str] | None = None
) -> dict[str, str]:
    """
    Generate paper content using Claude API.

    Returns dict with keys: abstract, introduction, preliminaries,
    main_results, proof_section, conclusion, bibliography
    """
    settings = get_settings()

    if not settings.has_anthropic_key:
        return _generate_placeholder_content(title, theorems, authors)

    client = anthropic.Anthropic(api_key=settings.anthropic_api_key)

    # Build theorem descriptions
    theorem_text = "\n\n".join([
        f"**{t.name}** (from {t.file_path}:{t.line_number}):\n```lean\n{t.statement}\n```"
        for t in theorems
    ])

    prompt = f"""You are writing an academic mathematics paper. Generate LaTeX content for each section.

Title: {title}
Authors: {', '.join(authors) if authors else 'Anonymous'}

The paper formalizes the following theorems in Lean 4:

{theorem_text}

{f'Abstract guidance: {abstract_hint}' if abstract_hint else ''}

Generate content for each section. Use proper LaTeX math notation. Keep the tone formal and academic.
Output as JSON with keys: abstract, introduction, preliminaries, main_results, proof_section, conclusion, bibliography

For bibliography, include relevant citations in BibTeX-style format within the thebibliography environment.
"""

    try:
        response = client.messages.create(
            model=settings.anthropic_model,
            max_tokens=4096,
            messages=[{"role": "user", "content": prompt}]
        )

        # Parse response
        content = response.content[0].text

        # Try to extract JSON
        import json
        import re

        # Find JSON block
        json_match = re.search(r'\{[\s\S]*\}', content)
        if json_match:
            return json.loads(json_match.group())

        # Fallback: return as-is with placeholder structure
        return {
            "abstract": content[:500],
            "introduction": "See generated content.",
            "preliminaries": "",
            "main_results": theorem_text,
            "proof_section": "Formal proofs are provided in the accompanying Lean files.",
            "conclusion": "",
            "bibliography": ""
        }
    except Exception as e:
        return _generate_placeholder_content(title, theorems, authors, error=str(e))


def _generate_placeholder_content(
    title: str,
    theorems: list[TheoremCandidate],
    authors: list[str] | None = None,
    error: str | None = None
) -> dict[str, str]:
    """Generate placeholder content when API is unavailable."""
    theorem_latex = "\n\n".join([
        f"\\begin{{theorem}}[{t.name}]\n{_lean_to_latex(t.statement)}\n\\end{{theorem}}"
        for t in theorems
    ])

    return {
        "abstract": f"This paper presents formal proofs of {len(theorems)} theorem(s) "
                   f"related to {title}, verified in Lean 4 with Mathlib."
                   + (f" [API Error: {error}]" if error else ""),
        "introduction": f"We present machine-verified proofs of key results in combinatorics. "
                       f"All proofs have been formalized in Lean 4 using the Mathlib library.",
        "preliminaries": "We assume familiarity with standard combinatorics and graph theory notation.",
        "main_results": theorem_latex,
        "proof_section": "The formal proofs are available in the accompanying Lean source files. "
                        "Here we provide informal sketches of the key arguments.",
        "conclusion": "We have presented formal, machine-verified proofs of the stated results.",
        "bibliography": "\\bibitem{mathlib} The Mathlib Community. \\textit{Mathlib: A Lean Mathematics Library}. "
                       "\\url{https://github.com/leanprover-community/mathlib4}"
    }


def _lean_to_latex(statement: str) -> str:
    """Convert Lean statement to approximate LaTeX."""
    # Basic conversions
    result = statement
    result = result.replace("→", "\\to")
    result = result.replace("∀", "\\forall")
    result = result.replace("∃", "\\exists")
    result = result.replace("∈", "\\in")
    result = result.replace("⊆", "\\subseteq")
    result = result.replace("∪", "\\cup")
    result = result.replace("∩", "\\cap")
    result = result.replace("≤", "\\leq")
    result = result.replace("≥", "\\geq")
    result = result.replace("ℕ", "\\mathbb{N}")
    result = result.replace("ℤ", "\\mathbb{Z}")
    result = result.replace("ℝ", "\\mathbb{R}")
    result = result.replace("_", "\\_")

    return f"$${result}$$"


async def generate_paper(
    title: str,
    theorem_names: list[str],
    abstract_hint: str | None = None,
    authors: list[str] | None = None,
    template: str = "ejc"
) -> tuple[str, Optional[str]]:
    """
    Generate a complete LaTeX paper.

    Returns (latex_content, pdf_path or None)
    """
    # Extract theorem information
    theorems = extract_theorems_from_files(theorem_names)

    if not theorems:
        raise ValueError(f"No theorems found matching: {theorem_names}")

    # Generate content
    content = await generate_paper_content(title, theorems, abstract_hint, authors)

    # Load and fill template
    template_str = load_template(template)
    jinja_template = Template(template_str)

    latex = jinja_template.render(
        title=title,
        authors=", ".join(authors) if authors else "Anonymous",
        abstract=content.get("abstract", ""),
        introduction=content.get("introduction", ""),
        preliminaries=content.get("preliminaries", ""),
        main_results=content.get("main_results", ""),
        proof_section=content.get("proof_section", ""),
        conclusion=content.get("conclusion", ""),
        bibliography=content.get("bibliography", "")
    )

    # Try to compile PDF
    pdf_path = None
    try:
        pdf_path = compile_latex(latex, title)
    except Exception:
        pass

    return latex, pdf_path


def compile_latex(latex_content: str, title: str) -> Optional[str]:
    """
    Compile LaTeX to PDF.

    Returns path to PDF if successful, None otherwise.
    """
    import tempfile
    import shutil

    # Check if pdflatex is available
    if not shutil.which("pdflatex"):
        return None

    with tempfile.TemporaryDirectory() as tmpdir:
        tex_path = Path(tmpdir) / "paper.tex"
        tex_path.write_text(latex_content)

        try:
            # Run pdflatex twice for references
            for _ in range(2):
                subprocess.run(
                    ["pdflatex", "-interaction=nonstopmode", "paper.tex"],
                    cwd=tmpdir,
                    capture_output=True,
                    timeout=60
                )

            pdf_src = Path(tmpdir) / "paper.pdf"
            if pdf_src.exists():
                # Copy to output location
                safe_title = "".join(c for c in title if c.isalnum() or c in " -_")[:50]
                pdf_dest = Path(f"{safe_title}.pdf")
                shutil.copy(pdf_src, pdf_dest)
                return str(pdf_dest)
        except Exception:
            pass

    return None
