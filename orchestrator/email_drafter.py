"""Draft personalized academic outreach emails."""

import anthropic

from .models import Reviewer, EmailDraftResponse
from .config import get_settings


async def draft_email(
    reviewer: Reviewer,
    paper_title: str,
    paper_abstract: str,
    sender_name: str,
    sender_affiliation: str | None = None
) -> EmailDraftResponse:
    """
    Draft a personalized outreach email to a potential reviewer.

    Args:
        reviewer: The reviewer to contact
        paper_title: Title of the paper
        paper_abstract: Abstract of the paper
        sender_name: Name of the sender
        sender_affiliation: Sender's institution (optional)

    Returns:
        EmailDraftResponse with subject and body
    """
    settings = get_settings()

    if not settings.has_anthropic_key:
        return _generate_template_email(reviewer, paper_title, sender_name, sender_affiliation)

    client = anthropic.Anthropic(api_key=settings.anthropic_api_key)

    # Build context about reviewer's work
    reviewer_context = f"Reviewer: {reviewer.name}"
    if reviewer.relevant_papers:
        reviewer_context += f"\nTheir relevant papers: {', '.join(reviewer.relevant_papers[:3])}"

    prompt = f"""Draft a professional academic email requesting feedback on a research paper.

{reviewer_context}

Paper Title: {paper_title}
Paper Abstract: {paper_abstract}

Sender: {sender_name}
{f"Affiliation: {sender_affiliation}" if sender_affiliation else ""}

Requirements:
1. Be respectful and professional
2. Reference the reviewer's relevant work if known
3. Be concise (under 200 words for body)
4. Include a clear subject line
5. Don't be presumptuous about their time

Output format:
SUBJECT: [subject line]
BODY:
[email body]
"""

    try:
        response = client.messages.create(
            model=settings.anthropic_model,
            max_tokens=1024,
            messages=[{"role": "user", "content": prompt}]
        )

        content = response.content[0].text

        # Parse response
        lines = content.strip().split("\n")
        subject = ""
        body_lines = []
        in_body = False

        for line in lines:
            if line.startswith("SUBJECT:"):
                subject = line.replace("SUBJECT:", "").strip()
            elif line.startswith("BODY:"):
                in_body = True
            elif in_body:
                body_lines.append(line)

        body = "\n".join(body_lines).strip()

        if not subject:
            subject = f"Request for Feedback: {paper_title}"
        if not body:
            body = content

        return EmailDraftResponse(
            subject=subject,
            body=body,
            reviewer_name=reviewer.name
        )
    except Exception as e:
        result = _generate_template_email(reviewer, paper_title, sender_name, sender_affiliation)
        result.body += f"\n\n[Note: API error occurred: {e}]"
        return result


def _generate_template_email(
    reviewer: Reviewer,
    paper_title: str,
    sender_name: str,
    sender_affiliation: str | None = None
) -> EmailDraftResponse:
    """Generate a template email when API is unavailable."""
    subject = f"Request for Feedback: {paper_title}"

    affiliation_line = f" at {sender_affiliation}" if sender_affiliation else ""

    paper_reference = ""
    if reviewer.relevant_papers:
        paper_reference = f"\n\nI came across your work on \"{reviewer.relevant_papers[0]}\" and believe your expertise would be particularly valuable for this paper."

    body = f"""Dear {reviewer.name},

I hope this email finds you well. My name is {sender_name}{affiliation_line}.

I am writing to respectfully request your feedback on a recent paper titled "{paper_title}".{paper_reference}

The paper presents formal, machine-verified proofs of key results in combinatorics, developed using Lean 4 and Mathlib.

I understand you have many demands on your time, and I would greatly appreciate any feedback you might be able to provide, however brief.

Thank you for considering this request.

Best regards,
{sender_name}"""

    return EmailDraftResponse(
        subject=subject,
        body=body,
        reviewer_name=reviewer.name
    )


async def draft_emails_batch(
    reviewers: list[Reviewer],
    paper_title: str,
    paper_abstract: str,
    sender_name: str,
    sender_affiliation: str | None = None
) -> list[EmailDraftResponse]:
    """Draft emails to multiple reviewers."""
    import asyncio

    tasks = [
        draft_email(r, paper_title, paper_abstract, sender_name, sender_affiliation)
        for r in reviewers
    ]
    return await asyncio.gather(*tasks)
