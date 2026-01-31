"""Find academic reviewers/experts via arXiv API."""

import arxiv
from collections import defaultdict

from .models import Reviewer, ReviewerFindResponse


def find_reviewers(
    keywords: list[str],
    max_results: int = 10,
    categories: list[str] | None = None
) -> ReviewerFindResponse:
    """
    Find academic experts based on arXiv papers.

    Args:
        keywords: Research keywords to search for
        max_results: Maximum number of reviewers to return
        categories: arXiv categories to search (default: math.CO, cs.DM)

    Returns:
        ReviewerFindResponse with found reviewers
    """
    if categories is None:
        categories = ["math.CO", "cs.DM"]

    # Build search query
    keyword_query = " OR ".join(f'"{kw}"' for kw in keywords)
    category_query = " OR ".join(f"cat:{cat}" for cat in categories)
    query = f"({keyword_query}) AND ({category_query})"

    # Search arXiv
    client = arxiv.Client()
    search = arxiv.Search(
        query=query,
        max_results=max_results * 5,  # Get more to filter
        sort_by=arxiv.SortCriterion.Relevance
    )

    # Aggregate authors
    author_papers: dict[str, list[tuple[str, str]]] = defaultdict(list)

    try:
        results = list(client.results(search))
    except Exception:
        results = []

    for paper in results:
        for author in paper.authors:
            author_name = author.name
            author_papers[author_name].append((paper.title, paper.entry_id))

    # Sort by number of relevant papers
    sorted_authors = sorted(
        author_papers.items(),
        key=lambda x: len(x[1]),
        reverse=True
    )[:max_results]

    reviewers = []
    for author_name, papers in sorted_authors:
        reviewers.append(Reviewer(
            name=author_name,
            affiliation=None,  # arXiv doesn't reliably provide this
            email=None,  # Privacy: don't extract emails
            relevant_papers=[p[0] for p in papers[:3]],
            arxiv_ids=[p[1].split("/")[-1] for p in papers[:3]]
        ))

    return ReviewerFindResponse(
        reviewers=reviewers,
        query_used=query
    )


async def find_reviewers_async(
    keywords: list[str],
    max_results: int = 10,
    categories: list[str] | None = None
) -> ReviewerFindResponse:
    """Async wrapper for find_reviewers."""
    import asyncio
    return await asyncio.to_thread(find_reviewers, keywords, max_results, categories)
