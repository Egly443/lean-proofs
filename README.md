# Energy Increment Lemma: A Compressed Formalization

A Lean 4 skeleton for formalizing the energy increment lemma from Szemerédi's Regularity Lemma, using an L²-projection approach that minimizes combinatorial bookkeeping.

## Quick Start with GitHub Codespaces

**One-click setup:** Open this repository in GitHub Codespaces for a fully configured Lean 4 + Python environment.

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/brian-sanders/lean-proofs)

The Codespace automatically:
- Installs Lean 4.8.0 via elan
- Downloads Mathlib cache (~2GB, runs on container creation)
- Installs Python dependencies
- Forwards port 8000 for the orchestrator API

## Proof-to-Publication Orchestrator

A turnkey pipeline for automated theorem proving and academic paper generation.

### Starting the Orchestrator

```bash
# Install dependencies (if not in Codespaces)
pip install -r requirements.txt

# Start the API server (port 8000)
python -m orchestrator.server
```

### API Endpoints

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/health` | GET | Health check and Lean bridge status |
| `/candidates` | POST | Scan for theorems with `sorry` |
| `/proof/start` | POST | Start async proof attempt |
| `/proof/status/{id}` | GET | Check proof progress |
| `/proof/list` | GET | List all proof jobs |
| `/paper/generate` | POST | Generate LaTeX paper |
| `/reviewers/find` | POST | Find academic experts via arXiv |
| `/emails/draft` | POST | Draft outreach emails |

### Example Workflow

**1. Check health and Lean bridge status:**
```bash
curl http://localhost:8000/health
```

**2. Scan for provable theorems:**
```bash
curl -X POST http://localhost:8000/candidates \
  -H "Content-Type: application/json" \
  -d '{"source": "local"}'
```

**3. Start the Lean bridge (required for proof attempts):**
```bash
# In a separate terminal
python lean_bridge.py server EnergyIncrement.lean
```

**4. Start a proof attempt:**
```bash
curl -X POST http://localhost:8000/proof/start \
  -H "Content-Type: application/json" \
  -d '{
    "theorem": "example (n : Nat) : n + 0 = n := by sorry",
    "lean_file": "EnergyIncrement.lean",
    "max_steps": 100
  }'
```

**5. Check proof status:**
```bash
curl http://localhost:8000/proof/status/{job_id}
```

**6. Generate a paper:**
```bash
curl -X POST http://localhost:8000/paper/generate \
  -H "Content-Type: application/json" \
  -d '{
    "title": "Formal Proof of the Energy Increment Lemma",
    "theorems": ["energy_increment", "variance_lower_bound"],
    "authors": ["Your Name"],
    "template": "ejc"
  }'
```

**7. Find reviewers:**
```bash
curl -X POST http://localhost:8000/reviewers/find \
  -H "Content-Type: application/json" \
  -d '{
    "keywords": ["Szemeredi regularity", "graph theory"],
    "max_results": 5
  }'
```

**8. Draft outreach email:**
```bash
curl -X POST http://localhost:8000/emails/draft \
  -H "Content-Type: application/json" \
  -d '{
    "reviewer": {"name": "Prof. Example", "relevant_papers": ["Related Paper"]},
    "paper_title": "Formal Proof of the Energy Increment Lemma",
    "paper_abstract": "We present machine-verified proofs...",
    "sender_name": "Your Name"
  }'
```

### Configuration

Create a `.env` file (see `.env.example`):

```bash
# Required for paper generation and email drafting
ANTHROPIC_API_KEY=sk-ant-...

# Optional
ORCHESTRATOR_PORT=8000
LEAN_FILES_DIR=.
```

---

## Mathematical Approach

The traditional proof of the energy increment lemma involves extensive case analysis over partition refinements. This formalization takes a different approach:

**Key insight:** The energy functional is the squared L² norm of the partition-conditional edge density. Refinement corresponds to conditioning on a finer σ-algebra, and the energy increment is the variance of that conditioning—a direct consequence of the Pythagorean theorem in Hilbert spaces.

### Core Lemmas (5 total)

| Lemma | Role | Difficulty |
|-------|------|------------|
| `energy_refinement_increment` | Pythagoras: increment = squared difference | Medium |
| `energy_monotone` | Corollary: refinement never decreases energy | Easy |
| `energy_bounded` | Energy ∈ [0,1] for termination | Easy |
| `irregular_has_witness` | Choice principle for witnesses | Easy |
| `energy_increment_lemma` | Main result: ε⁴ lower bound | Medium |

### Proof Strategy

```
                    ┌─────────────────────────────┐
                    │  Irregularity of (A,B)      │
                    │  ∃ X⊆A, Y⊆B witnessing     │
                    │  |d(X,Y) - d(A,B)| ≥ ε     │
                    └──────────────┬──────────────┘
                                   │
                                   ▼
         ┌─────────────────────────────────────────────────┐
         │  Refine partition: split A by X, split B by Y   │
         └──────────────────────────┬──────────────────────┘
                                    │
                                    ▼
    ┌───────────────────────────────────────────────────────────┐
    │  Energy increment = Σ (weight) × (density deviation)²    │
    │                                                           │
    │  ≥ (|X||Y|/|V|²) × ε²     [deviation from irregularity]  │
    │  ≥ (ε²|A||B|/|V|²) × ε²   [witness size lower bound]     │
    │  = ε⁴ × weight(A,B)                                       │
    └───────────────────────────────────────────────────────────┘
```

## Building Lean Files

```bash
# Install elan (Lean version manager) if needed
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Get dependencies and build
lake update
lake build
```

**Note:** First build downloads Mathlib (~2GB) and takes 10-30 minutes.

## Neuro-Symbolic Bridge

The bridge maintains a persistent Lean process to avoid reloading Mathlib on every command.

### Start the Server
```bash
python lean_bridge.py server EnergyIncrement.lean
# Wait for "[*] Server ready" before proceeding
```

### Client Commands
```bash
# Execute a command
python lean_bridge.py cmd "#eval 1 + 1"

# Apply a tactic (requires proofState ID)
python lean_bridge.py tactic "intro n" --id 0

# Stop the server
python lean_bridge.py stop
```

### Automated Proof Search
```bash
python agent.py
```

## Completing the Formalization

The `sorry`s fall into categories:

### Category 1: Routine Set Theory
- Partition constructions in `refineByWitness`
- These just need careful tracking of subset relations

### Category 2: Reindexing
- `energy_eq_energy'`: Converting between sum over parts and sum over vertices
- Standard bigop manipulation

### Category 3: The Core Inequality
- `energy_increment_lemma`: The actual mathematics
- Requires: variance decomposition + witness bounds

### Suggested Order of Attack

1. **`energy_bounded`** — Warm-up, just convexity
2. **`energy_monotone`** — Follows from sum-of-squares ≥ 0
3. **`irregular_has_witness`** — Classical logic unwinding
4. **`refineByWitness` fields** — Tedious but straightforward
5. **`energy_refinement_increment`** — The key algebraic identity
6. **`energy_increment_lemma`** — Assemble the pieces

## Comparison with Traditional Approaches

| Aspect | Textbook Proof | This Approach |
|--------|----------------|---------------|
| Case distinctions | Many (pair types, edge cases) | Zero |
| Auxiliary lemmas | ~15 | ~5 |
| Core principle | Counting + averaging | L² projection |
| ε-bookkeeping | Extensive | Minimal |
| Conceptual clarity | Obscured by details | Manifest |

## Extensions

The same framework applies to:

- **Hypergraph regularity**: Replace edge density with k-uniform hyperedge density; energy becomes a tensor norm
- **Sparse regularity**: Weight the probability measure by a density function
- **Frieze-Kannan weak regularity**: Use cut-norm instead of L²; weaker but faster convergence

## References

1. Szemerédi, E. (1978). Regular partitions of graphs. *Problèmes combinatoires et théorie des graphes*.
2. Komlós, J., & Simonovits, M. (1996). Szemerédi's regularity lemma and its applications in graph theory. *Combinatorics, Paul Erdős is eighty*.
3. Tao, T. (2006). Szemerédi's regularity lemma revisited. *Contrib. Discrete Math.*
4. Mathlib contributors. *Mathlib4*. https://github.com/leanprover-community/mathlib4

## License

MIT
