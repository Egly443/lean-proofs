# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This project formalizes the energy increment lemma from Szemerédi's Regularity Lemma in Lean 4, using an L²-projection approach. It includes a neuro-symbolic bridge that enables automated interaction with Lean's proof system for BFS-based proof search.

## Key Commands

### Building and Development

```bash
# First-time setup (downloads ~2GB of Mathlib, takes 10-30 minutes)
lake update
lake build

# After modifying .lean files
lake build
```

### Neuro-Symbolic Bridge Workflow

The bridge maintains a persistent Lean process to avoid reloading Mathlib on every command.

#### 1. Start the Server
```bash
# Start in one terminal (blocks that terminal)
python lean_bridge.py server <filename.lean>
# Wait for "[*] Server ready" before proceeding
```

#### 2. Interact via Client Commands

**Execute a command** (definitions, evaluations, start proofs):
```bash
python lean_bridge.py cmd "<lean_code>"
# Example: python lean_bridge.py cmd "#eval 1 + 1"
# Example: python lean_bridge.py cmd "example (n : Nat) : n + 0 = n := by sorry"
```

**Apply a tactic** (requires proofState ID from previous command):
```bash
python lean_bridge.py tactic "<tactic_code>" --id <state_id>
# Example: python lean_bridge.py tactic "intro n" --id 0
```

**Stop the server**:
```bash
python lean_bridge.py stop
```

#### 3. Automated Proof Search

The agent performs BFS over the proof tree with adaptive tactic ordering:

```bash
python agent.py
```

**Before running**: Modify `agent.py` to set:
- `THEOREM`: The proof statement (ending with `:= by sorry`)
- `BASE_TACTICS`: List of tactics to try (agent learns which work best)

**Agent memory**: Saves learning statistics to `agent_memory.json`, which speeds up subsequent runs by prioritizing successful tactics.

## Architecture

### Lean Formalization (EnergyIncrement.lean)

The proof uses an L² projection framework to minimize combinatorial bookkeeping:

1. **Core principle**: Energy = ‖d_𝒫‖²₂ (squared L² norm of partition-conditional edge density)
2. **Key insight**: Refinement = conditioning on finer σ-algebra; increment = variance (Pythagoras)
3. **Main result**: Irregularity witnesses imply ε⁴ energy increment

**Structure**:
- Lines 31-35: `edgeDensity` - edge density between vertex sets
- Lines 37-43: `IsIrregular` - ε-irregularity with witness sets
- Lines 45-49: `energy` - energy functional of a partition
- Lines 216-252: `variance_lower_bound` - core inequality showing irregularity → ε⁴ increment
- Lines 279-305: `energy_increment` - main theorem (currently has sorry)

**Categories of sorries**:
1. Routine set theory (partition constructions in `refinePartition`)
2. Reindexing lemmas (sum manipulations, line 266)
3. Union properties (line 277)
4. Core inequality assembly (line 305)
5. Termination argument (line 341)

### Neuro-Symbolic Bridge

**lean_bridge.py**: Infrastructure layer
- Wraps Lean's REPL binary in a persistent process
- Exposes Unix domain socket (.lean_bridge.sock) for client connections
- Parses Lean's JSON responses into structured format
- Maintains proof state IDs for navigating the proof tree

**agent.py**: Search algorithm (BFS with learning)
- Breadth-first exploration of proof tree
- Dynamic tactic reordering based on success rates
- Loop detection via goal hashing
- Saves learning metrics to `agent_memory.json`

**Key architectural pattern**:
- Server maintains single Lean process → no recompilation overhead
- State IDs track proof context → enables tree navigation
- JSON protocol → structured error handling and goal tracking

### State Management

Lean uses integer `proofState` IDs to track proof context:
- Initial proof creates state ID 0
- Each successful tactic returns new state ID
- Failed tactics return error message (state unchanged)
- Empty goals list `[]` indicates proof complete

**JSON Response Structure**:

Success with pending goals:
```json
{
  "status": "success",
  "goals": ["n : Nat ⊢ n + 0 = n"],
  "new_state_id": 5
}
```

Success (proof complete):
```json
{
  "status": "success",
  "goals": [],
  "new_state_id": 6
}
```

Error:
```json
{
  "status": "error",
  "message": "tactic failed"
}
```

## Configuration Files

- **lakefile.lean**: Lake build configuration
  - Package name: `SmithReduction` (note: name differs from project focus)
  - Mathlib version: v4.8.0
  - Optional REPL dependency for interactive use
  - Source directory: `src/` (defined but directory doesn't exist; .lean files in root)

## Troubleshooting

**"Broken Pipe" / "Connection Refused"**: Server crashed or not running. Check server terminal for Lean errors, restart server.

**"Expecting value..." (JSON Error)**: Non-JSON output mixed with response. Severe crash in Lean compilation.

**Heavy import timeout**: Mathlib initialization takes 30s+. Increase timeout in `lean_bridge.py` line 75 (currently 120s) if needed.

**Multiple goals**: Response `["goal1", "goal2"]` means current focus is goal1. Same state ID tracks entire goal set. Solving goal1 returns new state with only `["goal2"]`.
