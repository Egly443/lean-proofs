# Lean 4 Neuro-Symbolic Bridge Tools

This file documents custom tools available for working with Lean 4 files in this repository. These tools provide a persistent, stateful interface to the Lean proof environment, avoiding the overhead of restarting Lean for every command.

## Tool Overview

The neuro-symbolic bridge provides:
- **Persistent Lean process**: Mathlib loaded once, reused for all commands
- **Stateful proof navigation**: Track proof context via state IDs
- **Structured JSON responses**: Parse goals, errors, and state transitions
- **Automated proof search**: BFS exploration with adaptive tactic learning

## Available Tools

### 1. Start Lean Server

**Purpose**: Initialize a persistent Lean REPL process with file imports loaded.

**Command**:
```bash
python lean_bridge.py server <filename.lean>
```

**Usage**:
- Run this FIRST before any other bridge operations
- This command blocks the terminal - run in background or separate terminal
- Wait for `[*] Server ready` message before proceeding
- Server loads all imports from the specified .lean file (typically takes 10-120s for Mathlib)

**When to use**:
- At the start of any Lean development session
- After stopping a previous server
- When switching to a different .lean file

**Example**:
```bash
# Start server for EnergyIncrement.lean
python lean_bridge.py server EnergyIncrement.lean
```

---

### 2. Execute Lean Command

**Purpose**: Run arbitrary Lean code (definitions, theorems, evaluations).

**Command**:
```bash
python lean_bridge.py cmd "<lean_code>"
```

**Usage**:
- Execute definitions, theorems, or evaluations
- Start new proofs (ending with `:= by sorry`)
- Returns JSON with messages, errors, and proof state IDs

**When to use**:
- Test expressions with `#eval` or `#check`
- Define helper functions or lemmas
- Initialize a new proof (captures initial proof state ID)
- Verify syntax without modifying .lean files

**Parameters**:
- `<lean_code>`: Any valid Lean 4 code

**Response Format**:
```json
{
  "status": "success",
  "response": {
    "messages": [...],
    "sorries": [
      {
        "proofState": 0,
        "goal": "n : Nat ⊢ n + 0 = n"
      }
    ],
    "env": 1
  }
}
```

**Examples**:
```bash
# Evaluate an expression
python lean_bridge.py cmd "#eval 2 + 2"

# Check a type
python lean_bridge.py cmd "#check Nat.add_comm"

# Start a proof
python lean_bridge.py cmd "example (n : Nat) : n + 0 = n := by sorry"
```

**Key output**:
- Extract `proofState` ID from `sorries[0].proofState` for use with tactic commands
- Check `messages` for errors or warnings

---

### 3. Apply Tactic

**Purpose**: Execute a single proof tactic on a specific proof state.

**Command**:
```bash
python lean_bridge.py tactic "<tactic_code>" --id <state_id>
```

**Usage**:
- Apply tactics to progress a proof
- Navigate the proof tree by state ID
- Get updated goals and new state ID after each step

**When to use**:
- After initializing a proof with `cmd`
- To apply proof steps iteratively
- To explore different proof branches

**Parameters**:
- `<tactic_code>`: A Lean tactic (e.g., `intro n`, `rw [Nat.add_comm]`, `simp`)
- `--id <state_id>`: The proof state ID from previous command/tactic

**Response Format** (success):
```json
{
  "status": "success",
  "goals": ["n : Nat\n⊢ n + 0 = n"],
  "new_state_id": 5
}
```

**Response Format** (proof complete):
```json
{
  "status": "success",
  "goals": [],
  "new_state_id": 6
}
```

**Response Format** (error):
```json
{
  "status": "error",
  "message": "tactic 'intro' failed, ..."
}
```

**Examples**:
```bash
# Apply intro tactic to state 0
python lean_bridge.py tactic "intro n" --id 0

# Apply induction on state 5
python lean_bridge.py tactic "induction n" --id 5

# Try simplification
python lean_bridge.py tactic "simp [Nat.add_zero]" --id 7
```

**Key output**:
- If `goals` is empty `[]`: **Proof complete!**
- If `goals` has items: Use `new_state_id` for next tactic
- If error: Try different tactic on same state ID (state unchanged on failure)

---

### 4. Automated Proof Search

**Purpose**: Run BFS-based automated proof search with adaptive tactic learning.

**Command**:
```bash
python agent.py
```

**Usage**:
- BEFORE running: Edit `agent.py` to configure:
  - `THEOREM` (line 195): Set to the proof statement ending with `:= by sorry`
  - `BASE_TACTICS` (lines 16-26): List of tactics to try
- Requires server to be running first
- Explores proof tree automatically using BFS
- Learns which tactics work best and saves to `agent_memory.json`

**When to use**:
- To automate proof search for routine theorems
- To discover proof paths for well-structured goals
- When you have a library of likely tactics

**Configuration**:
Edit lines in `agent.py`:
```python
# Line 195 - Set your theorem
THEOREM = "example (n : Nat) : n + 0 = n := by sorry"

# Lines 16-26 - Customize tactic library
BASE_TACTICS = [
    "intro n",
    "induction n",
    "simp",
    "ring",
    "assumption",
]
```

**Output**:
- Progress updates every 10 steps
- On success: Prints complete tactic sequence
- On failure/timeout: Saves stuck goals to `agent_memory.json`

**Memory/Learning**:
- First run: Tries tactics in BASE_TACTICS order
- Subsequent runs: Reorders tactics based on past success (learns from `agent_memory.json`)
- Check `agent_memory.json` to see what the agent was stuck on

**Example**:
```bash
# 1. Start server (in separate terminal)
python lean_bridge.py server EnergyIncrement.lean

# 2. Edit agent.py to set THEOREM and tactics

# 3. Run agent
python agent.py

# Output:
# [*] Search started. Max Steps=600
# [Step 10] Q: 15 | Best Tactic: intro n
# [Step 20] Q: 23 | Best Tactic: simp
# ...
# [!!!] PROOF FOUND! [!!!]
# Solution Path:
#   -> intro n (State 1)
#   -> induction n (State 2)
#   -> simp (State 3)
```

---

### 5. Stop Server

**Purpose**: Cleanly terminate the Lean server process.

**Command**:
```bash
python lean_bridge.py stop
```

**Usage**:
- Stops the running Lean server
- Cleans up socket connection
- Required before starting a new server on the same file

**When to use**:
- When finished with Lean session
- Before switching to a different .lean file
- If server becomes unresponsive

---

## Typical Workflows

### Workflow 1: Interactive Proof Development

```bash
# Terminal 1: Start server
python lean_bridge.py server EnergyIncrement.lean
# Wait for "[*] Server ready"

# Terminal 2: Interactive commands
python lean_bridge.py cmd "example (n : Nat) : n + 0 = n := by sorry"
# Note the proofState ID (e.g., 0)

python lean_bridge.py tactic "intro n" --id 0
# Note new state ID (e.g., 1)

python lean_bridge.py tactic "induction n" --id 1
# Continue until goals = []

# When done
python lean_bridge.py stop
```

### Workflow 2: Automated Proof Search

```bash
# Terminal 1: Start server
python lean_bridge.py server EnergyIncrement.lean

# Terminal 2: Run agent
# (After editing agent.py with THEOREM and tactics)
python agent.py

# Agent explores automatically, prints solution path
# Apply solution to your .lean file

# When done
python lean_bridge.py stop
```

### Workflow 3: Testing and Exploration

```bash
# Start server
python lean_bridge.py server EnergyIncrement.lean

# Test available lemmas
python lean_bridge.py cmd "#check Finset.sum_congr"

# Evaluate expressions
python lean_bridge.py cmd "#eval [1, 2, 3].sum"

# Check if tactic works on a goal
python lean_bridge.py cmd "example : 2 + 2 = 4 := by sorry"
python lean_bridge.py tactic "norm_num" --id 0

# Stop when done
python lean_bridge.py stop
```

## Important Notes

### State Management
- **State IDs are proof-specific**: Each theorem has its own state tree
- **Failed tactics don't change state**: Reuse same ID after errors
- **Multiple goals**: State ID tracks ALL current goals, solving one returns new state with remaining goals

### Socket Communication
- Bridge uses Unix domain socket: `.lean_bridge.sock`
- Socket auto-created when server starts
- Socket auto-removed when server stops
- If "Connection Refused": Server not running or crashed

### Performance
- **First build**: Downloads Mathlib (~2GB), takes 10-30 minutes
- **Server startup**: Loading Mathlib takes 10-120 seconds
- **Command latency**: ~100ms per command after initialization
- **Agent search**: Can take minutes for complex proofs (MAX_STEPS = 600)

### Troubleshooting
- **Broken pipe**: Server crashed, check server terminal for errors
- **JSON decode error**: Severe Lean compilation error, check syntax
- **Timeout**: Increase timeout on line 75 of `lean_bridge.py` (default: 120s)
- **Agent stuck**: Check `agent_memory.json` for problematic goals

## Integration with Claude Code

When Claude Code works on .lean files in this repository, it can:

1. **Start the bridge server** as a background process
2. **Test theorems interactively** using `cmd` and `tactic` commands
3. **Automate routine proofs** by configuring and running `agent.py`
4. **Verify solutions** before writing to .lean files
5. **Explore available tactics** for specific goal types

The bridge enables rapid iteration without file modification overhead, making it ideal for:
- Exploring proof strategies
- Testing tactic combinations
- Verifying partial solutions
- Automating mechanical proofs
