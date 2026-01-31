import Lake
open Lake DSL

-- Project package
package SmithReduction where
  -- no extra fields needed

-- Lean 4 mathlib dependency
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"

-- Optional: REPL for Lean 4
require REPL from git
  "https://github.com/leanprover-community/repl" @ "439687b"

-- Library target
@[default_target]
lean_lib SmithReduction where
  srcDir := "src"
