/-
  SmithReduction: Lean 4 library root module

  This module serves as the entry point for the SmithReduction library.
  Individual formalizations can be imported from here.
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Algebra.GCDMonoid.Basic

namespace SmithReduction

variable {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Row operation: add a scalar multiple of row i₂ to row i₁ -/
noncomputable def rowOp (A : Matrix m n R) (i₁ i₂ : m) (c : R) : Matrix m n R :=
  Matrix.updateRow A i₁ (A i₁ + c • A i₂)

/-- Column operation: add a scalar multiple of column j₂ to column j₁ -/
noncomputable def colOp (A : Matrix m n R) (j₁ j₂ : n) (c : R) : Matrix m n R :=
  Matrix.updateColumn A j₁ (fun i => A i j₁ + c * A i j₂)

/-- Row operation preserves other rows -/
theorem rowOp_other (A : Matrix m n R) (i₁ i₂ i : m) (c : R) (hi : i ≠ i₁) :
    rowOp A i₁ i₂ c i = A i := by
  simp [rowOp, Matrix.updateRow_ne hi]

/-- Row operation on the target row -/
theorem rowOp_self (A : Matrix m n R) (i₁ i₂ : m) (c : R) :
    rowOp A i₁ i₂ c i₁ = A i₁ + c • A i₂ := by
  simp [rowOp, Matrix.updateRow_self]

end SmithReduction
