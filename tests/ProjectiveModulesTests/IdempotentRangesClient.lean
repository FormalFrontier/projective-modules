/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.LinearAlgebra.Matrix.IdempotentRanges

/-!
# First-coordinate ranges

The first-coordinate projection in dimension two and the identity in dimension one
have equivalent right-column ranges. The range equivalence sends a column to its first
coordinate, and the same rectangular factors give witnesses for the equivalence criterion.
-/

open scoped Matrix

namespace Matrix

private def A : Matrix (Fin 2) (Fin 2) ℕ :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

private def B : Matrix (Fin 1) (Fin 1) ℕ := fun _ _ => 1

private def X : Matrix (Fin 2) (Fin 1) ℕ :=
  fun i _ => if i = 0 then 1 else 0

private def Y : Matrix (Fin 1) (Fin 2) ℕ :=
  fun _ j => if j = 0 then 1 else 0

private theorem hA : A * A = A := by decide

private theorem hB : B * B = B := by decide

private theorem hXY : X * Y = A := by decide

private theorem hYX : Y * X = B := by decide

example (v : LinearMap.range (Matrix.mulVecBilin ℕ ℕᵐᵒᵖ A)) :
    (rangeEquivOfMulEq A B hA hB X Y hXY hYX v : Fin 1 → ℕ) 0 =
        (v : Fin 2 → ℕ) 0 ∧
      Nonempty
        (LinearMap.range (Matrix.mulVecBilin ℕ ℕᵐᵒᵖ A) ≃ₗ[ℕᵐᵒᵖ]
          LinearMap.range (Matrix.mulVecBilin ℕ ℕᵐᵒᵖ B)) := by
  constructor
  · simp [Y, Matrix.mulVec, dotProduct]
  · exact (nonempty_rangeEquiv_iff_exists_mul_eq A B hA hB).2
      ⟨X, Y, hXY, hYX⟩

end Matrix
