/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.RightRegular
public import ProjectiveModules.Category.FiniteProjective
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.Int.Basic
public import Mathlib.Data.Matrix.Basis

/-!
# Ordinary-carrier right regular module clients

The ordinary carrier of any ring can be bundled by `FiniteProjective.of` with
opposite-ring scalars, without extra freeness or finiteness hypotheses. These
clients use Mathlib's existing same-scalar opposite equivalence and test the
right-action convention on noncommuting integer matrices. The zero ring and
a semiring without additive inverses are also included.
-/

@[expose] public section

universe u

namespace ProjectiveModulesTests.RightRegularModuleClient

/-- The finite-projective constructor accepts the ordinary right regular
carrier of an arbitrary, possibly noncommutative ring. -/
theorem ordinary_regular_equiv (R : Type u) [Ring R] :
    Nonempty ((ModuleCat.FiniteProjective.of Rᵐᵒᵖ R) ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) :=
  ⟨MulOpposite.opLinearEquiv Rᵐᵒᵖ⟩

/-- Bundling the ordinary carrier retains multiplication on the right. -/
theorem ordinary_regular_right_action (R : Type u) [Ring R] (a : R)
    (x : ModuleCat.FiniteProjective.of Rᵐᵒᵖ R) :
    (MulOpposite.op a • x : R) = x * a :=
  op_smul_eq_mul a x

/-- The same constructor accepts the noncommutative ring of two-by-two
integer matrices on its ordinary carrier. -/
theorem matrix_regular_equiv :
    Nonempty ((ModuleCat.FiniteProjective.of (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ
      (Matrix (Fin 2) (Fin 2) ℤ)) ≃ₗ[(Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ]
        (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ) :=
  ordinary_regular_equiv _

/-- Opposite scalars act on the right, not on the left, as witnessed by two
matrix units that do not commute. -/
theorem matrix_right_action_ne_left :
    MulOpposite.op (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℤ) •
        (Matrix.single 1 0 1 : Matrix (Fin 2) (Fin 2) ℤ) ≠
      Matrix.single 0 1 1 * (Matrix.single 1 0 1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [op_smul_eq_mul]
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ ↦ M 0 0) h
  simp at hentry

/-- The zero ring is not excluded from the ordinary-carrier constructor. -/
theorem zero_ring_regular :
    Nonempty ((ModuleCat.FiniteProjective.of PUnit.{1}ᵐᵒᵖ PUnit.{1})
      ≃ₗ[PUnit.{1}ᵐᵒᵖ] PUnit.{1}ᵐᵒᵖ) ∧
      Subsingleton (ModuleCat.FiniteProjective.of PUnit.{1}ᵐᵒᵖ PUnit.{1}) :=
  ⟨ordinary_regular_equiv _, inferInstance⟩

/-- Freeness, finiteness and derived projectivity also hold for a semiring
without additive inverses. -/
theorem nat_right_regular :
    Module.Free ℕᵐᵒᵖ ℕ ∧ Module.Finite ℕᵐᵒᵖ ℕ ∧ Module.Projective ℕᵐᵒᵖ ℕ :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end ProjectiveModulesTests.RightRegularModuleClient
