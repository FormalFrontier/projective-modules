/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Free.StablePresentation
import ProjectiveModules.Free.InvariantBasisNumber
import Mathlib.Algebra.Module.Equiv.Opposite
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite stable presentation clients

Finite coordinate modules admit presentations with different complements,
including an empty one. Reindexing the coordinates across universes exercises
the numerical results over a semiring. Opposite scalars express a right-module
example; infinite free coordinates distinguish stable freeness from finite
generation.

The coordinate assembly and opposite-scalar translation follow the finite-
coordinate constructions previously formalized by Prism in Formal Frontier's
Weibel K-book research.
-/

private noncomputable def finProdEquiv (R : Type*) [Semiring R] (m n : ℕ) :
    ((Fin m → R) × (Fin n → R)) ≃ₗ[R] (Fin (m + n) → R) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin n) R R).symm.trans
    (LinearEquiv.funCongrLeft R R finSumFinEquiv).symm

private noncomputable def naturalEmptyPresentation :
    ((Fin 1 → ℕ) × (ULift.{1} (Fin 0) → ℕ)) ≃ₗ[ℕ]
      (ULift.{2} (Fin 1) → ℕ) :=
  ((LinearEquiv.refl ℕ (Fin 1 → ℕ)).prodCongr
    (LinearEquiv.funCongrLeft ℕ ℕ (Equiv.ulift : ULift.{1} (Fin 0) ≃ Fin 0)).symm).trans
      ((finProdEquiv ℕ 1 0).trans
        (LinearEquiv.funCongrLeft ℕ ℕ (Equiv.ulift : ULift.{2} (Fin 1) ≃ Fin 1)))

private noncomputable def naturalLargerPresentation :
    ((Fin 1 → ℕ) × (ULift.{3} (Fin 2) → ℕ)) ≃ₗ[ℕ]
      (ULift.{4} (Fin 3) → ℕ) :=
  ((LinearEquiv.refl ℕ (Fin 1 → ℕ)).prodCongr
    (LinearEquiv.funCongrLeft ℕ ℕ (Equiv.ulift : ULift.{3} (Fin 2) ≃ Fin 2)).symm).trans
      ((finProdEquiv ℕ 1 2).trans
        (LinearEquiv.funCongrLeft ℕ ℕ (Equiv.ulift : ULift.{4} (Fin 3) ≃ Fin 3)))

private theorem natural_cross_sum_from_two_presentations :
    1 + 2 = 3 + 0 := by
  have h := Module.card_add_card_eq_of_prod_linearEquiv ℕ (Fin 1 → ℕ)
    naturalEmptyPresentation naturalLargerPresentation
  convert h using 1 <;> simp only [Fintype.card_ulift, Fintype.card_fin]

private theorem natural_integer_rank_from_two_presentations :
    (1 : ℤ) - 0 = 3 - 2 := by
  have h := Module.int_card_sub_eq_of_prod_linearEquiv ℕ (Fin 1 → ℕ)
    naturalEmptyPresentation naturalLargerPresentation
  simpa only [Fintype.card_ulift, Fintype.card_fin, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] using h

private theorem integer_coordinates_finite_stably_free :
    Module.Finite ℤ (Fin 1 → ℤ) ∧ Module.IsStablyFree ℤ (Fin 1 → ℤ) :=
  (Module.exists_fin_prod_linearEquiv_iff_finite_isStablyFree ℤ (Fin 1 → ℤ)).mp
    ⟨0, 1, ⟨finProdEquiv ℤ 1 0⟩⟩

private theorem integer_coordinates_have_a_finite_presentation :
    ∃ m n : ℕ, Nonempty (((Fin 1 → ℤ) × (Fin m → ℤ)) ≃ₗ[ℤ] (Fin n → ℤ)) :=
  (Module.exists_fin_prod_linearEquiv_iff_finite_isStablyFree ℤ (Fin 1 → ℤ)).mpr
    ⟨inferInstance, inferInstance⟩

private theorem infinite_free_coordinates_are_not_finite :
    Module.IsStablyFree ℤ (ℕ →₀ ℤ) ∧ ¬ Module.Finite ℤ (ℕ →₀ ℤ) :=
  ⟨inferInstance, Module.not_finite_of_infinite_basis (Finsupp.basisSingleOne (R := ℤ))⟩

private noncomputable def rightCoordEquiv (n : ℕ) :
    (Fin n → ℤ) ≃ₗ[ℤᵐᵒᵖ] (Fin n → ℤᵐᵒᵖ) :=
  LinearEquiv.piCongrRight fun _ ↦ MulOpposite.opLinearEquiv ℤᵐᵒᵖ

private noncomputable def rightEmptyPresentation :
    ((Fin 1 → ℤ) × (Fin 0 → ℤᵐᵒᵖ)) ≃ₗ[ℤᵐᵒᵖ] (Fin 1 → ℤᵐᵒᵖ) :=
  ((rightCoordEquiv 1).prodCongr (LinearEquiv.refl ℤᵐᵒᵖ (Fin 0 → ℤᵐᵒᵖ))).trans
    (finProdEquiv ℤᵐᵒᵖ 1 0)

private noncomputable def rightLargerPresentation :
    ((Fin 1 → ℤ) × (Fin 2 → ℤᵐᵒᵖ)) ≃ₗ[ℤᵐᵒᵖ] (Fin 3 → ℤᵐᵒᵖ) :=
  ((rightCoordEquiv 1).prodCongr (LinearEquiv.refl ℤᵐᵒᵖ (Fin 2 → ℤᵐᵒᵖ))).trans
    (finProdEquiv ℤᵐᵒᵖ 1 2)

private theorem right_module_integer_rank : (1 : ℤ) - 0 = 3 - 2 := by
  let : InvariantBasisNumber ℤᵐᵒᵖ :=
    (MulOpposite.invariantBasisNumber_iff (R := ℤ)).mpr inferInstance
  have h := Module.int_card_sub_eq_of_prod_linearEquiv ℤᵐᵒᵖ (Fin 1 → ℤ)
    rightEmptyPresentation rightLargerPresentation
  simpa only [Fintype.card_fin, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] using h
