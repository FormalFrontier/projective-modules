/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules
public import Mathlib.Algebra.Quaternion

/-!
# Canonical right matrix-row clients

These clients exercise the row action over a noncommutative division ring,
singleton size, a zero module and an infinite direct sum. Empty matrix size
shows why the nonempty-index hypothesis is necessary.
-/

set_option warningAsError true

namespace ProjectiveModulesTests.MatrixRowClient

open scoped Quaternion
open Cardinal

private theorem singleton_multiplicity :
    (IsIsotypicOfType.of_isSimpleModule
      (Matrix (Fin 1) (Fin 1) ℚ)ᵐᵒᵖ (Fin 1 → ℚ)).multiplicity = 1 :=
  IsIsotypicOfType.multiplicity_self _ _

private def quaternionI : Quaternion ℚ := ⟨0, 1, 0, 0⟩
private def quaternionJ : Quaternion ℚ := ⟨0, 0, 1, 0⟩

private theorem quaternion_noncommutative :
    quaternionI * quaternionJ ≠ quaternionJ * quaternionI := by
  intro equality
  have imaginaryPart := congrArg (fun q : Quaternion ℚ => q.imK) equality
  norm_num [Quaternion.imK_mul, quaternionI, quaternionJ] at imaginaryPart

private theorem quaternion_row_action :
    (MulOpposite.op (Matrix.diagonal (fun _ : Fin 2 => quaternionI)) •
      (Pi.single 0 quaternionJ : Fin 2 → Quaternion ℚ)) 0 =
        quaternionJ * quaternionI ∧
    (MulOpposite.op (Matrix.diagonal (fun _ : Fin 2 => quaternionI)) •
      (Pi.single 0 quaternionJ : Fin 2 → Quaternion ℚ)) 0 ≠
        quaternionI * quaternionJ := by
  have action :
      (MulOpposite.op (Matrix.diagonal (fun _ : Fin 2 => quaternionI)) •
        (Pi.single 0 quaternionJ : Fin 2 → Quaternion ℚ)) 0 =
          quaternionJ * quaternionI := by
    simp [Matrix.op_smul_eq_vecMul, Matrix.vecMul_diagonal]
  exact ⟨action, fun equality => quaternion_noncommutative (action.symm.trans equality).symm⟩

private theorem quaternion_row_multiplicity :
    (IsIsotypicOfType.of_isSimpleModule
      (Matrix (Fin 2) (Fin 2) (Quaternion ℚ))ᵐᵒᵖ
      (Fin 2 → Quaternion ℚ)).multiplicity = 1 :=
  IsIsotypicOfType.multiplicity_self _ _

private theorem zero_row_multiplicity :
    (IsSimpleRing.isIsotypicOfType
      (Matrix (Fin 2) (Fin 2) ℚ)ᵐᵒᵖ
      (Empty →₀ (Fin 2 → ℚ)) (Fin 2 → ℚ)).multiplicity = 0 :=
  IsIsotypicOfType.multiplicity_eq_zero_of_subsingleton _

public theorem zero_decomposition_has_empty_index :
    ∃ κ : Type, IsEmpty κ ∧
      Nonempty ((Empty →₀ (Fin 2 → ℚ)) ≃ₗ[(Matrix (Fin 2) (Fin 2) ℚ)ᵐᵒᵖ]
        (κ →₀ Fin 2 → ℚ)) := by
  obtain ⟨κ, ⟨equivalence⟩⟩ :=
    Matrix.exists_linearEquiv_finsupp_vecMul (Fin 2) ℚ (Empty →₀ (Fin 2 → ℚ))
  have cardinality : (#κ : Cardinal) = #Empty := by
    simpa using Finsupp.lift_cardinalMk_eq_of_linearEquiv equivalence.symm
  exact ⟨κ, Cardinal.mk_eq_zero_iff.mp (by simpa using cardinality), ⟨equivalence⟩⟩

private theorem infinite_row_multiplicity :
    Cardinal.lift.{1} (IsSimpleRing.isIsotypicOfType
      (Matrix (Fin 2) (Fin 2) (Quaternion ℚ))ᵐᵒᵖ
      (ULift.{1} ℕ →₀ (Fin 2 → Quaternion ℚ))
      (Fin 2 → Quaternion ℚ)).multiplicity =
    Cardinal.lift.{1} (#(ULift.{1} ℕ)) := by
  exact (IsSimpleRing.isIsotypicOfType
    (Matrix (Fin 2) (Fin 2) (Quaternion ℚ))ᵐᵒᵖ
    (ULift.{1} ℕ →₀ (Fin 2 → Quaternion ℚ))
    (Fin 2 → Quaternion ℚ)).lift_multiplicity_eq_of_linearEquiv_finsupp
      (LinearEquiv.refl _ _)

private theorem infinite_decomposition_across_universes :
    ∃ κ : Type 2, Infinite κ ∧
      Nonempty ((ULift.{2} ℕ →₀ (ULift.{1} (Fin 2) → Quaternion ℚ)) ≃ₗ[
        (Matrix (ULift.{1} (Fin 2)) (ULift.{1} (Fin 2)) (Quaternion ℚ))ᵐᵒᵖ]
        (κ →₀ ULift.{1} (Fin 2) → Quaternion ℚ)) := by
  obtain ⟨κ, ⟨equivalence⟩⟩ :=
    Matrix.exists_linearEquiv_finsupp_vecMul
      (ULift.{1} (Fin 2)) (Quaternion ℚ)
      (ULift.{2} ℕ →₀ (ULift.{1} (Fin 2) → Quaternion ℚ))
  have cardinality : Nonempty ((ULift.{2} ℕ) ≃ κ) :=
    Cardinal.lift_mk_eq'.mp (by
      simpa using Finsupp.lift_cardinalMk_eq_of_linearEquiv equivalence)
  exact ⟨κ, Infinite.of_injective cardinality.some cardinality.some.injective,
    ⟨equivalence⟩⟩

private theorem empty_size_not_simple :
    ¬ IsSimpleModule (Matrix Empty Empty ℚ)ᵐᵒᵖ (Empty → ℚ) := by
  intro purportedSimplicity
  have : IsSimpleModule (Matrix Empty Empty ℚ)ᵐᵒᵖ (Empty → ℚ) :=
    purportedSimplicity
  have nontrivialRow : Nontrivial (Empty → ℚ) :=
    IsSimpleModule.nontrivial (Matrix Empty Empty ℚ)ᵐᵒᵖ (Empty → ℚ)
  exact (not_subsingleton_iff_nontrivial.mpr nontrivialRow)
    (inferInstance : Subsingleton (Empty → ℚ))

end ProjectiveModulesTests.MatrixRowClient
