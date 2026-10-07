/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules
public import Mathlib.Algebra.Quaternion
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-!
# Scalar rank clients

These clients use the scalar-rank formula on a singleton row, a noncentral
quaternion row, an empty sum, and an infinite sum with independent index and
matrix-size universes. A single two-coordinate row is not free over the
two-by-two matrix ring: a free matrix module has right-division-ring dimension
a multiple of four, whereas that row has dimension two. Thus a free-module
rank tower law cannot replace the fixed-simple multiplicity formula.
-/

set_option warningAsError true

namespace ProjectiveModulesTests.ScalarRankClient

noncomputable section

open scoped Quaternion
open Cardinal

private theorem nat_row_scalar_action :
    ((RingHom.op (Matrix.scalar (Fin 2))) (MulOpposite.op (3 : ℕ)) •
        (fun index : Fin 2 => (index : ℕ) + 1)) 1 = 6 := by
  rw [Matrix.op_scalar_smul_row (Fin 2) ℕ]
  norm_num [MulOpposite.smul_eq_mul_unop]

private theorem nat_row_scalar_rank :
    Module.rank ℕᵐᵒᵖ (Fin 2 → ℕ) = 2 := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using Matrix.rank_row_op_scalar (Fin 2) ℕ

local instance : Module ℚᵐᵒᵖ (Fin 1 → ℚ) :=
  Module.compHom _ (RingHom.op (Matrix.scalar (Fin 1)))

private theorem singleton_row_scalar_rank :
    Module.rank ℚᵐᵒᵖ (Fin 1 → ℚ) = 1 := by
  have multiplicity :
      (IsSimpleRing.isIsotypicOfType (Matrix (Fin 1) (Fin 1) ℚ)ᵐᵒᵖ
        (Fin 1 → ℚ) (Fin 1 → ℚ)).multiplicity = 1 :=
    IsIsotypicOfType.multiplicity_self _ _
  have scalarRank := Matrix.lift_rank_op_scalar_eq_card_mul_multiplicity (Fin 1) ℚ
    (M := Fin 1 → ℚ)
  rw [multiplicity] at scalarRank
  simpa only [Cardinal.lift_id, Fintype.card_fin, Nat.cast_one, one_mul] using scalarRank

private def quaternionI : Quaternion ℚ := ⟨0, 1, 0, 0⟩
private def quaternionJ : Quaternion ℚ := ⟨0, 0, 1, 0⟩

private theorem quaternion_row_scalar_action :
    (RingHom.op (Matrix.scalar (Fin 2))) (MulOpposite.op quaternionI) •
        (Pi.single 0 quaternionJ : Fin 2 → Quaternion ℚ) =
      MulOpposite.op quaternionI • (Pi.single 0 quaternionJ : Fin 2 → Quaternion ℚ) ∧
    ((RingHom.op (Matrix.scalar (Fin 2))) (MulOpposite.op quaternionI) •
        (Pi.single 0 quaternionJ : Fin 2 → Quaternion ℚ)) 0 ≠
      quaternionI * quaternionJ := by
  have action := Matrix.op_scalar_smul_row (Fin 2) (Quaternion ℚ)
    (MulOpposite.op quaternionI) (Pi.single 0 quaternionJ)
  refine ⟨action, ?_⟩
  rw [action]
  intro equality
  have imaginaryPart := congrArg (fun q : Quaternion ℚ => q.imK) equality
  norm_num [Quaternion.imK_mul, quaternionI, quaternionJ] at imaginaryPart

public theorem quaternion_row_scalar_rank :
    Module.rank (Quaternion ℚ)ᵐᵒᵖ (Fin 2 → Quaternion ℚ) = 2 := by
  have multiplicity :
      (IsSimpleRing.isIsotypicOfType
        (Matrix (Fin 2) (Fin 2) (Quaternion ℚ))ᵐᵒᵖ
        (Fin 2 → Quaternion ℚ) (Fin 2 → Quaternion ℚ)).multiplicity = 1 :=
    IsIsotypicOfType.multiplicity_self _ _
  have scalarRank := Matrix.lift_rank_op_scalar_eq_card_mul_multiplicity (Fin 2)
    (Quaternion ℚ) (M := Fin 2 → Quaternion ℚ)
  rw [multiplicity] at scalarRank
  rw [Matrix.op_scalar_module_row (Fin 2) (Quaternion ℚ)] at scalarRank
  simpa only [Cardinal.lift_id, Fintype.card_fin, Nat.cast_ofNat, mul_one] using scalarRank

local instance : Module ℚᵐᵒᵖ (Empty →₀ (Fin 2 → ℚ)) :=
  Module.compHom _ (RingHom.op (Matrix.scalar (Fin 2)))

private theorem zero_row_scalar_rank :
    Module.rank ℚᵐᵒᵖ (Empty →₀ (Fin 2 → ℚ)) = 0 := by
  have multiplicity :
      (IsSimpleRing.isIsotypicOfType (Matrix (Fin 2) (Fin 2) ℚ)ᵐᵒᵖ
        (Empty →₀ (Fin 2 → ℚ)) (Fin 2 → ℚ)).multiplicity = 0 :=
    IsIsotypicOfType.multiplicity_eq_zero_of_subsingleton _
  have scalarRank := Matrix.lift_rank_op_scalar_eq_card_mul_multiplicity (Fin 2) ℚ
    (M := Empty →₀ (Fin 2 → ℚ))
  rw [multiplicity, mul_zero] at scalarRank
  simpa only [Cardinal.lift_id] using scalarRank

local instance : Module (Quaternion ℚ)ᵐᵒᵖ
    (ULift.{2} ℕ →₀ (ULift.{1} (Fin 2) → Quaternion ℚ)) :=
  Module.compHom _ (RingHom.op (Matrix.scalar (ULift.{1} (Fin 2))))

private theorem infinite_row_scalar_rank :
    Cardinal.lift.{1} (@Module.rank (Quaternion ℚ)ᵐᵒᵖ
        (ULift.{2} ℕ →₀ (ULift.{1} (Fin 2) → Quaternion ℚ))
        inferInstance inferInstance
        (Module.compHom _ (RingHom.op (Matrix.scalar (ULift.{1} (Fin 2)))))) =
      (2 : Cardinal.{2}) * #(ULift.{2} ℕ) := by
  let h := IsSimpleRing.isIsotypicOfType
    (Matrix (ULift.{1} (Fin 2)) (ULift.{1} (Fin 2)) (Quaternion ℚ))ᵐᵒᵖ
    (ULift.{2} ℕ →₀ (ULift.{1} (Fin 2) → Quaternion ℚ))
    (ULift.{1} (Fin 2) → Quaternion ℚ)
  have multiplicity : h.multiplicity = #(ULift.{2} ℕ) := by
    simpa only [Cardinal.lift_id] using
      h.lift_multiplicity_eq_of_linearEquiv_finsupp (LinearEquiv.refl _ _)
  have scalarRank := Matrix.lift_rank_op_scalar_eq_card_mul_multiplicity
    (ULift.{1} (Fin 2)) (Quaternion ℚ)
    (M := ULift.{2} ℕ →₀ (ULift.{1} (Fin 2) → Quaternion ℚ))
  change _ = (Fintype.card (ULift.{1} (Fin 2)) : Cardinal.{2}) * h.multiplicity at scalarRank
  rw [multiplicity] at scalarRank
  simpa only [Cardinal.lift_id, Fintype.card_ulift, Fintype.card_fin, Nat.cast_ofNat]
    using scalarRank

private theorem three_complex_copies_real_rank :
    Module.rank ℝ (Fin 3 → ℂ) = 6 := by
  let h := IsSimpleRing.isIsotypicOfType ℂ (Fin 3 → ℂ) ℂ
  have multiplicity : h.multiplicity = 3 := by
    simpa [h] using h.lift_multiplicity_eq_of_linearEquiv_finsupp
      (Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 3)).symm
  have scalarRank := h.lift_rank_eq_mul_multiplicity (F := ℝ)
  rw [multiplicity] at scalarRank
  simpa only [Cardinal.lift_id, Complex.rank_real_complex, Nat.cast_ofNat,
    show (2 : Cardinal) * 3 = 6 by norm_num] using scalarRank

end

end ProjectiveModulesTests.ScalarRankClient
