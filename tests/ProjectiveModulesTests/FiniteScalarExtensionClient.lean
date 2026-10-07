/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite right scalar-extension clients

A chosen unital map from a division ring into a nonzero ring restricts right
modules via the induced homomorphism of opposite rings. Finite right dimension
of the target ring yields right invariant basis number, and the ranks of every
free right module satisfy a universe-polymorphic cardinal tower identity.
The corresponding quotient of natural-number finranks agrees with basis rank
when the basis is finite; for infinite free modules both finranks of the module
are zero, while their cardinal ranks retain the infinite basis size.

Dual numbers over rational quaternions give a noncommutative, non-matrix example.
Their two coordinate summands supply finite scalar dimension, and the inclusion
of the quaternions is noncentral. Empty, singleton, and infinite free modules
exhibit the different rank boundaries.

## References

Charles A. Weibel, *The K-book*, Example I.1.1.1, motivates the right-module
interpretation. Mathlib's Noetherian transfer and cardinal and finrank tower
theorems provide the underlying formal results.
-/

set_option warningAsError true

namespace ProjectiveModulesTests.FiniteScalarExtensionClient

noncomputable section

open Cardinal

universe u v w

section General

variable {D : Type u} {R : Type v} [DivisionRing D] [Ring R] [Nontrivial R]
variable (f : D →+* R)

private theorem finite_right_extension_rank_conditions
    [@Module.Finite Dᵐᵒᵖ Rᵐᵒᵖ inferInstance inferInstance
      (Module.compHom _ (RingHom.op f))] :
    IsNoetherianRing Rᵐᵒᵖ ∧ StrongRankCondition Rᵐᵒᵖ ∧
      InvariantBasisNumber Rᵐᵒᵖ := by
  let _ : Module Dᵐᵒᵖ Rᵐᵒᵖ := Module.compHom _ (RingHom.op f)
  let _ : SMul Dᵐᵒᵖ Rᵐᵒᵖ := SMul.comp _ (RingHom.op f)
  let _ : IsScalarTower Dᵐᵒᵖ Rᵐᵒᵖ Rᵐᵒᵖ := SMul.comp.isScalarTower _
  let _ : IsNoetherianRing Rᵐᵒᵖ := IsNoetherianRing.of_finite Dᵐᵒᵖ Rᵐᵒᵖ
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem free_right_scalar_rank_tower
    [@Module.Finite Dᵐᵒᵖ Rᵐᵒᵖ inferInstance inferInstance
      (Module.compHom _ (RingHom.op f))]
    {M : Type w} [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Free Rᵐᵒᵖ M] :
    Cardinal.lift.{v}
        (@Module.rank Dᵐᵒᵖ M inferInstance inferInstance
          (Module.compHom M (RingHom.op f))) =
      Cardinal.lift.{w}
        (@Module.rank Dᵐᵒᵖ Rᵐᵒᵖ inferInstance inferInstance
          (Module.compHom _ (RingHom.op f))) *
        Cardinal.lift.{v} (Module.rank Rᵐᵒᵖ M) := by
  let _ : Module Dᵐᵒᵖ Rᵐᵒᵖ := Module.compHom _ (RingHom.op f)
  let _ : Module Dᵐᵒᵖ M := Module.compHom _ (RingHom.op f)
  let _ : SMul Dᵐᵒᵖ Rᵐᵒᵖ := SMul.comp _ (RingHom.op f)
  let _ : SMul Dᵐᵒᵖ M := SMul.comp _ (RingHom.op f)
  let _ : IsScalarTower Dᵐᵒᵖ Rᵐᵒᵖ M := SMul.comp.isScalarTower _
  let _ : StrongRankCondition Rᵐᵒᵖ := (finite_right_extension_rank_conditions f).2.1
  let _ : Module.Free Dᵐᵒᵖ Rᵐᵒᵖ := Module.Free.of_divisionRing _ _
  exact (lift_rank_mul_lift_rank Dᵐᵒᵖ Rᵐᵒᵖ M).symm

private theorem free_right_finrank_quotient
    [@Module.Finite Dᵐᵒᵖ Rᵐᵒᵖ inferInstance inferInstance
      (Module.compHom _ (RingHom.op f))]
    {M : Type w} [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Free Rᵐᵒᵖ M] :
    Module.finrank Rᵐᵒᵖ M =
      @Module.finrank Dᵐᵒᵖ M inferInstance inferInstance
        (Module.compHom M (RingHom.op f)) /
        @Module.finrank Dᵐᵒᵖ Rᵐᵒᵖ inferInstance inferInstance
          (Module.compHom _ (RingHom.op f)) := by
  let _ : Module Dᵐᵒᵖ Rᵐᵒᵖ := Module.compHom _ (RingHom.op f)
  let _ : Module Dᵐᵒᵖ M := Module.compHom _ (RingHom.op f)
  let _ : SMul Dᵐᵒᵖ Rᵐᵒᵖ := SMul.comp _ (RingHom.op f)
  let _ : SMul Dᵐᵒᵖ M := SMul.comp _ (RingHom.op f)
  let _ : IsScalarTower Dᵐᵒᵖ Rᵐᵒᵖ M := SMul.comp.isScalarTower _
  let _ : StrongRankCondition Rᵐᵒᵖ := (finite_right_extension_rank_conditions f).2.1
  let _ : Module.Free Dᵐᵒᵖ Rᵐᵒᵖ := Module.Free.of_divisionRing _ _
  exact (Module.finrank_div_finrank_cancel_left_of_nontrivial Dᵐᵒᵖ Rᵐᵒᵖ M).symm

end General

section DualNumbers

private abbrev quaternionRing := Quaternion ℚ
private abbrev quaternionDual := DualNumber quaternionRing
private def quaternionScalar : quaternionRing →+* quaternionDual :=
  TrivSqZeroExt.inlHom _ _

private theorem quaternion_dual_right_action
    (coefficient : quaternionRing) (dual : quaternionDual) :
    (RingHom.op quaternionScalar) (MulOpposite.op coefficient) •
        (MulOpposite.op dual : quaternionDualᵐᵒᵖ) =
      MulOpposite.op (dual * quaternionScalar coefficient) := by
  rfl

private def quaternionI : quaternionRing := ⟨0, 1, 0, 0⟩
private def quaternionJ : quaternionRing := ⟨0, 0, 1, 0⟩

private theorem quaternion_dual_nonzero_square_zero :
    (DualNumber.eps : quaternionDual) ≠ 0 ∧
      (DualNumber.eps : quaternionDual) ^ 2 = 0 := by
  constructor
  · intro equality
    have component := congrArg TrivSqZeroExt.snd equality
    norm_num at component
  · exact DualNumber.eps_pow_two

local instance (priority := 10000) : SMul quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ :=
  SMul.comp _ (RingHom.op quaternionScalar)

local instance (priority := 10000) : Module quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ :=
  Module.compHom _ (RingHom.op quaternionScalar)

local instance (priority := 10000) :
    IsScalarTower quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ quaternionDualᵐᵒᵖ :=
  SMul.comp.isScalarTower _

private def quaternion_dual_scalar_equiv :
    (quaternionRingᵐᵒᵖ × quaternionRingᵐᵒᵖ) ≃ₗ[quaternionRingᵐᵒᵖ]
      quaternionDualᵐᵒᵖ where
  toFun coordinates := MulOpposite.op (coordinates.1.unop, coordinates.2.unop)
  invFun dual := (MulOpposite.op dual.unop.fst, MulOpposite.op dual.unop.snd)
  left_inv coordinates := by cases coordinates; rfl
  right_inv dual := by
    rcases dual with ⟨value⟩
    rcases value with ⟨first, second⟩
    rfl
  map_add' left right := by rfl
  map_smul' scalar coordinates := by
    let dual : quaternionDual := (coordinates.1.unop, coordinates.2.unop)
    have action : scalar • (MulOpposite.op dual : quaternionDualᵐᵒᵖ) =
        MulOpposite.op (dual * quaternionScalar scalar.unop) :=
      quaternion_dual_right_action scalar.unop dual
    simp only [RingHom.id_apply]
    rw [action]
    apply MulOpposite.unop_injective
    apply TrivSqZeroExt.ext
    · change coordinates.1.unop * scalar.unop =
        (dual * quaternionScalar scalar.unop).fst
      rw [TrivSqZeroExt.fst_mul]
      simp [dual, quaternionScalar]
    · change coordinates.2.unop * scalar.unop =
        (dual * quaternionScalar scalar.unop).snd
      rw [DualNumber.snd_mul]
      simp [dual, quaternionScalar]

private instance : Module.Free quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ :=
  Module.Free.of_equiv quaternion_dual_scalar_equiv

private theorem quaternion_dual_finite :
    Module.Finite quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ := by
  exact Module.Finite.of_surjective quaternion_dual_scalar_equiv.toLinearMap
    quaternion_dual_scalar_equiv.surjective

private instance : IsNoetherianRing quaternionDualᵐᵒᵖ := by
  let finite : Module.Finite quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ := quaternion_dual_finite
  exact IsNoetherianRing.of_finite quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ

private theorem quaternion_dual_scalar_rank :
    Module.rank quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ = 2 := by
  rw [← quaternion_dual_scalar_equiv.rank_eq, rank_prod']
  norm_num [Module.rank_self]

private theorem quaternion_regular_free_rank_quotient :
    Module.rank quaternionDualᵐᵒᵖ quaternionDualᵐᵒᵖ = 1 ∧
      @Module.rank quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ inferInstance inferInstance
        (Module.compHom _ (RingHom.op quaternionScalar)) = 2 ∧
      Module.finrank quaternionDualᵐᵒᵖ quaternionDualᵐᵒᵖ = 1 ∧
      @Module.finrank quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ inferInstance inferInstance
        (Module.compHom _ (RingHom.op quaternionScalar)) = 2 ∧
      Module.finrank quaternionDualᵐᵒᵖ quaternionDualᵐᵒᵖ =
        @Module.finrank quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ inferInstance inferInstance
          (Module.compHom _ (RingHom.op quaternionScalar)) /
          @Module.finrank quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ inferInstance inferInstance
            (Module.compHom _ (RingHom.op quaternionScalar)) := by
  have scalarFinrank :
      @Module.finrank quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ inferInstance inferInstance
        (Module.compHom _ (RingHom.op quaternionScalar)) = 2 := by
    rw [Module.finrank, quaternion_dual_scalar_rank]
    norm_num
  refine ⟨Module.rank_self _, quaternion_dual_scalar_rank,
    Module.finrank_self _, scalarFinrank, ?_⟩
  rw [scalarFinrank, Module.finrank_self]

private theorem quaternion_zero_free_rank :
    Module.rank quaternionDualᵐᵒᵖ (Fin 0 →₀ quaternionDualᵐᵒᵖ) = 0 := by
  simp

private theorem quaternion_singleton_free_rank :
    Module.rank quaternionDualᵐᵒᵖ (Fin 1 →₀ quaternionDualᵐᵒᵖ) = 1 := by
  simp

private theorem quaternion_infinite_free_rank :
    Module.rank quaternionDualᵐᵒᵖ (ULift.{1} ℕ →₀ quaternionDualᵐᵒᵖ) =
      Cardinal.lift.{0} #(ULift.{1} ℕ) := by
  exact rank_finsupp_self _ _

private theorem quaternion_infinite_free_rank_nonzero :
    Module.rank quaternionDualᵐᵒᵖ (ULift.{1} ℕ →₀ quaternionDualᵐᵒᵖ) ≠ 0 := by
  rw [quaternion_infinite_free_rank]
  exact Cardinal.lift_eq_zero.not.mpr (Cardinal.mk_ne_zero _)

private theorem quaternion_infinite_free_finrank_zero :
    Module.finrank quaternionDualᵐᵒᵖ (ULift.{1} ℕ →₀ quaternionDualᵐᵒᵖ) = 0 := by
  rw [Module.finrank, quaternion_infinite_free_rank]
  exact Cardinal.toNat_apply_of_aleph0_le
    (Cardinal.aleph0_le_lift.mpr (Cardinal.aleph0_le_mk _))

/-- The explicitly restricted infinite free module retains infinite scalar rank. -/
private theorem quaternion_infinite_restricted_rank :
    Cardinal.lift.{0} (@Module.rank quaternionRingᵐᵒᵖ
      (ULift.{1} ℕ →₀ quaternionDualᵐᵒᵖ) inferInstance inferInstance
      (Module.compHom _ (RingHom.op quaternionScalar))) =
      #(ULift.{1} ℕ) * (2 : Cardinal.{1}) := by
  let _ : Module quaternionRingᵐᵒᵖ (ULift.{1} ℕ →₀ quaternionDualᵐᵒᵖ) :=
    Module.compHom _ (RingHom.op quaternionScalar)
  simpa only [Cardinal.lift_uzero, quaternion_dual_scalar_rank, Cardinal.lift_ofNat] using
    (rank_finsupp quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ (ULift.{1} ℕ))

private theorem quaternion_infinite_restricted_rank_nonzero :
    Cardinal.lift.{0} (@Module.rank quaternionRingᵐᵒᵖ
      (ULift.{1} ℕ →₀ quaternionDualᵐᵒᵖ) inferInstance inferInstance
      (Module.compHom _ (RingHom.op quaternionScalar))) ≠ 0 := by
  rw [quaternion_infinite_restricted_rank]
  exact mul_ne_zero (Cardinal.mk_ne_zero _) (by norm_num)

private theorem quaternion_infinite_restricted_finrank_zero :
    @Module.finrank quaternionRingᵐᵒᵖ
      (ULift.{1} ℕ →₀ quaternionDualᵐᵒᵖ) inferInstance inferInstance
      (Module.compHom _ (RingHom.op quaternionScalar)) = 0 := by
  rw [Module.finrank]
  have infiniteRank : ℵ₀ ≤ Cardinal.lift.{0} (@Module.rank quaternionRingᵐᵒᵖ
      (ULift.{1} ℕ →₀ quaternionDualᵐᵒᵖ) inferInstance inferInstance
      (Module.compHom _ (RingHom.op quaternionScalar))) := by
    rw [quaternion_infinite_restricted_rank]
    exact (Cardinal.aleph0_le_mk _).trans (Cardinal.le_mul_right (by norm_num))
  exact Cardinal.toNat_apply_of_aleph0_le (by simpa using infiniteRank)

-- These specializations apply the general results to the quaternionic dual numbers;
-- the ranks and finranks above are computed independently from their coordinates.
private theorem quaternion_rank_conditions_smoke :
    IsNoetherianRing quaternionDualᵐᵒᵖ ∧ StrongRankCondition quaternionDualᵐᵒᵖ ∧
      InvariantBasisNumber quaternionDualᵐᵒᵖ := by
  let _ : Module.Finite quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ := quaternion_dual_finite
  exact finite_right_extension_rank_conditions quaternionScalar

private theorem quaternion_infinite_rank_tower_smoke :
    Cardinal.lift.{0} (@Module.rank quaternionRingᵐᵒᵖ
      (ULift.{1} ℕ →₀ quaternionDualᵐᵒᵖ) inferInstance inferInstance
      (Module.compHom _ (RingHom.op quaternionScalar))) =
      Cardinal.lift.{1} (@Module.rank quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ
        inferInstance inferInstance (Module.compHom _ (RingHom.op quaternionScalar))) *
        Cardinal.lift.{0} (Module.rank quaternionDualᵐᵒᵖ
          (ULift.{1} ℕ →₀ quaternionDualᵐᵒᵖ)) := by
  let _ : Module.Finite quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ := quaternion_dual_finite
  exact free_right_scalar_rank_tower quaternionScalar

private theorem quaternion_regular_finrank_quotient_smoke :
    Module.finrank quaternionDualᵐᵒᵖ quaternionDualᵐᵒᵖ =
      @Module.finrank quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ inferInstance inferInstance
        (Module.compHom _ (RingHom.op quaternionScalar)) /
        @Module.finrank quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ inferInstance inferInstance
          (Module.compHom _ (RingHom.op quaternionScalar)) := by
  let _ : Module.Finite quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ := quaternion_dual_finite
  exact free_right_finrank_quotient quaternionScalar

private theorem quaternion_infinite_finrank_quotient_smoke :
    Module.finrank quaternionDualᵐᵒᵖ (ULift.{1} ℕ →₀ quaternionDualᵐᵒᵖ) =
      @Module.finrank quaternionRingᵐᵒᵖ
        (ULift.{1} ℕ →₀ quaternionDualᵐᵒᵖ) inferInstance inferInstance
        (Module.compHom _ (RingHom.op quaternionScalar)) /
        @Module.finrank quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ inferInstance inferInstance
          (Module.compHom _ (RingHom.op quaternionScalar)) := by
  let _ : Module.Finite quaternionRingᵐᵒᵖ quaternionDualᵐᵒᵖ := quaternion_dual_finite
  exact free_right_finrank_quotient quaternionScalar

/-- The rational-quaternion scalars do not lie in the center of their dual-number ring. -/
public theorem quaternion_scalar_image_noncentral :
    ∃ (coefficient : Quaternion ℚ) (dual : DualNumber (Quaternion ℚ)),
      TrivSqZeroExt.inlHom _ _ coefficient * dual ≠
        dual * TrivSqZeroExt.inlHom _ _ coefficient := by
  refine ⟨quaternionI, quaternionScalar quaternionJ, ?_⟩
  intro equality
  have imaginaryPart := congrArg (fun value : quaternionRing => value.imK)
    (congrArg TrivSqZeroExt.fst equality)
  norm_num [quaternionScalar, quaternionI, quaternionJ, Quaternion.imK_mul] at imaginaryPart

end DualNumbers

end

end ProjectiveModulesTests.FiniteScalarExtensionClient
