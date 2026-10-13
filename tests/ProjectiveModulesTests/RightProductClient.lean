/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.RightProduct
import ProjectiveModules.Module.RightRegular
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.PUnit
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Tactic.NormNum

/-!
# Coordinate calculations in right coefficient-product modules

Rational regular modules give concrete supported values, finite reconstruction,
scalar actions and linear comparisons on binary and three-coordinate products.
The finite-projective factors come from regular free modules. Empty families and
a zero-ring factor use the same canonical bundles. Scalar extension of a regular
module and a separate carrier lift exercise independent universes.

Quaternion multiplication distinguishes a right action from a left action.
Countably supported rational coordinates give projective factors without a
finite-generation assumption; coordinate scalar extension recovers their values.
-/

@[expose] public section

noncomputable section

namespace ProjectiveModulesTests.RightProductClient

open ModuleCat

private abbrev qModule := ModuleCat.of ℚᵐᵒᵖ ℚᵐᵒᵖ
private abbrev qProjective := FiniteProjective.of ℚᵐᵒᵖ ℚᵐᵒᵖ
private abbrev qR := fun _ : Fin 3 => ℚ
private abbrev qM := fun _ : Fin 3 => qModule
private abbrev qP := fun _ : Fin 3 => qProjective
private abbrev three := ModuleCat.piRight qR qM

private def seven : three :=
  ModuleCat.piRightSingle qR qM 1 (MulOpposite.op 7)

private theorem supported_values : seven 1 = MulOpposite.op 7 ∧ seven 2 = 0 := by
  constructor
  · exact ModuleCat.piRightSingle_apply_same qR qM 1 _
  · exact ModuleCat.piRightSingle_apply_ne qR qM 1 2 (by norm_num) _

private theorem seven_apply_ne (i : Fin 3) (h : i ≠ 1) : seven i = 0 :=
  ModuleCat.piRightSingle_apply_ne qR qM 1 i h _

private theorem supported_nonzero : seven ≠ 0 := by
  intro h
  have h7 := congrArg (fun x : three => x 1) h
  rw [supported_values.1, ModuleCat.piRight_zero_apply] at h7
  have := congrArg MulOpposite.unop h7
  norm_num at this

private theorem raw_pi_action :
    @SMul.smul _ _ (Module.piRightModule qR (fun _ => ℚᵐᵒᵖ)).toSMul
        (MulOpposite.op (fun _ => (3 : ℚ)))
        (Pi.single (1 : Fin 3) (MulOpposite.op 7)) =
      Pi.single (1 : Fin 3) (MulOpposite.op 21) := by
  funext i
  rw [Module.piRightModule_smul_apply]
  by_cases h : i = 1
  · subst i
    norm_num [Pi.single_eq_same, smul_eq_mul, ← MulOpposite.op_mul]
  · simp [Pi.single_eq_of_ne h]

private theorem raw_binary_action :
    @SMul.smul _ _ (Module.prodRightModule ℚ ℚ ℚᵐᵒᵖ ℚᵐᵒᵖ).toSMul
        (MulOpposite.op (3, 5)) (MulOpposite.op 7, MulOpposite.op 11) =
      (MulOpposite.op 21, MulOpposite.op 55) := by
  rw [Module.prodRightModule_smul]
  norm_num [smul_eq_mul, ← MulOpposite.op_mul]

private theorem bundled_scalar_coordinate :
    (MulOpposite.op (fun _ : Fin 3 => (3 : ℚ)) • seven) 1 = MulOpposite.op 21 := by
  rw [ModuleCat.piRight_smul_apply, supported_values.1]
  norm_num [smul_eq_mul, ← MulOpposite.op_mul]

private theorem raw_semilinear_value :
    Module.piRightEval qR (fun _ => ℚᵐᵒᵖ) 1
      (Pi.single (1 : Fin 3) (MulOpposite.op 7)) = MulOpposite.op 7 := by
  rw [Module.piRightEval_apply]
  exact Pi.single_eq_same _ _

private theorem supported_finite_reconstruction :
    seven = ∑ᶠ i, ModuleCat.piRightSingle qR qM i (seven i) :=
  ModuleCat.piRight_eq_finsum_single qR qM seven

private theorem raw_direct_sum_comparison :
    Module.piRightProdLinearEquiv qR (fun _ => ℚᵐᵒᵖ) (fun _ => ℚᵐᵒᵖ)
        (fun i => (seven i, MulOpposite.op 11)) =
      (seven, fun _ => MulOpposite.op 11) :=
  Module.piRightProdLinearEquiv_apply qR _ _ _

private abbrev threeProjective := FiniteProjective.pi qR qP
private abbrev oneTwoThree : threeProjective :=
  FiniteProjective.piMk qR qP (fun i => MulOpposite.op ((i.val : ℚ) + 1))

private theorem oneTwoThree_apply (i : Fin 3) :
    oneTwoThree i = MulOpposite.op ((i.val : ℚ) + 1) :=
  FiniteProjective.piMk_apply qR qP _ i

private theorem projective_comparison_value :
    FiniteProjective.piLinearEquiv qR qP oneTwoThree 2 = MulOpposite.op 3 := by
  rw [FiniteProjective.piLinearEquiv_apply, oneTwoThree_apply]
  norm_num

private theorem projective_scalar_value :
    (MulOpposite.op (fun _ : Fin 3 => (3 : ℚ)) • oneTwoThree) 2 = MulOpposite.op 9 := by
  rw [FiniteProjective.pi_smul_apply, oneTwoThree_apply]
  norm_num [smul_eq_mul, ← MulOpposite.op_mul]

private theorem projective_finite_reconstruction :
    oneTwoThree = ∑ᶠ i, (FiniteProjective.piLinearEquiv qR qP).symm
      (ModuleCat.piRightSingle qR qM i (oneTwoThree i)) :=
  FiniteProjective.pi_eq_finsum_single qR qP oneTwoThree

private abbrev twoProjective := FiniteProjective.prodRight ℚ ℚ qProjective qProjective
private abbrev sevenEleven : twoProjective :=
  FiniteProjective.prodRightMk ℚ ℚ qProjective qProjective (MulOpposite.op 7) (MulOpposite.op 11)

private theorem binary_projective_scalar :
    MulOpposite.op ((3 : ℚ), (5 : ℚ)) • sevenEleven =
      FiniteProjective.prodRightMk ℚ ℚ qProjective qProjective
        (MulOpposite.op 21) (MulOpposite.op 55) := by
  rw [FiniteProjective.prodRight_smul]
  apply (FiniteProjective.prodRight_ext_iff ℚ ℚ qProjective qProjective _ _).2
  norm_num [smul_eq_mul, ← MulOpposite.op_mul, sevenEleven,
    FiniteProjective.prodRightMk_apply]

private theorem binary_projective_comparison :
    FiniteProjective.prodRightLinearEquiv ℚ ℚ qProjective qProjective sevenEleven =
      ModuleCat.prodRightMk ℚ ℚ qModule qModule (MulOpposite.op 7) (MulOpposite.op 11) :=
  FiniteProjective.prodRightLinearEquiv_apply ℚ ℚ qProjective qProjective sevenEleven

private theorem binary_supported_reconstruction :
    sevenEleven =
      FiniteProjective.prodRightMk ℚ ℚ qProjective qProjective sevenEleven.1 0 +
      FiniteProjective.prodRightMk ℚ ℚ qProjective qProjective 0 sevenEleven.2 :=
  FiniteProjective.prodRight_eq_add ℚ ℚ qProjective qProjective sevenEleven

private theorem empty_canonical_bundle
    (x : FiniteProjective.pi (fun _ : Fin 0 => ℚ) (fun _ => qProjective)) : x = 0 := by
  apply (FiniteProjective.pi_ext_iff _ _ _ _).2
  intro i
  exact Fin.elim0 i

private abbrev zeroFactor := FiniteProjective.of PUnitᵐᵒᵖ PUnit
private theorem zero_ring_factor_survives :
    (MulOpposite.op ((3 : ℚ), (0 : PUnit)) •
      FiniteProjective.prodRightMk ℚ PUnit qProjective zeroFactor (MulOpposite.op 7) 0).1 =
        MulOpposite.op 21 := by
  rw [FiniteProjective.prodRight_smul]
  norm_num [FiniteProjective.prodRightMk_apply, smul_eq_mul, ← MulOpposite.op_mul]

private def raiseScalar : ℚ →+* ULift.{1} ℚ := ULift.ringEquiv.symm.toRingHom
private abbrev raisedScalarFactor :=
  FiniteProjective.of (ULift.{1} ℚ)ᵐᵒᵖ (RightExtension.Obj raiseScalar ℚᵐᵒᵖ)
private abbrev raisedScalars : FiniteProjective.{1, 1} (ℚ × ULift.{1} ℚ)ᵐᵒᵖ :=
  FiniteProjective.prodRight ℚ (ULift.{1} ℚ) qProjective raisedScalarFactor

private theorem scalar_lift_tensor_value :
    (MulOpposite.op ((3 : ℚ), ULift.up (5 : ℚ)) •
      (FiniteProjective.prodRightMk ℚ (ULift.{1} ℚ) qProjective raisedScalarFactor
        (MulOpposite.op 7) (RightExtension.tmul raiseScalar (MulOpposite.op 11) 1) :
          raisedScalars)).2 = RightExtension.tmul raiseScalar (MulOpposite.op 11) (ULift.up 5) := by
  rw [FiniteProjective.prodRight_smul]
  simp only [FiniteProjective.prodRightMk_apply, RightExtension.tmul_smul,
    op_smul_eq_mul, one_mul]

private abbrev raisedCarrierFactor := FiniteProjective.of ℚᵐᵒᵖ (ULift.{2} ℚᵐᵒᵖ)
private abbrev raisedCarriers : FiniteProjective.{0, 2} (ℚ × ℚ)ᵐᵒᵖ :=
  FiniteProjective.prodRight ℚ ℚ raisedCarrierFactor qProjective
private theorem carrier_lift_coordinate_value :
    (MulOpposite.op ((3 : ℚ), (5 : ℚ)) •
      (FiniteProjective.prodRightMk ℚ ℚ raisedCarrierFactor qProjective
        (ULift.up (MulOpposite.op 7)) (MulOpposite.op 11) : raisedCarriers)).1.down =
      MulOpposite.op 21 := by
  rw [FiniteProjective.prodRight_smul, FiniteProjective.prodRightMk_apply, ULift.smul_down]
  norm_num [smul_eq_mul, ← MulOpposite.op_mul]

private def quaternionI : Quaternion ℚ := ⟨0, 1, 0, 0⟩
private def quaternionJ : Quaternion ℚ := ⟨0, 0, 1, 0⟩

private theorem quaternion_products_imK :
    (quaternionJ * quaternionI).imK = -1 ∧ (quaternionI * quaternionJ).imK = 1 := by
  constructor <;> rw [QuaternionAlgebra.imK_mul] <;> norm_num [quaternionI, quaternionJ]

private abbrev quaternionModule := ModuleCat.of (Quaternion ℚ)ᵐᵒᵖ (Quaternion ℚ)
private theorem quaternion_right_not_left :
    (MulOpposite.op (quaternionI, (3 : ℚ)) •
      ModuleCat.prodRightMk (Quaternion ℚ) ℚ quaternionModule qModule
        quaternionJ (MulOpposite.op 7)).1 ≠ quaternionI * quaternionJ := by
  rw [ModuleCat.prodRight_smul, ModuleCat.prodRightMk_apply, op_smul_eq_mul]
  intro h
  have hk : (quaternionJ * quaternionI).imK = (quaternionI * quaternionJ).imK :=
    congrArg (fun q : Quaternion ℚ => q.imK) h
  rw [quaternion_products_imK.1, quaternion_products_imK.2] at hk
  norm_num at hk

private abbrev countableFactor := ModuleCat.of ℚᵐᵒᵖ (ℕ →₀ ℚᵐᵒᵖ)
private theorem arbitrary_projective_factors :
    @Module.Projective (Fin 3 → ℚ)ᵐᵒᵖ _ (Fin 3 → ℕ →₀ ℚᵐᵒᵖ) _
        (Module.piRightModule qR (fun _ => ℕ →₀ ℚᵐᵒᵖ)) ∧
      @Module.Projective (ℚ × ℚ)ᵐᵒᵖ _ ((ℕ →₀ ℚᵐᵒᵖ) × ℚᵐᵒᵖ) _
        (Module.prodRightModule ℚ ℚ (ℕ →₀ ℚᵐᵒᵖ) ℚᵐᵒᵖ) :=
  ⟨Module.projective_piRight qR (fun _ => ℕ →₀ ℚᵐᵒᵖ),
    Module.projective_prodRight ℚ ℚ (ℕ →₀ ℚᵐᵒᵖ) ℚᵐᵒᵖ⟩

private abbrev countableSeven :=
  ModuleCat.piRightSingle qR (fun _ => countableFactor) 1
    (Finsupp.single 5 (MulOpposite.op 7))

private theorem countableSeven_apply :
    countableSeven 1 = Finsupp.single 5 (MulOpposite.op 7) :=
  ModuleCat.piRightSingle_apply_same qR (fun _ => countableFactor) 1 _

private theorem recover_countable_value :
    RightExtension.piRecoverLinearEquiv qR (fun _ => countableFactor) 1
        (RightExtension.tmul (Pi.evalRingHom qR 1) countableSeven 3) 5 = MulOpposite.op 21 := by
  rw [RightExtension.piRecoverLinearEquiv_tmul, countableSeven_apply]
  change ((MulOpposite.op (3 : ℚ) •
    (Finsupp.single (5 : ℕ) (MulOpposite.op (7 : ℚ)) : ℕ →₀ ℚᵐᵒᵖ)) 5) =
      MulOpposite.op (21 : ℚ)
  rw [Finsupp.smul_apply, Finsupp.single_eq_same]
  norm_num [smul_eq_mul, ← MulOpposite.op_mul]

private theorem reconstruct_supported_value :
    (RightExtension.piLinearEquiv qR three).symm
      (ModuleCat.piRightSingle qR
        (fun i => ModuleCat.of ℚᵐᵒᵖ (RightExtension.Obj (Pi.evalRingHom qR i) three))
        1 (RightExtension.tmul (Pi.evalRingHom qR 1) seven 3)) =
      ModuleCat.piRightSingle qR qM 1 (MulOpposite.op 21) := by
  rw [RightExtension.piLinearEquiv_symm_single_tmul]
  apply (ModuleCat.piRight_ext_iff qR qM _ _).2
  intro i
  rw [ModuleCat.piRight_smul_apply]
  by_cases h : i = 1
  · subst i
    rw [ModuleCat.piRightSingle_apply_same, supported_values.1]
    norm_num [Pi.single_eq_same, smul_eq_mul, ← MulOpposite.op_mul]
  · rw [ModuleCat.piRightSingle_apply_ne qR qM 1 i h, seven_apply_ne i h, smul_zero]

end ProjectiveModulesTests.RightProductClient
