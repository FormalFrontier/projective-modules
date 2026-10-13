/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules
public import ProjectiveModulesTests.FiniteProjectiveHomMatrixClient
public import ProjectiveModulesTests.FiniteProjectiveRestrictionUniverseClient
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Module.ULift

/-!
# Matrix-ideal evaluation in different scalar and source universes

The scalar ring and the nonfree matrix right ideal are lifted independently.
The coefficient of bidual evaluation is the scalar ring itself, not a third
independently lifted carrier. The two examples have scalar/source levels
`(1, 0)` and `(0, 2)`; the double-Hom carriers have levels `1` and `2`.

The lifted inclusion is assembled from the public matrix inclusion and
Mathlib's `ULift.moduleEquiv`. Pullback module data are confined to the
construction. Their parent actions are compared with the stored source action
and canonical right-regular coefficient action before bundling the inclusion.
The opposite linear equivalence then encodes its coefficients in the scalar ring.

## References

The nonfree right ideal and its separately lifted source are the public
matrix models of Projective Modules. Scalar pullback, carrier lifting and
opposite coefficient encoding use Mathlib's module APIs.
-/

universe uR uM

namespace ProjectiveModulesTests.BidualEvaluationUniverseClient

open IdempotentSpanSemiringClient RightIdealRingConstructorClient
open FiniteProjectiveHomMatrixClient FiniteProjectiveRestrictionUniverseClient

private noncomputable def liftedInclusion :
    matrixIdealSource.{uR, uM} →ₗ[(ULift.{uR} IntMatrix)ᵐᵒᵖ] ULift.{uR} IntMatrix := by
  let S := (ULift.{uR} IntMatrix)ᵐᵒᵖ
  let down : S →+* IntMatrixᵐᵒᵖ :=
    (ULift.ringEquiv : ULift.{uR} IntMatrix ≃+* IntMatrix).op.toRingHom
  let sourceCanonical : Module S matrixIdealSource.{uR, uM} := inferInstance
  let coefficientCanonical : Module S (ULift.{uR} IntMatrix) := inferInstance
  let sourceBase : Module S matrixRightIdeal := Module.compHom matrixRightIdeal down
  let coefficientBase : Module S IntMatrix := Module.compHom IntMatrix down
  let sourceUp : Module S (ULift.{uM} matrixRightIdeal) :=
    @ULift.module' S matrixRightIdeal _ _ sourceBase
  let coefficientUp : Module S (ULift.{uR} IntMatrix) :=
    @ULift.module' S IntMatrix _ _ coefficientBase
  have source_alignment : sourceCanonical = sourceUp :=
    Module.ext' _ _ (fun _ _ ↦ rfl)
  have coefficient_alignment : coefficientCanonical = coefficientUp :=
    Module.ext' _ _ (fun _ _ ↦ rfl)
  letI := sourceBase
  letI := coefficientBase
  let pulled : matrixRightIdeal →ₗ[S] IntMatrix :=
    { toFun := matrixInclusion
      map_add' := matrixInclusion.map_add
      map_smul' := fun r m ↦ matrixInclusion.map_smul (down r) m }
  let lifted : ULift.{uM} matrixRightIdeal →ₗ[S] ULift.{uR} IntMatrix :=
    (@ULift.moduleEquiv S IntMatrix _ _ coefficientBase).symm.toLinearMap.comp
      (pulled.comp (@ULift.moduleEquiv S matrixRightIdeal _ _ sourceBase).toLinearMap)
  refine
    { toFun := fun m ↦ lifted m
      map_add' := fun m n ↦ lifted.map_add m n
      map_smul' := ?_ }
  intro r m
  change lifted (@SMul.smul S (ULift.{uM} matrixRightIdeal)
      sourceCanonical.toDistribMulAction.toMulAction.toSMul r m) =
    @SMul.smul S (ULift.{uR} IntMatrix)
      coefficientCanonical.toDistribMulAction.toMulAction.toSMul r (lifted m)
  rw [source_alignment, coefficient_alignment]
  exact lifted.map_smul r m

private theorem liftedInclusion_apply (m : matrixRightIdeal) :
    liftedInclusion.{uR, uM} (show matrixIdealSource.{uR, uM} from ULift.up m) =
      ULift.up (matrixInclusion m) := rfl

private noncomputable def liftedForm :
    matrixIdealSource.{uR, uM} →ₗ[(ULift.{uR} IntMatrix)ᵐᵒᵖ]
      (ULift.{uR} IntMatrix)ᵐᵒᵖ :=
  (MulOpposite.opLinearEquiv (M := ULift.{uR} IntMatrix)
    (ULift.{uR} IntMatrix)ᵐᵒᵖ).toLinearMap.comp liftedInclusion

local instance sourceFinite :
    Module.Finite (ULift.{uR} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uR, uM} :=
  matrixIdealSource_finite_projective.1

local instance sourceProjective :
    Module.Projective (ULift.{uR} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uR, uM} :=
  matrixIdealSource_finite_projective.2

private theorem evaluated_lift (m : matrixRightIdeal) :
    LinearMap.bidualEvalEquiv (ULift.{uR} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uR, uM}
      (show matrixIdealSource.{uR, uM} from ULift.up m) liftedForm =
        MulOpposite.op (ULift.up (matrixInclusion m)) := by
  rw [LinearMap.bidualEvalEquiv_apply]
  rfl

private theorem lifted_order :
    LinearMap.flip (LinearMap.id :
      (matrixIdealSource.{uR, uM} →ₗ[(ULift.{uR} IntMatrix)ᵐᵒᵖ] ULift.{uR} IntMatrix)
        →ₗ[ULift.{uR} IntMatrix]
      (matrixIdealSource.{uR, uM} →ₗ[(ULift.{uR} IntMatrix)ᵐᵒᵖ] ULift.{uR} IntMatrix))
      (show matrixIdealSource.{uR, uM} from ULift.up matrixUpperRightMember)
      (ULift.up intE11 • liftedInclusion) = ULift.up intE01 ∧
      (MulOpposite.op (ULift.up intE11) • (LinearMap.flip (LinearMap.id :
        (matrixIdealSource.{uR, uM} →ₗ[(ULift.{uR} IntMatrix)ᵐᵒᵖ] ULift.{uR} IntMatrix)
          →ₗ[ULift.{uR} IntMatrix]
        (matrixIdealSource.{uR, uM} →ₗ[(ULift.{uR} IntMatrix)ᵐᵒᵖ] ULift.{uR} IntMatrix))
        (show matrixIdealSource.{uR, uM} from ULift.up matrixUpperRightMember)))
          liftedInclusion = 0 := by
  constructor
  · change ULift.up (intE11 * matrixInclusion matrixUpperRightMember) =
      (ULift.up intE01 : ULift.{uR} IntMatrix)
    rw [matrixInclusion_upperRight, intE11_mul_e01]
  · change ULift.up (matrixInclusion matrixUpperRightMember * intE11) =
      (0 : ULift.{uR} IntMatrix)
    rw [matrixInclusion_upperRight, intE01_mul_e11]
    rfl

private theorem lifted_source_action :
    liftedInclusion.{uR, uM}
      (MulOpposite.op (ULift.up intE11) •
        (show matrixIdealSource.{uR, uM} from ULift.up matrixUpperRightMember)) = 0 := by
  rw [map_smul, liftedInclusion_apply, matrixInclusion_upperRight]
  change ULift.up (intE01 * intE11) = (0 : ULift.{uR} IntMatrix)
  rw [intE01_mul_e11]
  rfl

private theorem lifted_moves :
    (ULift.up intE01 • liftedInclusion.{uR, uM})
        (show matrixIdealSource.{uR, uM} from ULift.up matrixGenerator) ≠
      liftedInclusion.{uR, uM}
        (show matrixIdealSource.{uR, uM} from ULift.up matrixGenerator) := by
  change ULift.up (intE01 * matrixInclusion matrixGenerator) ≠
    (ULift.up (matrixInclusion matrixGenerator) : ULift.{uR} IntMatrix)
  intro h
  exact matrixInclusion_left_moves.2.1 (congrArg ULift.down h)

private theorem evaluated_lift_moves :
    LinearMap.bidualEvalEquiv (ULift.{uR} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uR, uM}
        (show matrixIdealSource.{uR, uM} from ULift.up matrixGenerator)
        ((MulOpposite.opLinearEquiv (M := ULift.{uR} IntMatrix)
          (ULift.{uR} IntMatrix)ᵐᵒᵖ).toLinearMap.comp
            (ULift.up intE01 • liftedInclusion)) ≠
      LinearMap.bidualEvalEquiv (ULift.{uR} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uR, uM}
        (show matrixIdealSource.{uR, uM} from ULift.up matrixGenerator) liftedForm := by
  intro h
  rw [LinearMap.bidualEvalEquiv_apply, LinearMap.bidualEvalEquiv_apply] at h
  apply lifted_moves.{uR, uM}
  exact MulOpposite.op_injective h

example :
    ¬ Module.Free (ULift.{1} IntMatrix)ᵐᵒᵖ matrixIdealSource.{1, 0} ∧
      LinearMap.bidualEvalEquiv (ULift.{1} IntMatrix)ᵐᵒᵖ matrixIdealSource.{1, 0}
        (show matrixIdealSource.{1, 0} from ULift.up matrixGenerator)
        liftedForm.{1, 0} ≠ 0 := by
  refine ⟨matrixIdealSource_not_free, ?_⟩
  rw [evaluated_lift, matrixInclusion_generator]
  intro h
  exact intE11_proper_generator.1
    (congrArg (fun x : (ULift.{1} IntMatrix)ᵐᵒᵖ ↦ (MulOpposite.unop x).down) h)

example :
    ¬ Module.Free (ULift.{0} IntMatrix)ᵐᵒᵖ matrixIdealSource.{0, 2} ∧
      LinearMap.bidualEvalEquiv (ULift.{0} IntMatrix)ᵐᵒᵖ matrixIdealSource.{0, 2}
        (show matrixIdealSource.{0, 2} from ULift.up matrixUpperRightMember)
        liftedForm.{0, 2} ≠ 0 := by
  refine ⟨matrixIdealSource_not_free, ?_⟩
  rw [evaluated_lift, matrixInclusion_upperRight]
  intro h
  exact intE01_ne_zero
    (congrArg (fun x : (ULift.{0} IntMatrix)ᵐᵒᵖ ↦ (MulOpposite.unop x).down) h)

end ProjectiveModulesTests.BidualEvaluationUniverseClient
