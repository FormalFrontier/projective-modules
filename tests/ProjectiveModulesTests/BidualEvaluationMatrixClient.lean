/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules
public import ProjectiveModulesTests.FiniteProjectiveHomMatrixClient
import ProjectiveModules.KTheory.Dual

/-!
# Bidual evaluation on a nonfree matrix right ideal

The principal right ideal of the first diagonal unit in `M₂(ℤ)` is a nonzero,
nonfree finite projective module over the opposite matrix ring. The inclusion
into the ordinary matrix carrier is reused from the finite-projective Hom
client. Composing it with Mathlib's opposite linear equivalence gives a form
whose coefficient is the scalar ring itself, as required by bidual evaluation.

The ordinary-matrix mixed pairing separately distinguishes left coefficient
action on the first Hom from right coefficient action on its second Hom.
The diagonal unit preserves the upper-right value on the left and kills it on
the right; the upper-right unit changes the form at the principal generator.

## References

The right ideal, nonfreeness, matrix units and inclusion are the public matrix
models of Projective Modules. The coefficient encoding and mixed evaluation
use Mathlib's opposite linear equivalence and `LinearMap.flip`.
-/

namespace ProjectiveModulesTests.BidualEvaluationMatrixClient

open IdempotentSpanSemiringClient RightIdealRingConstructorClient
open FiniteProjectiveRestrictionModelClient FiniteProjectiveHomMatrixClient

private noncomputable def matrixOppositeForm :
    matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrixᵐᵒᵖ :=
  (MulOpposite.opLinearEquiv (M := IntMatrix) IntMatrixᵐᵒᵖ).toLinearMap.comp
    matrixInclusion

private theorem evaluated_generator :
    LinearMap.bidualEvalEquiv IntMatrixᵐᵒᵖ matrixRightIdeal matrixGenerator
      matrixOppositeForm = MulOpposite.op intE11 := by
  rw [LinearMap.bidualEvalEquiv_apply]
  change MulOpposite.op (matrixInclusion matrixGenerator) = MulOpposite.op intE11
  rw [matrixInclusion_generator]

private theorem evaluated_upperRight :
    LinearMap.bidualEvalEquiv IntMatrixᵐᵒᵖ matrixRightIdeal matrixUpperRightMember
      matrixOppositeForm = MulOpposite.op intE01 := by
  rw [LinearMap.bidualEvalEquiv_apply]
  change MulOpposite.op (matrixInclusion matrixUpperRightMember) = MulOpposite.op intE01
  rw [matrixInclusion_upperRight]

example :
    ¬ Module.Free IntMatrixᵐᵒᵖ matrixRightIdeal ∧ Nontrivial matrixRightIdeal ∧
      ¬ Commute intE11 intE01 ∧
      LinearMap.bidualEvalEquiv IntMatrixᵐᵒᵖ matrixRightIdeal matrixGenerator
        matrixOppositeForm ≠ 0 ∧
      LinearMap.bidualEvalEquiv IntMatrixᵐᵒᵖ matrixRightIdeal matrixUpperRightMember
        matrixOppositeForm ≠ 0 := by
  refine ⟨matrixRightIdeal_not_free, matrixRightIdeal_controls.2.2.1,
    intE11_not_commute, ?_, ?_⟩
  · rw [evaluated_generator]
    intro h
    exact intE11_proper_generator.1 (by simpa using congrArg MulOpposite.unop h)
  · rw [evaluated_upperRight]
    intro h
    exact intE01_ne_zero (by simpa using congrArg MulOpposite.unop h)

example :
    LinearMap.bidualEvalEquiv IntMatrixᵐᵒᵖ matrixRightIdeal matrixGenerator
        ((MulOpposite.opLinearEquiv (M := IntMatrix) IntMatrixᵐᵒᵖ).toLinearMap.comp
          (intE01 • matrixInclusion)) ≠
      LinearMap.bidualEvalEquiv IntMatrixᵐᵒᵖ matrixRightIdeal matrixGenerator
        matrixOppositeForm := by
  intro h
  apply matrixInclusion_left_moves.2.1
  simpa [matrixOppositeForm] using congrArg MulOpposite.unop h

example :
    (MulOpposite.op intE11 •
        (LinearMap.bidualEvalEquiv IntMatrixᵐᵒᵖ matrixRightIdeal matrixUpperRightMember))
      matrixOppositeForm = 0 ∧
      LinearMap.bidualEvalEquiv IntMatrixᵐᵒᵖ matrixRightIdeal
        (MulOpposite.op intE11 • matrixUpperRightMember) matrixOppositeForm = 0 := by
  constructor
  · change MulOpposite.op intE11 *
      (LinearMap.bidualEvalEquiv IntMatrixᵐᵒᵖ matrixRightIdeal matrixUpperRightMember
        matrixOppositeForm) = 0
    rw [evaluated_upperRight]
    change MulOpposite.op (intE01 * intE11) = 0
    rw [intE01_mul_e11]
    rfl
  · rw [matrix_right_action_boundary.1]
    simp

noncomputable example :
    matrixRightIdeal ≃ₗ[IntMatrixᵐᵒᵖ]
      ((matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrixᵐᵒᵖ) →ₗ[(IntMatrixᵐᵒᵖ)ᵐᵒᵖ]
        IntMatrixᵐᵒᵖ) :=
  LinearMap.bidualEvalEquiv IntMatrixᵐᵒᵖ matrixRightIdeal

example :
    LinearMap.flip (LinearMap.id :
      (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix) →ₗ[IntMatrix]
        (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix)) matrixGenerator
      matrixInclusion = intE11 ∧
      LinearMap.flip (LinearMap.id :
        (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix) →ₗ[IntMatrix]
          (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix)) matrixUpperRightMember
        matrixInclusion = intE01 :=
  ⟨matrixInclusion_generator, matrixInclusion_upperRight⟩

example :
    LinearMap.flip (LinearMap.id :
      (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix) →ₗ[IntMatrix]
        (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix)) matrixUpperRightMember
      (intE11 • matrixInclusion) = intE01 ∧
      (MulOpposite.op intE11 • (LinearMap.flip (LinearMap.id :
        (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix) →ₗ[IntMatrix]
          (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix)) matrixUpperRightMember))
        matrixInclusion = 0 := by
  refine ⟨matrixInclusion_left_order.1, ?_⟩
  change matrixInclusion matrixUpperRightMember * intE11 = 0
  exact matrixInclusion_left_order.2.2

example :
    LinearMap.flip (LinearMap.id :
      (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix) →ₗ[IntMatrix]
        (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix))
      (MulOpposite.op intE11 • matrixUpperRightMember) matrixInclusion = 0 :=
  matrixInclusion_source_action_boundary.1

example :
    LinearMap.flip (LinearMap.id :
      (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix) →ₗ[IntMatrix]
        (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix)) matrixGenerator
      (intE01 • matrixInclusion) ≠
      LinearMap.flip (LinearMap.id :
        (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix) →ₗ[IntMatrix]
          (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix)) matrixGenerator
        matrixInclusion :=
  matrixInclusion_left_moves.2.1

/- The class dual below uses the same nonfree source as `matrixOppositeForm`.
The existing `evaluated_upperRight` and ordinary-matrix `LinearMap.flip`
examples distinguish the op-valued bidual from the ordinary-valued pairing;
`matrixInclusion_left_order` and `matrixInclusion_right_product_not_linear`
already rule out reversing the coefficient action. -/

-- The target is a right module over the opposite matrix ring: its scalar ring
-- is the double opposite, obtained by canonical bundled restriction. Both
-- finite-projective witnesses are supplied by the dual closure theorem.
private theorem matrix_class_dual :
    KTheory.ProjectiveClass.dualEquiv IntMatrix
        (KTheory.ProjectiveClass.of IntMatrix matrixRightIdeal) =
      @KTheory.ProjectiveClass.of IntMatrixᵐᵒᵖ _
        ((ModuleCat.restrictScalars (RingEquiv.opOp IntMatrix).symm.toRingHom).obj
          ((ModuleCat.rightDual IntMatrix).obj
            (Opposite.op (ModuleCat.of IntMatrixᵐᵒᵖ matrixRightIdeal)))) _ _
        (ModuleCat.isFiniteProjective_rightDual_restrictScalars IntMatrix
          (ModuleCat.of IntMatrixᵐᵒᵖ matrixRightIdeal) matrixRightIdeal.property).1
        (ModuleCat.isFiniteProjective_rightDual_restrictScalars IntMatrix
          (ModuleCat.of IntMatrixᵐᵒᵖ matrixRightIdeal) matrixRightIdeal.property).2 := by
  exact KTheory.ProjectiveClass.dualEquiv_of_module IntMatrix matrixRightIdeal

-- Twice duality lands over the double-opposite ring. The signed K₀ input
-- also exercises the completion, rather than only its positive generators.
private theorem matrix_dual_twice :
    KTheory.ProjectiveClass.dualEquiv IntMatrixᵐᵒᵖ
        (KTheory.ProjectiveClass.dualEquiv IntMatrix
          (KTheory.ProjectiveClass.of IntMatrix matrixRightIdeal)) =
      KTheory.ProjectiveClass.map (RingEquiv.opOp IntMatrix).toRingHom
        (KTheory.ProjectiveClass.of IntMatrix matrixRightIdeal) ∧
      KTheory.K0.dualEquiv IntMatrixᵐᵒᵖ
          (KTheory.K0.dualEquiv IntMatrix (-(KTheory.K0.of IntMatrix matrixRightIdeal))) =
        KTheory.K0.map (RingEquiv.opOp IntMatrix).toRingHom
          (-(KTheory.K0.of IntMatrix matrixRightIdeal)) := by
  constructor
  · exact DFunLike.congr_fun
      (KTheory.ProjectiveClass.dualEquiv_comp_dualEquiv IntMatrix)
      (KTheory.ProjectiveClass.of IntMatrix matrixRightIdeal)
  · exact DFunLike.congr_fun (KTheory.K0.dualEquiv_comp_dualEquiv IntMatrix)
      (-(KTheory.K0.of IntMatrix matrixRightIdeal))

end ProjectiveModulesTests.BidualEvaluationMatrixClient
