/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.FiniteProjectiveRestriction
public import ProjectiveModulesTests.FiniteProjectiveRestrictionUniverseClient

/-!
# Finite-projective restriction of a nonfree matrix ideal

Restriction along the lifted identity on opposite integer-matrix rings preserves
carriers, the stored right action and doubling on a nonzero generator. The
underlying-functor comparison fixes that generator in both directions. Source
scalars, target scalars and the ideal carrier have independent universes.

## References

These examples use the finite-projective restriction API of Projective Modules,
its matrix-ideal and semilinear-transport examples, and Mathlib's full-subcategory
morphism constructor and functor laws.
-/

@[expose] public section

universe uR uS uM

noncomputable section

namespace ProjectiveModulesTests.FiniteProjectiveRestrictionFunctorClient

open scoped Matrix
open CategoryTheory ModuleCat
open IdempotentSpanSemiringClient RightIdealRingConstructorClient
open FiniteProjectiveRestrictionUniverseClient

/-- Finite-projective restriction computes on the nonfree matrix ideal and its
nonzero members through its object, carrier, scalar, morphism and comparison API. -/
theorem matrixIdeal_restriction :
    let F : FiniteProjective.{uS, uM} (ULift.{uS} IntMatrix)ᵐᵒᵖ ⥤
        FiniteProjective.{uR, uM} (ULift.{uR} IntMatrix)ᵐᵒᵖ :=
      FiniteProjective.restrictScalars matrixIdentityEquiv.{uR, uS}.toRingHom.op
        matrixCoefficient_finite_projective.{uR, uS}
    let M := matrixIdeal.{uS, uM}
    let d : M ⟶ M := ObjectProperty.homMk matrixIdealDouble.{uS, uM}
    let E := FiniteProjective.restrictScalarsCompιIso
      matrixIdentityEquiv.{uR, uS}.toRingHom.op matrixCoefficient_finite_projective.{uR, uS}
    (F.obj M).obj = restrictedIdeal.{uR, uS, uM} ∧
      (F.obj M : Type uM) = ULift.{uM} matrixRightIdeal ∧
      ¬ Module.Free (ULift.{uS} IntMatrix)ᵐᵒᵖ M ∧ sourceGenerator.{uS, uM} ≠ 0 ∧
      @SMul.smul (ULift.{uR} IntMatrix)ᵐᵒᵖ (F.obj M) (F.obj M).obj.isModule.toSMul
        (MulOpposite.op (ULift.up intE11))
        (show F.obj M from restrictedUpperRightMember.{uR, uS, uM}) = 0 ∧
      (show F.obj M from restrictedUpperRightMember.{uR, uS, uM}) ≠ 0 ∧
      (F.map d).hom sourceGenerator.{uS, uM} ≠ sourceGenerator.{uS, uM} ∧
      (F.map d).hom sourceGenerator.{uS, uM} ≠ 0 ∧
      (E.hom.app M).hom sourceGenerator.{uS, uM} = sourceGenerator.{uS, uM} ∧
      (E.inv.app M).hom sourceGenerator.{uS, uM} = sourceGenerator.{uS, uM} ∧
      F.map (𝟙 M) = 𝟙 (F.obj M) ∧ F.map (d ≫ d) = F.map d ≫ F.map d := by
  dsimp only
  let φ : (ULift.{uR} IntMatrix)ᵐᵒᵖ →+* (ULift.{uS} IntMatrix)ᵐᵒᵖ :=
    matrixIdentityEquiv.{uR, uS}.toRingHom.op
  let hC : isFiniteProjective (ULift.{uR} IntMatrix)ᵐᵒᵖ
      ((ModuleCat.restrictScalars.{uS} φ).obj
        (ModuleCat.of (ULift.{uS} IntMatrix)ᵐᵒᵖ (ULift.{uS} IntMatrix)ᵐᵒᵖ)) :=
    matrixCoefficient_finite_projective.{uR, uS}
  let F : FiniteProjective.{uS, uM} (ULift.{uS} IntMatrix)ᵐᵒᵖ ⥤
      FiniteProjective.{uR, uM} (ULift.{uR} IntMatrix)ᵐᵒᵖ :=
    FiniteProjective.restrictScalars φ hC
  let M : FiniteProjective.{uS, uM} (ULift.{uS} IntMatrix)ᵐᵒᵖ := matrixIdeal.{uS, uM}
  let d : M ⟶ M := ObjectProperty.homMk matrixIdealDouble.{uS, uM}
  let x : M := sourceGenerator.{uS, uM}
  let y : F.obj M := restrictedDouble.{uR, uS, uM} restrictedGenerator
  have hmap : (F.map d).hom x = y :=
    (FiniteProjective.restrictScalars_map_apply φ hC d x).trans
      ((matrixIdealDouble_apply x).trans
        (restrictedDouble_apply restrictedGenerator.{uR, uS, uM}).symm)
  refine ⟨?_, ?_, matrixIdealSource_not_free, sourceGenerator_ne_zero, ?_,
    restrictedUpperRightMember_ne_zero, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FiniteProjective.restrictScalars_obj φ hC M
  · exact (FiniteProjective.restrictScalars_carrier φ hC M).trans
      matrixIdealSource_carrier.{uS, uM}
  · let r : (ULift.{uR} IntMatrix)ᵐᵒᵖ := MulOpposite.op (ULift.up intE11)
    let xUpper : M := restrictedUpperRightMember.{uR, uS, uM}
    have hsource :
        @SMul.smul (ULift.{uS} IntMatrix)ᵐᵒᵖ M M.obj.isModule.toSMul (φ r) xUpper = 0 :=
      (ModuleCat.restrictScalars.smul_def' φ (M := M.obj) r xUpper).symm.trans
        restrictedIdeal_action_boundary.{uR, uS, uM}.1
    exact (FiniteProjective.restrictScalars_smul φ hC M r xUpper).trans hsource
  · exact fun h ↦ restrictedDouble_generator_ne.{uR, uS, uM} (hmap.symm.trans h)
  · exact fun h ↦ restrictedDouble_generator_ne_zero.{uR, uS, uM} (hmap.symm.trans h)
  · exact FiniteProjective.restrictScalarsCompιIso_hom_app_apply φ hC M sourceGenerator
  · exact FiniteProjective.restrictScalarsCompιIso_inv_app_apply φ hC M sourceGenerator
  · exact F.map_id M
  · exact F.map_comp d d

example :
    let F := FiniteProjective.restrictScalars matrixIdentityEquiv.{0, 1}.toRingHom.op
      matrixCoefficient_finite_projective.{0, 1}
    let M := matrixIdeal.{1, 0}
    let d : M ⟶ M := ObjectProperty.homMk matrixIdealDouble.{1, 0}
    (F.map d).hom sourceGenerator.{1, 0} ≠ 0 ∧
      (F.map d).hom sourceGenerator.{1, 0} ≠ sourceGenerator.{1, 0} := by
  rcases matrixIdeal_restriction.{0, 1, 0} with ⟨_, _, _, _, _, _, hne, hnz, _⟩
  exact ⟨hnz, hne⟩

example :
    let F := FiniteProjective.restrictScalars matrixIdentityEquiv.{1, 0}.toRingHom.op
      matrixCoefficient_finite_projective.{1, 0}
    let M := matrixIdeal.{0, 0}
    let d : M ⟶ M := ObjectProperty.homMk matrixIdealDouble.{0, 0}
    (F.map d).hom sourceGenerator.{0, 0} ≠ 0 ∧
      (F.map d).hom sourceGenerator.{0, 0} ≠ sourceGenerator.{0, 0} := by
  rcases matrixIdeal_restriction.{1, 0, 0} with ⟨_, _, _, _, _, _, hne, hnz, _⟩
  exact ⟨hnz, hne⟩

example :
    let F := FiniteProjective.restrictScalars matrixIdentityEquiv.{0, 0}.toRingHom.op
      matrixCoefficient_finite_projective.{0, 0}
    let M := matrixIdeal.{0, 1}
    let d : M ⟶ M := ObjectProperty.homMk matrixIdealDouble.{0, 1}
    (F.map d).hom sourceGenerator.{0, 1} ≠ 0 ∧
      (F.map d).hom sourceGenerator.{0, 1} ≠ sourceGenerator.{0, 1} := by
  rcases matrixIdeal_restriction.{0, 0, 1} with ⟨_, _, _, _, _, _, hne, hnz, _⟩
  exact ⟨hnz, hne⟩

end ProjectiveModulesTests.FiniteProjectiveRestrictionFunctorClient
