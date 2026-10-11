/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Lens
module

import ProjectiveModules.Category.FiniteProjective
import ProjectiveModules.Module.RightExtension
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Right scalar extension of regular matrix modules

The finite-projective restriction uses Mathlib's full-subcategory lift. Its
additivity uses the additive right-extension functor, together with Mathlib's
instances for inclusion, composition and lifting. The biproduct comparison and
forgetful isomorphism use the generic categorical API.

The coefficient homomorphism reduces integral two-by-two matrices modulo five.
Matrix units distinguish the order of multiplication and witness a nontrivial
morphism. Scalar and carrier lifts vary independently.

The declarations are private importing examples. They use scalar extension,
full-subcategory lifting and biproduct comparison without adding the chosen
matrix rings, morphisms or lifts to the library's public API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ModuleCat

namespace ProjectiveModulesTests.RightFiniteProjectiveExtension

universe uR uS uM

private theorem finiteProjectiveExtension_property
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S)
    (M : FiniteProjective.{uR, uM} Rᵐᵒᵖ) :
    isFiniteProjective.{uS, max uM uS} Sᵐᵒᵖ
      (((isFiniteProjective.{uR, uM} Rᵐᵒᵖ).ι ⋙ RightExtension.functor' f).obj M) := by
  let _ : Module.Finite Rᵐᵒᵖ M.obj := M.property.1
  let _ : Module.Projective Rᵐᵒᵖ M.obj := M.property.2
  simpa only [isFiniteProjective_iff, CategoryTheory.Functor.comp_obj,
    ObjectProperty.ι_obj, RightExtension.functor'_obj] using
    (show Module.Finite Sᵐᵒᵖ (RightExtension.Obj f M.obj) ∧
      Module.Projective Sᵐᵒᵖ (RightExtension.Obj f M.obj) from
      ⟨inferInstance, inferInstance⟩)

private abbrev finiteProjectiveExtension
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    FiniteProjective.{uR, uM} Rᵐᵒᵖ ⥤ FiniteProjective.{uS, max uM uS} Sᵐᵒᵖ :=
  (isFiniteProjective.{uS, max uM uS} Sᵐᵒᵖ).lift
    ((isFiniteProjective.{uR, uM} Rᵐᵒᵖ).ι ⋙ RightExtension.functor' f)
    (finiteProjectiveExtension_property f)

private instance finiteProjectiveExtensionAdditive
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (finiteProjectiveExtension.{uR, uS, uM} f).Additive :=
  inferInstanceAs
    ((isFiniteProjective.{uS, max uM uS} Sᵐᵒᵖ).lift
      ((isFiniteProjective.{uR, uM} Rᵐᵒᵖ).ι ⋙ RightExtension.functor' f)
      (finiteProjectiveExtension_property f)).Additive

private abbrev IntMatrices := Matrix (Fin 2) (Fin 2) ℤ
private abbrev ModFiveMatrices := Matrix (Fin 2) (Fin 2) (ZMod 5)

private def modFive : IntMatrices →+* ModFiveMatrices :=
  (Int.castRingHom (ZMod 5)).mapMatrix

private abbrev intRegular : FiniteProjective IntMatricesᵐᵒᵖ :=
  FiniteProjective.of IntMatricesᵐᵒᵖ IntMatricesᵐᵒᵖ

private abbrev matrixExtension := finiteProjectiveExtension modFive

private abbrev zeroModule : FiniteProjective IntMatricesᵐᵒᵖ :=
  FiniteProjective.of IntMatricesᵐᵒᵖ PUnit

private def zeroExtension : FiniteProjective ModFiveMatricesᵐᵒᵖ :=
  matrixExtension.obj zeroModule

private def identityScalarUnit :
    (finiteProjectiveExtension (RingHom.id IntMatrices)).obj intRegular :=
  RightExtension.tmul (RingHom.id IntMatrices) (1 : intRegular) 1

private def leftUnitMap : intRegular ⟶ intRegular :=
  FiniteProjective.ofHom IntMatricesᵐᵒᵖ
    (LinearMap.mulRight IntMatricesᵐᵒᵖ
      (MulOpposite.op (Matrix.single (0 : Fin 2) 1 (1 : ℤ))))

private theorem intMatrices_noncommutative :
    (Matrix.single (0 : Fin 2) 1 (1 : ℤ) : IntMatrices) * Matrix.single 1 0 1 ≠
      Matrix.single 1 0 1 * Matrix.single 0 1 1 := by
  intro h
  have h00 := congrArg (fun A : IntMatrices ↦ A 0 0) h
  norm_num at h00

private theorem modFiveMatrices_noncommutative :
    (Matrix.single (0 : Fin 2) 1 (1 : ZMod 5) : ModFiveMatrices) *
        Matrix.single 1 0 1 ≠ Matrix.single 1 0 1 * Matrix.single 0 1 1 := by
  intro h
  have h00 := congrArg (fun A : ModFiveMatrices ↦ A 0 0) h
  norm_num at h00
  have h51 : (5 : ℕ) = 1 := ZMod.one_eq_zero_iff.mp h00
  norm_num at h51

private theorem modFive_not_injective : ¬ Function.Injective modFive := by
  have hfive : (5 : ZMod 5) = 0 := ZMod.natCast_self 5
  have hz : modFive (Matrix.single (0 : Fin 2) 1 (5 : ℤ)) = modFive 0 := by
    ext i j
    by_cases hi : (0 : Fin 2) = i <;> by_cases hj : (1 : Fin 2) = j <;>
      simp [modFive, hi, hj, hfive]
  intro h
  have h01 := congrArg (fun A : IntMatrices ↦ A 0 1) (h hz)
  norm_num at h01

private def regularSemilinear
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Rᵐᵒᵖ →ₛₗ[RingHom.op f] Sᵐᵒᵖ where
  toFun := RingHom.op f
  map_add' := (RingHom.op f).map_add
  map_smul' := (RingHom.op f).map_mul

private def regularEvaluation
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    RightExtension.Obj f Rᵐᵒᵖ →ₗ[Sᵐᵒᵖ] Sᵐᵒᵖ :=
  RightExtension.fromSemilinear f (regularSemilinear f)

private theorem extended_unit_ne_zero :
    (RightExtension.tmul modFive (1 : intRegular) 1 :
      matrixExtension.obj intRegular) ≠ 0 := by
  intro h
  have he := congrArg (regularEvaluation modFive) h
  have h10 : (1 : ModFiveMatricesᵐᵒᵖ) = 0 := by
    simpa [regularEvaluation, regularSemilinear] using he
  have h00 : (1 : ZMod 5) = 0 := by
    simpa only [MulOpposite.unop_one, MulOpposite.unop_zero, Matrix.one_apply_eq,
      Matrix.zero_apply] using
      congrArg (fun A : ModFiveMatricesᵐᵒᵖ ↦ MulOpposite.unop A 0 0) h10
  have h51 : (5 : ℕ) = 1 := ZMod.one_eq_zero_iff.mp h00
  norm_num at h51

private theorem extended_leftUnitMap_on_tmul :
    (matrixExtension.map leftUnitMap).hom.hom
        (RightExtension.tmul modFive
          (MulOpposite.op (Matrix.single (1 : Fin 2) 0 (1 : ℤ))) 1) =
      RightExtension.tmul modFive
        (MulOpposite.op (Matrix.single (0 : Fin 2) 0 (1 : ℤ))) 1 := by
  have h := ObjectProperty.ι_obj_lift_map
    (isFiniteProjective ModFiveMatricesᵐᵒᵖ)
    ((isFiniteProjective IntMatricesᵐᵒᵖ).ι ⋙ RightExtension.functor' modFive)
    (finiteProjectiveExtension_property modFive) leftUnitMap
  rw [ObjectProperty.ι_map] at h
  rw [h, CategoryTheory.Functor.comp_map, ObjectProperty.ι_map,
    RightExtension.functor'_map_tmul]
  congr 1
  change ConcreteCategory.hom leftUnitMap
      (MulOpposite.op (Matrix.single (1 : Fin 2) 0 (1 : ℤ))) = _
  simp only [leftUnitMap, FiniteProjective.ofHom, ConcreteCategory.hom_ofHom,
    LinearMap.mulRight_apply, ← MulOpposite.op_mul, Matrix.single_mul_single_same, mul_one]

private theorem extended_identity_on_unit :
    (matrixExtension.map (𝟙 intRegular)).hom.hom
        (RightExtension.tmul modFive (1 : intRegular) 1) =
      RightExtension.tmul modFive (1 : intRegular) 1 := by
  rw [matrixExtension.map_id]
  rfl

private theorem extended_zero_on_unit :
    (matrixExtension.map (0 : intRegular ⟶ intRegular)).hom.hom
        (RightExtension.tmul modFive (1 : intRegular) 1) = 0 := by
  rw [matrixExtension.map_zero]
  rfl

private def matrixForgetIso :
    matrixExtension ⋙ (isFiniteProjective ModFiveMatricesᵐᵒᵖ).ι ≅
      (isFiniteProjective IntMatricesᵐᵒᵖ).ι ⋙ RightExtension.functor' modFive :=
  ObjectProperty.liftCompιIso _ _ _

private theorem matrixForgetIso_on_unit :
    matrixForgetIso.hom.app intRegular
        (RightExtension.tmul modFive (1 : intRegular) 1) =
      RightExtension.tmul modFive (1 : intRegular) 1 :=
  rfl

-- Mathlib's finite-to-binary construction is deliberately not a global instance.
private noncomputable instance intMatricesBinaryBiproducts :
    HasBinaryBiproducts (FiniteProjective.{0, 0} IntMatricesᵐᵒᵖ) :=
  hasBinaryBiproducts_of_finite_biproducts _

private noncomputable instance modFiveMatricesBinaryBiproducts :
    HasBinaryBiproducts (FiniteProjective.{0, 0} ModFiveMatricesᵐᵒᵖ) :=
  hasBinaryBiproducts_of_finite_biproducts _

private instance matrixExtensionPreservesBinaryBiproducts :
    PreservesBinaryBiproducts matrixExtension :=
  preservesBinaryBiproducts_of_preservesBiproducts matrixExtension

private noncomputable def matrixBiprodIso :
    matrixExtension.obj (intRegular ⊞ intRegular) ≅
      matrixExtension.obj intRegular ⊞ matrixExtension.obj intRegular :=
  matrixExtension.mapBiprod intRegular intRegular

private theorem matrixBiprodIso_fst :
    matrixBiprodIso.hom ≫ biprod.fst =
      matrixExtension.map (biprod.fst : intRegular ⊞ intRegular ⟶ intRegular) := by
  simp only [matrixBiprodIso, Functor.mapBiprod_hom, biprod.lift_fst]

private abbrev liftedSourceEquiv :
    IntMatricesᵐᵒᵖ ≃+* (ULift.{uR} IntMatrices)ᵐᵒᵖ :=
  (ULift.ringEquiv : ULift.{uR} IntMatrices ≃+* IntMatrices).symm.op

private instance liftedSourceInvPair :
    RingHomInvPair liftedSourceEquiv.{uR}.toRingHom liftedSourceEquiv.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv liftedSourceEquiv

private instance liftedSourceInvPairSymm :
    RingHomInvPair liftedSourceEquiv.{uR}.symm.toRingHom liftedSourceEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm liftedSourceEquiv

private instance liftedCarrierModule :
    Module (ULift.{uR} IntMatrices)ᵐᵒᵖ (ULift.{uM} IntMatricesᵐᵒᵖ) :=
  Module.compHom _ liftedSourceEquiv.symm.toRingHom

private def liftedRegularEquiv :
    IntMatricesᵐᵒᵖ ≃ₛₗ[liftedSourceEquiv.{uR}.toRingHom]
      ULift.{uM} IntMatricesᵐᵒᵖ where
  __ := (AddEquiv.ulift : ULift.{uM} IntMatricesᵐᵒᵖ ≃+ IntMatricesᵐᵒᵖ).symm
  map_smul' _ _ := rfl

private instance liftedCarrierFinite :
    Module.Finite (ULift.{uR} IntMatrices)ᵐᵒᵖ (ULift.{uM} IntMatricesᵐᵒᵖ) :=
  Module.Finite.of_surjective liftedRegularEquiv.{uR, uM}.toLinearMap
    liftedRegularEquiv.{uR, uM}.surjective

private instance liftedCarrierProjective :
    Module.Projective (ULift.{uR} IntMatrices)ᵐᵒᵖ (ULift.{uM} IntMatricesᵐᵒᵖ) :=
  Module.Projective.of_equiv liftedRegularEquiv.{uR, uM}

private def liftedModFive : ULift.{uR} IntMatrices →+* ULift.{uS} ModFiveMatrices :=
  ULift.ringEquiv.symm.toRingHom.comp (modFive.comp ULift.ringEquiv.toRingHom)

private abbrev liftedRegular :
    FiniteProjective.{uR, uM} (ULift.{uR} IntMatrices)ᵐᵒᵖ :=
  FiniteProjective.of (ULift.{uR} IntMatrices)ᵐᵒᵖ (ULift.{uM} IntMatricesᵐᵒᵖ)

private def liftedExtension :
    FiniteProjective.{uS, max uM uS} (ULift.{uS} ModFiveMatrices)ᵐᵒᵖ :=
  (finiteProjectiveExtension liftedModFive.{uR, uS}).obj liftedRegular.{uR, uM}

private def liftedUnit : liftedExtension.{uR, uS, uM} :=
  RightExtension.tmul liftedModFive (ULift.up 1) (ULift.up 1)

private def liftedIdentity : liftedExtension.{uR, uS, uM} ⟶ liftedExtension.{uR, uS, uM} :=
  (finiteProjectiveExtension liftedModFive.{uR, uS}).map (𝟙 liftedRegular.{uR, uM})

private theorem liftedIdentity_on_unit :
    liftedIdentity.{uR, uS, uM}.hom.hom liftedUnit = liftedUnit := by
  have h : liftedIdentity.{uR, uS, uM} = 𝟙 liftedExtension.{uR, uS, uM} :=
    (finiteProjectiveExtension.{uR, uS, uM} liftedModFive.{uR, uS}).map_id
      liftedRegular.{uR, uM}
  rw [h]
  rfl

private def higherScalarExtension :
    FiniteProjective.{1, 1} (ULift.{1} ModFiveMatrices)ᵐᵒᵖ :=
  (finiteProjectiveExtension liftedModFive.{0, 1}).obj liftedRegular.{0, 0}

private def higherScalarUnit : higherScalarExtension :=
  RightExtension.tmul liftedModFive.{0, 1} (ULift.up 1) (ULift.up 1)

private def higherSourceScalarExtension :
    FiniteProjective.{0, 0} (ULift.{0} ModFiveMatrices)ᵐᵒᵖ :=
  (finiteProjectiveExtension liftedModFive.{1, 0}).obj liftedRegular.{1, 0}

private def higherSourceScalarUnit : higherSourceScalarExtension :=
  RightExtension.tmul liftedModFive.{1, 0} (ULift.up 1) (ULift.up 1)

private def higherScalarIdentity : higherScalarExtension ⟶ higherScalarExtension :=
  (finiteProjectiveExtension liftedModFive.{0, 1}).map (𝟙 liftedRegular.{0, 0})

private theorem higherScalarIdentity_on_unit :
    higherScalarIdentity.hom.hom higherScalarUnit = higherScalarUnit := by
  have h : higherScalarIdentity = 𝟙 higherScalarExtension :=
    (finiteProjectiveExtension.{0, 1, 0} liftedModFive.{0, 1}).map_id
      liftedRegular.{0, 0}
  rw [h]
  rfl

private abbrev closedExplicitExtension :=
  (RightExtension.functor.{0, 1, 0} liftedModFive.{0, 1}).obj liftedRegular.{0, 1}.obj

private def closedExplicitUnit : closedExplicitExtension :=
  RightExtension.tmul liftedModFive.{0, 1} (ULift.up 1) (ULift.up 1)

private def closedExplicitIdentity : closedExplicitExtension ⟶ closedExplicitExtension :=
  (RightExtension.functor.{0, 1, 0} liftedModFive.{0, 1}).map (𝟙 liftedRegular.{0, 1}.obj)

private theorem closedExplicitIdentity_on_unit :
    closedExplicitIdentity.hom closedExplicitUnit = closedExplicitUnit := by
  simpa only [closedExplicitIdentity, ConcreteCategory.id_apply] using
    ConcreteCategory.congr_hom
      ((RightExtension.functor.{0, 1, 0} liftedModFive.{0, 1}).map_id
        liftedRegular.{0, 1}.obj) closedExplicitUnit

end ProjectiveModulesTests.RightFiniteProjectiveExtension
