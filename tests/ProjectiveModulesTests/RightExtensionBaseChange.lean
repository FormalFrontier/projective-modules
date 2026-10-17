/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.RightExtensionTensorProduct
import ProjectiveModules.Module.RightExtensionFree
import ProjectiveModules.Module.RightRegular
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.ZMod.Basic

/-!
# Pointwise right-module tensor base change

The public pointwise comparisons identify right scalar extension with
opposite-base scalar extension and distribute it over tensor products. The
source actions are the given opposite-ring actions, and the extended objects
retain their stored right-module structures. Private coefficient controls
identify restriction along the opposite ring homomorphism with its canonical
homomorphism-induced algebra, including the whole module structure.

The comparisons are instantiated for the noninjective homomorphism
`ℤ → ZMod 2` and for arbitrary independently sized source modules with the
one-element target ring. Two pure-tensor computations use the public
characteristic lemmas over `ℤ → ZMod 2`. An independent regular-module
equivalence detects the nonzero extended unit; the zero-target example records
its collapse.

## References

* Projective Modules' right scalar extension and finite right-free coordinate
  equivalences. The regular-module composition is the one used in
  `KTheory.ProjectiveClass.map_of_self`.
* Mathlib's change-of-rings and opposite-module interfaces, finite-coordinate
  linear equivalences, `ZMod 2`, and subsingleton modules over the zero ring.
-/

universe uR uS uM uN

open scoped TensorProduct ChangeOfRings

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

private abbrev oppositeScalarComparison (φ : R →+* S) (M : ModuleCat.{uM} Rᵐᵒᵖ) :=
  Obj φ M ≃ₗ[Sᵐᵒᵖ] (ModuleCat.extendScalars (RingHom.op φ)).obj M

private abbrev tensorComparison (φ : R →+* S)
    (M : ModuleCat.{uM} Rᵐᵒᵖ) (N : ModuleCat.{uN} Rᵐᵒᵖ) :=
  Obj φ (M ⊗[Rᵐᵒᵖ] N) ≃ₗ[Sᵐᵒᵖ] Obj φ M ⊗[Sᵐᵒᵖ] Obj φ N

private noncomputable def oppositeCoefficientModule (φ : R →+* S) : Module Rᵐᵒᵖ Sᵐᵒᵖ :=
  ((ModuleCat.restrictScalars (RingHom.op φ)).obj
    (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)).isModule

private theorem oppositeCoefficientModule_eq_compHom (φ : R →+* S) :
    oppositeCoefficientModule φ = Module.compHom Sᵐᵒᵖ (RingHom.op φ) :=
  rfl

private def oppositeCoefficientAlgebra (φ : R →+* S) : Algebra Rᵐᵒᵖ Sᵐᵒᵖ :=
  (RingHom.op φ).toAlgebra

private theorem oppositeCoefficientAlgebra_toModule (φ : R →+* S) :
    @Algebra.toModule Rᵐᵒᵖ Sᵐᵒᵖ _ _ (oppositeCoefficientAlgebra φ) =
      oppositeCoefficientModule φ :=
  rfl

private theorem oppositeCoefficientAlgebra_toSMul (φ : R →+* S) :
    (oppositeCoefficientAlgebra φ).toSMul = (oppositeCoefficientModule φ).toSMul :=
  rfl

private theorem oppositeCoefficientModule_smul (φ : R →+* S) (r : R) (s : S) :
    @SMul.smul Rᵐᵒᵖ Sᵐᵒᵖ (oppositeCoefficientModule φ).toSMul
      (MulOpposite.op r) (MulOpposite.op s) = MulOpposite.op (s * φ r) :=
  rfl

private def modTwoHom : ℤ →+* ZMod 2 :=
  Int.castRingHom (ZMod 2)

private noncomputable def modTwoRegularEquiv :
    Obj modTwoHom ℤᵐᵒᵖ ≃ₗ[(ZMod 2)ᵐᵒᵖ] (ZMod 2)ᵐᵒᵖ :=
  (mapLinearEquiv modTwoHom
    ((LinearEquiv.piUnique ℤᵐᵒᵖ (fun _ : Fin 1 ↦ ℤᵐᵒᵖ)).symm.trans
      (Module.rightFreeCoordEquiv ℤ (Fin 1)))).trans
    ((rightFreeLinearEquiv modTwoHom (Fin 1)).trans
      ((Module.rightFreeCoordEquiv (ZMod 2) (Fin 1)).symm.trans
        (LinearEquiv.piUnique (ZMod 2)ᵐᵒᵖ (fun _ : Fin 1 ↦ (ZMod 2)ᵐᵒᵖ))))

private noncomputable def modTwoScalarComparison :
    oppositeScalarComparison modTwoHom (ModuleCat.of ℤᵐᵒᵖ ℤᵐᵒᵖ) :=
  oppositeScalarEquiv modTwoHom (ModuleCat.of ℤᵐᵒᵖ ℤᵐᵒᵖ)

private noncomputable def modTwoTensorComparison :
    tensorComparison modTwoHom
      (ModuleCat.of ℤᵐᵒᵖ ℤᵐᵒᵖ) (ModuleCat.of ℤᵐᵒᵖ ℤᵐᵒᵖ) :=
  tensorBaseChangeEquiv modTwoHom
    (ModuleCat.of ℤᵐᵒᵖ ℤᵐᵒᵖ) (ModuleCat.of ℤᵐᵒᵖ ℤᵐᵒᵖ)

private theorem modTwoUnit_ne_zero :
    tmul modTwoHom (MulOpposite.op (1 : ℤ)) (1 : ZMod 2) ≠ 0 := by
  intro hzero
  have hunit :
      modTwoRegularEquiv (tmul modTwoHom (MulOpposite.op (1 : ℤ)) (1 : ZMod 2)) = 1 := by
    simp [modTwoRegularEquiv]
  have h := congrArg modTwoRegularEquiv hzero
  rw [hunit, LinearEquiv.map_zero] at h
  exact one_ne_zero h

private def punitHom (R : Type uR) [CommRing R] : R →+* PUnit.{uS + 1} where
  toFun _ := PUnit.unit
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private noncomputable def punitScalarComparison (M : ModuleCat.{uM} Rᵐᵒᵖ) :
    oppositeScalarComparison (punitHom.{uR, uS} R) M :=
  oppositeScalarEquiv (punitHom.{uR, uS} R) M

private noncomputable def punitTensorComparison
    (M : ModuleCat.{uM} Rᵐᵒᵖ) (N : ModuleCat.{uN} Rᵐᵒᵖ) :
    tensorComparison (punitHom.{uR, uS} R) M N :=
  tensorBaseChangeEquiv (punitHom.{uR, uS} R) M N

private theorem punitUnit_eq_zero :
    tmul (punitHom.{uR, uS} R) (MulOpposite.op (1 : R)) (1 : PUnit.{uS + 1}) = 0 := by
  letI : Subsingleton (Obj (punitHom.{uR, uS} R) Rᵐᵒᵖ) :=
    Module.subsingleton (PUnit.{uS + 1})ᵐᵒᵖ _
  exact Subsingleton.elim _ _

example :
    oppositeScalarEquiv modTwoHom (ModuleCat.of ℤᵐᵒᵖ ℤᵐᵒᵖ)
        (tmul modTwoHom (MulOpposite.op (1 : ℤ)) (1 : ZMod 2)) =
      MulOpposite.op (1 : ZMod 2) ⊗ₜ[ℤᵐᵒᵖ, RingHom.op modTwoHom]
        MulOpposite.op (1 : ℤ) :=
  oppositeScalarEquiv_tmul modTwoHom (ModuleCat.of ℤᵐᵒᵖ ℤᵐᵒᵖ)
    (MulOpposite.op (1 : ℤ)) (1 : ZMod 2)

example :
    tensorBaseChangeEquiv modTwoHom
        (ModuleCat.of ℤᵐᵒᵖ ℤᵐᵒᵖ) (ModuleCat.of ℤᵐᵒᵖ ℤᵐᵒᵖ)
        (tmul modTwoHom
          (MulOpposite.op (1 : ℤ) ⊗ₜ[ℤᵐᵒᵖ] MulOpposite.op (1 : ℤ)) (1 : ZMod 2)) =
      tmul modTwoHom (MulOpposite.op (1 : ℤ)) (1 : ZMod 2) ⊗ₜ[(ZMod 2)ᵐᵒᵖ]
        tmul modTwoHom (MulOpposite.op (1 : ℤ)) (1 : ZMod 2) :=
  tensorBaseChangeEquiv_tmul modTwoHom
    (ModuleCat.of ℤᵐᵒᵖ ℤᵐᵒᵖ) (ModuleCat.of ℤᵐᵒᵖ ℤᵐᵒᵖ)
    (MulOpposite.op (1 : ℤ)) (MulOpposite.op (1 : ℤ)) (1 : ZMod 2)

end ModuleCat.RightExtension
