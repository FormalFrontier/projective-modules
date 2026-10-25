/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine
import ProjectiveModules.ExteriorPower.DeterminantLineBaseChange
public import ProjectiveModules.Module.Product
public import ProjectiveModules.Module.RightExtension
public import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.PicardGroup

/-!
# Determinant classes under changes of coefficients

The coefficient maps below include integer reduction modulo two, the two
projections of a dependent product with component ranks zero and one, and maps
to and within a zero ring. Integer coefficients, residue coefficients and the
regular-module carrier have independent `ULift` heights. The product's zero
component is over the nonzero ring `ℤ`, unlike the zero coefficient ring.
An arbitrary Picard representative under the identity map supplies an
invertible module without any freeness or unit-class assumption.

Each proposition displays the determinant classes of the source module and
its right scalar extension. Finite generation, projectivity and the coordinate
recovery maps are supplied by the existing module interfaces, independently of
these propositions.

## References

C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, for the
mathematical determinant construction. These examples use Mathlib's Picard and
invertible-module formalization by Junyan Xu, its `ULift` and finite-projective
interfaces, and the right scalar-extension and product constructions by
Formal Frontier Agents in this library. The scalar and carrier transports
follow the regular-module examples in `RightFiniteProjectiveExtensionClient`.
-/

@[expose] public section

noncomputable section

universe u v w

open ModuleCat

namespace ProjectiveModulesTests.DeterminantLineBaseChange

namespace IntegerReduction

example : Nontrivial (ULift.{w} ℤᵐᵒᵖ) := inferInstance

/-- Determinant classes for reduction of a positive-rank integral free module
modulo two, with independent scalar and carrier lifts. -/
def determinantClass : Prop := by
  let e : ℤᵐᵒᵖ ≃+* (ULift.{u} ℤ)ᵐᵒᵖ :=
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm.op
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm e
  letI : Module (ULift.{u} ℤ)ᵐᵒᵖ (ULift.{w} ℤᵐᵒᵖ) :=
    Module.compHom _ e.symm.toRingHom
  let a : ℤᵐᵒᵖ ≃ₛₗ[e.toRingHom] ULift.{w} ℤᵐᵒᵖ :=
    { __ := (AddEquiv.ulift : ULift.{w} ℤᵐᵒᵖ ≃+ ℤᵐᵒᵖ).symm
      map_smul' _ _ := rfl }
  letI : Module.Finite (ULift.{u} ℤ)ᵐᵒᵖ (ULift.{w} ℤᵐᵒᵖ) :=
    Module.Finite.of_surjective a.toLinearMap a.surjective
  letI : Module.Projective (ULift.{u} ℤ)ᵐᵒᵖ (ULift.{w} ℤᵐᵒᵖ) :=
    Module.Projective.of_equiv a
  let f : ULift.{u} ℤ →+* ULift.{v} (ZMod 2) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((Int.castRingHom (ZMod 2)).comp ULift.ringEquiv.toRingHom)
  letI : Module.Finite (ULift.{v} (ZMod 2))ᵐᵒᵖ
      (RightExtension.Obj f (ULift.{w} ℤᵐᵒᵖ)) := inferInstance
  letI : Module.Projective (ULift.{v} (ZMod 2))ᵐᵒᵖ
      (RightExtension.Obj f (ULift.{w} ℤᵐᵒᵖ)) := inferInstance
  exact
    @CommRing.Pic.mk (ULift.{v} (ZMod 2))ᵐᵒᵖ
        (Module.DeterminantLine (ULift.{v} (ZMod 2))ᵐᵒᵖ
          (RightExtension.Obj f (ULift.{w} ℤᵐᵒᵖ)))
        _ _ _ (Module.determinantLine_invertible (ULift.{v} (ZMod 2))ᵐᵒᵖ
          (RightExtension.Obj f (ULift.{w} ℤᵐᵒᵖ))) =
      CommRing.Pic.mapRingHom f.op
        (@CommRing.Pic.mk (ULift.{u} ℤ)ᵐᵒᵖ
          (Module.DeterminantLine (ULift.{u} ℤ)ᵐᵒᵖ (ULift.{w} ℤᵐᵒᵖ))
          _ _ _ (Module.determinantLine_invertible (ULift.{u} ℤ)ᵐᵒᵖ
            (ULift.{w} ℤᵐᵒᵖ)))

example : determinantClass.{u, v, w} := by
  dsimp (config := { zeta := false }) only [determinantClass]
  intro e f
  have : RingHomInvPair e.toRingHom e.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e
  have : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm e
  letI : Module (ULift.{u} ℤ)ᵐᵒᵖ (ULift.{w} ℤᵐᵒᵖ) :=
    Module.compHom _ e.symm.toRingHom
  let a : ℤᵐᵒᵖ ≃ₛₗ[e.toRingHom] ULift.{w} ℤᵐᵒᵖ :=
    { __ := (AddEquiv.ulift : ULift.{w} ℤᵐᵒᵖ ≃+ ℤᵐᵒᵖ).symm
      map_smul' _ _ := rfl }
  have : Module.Finite (ULift.{u} ℤ)ᵐᵒᵖ (ULift.{w} ℤᵐᵒᵖ) :=
    Module.Finite.of_surjective a.toLinearMap a.surjective
  have : Module.Projective (ULift.{u} ℤ)ᵐᵒᵖ (ULift.{w} ℤᵐᵒᵖ) :=
    Module.Projective.of_equiv a
  exact @RightExtension.determinantLine_mk _ _ _ _ f _ _ _ _ _

end IntegerReduction

namespace ProductProjection

example : Nontrivial ℤ := inferInstance
example : Subsingleton (Fin 0 → ℤᵐᵒᵖ) :=
  ⟨fun _ _ => funext (fun i => Fin.elim0 i)⟩
example : Nontrivial (Fin 1 → ℤᵐᵒᵖ) := inferInstance

example (b : Bool) :
    RightExtension.Obj (Pi.evalRingHom (fun _ : Bool => ℤ) b)
        (ModuleCat.piRight (fun _ : Bool => ℤ)
          (fun c => ModuleCat.of ℤᵐᵒᵖ (Fin (if c then 1 else 0) → ℤᵐᵒᵖ))) ≃ₗ[ℤᵐᵒᵖ]
      (Fin (if b then 1 else 0) → ℤᵐᵒᵖ) :=
  RightExtension.piRecoverLinearEquiv (fun _ : Bool => ℤ)
    (fun c => ModuleCat.of ℤᵐᵒᵖ (Fin (if c then 1 else 0) → ℤᵐᵒᵖ)) b

/-- Determinant classes for either coordinate of a dependent product whose
component free ranks are zero and one. -/
def determinantClass (b : Bool) : Prop := by
  let Ri : Bool → Type := fun _ => ℤ
  let Mi : ∀ c, ModuleCat (Ri c)ᵐᵒᵖ :=
    fun c => ModuleCat.of ℤᵐᵒᵖ (Fin (if c then 1 else 0) → ℤᵐᵒᵖ)
  letI : Module.Finite (∀ c, Ri c)ᵐᵒᵖ (ModuleCat.piRight Ri Mi) :=
    Module.finite_piRight Ri (fun c => Mi c)
  letI : Module.Projective (∀ c, Ri c)ᵐᵒᵖ (ModuleCat.piRight Ri Mi) :=
    Module.projective_piRight Ri (fun c => Mi c)
  letI : Module.Finite (Ri b)ᵐᵒᵖ
      (RightExtension.Obj (Pi.evalRingHom Ri b) (ModuleCat.piRight Ri Mi)) := inferInstance
  letI : Module.Projective (Ri b)ᵐᵒᵖ
      (RightExtension.Obj (Pi.evalRingHom Ri b) (ModuleCat.piRight Ri Mi)) := inferInstance
  exact
    @CommRing.Pic.mk (Ri b)ᵐᵒᵖ
        (Module.DeterminantLine (Ri b)ᵐᵒᵖ
          (RightExtension.Obj (Pi.evalRingHom Ri b) (ModuleCat.piRight Ri Mi)))
        _ _ _ (Module.determinantLine_invertible (Ri b)ᵐᵒᵖ
          (RightExtension.Obj (Pi.evalRingHom Ri b) (ModuleCat.piRight Ri Mi))) =
      CommRing.Pic.mapRingHom (Pi.evalRingHom Ri b).op
        (@CommRing.Pic.mk (∀ c, Ri c)ᵐᵒᵖ
          (Module.DeterminantLine (∀ c, Ri c)ᵐᵒᵖ (ModuleCat.piRight Ri Mi))
          _ _ _ (Module.determinantLine_invertible (∀ c, Ri c)ᵐᵒᵖ
            (ModuleCat.piRight Ri Mi)))

example (b : Bool) : determinantClass b := by
  dsimp (config := { zeta := false }) only [determinantClass]
  intro Ri Mi
  have : Module.Finite (∀ c, Ri c)ᵐᵒᵖ (ModuleCat.piRight Ri Mi) :=
    Module.finite_piRight Ri (fun c => Mi c)
  have : Module.Projective (∀ c, Ri c)ᵐᵒᵖ (ModuleCat.piRight Ri Mi) :=
    Module.projective_piRight Ri (fun c => Mi c)
  exact @RightExtension.determinantLine_mk _ _ _ _ (Pi.evalRingHom Ri b) _ _ _ _ _

end ProductProjection

namespace ZeroRing

example : Subsingleton (ZMod 1) := inferInstance

/-- The coefficient target may be the zero ring even for a positive-rank
source over the nonzero ring of integers. -/
def zeroTarget : Prop :=
  @CommRing.Pic.mk (ZMod 1)ᵐᵒᵖ
      (Module.DeterminantLine (ZMod 1)ᵐᵒᵖ
        (RightExtension.Obj (Int.castRingHom (ZMod 1)) ℤᵐᵒᵖ))
      _ _ _ (Module.determinantLine_invertible (ZMod 1)ᵐᵒᵖ
        (RightExtension.Obj (Int.castRingHom (ZMod 1)) ℤᵐᵒᵖ)) =
    CommRing.Pic.mapRingHom (Int.castRingHom (ZMod 1)).op
      (@CommRing.Pic.mk ℤᵐᵒᵖ (Module.DeterminantLine ℤᵐᵒᵖ ℤᵐᵒᵖ)
        _ _ _ (Module.determinantLine_invertible ℤᵐᵒᵖ ℤᵐᵒᵖ))

/-- Determinant classes are also defined when the coefficient source itself
is the zero ring. -/
def zeroCoefficients : Prop :=
  @CommRing.Pic.mk (ZMod 1)ᵐᵒᵖ
      (Module.DeterminantLine (ZMod 1)ᵐᵒᵖ
        (RightExtension.Obj (RingHom.id (ZMod 1)) (ZMod 1)ᵐᵒᵖ))
      _ _ _ (Module.determinantLine_invertible (ZMod 1)ᵐᵒᵖ
        (RightExtension.Obj (RingHom.id (ZMod 1)) (ZMod 1)ᵐᵒᵖ)) =
    CommRing.Pic.mapRingHom (RingHom.id (ZMod 1)).op
      (@CommRing.Pic.mk (ZMod 1)ᵐᵒᵖ
        (Module.DeterminantLine (ZMod 1)ᵐᵒᵖ (ZMod 1)ᵐᵒᵖ)
        _ _ _ (Module.determinantLine_invertible (ZMod 1)ᵐᵒᵖ (ZMod 1)ᵐᵒᵖ))

example : zeroTarget := by
  unfold zeroTarget
  exact RightExtension.determinantLine_mk (Int.castRingHom (ZMod 1)) ℤᵐᵒᵖ

example : zeroCoefficients := by
  unfold zeroCoefficients
  exact RightExtension.determinantLine_mk (RingHom.id (ZMod 1)) (ZMod 1)ᵐᵒᵖ

end ZeroRing

namespace InvertibleIdentity

example (R : Type u) [CommRing R] (ℓ : CommRing.Pic Rᵐᵒᵖ) :
    Module.Invertible Rᵐᵒᵖ (CommRing.Pic.AsModule ℓ) := inferInstance

/-- The identity coefficient map applied to an arbitrary invertible
representative, without a freeness or unit-class hypothesis. -/
def determinantClass (R : Type u) [CommRing R] (ℓ : CommRing.Pic Rᵐᵒᵖ) : Prop :=
  @CommRing.Pic.mk Rᵐᵒᵖ
      (Module.DeterminantLine Rᵐᵒᵖ
        (RightExtension.Obj (RingHom.id R) (CommRing.Pic.AsModule ℓ)))
      _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ
        (RightExtension.Obj (RingHom.id R) (CommRing.Pic.AsModule ℓ))) =
    CommRing.Pic.mapRingHom (RingHom.id R).op
      (@CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ (CommRing.Pic.AsModule ℓ))
        _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ (CommRing.Pic.AsModule ℓ)))

example (R : Type u) [CommRing R] (ℓ : CommRing.Pic Rᵐᵒᵖ) :
    determinantClass R ℓ := by
  unfold determinantClass
  exact RightExtension.determinantLine_mk (RingHom.id R) (CommRing.Pic.AsModule ℓ)

end InvertibleIdentity

end ProjectiveModulesTests.DeterminantLineBaseChange
