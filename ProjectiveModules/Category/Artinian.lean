/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.ModuleEquivalence
public import ProjectiveModules.Category.SubmoduleEquivalence
public import Mathlib.RingTheory.Artinian.Module
import Mathlib.Algebra.Module.ULift
import Mathlib.Order.Hom.Basic

/-!
# Artinian modules and equivalences of module categories

Equivalences of module categories preserve and reflect Artinian modules, with
independent scalar and carrier universes. They also preserve the left-Artinian
ring property when the target carrier universe contains its scalar ring. The
ring equivalence theorem uses this bound on both sides. The rings need not be
commutative or nontrivial.

## Main results

* `ModuleCat.isArtinian_iff_of_equivalence`
* `ModuleCat.isArtinianRing_of_equivalence`
* `ModuleCat.isArtinianRing_iff_of_equivalence`

## Implementation notes

The existing submodule order isomorphism transports well-foundedness of strict
inclusion in the ordinary submodule order, without order duality or a
finite-generation assumption on the module. For ring transport, the inverse
image of a lifted regular target module is finitely generated, hence Artinian
over a left-Artinian source ring. The counit and the linear equivalence removing
the lift give Artinianity of the regular target module. This does not identify
the image of the regular source module with the regular target module.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, for Morita
  invariance.
* Mathlib's Artinian module formalization by Chris Hughes, and its
  module-category and subobject formalizations by Markus Himmel, Bhavik Mehta
  and Kim Morrison.
* Mathlib's finiteness formalization by Johan Commelin and lifted-module linear
  equivalence by Kim Morrison.
* The submodule, finite-generation and Noetherian transport interfaces in
  `ProjectiveModules.Category` by Formal Frontier Agents.
-/

@[expose] public section

universe uR uS vR vS

open CategoryTheory

namespace ModuleCat

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

/-- An equivalence of module categories preserves and reflects Artinian modules,
with independent scalar and carrier universes.

This is the module form of Morita invariance of the Artinian property; see
Weibel, *The K-book*. -/
theorem isArtinian_iff_of_equivalence
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S) (X : ModuleCat.{vR} R) :
    IsArtinian R X ↔ IsArtinian S (e.functor.obj X) := by
  let φ : Submodule R X ≃o Submodule S (e.functor.obj X) :=
    submoduleOrderIsoOfEquivalence e X
  constructor
  · intro h
    have : IsArtinian R X := h
    exact φ.symm.toOrderEmbedding.wellFoundedLT
  · intro h
    have : IsArtinian S (e.functor.obj X) := h
    exact φ.toOrderEmbedding.wellFoundedLT

/-- An equivalence of module categories sends a left-Artinian ring to a
left-Artinian ring when the target carrier universe contains its ring.
There is no restriction on the source carrier universe.

This is the forward ring form of Morita invariance of the Artinian property; see
Weibel, *The K-book*. -/
theorem isArtinianRing_of_equivalence
    (e : ModuleCat.{vR} R ≌ ModuleCat.{max uS vS} S) :
    IsArtinianRing R → IsArtinianRing S := by
  intro hR
  have : IsArtinianRing R := hR
  let Y : ModuleCat.{max uS vS} S := ModuleCat.of S (ULift.{vS} S)
  have : Module.Finite S Y := inferInstance
  have : Module.Finite R (e.inverse.obj Y) :=
    (finite_iff_of_equivalence S R e.symm Y).mpr inferInstance
  have hGY : IsArtinian R (e.inverse.obj Y) := inferInstance
  have hFGY : IsArtinian S (e.functor.obj (e.inverse.obj Y)) :=
    (isArtinian_iff_of_equivalence R S e (e.inverse.obj Y)).mp hGY
  let ε : e.functor.obj (e.inverse.obj Y) ≃ₗ[S] Y :=
    (e.counitIso.app Y).toLinearEquiv
  have hY : IsArtinian S Y := ε.isArtinian_iff.mp hFGY
  let l : Y ≃ₗ[S] S := ULift.moduleEquiv
  exact l.isArtinian_iff.mp hY

/-- An equivalence of module categories preserves and reflects the
left-Artinian ring property when each carrier universe contains its ring.

This is the ring form of Morita invariance of the Artinian property; see
Weibel, *The K-book*. -/
theorem isArtinianRing_iff_of_equivalence
    (e : ModuleCat.{max uR vR} R ≌ ModuleCat.{max uS vS} S) :
    IsArtinianRing R ↔ IsArtinianRing S :=
  ⟨isArtinianRing_of_equivalence R S e,
    isArtinianRing_of_equivalence S R e.symm⟩

end ModuleCat
