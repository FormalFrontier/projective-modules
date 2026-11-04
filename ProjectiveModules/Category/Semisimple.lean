/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.SubmoduleEquivalence
public import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Module.ULift

/-!
# Semisimple modules and equivalences of module categories

An ordinary equivalence of categories of left modules preserves and reflects
semisimplicity of each module. The scalar and carrier universes are independent,
and the rings need not be commutative or nontrivial.

For rings, the forward theorem uses a target carrier universe containing the
regular target module. Its inverse image is semisimple because every module over
a semisimple ring is semisimple. The counit and the equivalence removing a lift
then give the regular target module. No identification of the two regular modules
under the equivalence, or finite-generation hypothesis, is needed.

## Main results

* `ModuleCat.isSemisimpleModule_iff_of_equivalence`
* `ModuleCat.isSemisimpleRing_of_equivalence`
* `ModuleCat.isSemisimpleRing_iff_of_equivalence`

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, for Morita
  invariance of semisimplicity.
* Mathlib's semisimple-module formalization by Aaron Anderson and Robert A. Spencer.
* Mathlib's module-category and subobject formalizations by Markus Himmel,
  Bhavik Mehta and Kim Morrison, and its lifted-module equivalence by Kim Morrison.
* Mathlib's order-isomorphism API, with contributions by Stephen Morgan, Kim Morrison,
  Johannes Hölzl and Reid Barton.
* The submodule order isomorphism in
  `ProjectiveModules.Category.SubmoduleEquivalence` and the lifted-regular-module
  argument in `ProjectiveModules.Category.Noetherian`, by Formal Frontier Agents.
-/

@[expose] public section

universe uR uS vR vS

open CategoryTheory

namespace ModuleCat

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

/-- An equivalence of module categories preserves and reflects semisimple modules,
with independent scalar and carrier universes.

This is the module form of Morita invariance of semisimplicity; see
C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*. -/
theorem isSemisimpleModule_iff_of_equivalence
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S) (X : ModuleCat.{vR} R) :
    IsSemisimpleModule R X ↔ IsSemisimpleModule S (e.functor.obj X) := by
  simpa only [isSemisimpleModule_iff] using
    (submoduleOrderIsoOfEquivalence e X).complementedLattice_iff

/-- An equivalence of module categories sends a semisimple ring to a semisimple ring
when the target carrier universe contains its ring. The source carrier universe
is unrestricted.

This is the forward ring form of Morita invariance of semisimplicity; see
C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*. -/
theorem isSemisimpleRing_of_equivalence
    (e : ModuleCat.{vR} R ≌ ModuleCat.{max uS vS} S) :
    IsSemisimpleRing R → IsSemisimpleRing S := by
  intro hR
  have : IsSemisimpleRing R := hR
  let Y : ModuleCat.{max uS vS} S := ModuleCat.of S (ULift.{vS} S)
  have hGY : IsSemisimpleModule R (e.inverse.obj Y) := inferInstance
  have hFGY : IsSemisimpleModule S (e.functor.obj (e.inverse.obj Y)) :=
    (isSemisimpleModule_iff_of_equivalence R S e (e.inverse.obj Y)).mp hGY
  let ε : e.functor.obj (e.inverse.obj Y) ≃ₗ[S] Y :=
    (e.counitIso.app Y).toLinearEquiv
  have hY : IsSemisimpleModule S Y := ε.isSemisimpleModule_iff.mp hFGY
  let l : Y ≃ₗ[S] S := ULift.moduleEquiv
  exact l.isSemisimpleModule_iff.mp hY

/-- An equivalence of module categories preserves and reflects semisimple rings
when each carrier universe contains its ring.

This is the ring form of Morita invariance of semisimplicity; see
C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*. -/
theorem isSemisimpleRing_iff_of_equivalence
    (e : ModuleCat.{max uR vR} R ≌ ModuleCat.{max uS vS} S) :
    IsSemisimpleRing R ↔ IsSemisimpleRing S :=
  ⟨isSemisimpleRing_of_equivalence R S e,
    isSemisimpleRing_of_equivalence S R e.symm⟩

end ModuleCat
