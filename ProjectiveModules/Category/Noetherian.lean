/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.ModuleEquivalence
public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Noetherian modules and equivalences of module categories

A module is a Noetherian object of its module category exactly when it is
Noetherian as a module. Equivalences of module categories preserve and reflect
this property, with independent scalar and carrier universes.

The forward ring theorem takes its target carrier universe to be `max uS vS`,
without restricting the source carrier universe. The ring equivalence theorem
uses this form on both sides. Here `IsNoetherianRing` means left Noetherian;
commutativity is not assumed.

## Main results

* `CategoryTheory.isNoetherianObject_iff_of_equivalence`
* `ModuleCat.isNoetherianObject_iff`
* `ModuleCat.isNoetherian_iff_of_equivalence`
* `ModuleCat.isNoetherianRing_of_equivalence`
* `ModuleCat.isNoetherianRing_iff_of_equivalence`

## Implementation notes

The order isomorphisms on subobjects and submodules transport the ascending
chain condition. Well-foundedness passes along dual order embeddings, as in
Mathlib's Noetherian-module proofs. All submodules occur, without a
finite-generation assumption. For ring transport, the inverse image of a lifted
regular target module is finitely generated, hence Noetherian over a
left-Noetherian source ring. The
counit and the linear equivalence removing the lift then give the conclusion.
The target maximum universe suffices to represent this lifted module; the
source regular module is not needed for the forward implication.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, for Morita
  invariance.
* Mathlib's Noetherian module formalization by Mario Carneiro, Kevin Buzzard
  and María Inés de Frutos-Fernández, and its Noetherian object formalization
  by Joël Riou.
* Mathlib's module-category and subobject formalizations by Markus Himmel,
  Bhavik Mehta and Kim Morrison, finiteness formalization by Johan Commelin,
  and lifted-module linear equivalence by Kim Morrison.
* The finite-generation transport in
  `ProjectiveModules.Category.ModuleEquivalence` by Formal Frontier Agents.
-/

@[expose] public section

universe uC uD vC vD uR uS vR vS

open CategoryTheory

namespace CategoryTheory

/-- An equivalence of categories preserves and reflects Noetherian objects,
with independent object and morphism universes. -/
theorem isNoetherianObject_iff_of_equivalence
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    (e : C ≌ D) (X : C) :
    IsNoetherianObject X ↔ IsNoetherianObject (e.functor.obj X) := by
  let φ : Subobject X ≃o Subobject (e.functor.obj X) :=
    (Subobject.lowerEquivalence (MonoOver.congr X e)).toOrderIso
  simp only [IsNoetherianObject, ObjectProperty.is_iff, isNoetherianObject]
  constructor
  · intro h
    exact ⟨φ.symm.toOrderEmbedding.dual.wellFounded h.wf⟩
  · intro h
    exact ⟨φ.toOrderEmbedding.dual.wellFounded h.wf⟩

end CategoryTheory

namespace ModuleCat

/-- A module is a Noetherian object exactly when all its submodules are
finitely generated. -/
theorem isNoetherianObject_iff {R : Type uR} [Ring R] (X : ModuleCat.{vR} R) :
    CategoryTheory.IsNoetherianObject X ↔ IsNoetherian R X := by
  let φ : Subobject X ≃o Submodule R X := subobjectModule X
  simp only [CategoryTheory.IsNoetherianObject, ObjectProperty.is_iff,
    CategoryTheory.isNoetherianObject, _root_.isNoetherian_iff']
  constructor
  · intro h
    exact ⟨φ.symm.toOrderEmbedding.dual.wellFounded h.wf⟩
  · intro h
    exact ⟨φ.toOrderEmbedding.dual.wellFounded h.wf⟩

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

/-- An equivalence of module categories preserves and reflects Noetherian
modules, with independent scalar and carrier universes.

This is the module form of Morita invariance of the Noetherian property; see
C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*. -/
theorem isNoetherian_iff_of_equivalence
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S) (X : ModuleCat.{vR} R) :
    IsNoetherian R X ↔ IsNoetherian S (e.functor.obj X) := by
  rw [← isNoetherianObject_iff X, ← isNoetherianObject_iff (e.functor.obj X)]
  exact CategoryTheory.isNoetherianObject_iff_of_equivalence e X

/-- An equivalence of module categories sends a left-Noetherian ring to a
left-Noetherian ring when the target carrier universe contains its ring.
There is no restriction on the source carrier universe.

This is the forward ring form of Morita invariance of the Noetherian property;
see C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*. -/
theorem isNoetherianRing_of_equivalence
    (e : ModuleCat.{vR} R ≌ ModuleCat.{max uS vS} S) :
    IsNoetherianRing R → IsNoetherianRing S := by
  intro hR
  haveI : IsNoetherianRing R := hR
  let Y : ModuleCat.{max uS vS} S := ModuleCat.of S (ULift.{vS} S)
  haveI : Module.Finite S Y := inferInstance
  haveI : Module.Finite R (e.inverse.obj Y) :=
    (finite_iff_of_equivalence S R e.symm Y).mpr inferInstance
  have hGY : IsNoetherian R (e.inverse.obj Y) := inferInstance
  have hFGY : IsNoetherian S (e.functor.obj (e.inverse.obj Y)) :=
    (isNoetherian_iff_of_equivalence R S e (e.inverse.obj Y)).mp hGY
  let ε : e.functor.obj (e.inverse.obj Y) ≃ₗ[S] Y :=
    (e.counitIso.app Y).toLinearEquiv
  have hY : IsNoetherian S Y := ε.isNoetherian_iff.mp hFGY
  let l : Y ≃ₗ[S] S := ULift.moduleEquiv
  exact l.isNoetherian_iff.mp hY

/-- An equivalence of module categories preserves and reflects the
left-Noetherian ring property when each carrier universe contains its ring.

This is the ring form of Morita invariance of the Noetherian property; see
C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*. -/
theorem isNoetherianRing_iff_of_equivalence
    (e : ModuleCat.{max uR vR} R ≌ ModuleCat.{max uS vS} S) :
    IsNoetherianRing R ↔ IsNoetherianRing S :=
  ⟨isNoetherianRing_of_equivalence R S e,
    isNoetherianRing_of_equivalence S R e.symm⟩

end ModuleCat
