/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.FiniteProjective
public import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.CategoryTheory.Category.Preorder
import ProjectiveModules.Order.CompactlyGenerated

/-!
# Finiteness and finite projectivity under module-category equivalences

A given equivalence of module categories preserves and reflects finite generation.
The scalar and carrier universes may be independent. It also preserves finite
projectivity when the target carrier universe is `max uS vS`, and reflects finite
projectivity when both carrier universes have this form. The forward theorem
places no such restriction on the source carrier universe.

## Main results

* `ModuleCat.finite_iff_of_equivalence`
* `ModuleCat.isFiniteProjective_of_equivalence`
* `ModuleCat.isFiniteProjective_iff_of_equivalence`

The conclusions use `Module.Finite` and the existing
`ModuleCat.isFiniteProjective` property defining `ModuleCat.FiniteProjective`.
The lemmas `ModuleCat.isFG_iff` and `ModuleCat.isFiniteProjective_iff` give the
corresponding object-property and algebraic formulations. No linearity of the
functor, commutativity of the rings or freeness of the modules is assumed.

## Implementation notes

The equivalence induces an order isomorphism on submodule lattices via
`ModuleCat.subobjectModule`. Finite generation is compactness of the greatest
submodule. Projectivity passes through categorical projectivity; the local
`small_max` instance is used only to return to algebraic projectivity. All
statements assume a given equivalence; they do not assert its existence.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, for Morita
  invariance of finite projective modules.
* Mathlib's module-category and subobject formalizations by Markus Himmel,
  Bhavik Mehta and Kim Morrison, and its categorical projectivity formalization
  by Markus Himmel and Kim Morrison.
* Mathlib's finiteness formalization by Johan Commelin, for the
  compact-submodule characterization. The order-theoretic transport uses
  `ProjectiveModules.Order.CompactlyGenerated` and the Mathlib APIs credited there.
* The finite-projective object property and category by Formal Frontier Agents.
-/

@[expose] public section

universe uR uS vR vS

open CategoryTheory

section Finiteness

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

namespace ModuleCat

/-- An equivalence of module categories preserves and reflects finite generation,
with independent scalar and carrier universes.

This is the finite-generation component of Morita invariance; see C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*. -/
theorem finite_iff_of_equivalence
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S) (X : ModuleCat.{vR} R) :
    Module.Finite S (e.functor.obj X) ↔ Module.Finite R X := by
  -- Every subobject is represented by a submodule, with no smallness of the ring.
  let φ : Submodule R X ≃o Submodule S (e.functor.obj X) :=
    (subobjectModule X).symm.trans
      ((Subobject.lowerEquivalence (MonoOver.congr X e)).toOrderIso.trans
        (subobjectModule (e.functor.obj X)))
  -- Finite generation means compactness of the greatest submodule.
  simp only [Module.finite_def, Submodule.fg_iff_compact]
  simpa only [φ.map_top] using φ.isCompactElement_iff (⊤ : Submodule R X)

end ModuleCat

end Finiteness

section FiniteProjectivity

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

namespace ModuleCat

/-- An equivalence of module categories sends finite projective modules to finite
projective modules when the target carrier universe contains the target ring.

This is the forward finite-projective part of Morita invariance; see C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*. -/
theorem isFiniteProjective_of_equivalence
    (e : ModuleCat.{vR} R ≌ ModuleCat.{max uS vS} S) (X : ModuleCat.{vR} R) :
    ModuleCat.isFiniteProjective R X →
      ModuleCat.isFiniteProjective S (e.functor.obj X) := by
  intro hX
  obtain ⟨hfin, hproj⟩ := (isFiniteProjective_iff X).mp hX
  let : Module.Finite R X := hfin
  let : Module.Projective R X := hproj
  -- Algebraic projectivity gives categorical projectivity at any source height.
  let : CategoryTheory.Projective X :=
    projective_of_categoryTheory_projective X
  let : CategoryTheory.Projective (e.functor.obj X) :=
    (e.map_projective_iff X).mpr inferInstance
  -- Only the return to algebraic projectivity needs the supported target height.
  let : Small.{max uS vS} S := small_max S
  exact (isFiniteProjective_iff (e.functor.obj X)).mpr
    ⟨(finite_iff_of_equivalence R S e X).mpr inferInstance,
      projective_of_module_projective (e.functor.obj X)⟩

/-- An equivalence of module categories preserves and reflects finite projectivity
when each carrier universe contains its scalar-ring universe.

This is the finite-projective part of Morita invariance; see C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*. -/
theorem isFiniteProjective_iff_of_equivalence
    (e : ModuleCat.{max uR vR} R ≌ ModuleCat.{max uS vS} S)
    (X : ModuleCat.{max uR vR} R) :
    ModuleCat.isFiniteProjective S (e.functor.obj X) ↔
      ModuleCat.isFiniteProjective R X := by
  constructor
  · intro hY
    obtain ⟨hfin, hproj⟩ := (isFiniteProjective_iff (e.functor.obj X)).mp hY
    let : Module.Finite S (e.functor.obj X) := hfin
    let : Module.Projective S (e.functor.obj X) := hproj
    let : CategoryTheory.Projective (e.functor.obj X) :=
      projective_of_categoryTheory_projective (e.functor.obj X)
    -- Reflection uses the given equivalence, not an enlarged or chosen equivalence.
    let : CategoryTheory.Projective X :=
      (e.map_projective_iff X).mp inferInstance
    let : Small.{max uR vR} R := small_max R
    exact (isFiniteProjective_iff X).mpr
      ⟨(finite_iff_of_equivalence R S e X).mp inferInstance,
        projective_of_module_projective X⟩
  · exact isFiniteProjective_of_equivalence R S e X

end ModuleCat

end FiniteProjectivity
