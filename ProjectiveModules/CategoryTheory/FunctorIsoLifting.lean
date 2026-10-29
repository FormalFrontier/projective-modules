/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Lifting isomorphisms

Full functors that reflect isomorphisms lift image isomorphisms.

## References

The proofs use the Mathlib contributors' fullness, isomorphism-reflection and
isomorphism APIs from `Mathlib.CategoryTheory.Functor.ReflectsIso.Basic`,
`Mathlib.CategoryTheory.Functor.FullyFaithful` and `Mathlib.CategoryTheory.Iso`.
-/

@[expose] public section

open CategoryTheory

universe uC vC uD vD

/-- Every isomorphism between two image objects lifts to the source. -/
theorem CategoryTheory.Functor.mapIso_surjective
    {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) [F.Full] [F.ReflectsIsomorphisms]
    {X Y : C} :
    Function.Surjective
      (F.mapIso : (X ≅ Y) → (F.obj X ≅ F.obj Y)) := by
  intro e
  obtain ⟨f, hf⟩ := F.map_surjective e.hom
  have : IsIso (F.map f) := by
    rw [hf]
    infer_instance
  have : IsIso f := isIso_of_reflects_iso f F
  refine ⟨asIso f, ?_⟩
  apply Iso.ext
  change F.map f = e.hom
  exact hf

/-- The image objects are isomorphic exactly when their sources are. -/
theorem CategoryTheory.Functor.nonempty_iso_map_iff
    {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) [F.Full] [F.ReflectsIsomorphisms] (X Y : C) :
    Nonempty (F.obj X ≅ F.obj Y) ↔ Nonempty (X ≅ Y) := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨i, _⟩ := F.mapIso_surjective e
    exact ⟨i⟩
  · rintro ⟨i⟩
    exact ⟨F.mapIso i⟩
