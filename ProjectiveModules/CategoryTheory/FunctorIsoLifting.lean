/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.Skeletal

/-!
# Isomorphisms and object-isomorphism classes

Full functors that reflect isomorphisms lift image isomorphisms and induce injective
maps on object-isomorphism classes.

## References

The proofs use the Mathlib contributors' fullness, isomorphism-reflection and
isomorphism APIs from `Mathlib.CategoryTheory.Functor.ReflectsIso.Basic`,
`Mathlib.CategoryTheory.Functor.FullyFaithful`, `Mathlib.CategoryTheory.Iso` and
`Mathlib.CategoryTheory.Skeletal`.
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

/-- Injectivity on isomorphism classes for full functors reflecting isomorphisms. -/
theorem CategoryTheory.ThinSkeleton.map_obj_injective
    {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) [F.Full] [F.ReflectsIsomorphisms] :
    Function.Injective ((ThinSkeleton.map F).obj) := by
  intro X Y
  refine Quotient.inductionOn₂ X Y ?_
  intro X Y h
  exact Quotient.sound ((F.nonempty_iso_map_iff X Y).mp (Quotient.exact h))

namespace CategoryTheory

universe u₁ v₁ u₂ v₂

/-- Every object of the thin skeleton is the image of an object of the original category. -/
theorem toThinSkeleton_obj_surjective
    {C : Type u₁} [Category.{v₁} C] :
    Function.Surjective (toThinSkeleton C).obj := by
  exact Quotient.mk_surjective

/-- Two objects have equal images in the thin skeleton exactly when they are isomorphic. -/
theorem toThinSkeleton_obj_eq_iff
    {C : Type u₁} [Category.{v₁} C] (X Y : C) :
    (toThinSkeleton C).obj X = (toThinSkeleton C).obj Y ↔ Nonempty (X ≅ Y) := by
  exact Quotient.eq

namespace ThinSkeleton

/-- An essentially surjective functor is surjective on objects of thin skeletons. -/
theorem map_obj_surjective
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) [F.EssSurj] :
    Function.Surjective ((ThinSkeleton.map F).obj) := by
  intro q
  obtain ⟨Y, rfl⟩ := toThinSkeleton_obj_surjective (C := D) q
  have hY := Functor.EssSurj.mem_essImage F Y
  rw [← Functor.isoClosure_eq_essImage (F := F),
    ObjectProperty.prop_isoClosure_iff] at hY
  obtain ⟨Z, hZ, hYZ⟩ := hY
  obtain ⟨X, rfl⟩ := hZ
  refine ⟨(toThinSkeleton C).obj X, ?_⟩
  change (toThinSkeleton C ⋙ ThinSkeleton.map F).obj X = (toThinSkeleton D).obj Y
  rw [← ThinSkeleton.comp_toThinSkeleton F]
  symm
  exact (toThinSkeleton_obj_eq_iff Y (F.obj X)).2 hYZ

/-- A full, isomorphism-reflecting, essentially surjective functor induces a bijection
on the objects of thin skeletons. -/
theorem map_obj_bijective
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) [F.Full] [F.ReflectsIsomorphisms] [F.EssSurj] :
    Function.Bijective ((ThinSkeleton.map F).obj) := by
  exact ⟨map_obj_injective F, map_obj_surjective F⟩

end ThinSkeleton

end CategoryTheory
