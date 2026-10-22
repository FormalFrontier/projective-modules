/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

The free-functor construction is adapted from Mathlib's ModuleCat/Adjunctions.lean:
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Free modules on types in independent universes

`ModuleCat.freeOn R` sends a type `A` to the ordinary module `A →₀ R`.
The coefficient ring and generator type may lie in independent universes; the
carrier lies in their maximum. Morphisms are the coefficient-summing maps
`Finsupp.lmapDomain`, including for noninjective functions.

This generalizes Mathlib's `ModuleCat.free`. In equal universes,
`ModuleCat.freeOnIsoFree` identifies the two functors by identity maps on Finsupp.
The comparison lemmas recover its generators, extension maps, Hom equivalence,
and the Hom equivalence of the free-forgetful adjunction.

`ModuleCat.freeOnLinearEquiv` expresses the universal property for a target
module in a third, independent universe. It is an ordinary equivalence of types,
not an equivalence of `R`-modules of linear maps. For a noncommutative ring such
an `R`-module structure on Hom is not available in general. No adjunction with
forget landing in the generator universe is asserted in unequal universes.

## References

* Mathlib's `ModuleCat.free` and its adjunction API, by Kim Morrison and Johan
  Commelin. This is a universe generalization of that construction.
* Mathlib's Finsupp linear maps and `Finsupp.lift`, by Johannes Hölzl.
-/

@[expose] public section

universe r s t u

open CategoryTheory

namespace ModuleCat

variable (R : Type r) [Ring R]

/-- The free `R`-module functor on types in an independent universe, with
ordinary Finsupp carriers and coefficient-summing maps. -/
noncomputable def freeOn : Type s ⥤ ModuleCat.{max r s} R where
  obj A := of R (A →₀ R)
  map f := ofHom (Finsupp.lmapDomain R R (f : _ → _))
  map_id A := by
    apply ModuleCat.hom_ext
    exact Finsupp.lmapDomain_id R R
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact Finsupp.lmapDomain_comp R R (f : _ → _) (g : _ → _)

/-- The object of `freeOn` is the ordinary Finsupp module. -/
theorem freeOn_obj (A : Type s) :
    (freeOn R).obj A = of R (A →₀ R) := by
  rfl

/-- The distinguished unit generator indexed by `a`. -/
noncomputable def freeOnMk {A : Type s} (a : A) : (freeOn R).obj A :=
  Finsupp.single a 1

/-- The unit generator is the single finitely supported function with value one. -/
@[simp]
theorem freeOnMk_apply {A : Type s} (a : A) :
    freeOnMk R a = Finsupp.single a 1 := by
  rfl

/-- Mapping an arbitrary element sums its coefficients over fibers. -/
@[simp]
theorem freeOn_map_apply {A B : Type s} (f : A → B) (c : (freeOn R).obj A) :
    (freeOn R).map (↾f) c = Finsupp.mapDomain f c := by
  rfl

/-- A generator is sent to the generator indexed by its image. -/
@[simp]
theorem freeOn_map_mk {A B : Type s} (f : A → B) (a : A) :
    (freeOn R).map (↾f) (Finsupp.single a 1) = Finsupp.single (f a) 1 := by
  exact Finsupp.mapDomain_single

/-- Extend a function to a linear map into a module in any universe. -/
noncomputable def freeOnDescLinear {A : Type s} {M : Type t}
    [AddCommGroup M] [Module R M] (h : A → M) : (A →₀ R) →ₗ[R] M :=
  Finsupp.lift M R A h

/-- Extension evaluates an arbitrary finitely supported function by a finite sum. -/
theorem freeOnDescLinear_apply {A : Type s} {M : Type t}
    [AddCommGroup M] [Module R M] (h : A → M) (c : A →₀ R) :
    freeOnDescLinear R h c = c.sum (fun a x => x • h a) := by
  exact Finsupp.lift_apply M R A h c

/-- Extension takes each unit generator to its prescribed value. -/
@[simp]
theorem freeOnDescLinear_mk {A : Type s} {M : Type t}
    [AddCommGroup M] [Module R M] (h : A → M) (a : A) :
    freeOnDescLinear R h (Finsupp.single a 1) = h a := by
  simp [freeOnDescLinear]

/-- Linear maps from the ordinary free module are determined by unit generators,
including when the target lies in a different universe. -/
@[ext]
theorem freeOn_linearMap_ext {A : Type s} {M : Type t}
    [AddCommGroup M] [Module R M] {k l : (A →₀ R) →ₗ[R] M}
    (h : ∀ a, k (freeOnMk R a) = l (freeOnMk R a)) : k = l := by
  exact Finsupp.lhom_ext' (fun a => LinearMap.ext_ring (h a))

/-- The ordinary free-module universal property with an independent target
universe, obtained from `Finsupp.lift` without a module structure on Hom. -/
noncomputable def freeOnLinearEquiv (A : Type s) (M : Type t)
    [AddCommGroup M] [Module R M] : ((A →₀ R) →ₗ[R] M) ≃ (A → M) :=
  (Finsupp.lift M R A).toEquiv.symm

/-- The universal-property equivalence evaluates a linear map on generators. -/
@[simp]
theorem freeOnLinearEquiv_apply {A : Type s} {M : Type t}
    [AddCommGroup M] [Module R M] (k : (A →₀ R) →ₗ[R] M) (a : A) :
    freeOnLinearEquiv R A M k a = k (freeOnMk R a) := by
  rfl

/-- The inverse universal-property equivalence is extension by a finite sum. -/
@[simp]
theorem freeOnLinearEquiv_symm_apply {A : Type s} {M : Type t}
    [AddCommGroup M] [Module R M] (h : A → M) :
    (freeOnLinearEquiv R A M).symm h = freeOnDescLinear R h := by
  rfl

/-- The universal property is natural under functions on generators. -/
theorem freeOnLinearEquiv_precomp {A B : Type s} {M : Type t}
    [AddCommGroup M] [Module R M] (f : A → B) (k : (B →₀ R) →ₗ[R] M) :
    freeOnLinearEquiv R A M (k.comp (Finsupp.lmapDomain R R f)) =
      (freeOnLinearEquiv R B M k) ∘ f := by
  funext a
  simp only [freeOnLinearEquiv_apply, LinearMap.comp_apply, Function.comp_apply,
    freeOnMk_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The universal property is natural under linear maps of target modules. -/
theorem freeOnLinearEquiv_postcomp {A : Type s} {M : Type t} {N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (k : (A →₀ R) →ₗ[R] M) (g : M →ₗ[R] N) :
    freeOnLinearEquiv R A N (g.comp k) = g ∘ (freeOnLinearEquiv R A M k) := by
  funext a
  rfl

/-- A linear extension is the unique map with the given values on generators. -/
theorem freeOnDescLinear_unique {A : Type s} {M : Type t}
    [AddCommGroup M] [Module R M] (h : A → M) (k : (A →₀ R) →ₗ[R] M)
    (hk : ∀ a, k (freeOnMk R a) = h a) : k = freeOnDescLinear R h := by
  apply freeOn_linearMap_ext R
  intro a
  exact (hk a).trans (freeOnDescLinear_mk R h a).symm

/-- Extension bundled as a morphism in the functor's module category. -/
noncomputable def freeOnDesc {A : Type s} {M : ModuleCat.{max r s} R}
    (h : A → M) : (freeOn R).obj A ⟶ M :=
  ofHom (freeOnDescLinear R h)

/-- Bundled extension evaluates an arbitrary element by a finite sum. -/
theorem freeOnDesc_apply {A : Type s} {M : ModuleCat.{max r s} R}
    (h : A → M) (c : (freeOn R).obj A) :
    freeOnDesc R h c = c.sum (fun a x => x • h a) := by
  exact freeOnDescLinear_apply R h c

/-- Bundled extension takes each generator to its prescribed value. -/
@[simp]
theorem freeOnDesc_mk {A : Type s} {M : ModuleCat.{max r s} R}
    (h : A → M) (a : A) : freeOnDesc R h (Finsupp.single a 1) = h a := by
  exact freeOnDescLinear_mk R h a

/-- Morphisms from the free module are determined by unit generators. -/
@[ext]
theorem freeOn_hom_ext {A : Type s} {M : ModuleCat.{max r s} R}
    {k l : (freeOn R).obj A ⟶ M}
    (h : ∀ a, k (freeOnMk R a) = l (freeOnMk R a)) : k = l := by
  exact ModuleCat.hom_ext (freeOn_linearMap_ext R h)

/-- The categorical Hom universal property, retaining ordinary functions on
its right side rather than asserting an unequal-universe adjunction. -/
noncomputable def freeOnHomEquiv {A : Type s} {M : ModuleCat.{max r s} R} :
    ((freeOn R).obj A ⟶ M) ≃ (A → M) :=
  ModuleCat.homEquiv.trans (freeOnLinearEquiv R A M)

/-- The Hom equivalence evaluates a morphism on generators. -/
@[simp]
theorem freeOnHomEquiv_apply {A : Type s} {M : ModuleCat.{max r s} R}
    (k : (freeOn R).obj A ⟶ M) (a : A) :
    freeOnHomEquiv R k a = k (freeOnMk R a) := by
  rfl

/-- The inverse Hom equivalence is bundled extension. -/
@[simp]
theorem freeOnHomEquiv_symm_apply {A : Type s} {M : ModuleCat.{max r s} R}
    (h : A → M) : (freeOnHomEquiv R).symm h = freeOnDesc R h := by
  rfl

/-- The free module on an empty type has only its zero element. -/
theorem freeOn_eq_zero_of_isEmpty {A : Type s} [IsEmpty A]
    (c : (freeOn R).obj A) : c = 0 := by
  apply Finsupp.ext
  intro a
  exact isEmptyElim a

/-- In matching universes the generalized functor is naturally isomorphic to
Mathlib's original free functor, by identity maps on ordinary Finsupp. -/
noncomputable def freeOnIsoFree :
    (freeOn R : Type r ⥤ ModuleCat.{r} R) ≅ ModuleCat.free R :=
  NatIso.ofComponents (fun A => Iso.refl (of R (A →₀ R))) (by
    intro A B f
    change (freeOn R).map f ≫ 𝟙 _ = 𝟙 _ ≫ (ModuleCat.free R).map f
    simp only [Category.comp_id, Category.id_comp]
    rfl)

/-- The forward equal-universe comparison is the identity on every element. -/
@[simp]
theorem freeOnIsoFree_hom_apply (A : Type r) (c : A →₀ R) :
    (freeOnIsoFree R).hom.app A c = c := by
  rfl

/-- The inverse equal-universe comparison is the identity on every element. -/
@[simp]
theorem freeOnIsoFree_inv_apply (A : Type r) (c : A →₀ R) :
    (freeOnIsoFree R).inv.app A c = c := by
  rfl

/-- The comparison commutes with the free-module maps. -/
theorem freeOnIsoFree_naturality {A B : Type r} (f : A ⟶ B) :
    (freeOn R).map f ≫ (freeOnIsoFree R).hom.app B =
      (freeOnIsoFree R).hom.app A ≫ (ModuleCat.free R).map f := by
  exact (freeOnIsoFree R).hom.naturality f

/-- The comparison identifies the generalized generators with `freeMk`. -/
theorem freeOnIsoFree_mk {A : Type r} (a : A) :
    (freeOnIsoFree R).hom.app A (freeOnMk R a) = ModuleCat.freeMk a := by
  exact freeOnIsoFree_hom_apply R A (freeOnMk R a)

/-- The comparison identifies extension with the original `freeDesc`. -/
theorem freeOnIsoFree_desc {A : Type r} {M : ModuleCat.{r} R} (h : A → M) :
    (freeOnIsoFree R).hom.app A ≫ ModuleCat.freeDesc (↾h) = freeOnDesc R h := by
  apply freeOn_hom_ext R
  intro a
  exact Eq.trans
    (congrArg (fun x => ModuleCat.freeDesc (↾h) x) (freeOnIsoFree_mk R a))
    (Eq.trans
      (congrArg
        (fun f : A ⟶ (forget (ModuleCat R)).obj M => f a)
        ((show ((ModuleCat.free R).obj A ⟶ M) ≃
            (A ⟶ (forget (ModuleCat R)).obj M) from
          ModuleCat.freeHomEquiv).apply_symm_apply (↾h)))
      (freeOnDesc_mk R h a).symm)

/-- Transport through the comparison recovers the original `freeHomEquiv`. -/
theorem freeOnIsoFree_homEquiv {A : Type r} {M : ModuleCat.{r} R}
    (k : (freeOn R).obj A ⟶ M) :
    ModuleCat.freeHomEquiv ((freeOnIsoFree R).inv.app A ≫ k) =
      ↾(freeOnHomEquiv R k) := by
  ext a
  rfl

/-- In matching universes, the universal property is the Hom equivalence of
Mathlib's original free-forgetful adjunction after the identity comparison. -/
theorem freeOnIsoFree_adj_homEquiv (A : Type r) (M : ModuleCat.{r} R)
    (k : (freeOn R).obj A ⟶ M) :
    (ModuleCat.adj R).homEquiv A M ((freeOnIsoFree R).inv.app A ≫ k) =
      ↾(freeOnHomEquiv R k) := by
  simpa only [ModuleCat.adj_homEquiv] using (freeOnIsoFree_homEquiv R k)

end ModuleCat
