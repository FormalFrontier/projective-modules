/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Complements of projective modules

This file packages the splitting of a surjection onto a projective module as
an explicit product equivalence.  As a finite-coordinate consequence, a
projective module has an `n`-element spanning family exactly when it has a
complement in the free module of rank `n`.  In particular, every finite
projective module over an arbitrary ring has a finite complement and an
explicit finite-standard-free product equivalence.
-/

@[expose] public section

universe uR uF uP uA uM uB

open Function Set CategoryTheory CategoryTheory.Limits

private theorem rightSplitExact_characteristic
    {R : Type uR} [Ring R]
    {A : Type uA} [AddCommGroup A] [Module R A]
    {M : Type uM} [AddCommGroup M] [Module R M]
    {B : Type uB} [AddCommGroup B] [Module R B]
    {j : A →ₗ[R] M} {g : M →ₗ[R] B} {s : B →ₗ[R] M}
    (hj : Injective j) (hexac : LinearMap.range j = LinearMap.ker g)
    (hs : g.comp s = LinearMap.id) :
    (∀ x : M, ((lequivProdOfRightSplitExact hj hexac hs).symm x).2 = g x) ∧
      (∀ a : A, lequivProdOfRightSplitExact hj hexac hs (a, 0) = j a) := by
  let liftedJ : ULift.{max uA uM uB} A →ₗ[R] ULift.{max uA uM uB} M :=
    ULift.moduleEquiv.symm.toLinearMap ∘ₗ j ∘ₗ ULift.moduleEquiv.toLinearMap
  let liftedG : ULift.{max uA uM uB} M →ₗ[R] ULift.{max uA uM uB} B :=
    ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ ULift.moduleEquiv.toLinearMap
  let liftedS : ULift.{max uA uM uB} B →ₗ[R] ULift.{max uA uM uB} M :=
    ULift.moduleEquiv.symm.toLinearMap ∘ₗ s ∘ₗ ULift.moduleEquiv.toLinearMap
  have hj' : Injective liftedJ := by simpa [liftedJ] using hj
  have hexac' : LinearMap.range liftedJ = LinearMap.ker liftedG := by
    simp [liftedJ, liftedG, LinearMap.range_comp, LinearMap.ker_comp, hexac,
      Submodule.comap_equiv_eq_map_symm]
  have hs' : liftedG.comp liftedS = LinearMap.id := by
    ext y
    simpa [liftedG, liftedS] using congr($hs y.down)
  let S := CategoryTheory.ShortComplex.moduleCatMkOfKerLERange
    (ModuleCat.ofHom liftedJ) (ModuleCat.ofHom liftedG) (by
      change LinearMap.range liftedJ ≤ LinearMap.ker liftedG
      rw [hexac'])
  let spl : S.Splitting := CategoryTheory.ShortComplex.Splitting.ofExactOfSection S
    (CategoryTheory.ShortComplex.Exact.moduleCat_of_range_eq_ker _ _ hexac')
    (ModuleCat.ofHom liftedS) (ModuleCat.hom_ext hs')
    (by
      change Mono (ModuleCat.ofHom liftedJ)
      exact (ModuleCat.mono_iff_injective _).2 hj')
  have hproj (X Y : ModuleCat.{max uA uM uB} R) :
      (ModuleCat.biprodIsoProd X Y).hom ≫
        ModuleCat.ofHom (LinearMap.snd R X Y) = CategoryTheory.Limits.biprod.snd := by
    calc
      _ = (ModuleCat.biprodIsoProd X Y).hom ≫
            ((ModuleCat.biprodIsoProd X Y).inv ≫ CategoryTheory.Limits.biprod.snd) := by
              rw [ModuleCat.biprodIsoProd_inv_comp_snd]
      _ = CategoryTheory.Limits.biprod.snd := by
        rw [← CategoryTheory.Category.assoc, CategoryTheory.Iso.hom_inv_id,
          CategoryTheory.Category.id_comp]
  have hproj_apply (X Y : ModuleCat.{max uA uM uB} R)
      (z : ↑(X ⊞ Y : ModuleCat.{max uA uM uB} R)) :
      ((ModuleCat.biprodIsoProd X Y).hom z).2 =
        (CategoryTheory.Limits.biprod.snd : X ⊞ Y ⟶ Y) z := by
    exact congrArg (fun arrow : X ⊞ Y ⟶ Y ↦ arrow z) (hproj X Y)
  constructor
  · intro x
    change (((ModuleCat.biprodIsoProd S.X₁ S.X₃).hom
      (spl.isoBinaryBiproduct.hom (ULift.up x))).2).down = g x
    rw [hproj_apply]
    have hcat : spl.isoBinaryBiproduct.hom ≫
        (CategoryTheory.Limits.biprod.snd : S.X₁ ⊞ S.X₃ ⟶ S.X₃) = S.g := by
      change CategoryTheory.Limits.biprod.lift spl.r S.g ≫
        CategoryTheory.Limits.biprod.snd = S.g
      exact CategoryTheory.Limits.biprod.lift_snd _ _
    change ((spl.isoBinaryBiproduct.hom ≫
      (CategoryTheory.Limits.biprod.snd : S.X₁ ⊞ S.X₃ ⟶ S.X₃))
      (ULift.up x : ↑S.X₂)).down = g x
    rw [hcat]
    rfl
  · intro a
    have hcat : ModuleCat.ofHom (LinearMap.inl R S.X₁ S.X₃) ≫
        (ModuleCat.biprodIsoProd S.X₁ S.X₃).inv =
          (CategoryTheory.Limits.biprod.inl : S.X₁ ⟶ S.X₁ ⊞ S.X₃) := by
      apply CategoryTheory.Limits.biprod.hom_ext
      · rw [CategoryTheory.Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst,
          CategoryTheory.Limits.biprod.inl_fst]
        apply ModuleCat.hom_ext
        ext y
        rfl
      · rw [CategoryTheory.Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd,
          CategoryTheory.Limits.biprod.inl_snd]
        apply ModuleCat.hom_ext
        ext y
        rfl
    have hcat_apply (y : ↑S.X₁) :
        (ModuleCat.biprodIsoProd S.X₁ S.X₃).inv (y, 0) =
          (CategoryTheory.Limits.biprod.inl : S.X₁ ⟶ S.X₁ ⊞ S.X₃) y := by
      exact congrArg (fun arrow : S.X₁ ⟶ S.X₁ ⊞ S.X₃ ↦ arrow y) hcat
    change ((spl.isoBinaryBiproduct.inv
      ((ModuleCat.biprodIsoProd S.X₁ S.X₃).inv
        ((ULift.up a : ↑S.X₁), (0 : ↑S.X₃)))).down) = j a
    calc
      _ = ((spl.isoBinaryBiproduct.inv
          ((CategoryTheory.Limits.biprod.inl : S.X₁ ⟶ S.X₁ ⊞ S.X₃)
            (ULift.up a : ↑S.X₁))).down) := by
          exact congrArg (fun z : ↑(S.X₁ ⊞ S.X₃) ↦
            (spl.isoBinaryBiproduct.inv z).down) (hcat_apply (ULift.up a : ↑S.X₁))
      _ = j a := by
          change ((CategoryTheory.Limits.biprod.desc S.f spl.s)
            ((CategoryTheory.Limits.biprod.inl : S.X₁ ⟶ S.X₁ ⊞ S.X₃)
              (ULift.up a : ↑S.X₁))).down = j a
          change ((CategoryTheory.Limits.biprod.inl ≫
            CategoryTheory.Limits.biprod.desc S.f spl.s)
            (ULift.up a : ↑S.X₁)).down = j a
          rw [CategoryTheory.Limits.biprod.inl_desc]
          rfl

namespace Module.Projective

variable {R : Type uR} [Ring R]
variable {F : Type uF} [AddCommGroup F] [Module R F]
variable {P : Type uP} [AddCommGroup P] [Module R P]

/-- A surjection onto a projective module identifies its domain with the
product of the target and its kernel. -/
noncomputable def prodKerEquivOfSurjective [Module.Projective R P]
    (f : F →ₗ[R] P) (hf : Surjective f) :
    (P × LinearMap.ker f) ≃ₗ[R] F := by
  let h := Module.projective_lifting_property
    f (LinearMap.id (R := R) (M := P)) hf
  let s := Classical.choose h
  have hs := Classical.choose_spec h
  exact (LinearEquiv.prodComm R P (LinearMap.ker f)).trans <|
    lequivProdOfRightSplitExact
      (j := (LinearMap.ker f).subtype) (g := f) (f := s)
      Subtype.val_injective (Submodule.range_subtype _) hs

/-- The target coordinate of the inverse splitting is the original surjection. -/
@[simp] theorem prodKerEquivOfSurjective_symm_fst [Module.Projective R P]
    (f : F →ₗ[R] P) (hf : Surjective f) (x : F) :
    ((prodKerEquivOfSurjective f hf).symm x).1 = f x := by
  unfold prodKerEquivOfSurjective
  simp only [LinearEquiv.symm_trans_apply, LinearEquiv.symm_prodComm,
    LinearEquiv.prodComm_apply]
  exact (rightSplitExact_characteristic Subtype.val_injective (Submodule.range_subtype _)
    (Classical.choose_spec (Module.projective_lifting_property
      f (LinearMap.id (R := R) (M := P)) hf))).1 x

/-- Projecting a split element to the target recovers its target coordinate. -/
@[simp] theorem prodKerEquivOfSurjective_apply_fst [Module.Projective R P]
    (f : F →ₗ[R] P) (hf : Surjective f) (p : P) (k : LinearMap.ker f) :
    f ((prodKerEquivOfSurjective f hf) (p, k)) = p := by
  have h := prodKerEquivOfSurjective_symm_fst f hf
    ((prodKerEquivOfSurjective f hf) (p, k))
  simpa only [LinearEquiv.symm_apply_apply] using h.symm

/-- The kernel factor embeds in the domain by its original subtype map. -/
@[simp] theorem prodKerEquivOfSurjective_apply_zero_snd [Module.Projective R P]
    (f : F →ₗ[R] P) (hf : Surjective f) (k : LinearMap.ker f) :
    prodKerEquivOfSurjective f hf (0, k) = (k : F) := by
  unfold prodKerEquivOfSurjective
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodComm_apply]
  exact (rightSplitExact_characteristic Subtype.val_injective (Submodule.range_subtype _)
    (Classical.choose_spec (Module.projective_lifting_property
      f (LinearMap.id (R := R) (M := P)) hf))).2 k

/-- A projective module is a quotient of `F` exactly when it is a direct
summand of `F`. -/
theorem exists_surjective_iff_exists_prod_equiv [Module.Projective R P] :
    (∃ f : F →ₗ[R] P, Surjective f) ↔
      ∃ (Q : Type uF) (_ : AddCommGroup Q) (_ : Module R Q),
        Nonempty ((P × Q) ≃ₗ[R] F) := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨LinearMap.ker f, inferInstance, inferInstance,
      ⟨prodKerEquivOfSurjective f hf⟩⟩
  · rintro ⟨Q, _, _, ⟨e⟩⟩
    let f : F →ₗ[R] P := (LinearMap.fst R P Q).comp e.symm.toLinearMap
    refine ⟨f, ?_⟩
    intro p
    exact ⟨e (p, 0), by simp [f]⟩

/-- A projective module has an `n`-element spanning family exactly when it is
a direct summand of the standard free module of rank `n`. -/
theorem exists_fin_generating_family_iff_exists_prod_equiv
    [Module.Projective R P] (n : ℕ) :
    (∃ v : Fin n → P, Submodule.span R (range v) = ⊤) ↔
      ∃ (Q : Type uR) (_ : AddCommGroup Q) (_ : Module R Q),
        Nonempty ((P × Q) ≃ₗ[R] (Fin n → R)) := by
  constructor
  · rintro ⟨v, hv⟩
    apply (exists_surjective_iff_exists_prod_equiv
      (R := R) (F := Fin n → R) (P := P)).mp
    exact ⟨Fintype.linearCombination R v,
      (span_range_eq_top_iff_surjective_fintypeLinearCombination R v).mp hv⟩
  · intro h
    obtain ⟨f, hf⟩ := (exists_surjective_iff_exists_prod_equiv
      (R := R) (F := Fin n → R) (P := P)).mpr h
    let v : Fin n → P := fun i ↦ f (Pi.single i 1)
    have hcomb : Fintype.linearCombination R v = f := by
      apply LinearMap.pi_ext
      intro i r
      rw [Fintype.linearCombination_apply_single]
      change r • f (Pi.single i 1) = f (Pi.single i r)
      rw [← f.map_smul, ← Pi.single_smul']
      simp
    refine ⟨v, (span_range_eq_top_iff_surjective_fintypeLinearCombination R v).mpr ?_⟩
    simpa only [hcomb] using hf

/-- A finite projective module has a finite complement whose product with it
is explicitly equivalent to a finite standard free module. -/
theorem exists_finite_complement_linearEquiv
    [Module.Finite R P] [Module.Projective R P] :
    ∃ (n : ℕ) (Q : Type uR) (_ : AddCommGroup Q) (_ : Module R Q),
      Module.Finite R Q ∧ Nonempty ((P × Q) ≃ₗ[R] (Fin n → R)) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  let Q := LinearMap.ker f
  let e : (P × Q) ≃ₗ[R] (Fin n → R) :=
    prodKerEquivOfSurjective f hf
  have hprodFinite : Module.Finite R (P × Q) := Module.Finite.equiv e.symm
  let _ : Module.Finite R (P × Q) := hprodFinite
  have hQ : Module.Finite R Q :=
    Module.Finite.of_surjective (LinearMap.snd R P Q) LinearMap.snd_surjective
  exact ⟨n, Q, inferInstance, inferInstance, hQ, ⟨e⟩⟩

end Module.Projective

namespace Module

variable {R : Type uR} [Ring R]

/-- A finite projective module has a finite complement whose product with the
module is finite free. -/
theorem exists_finite_free_product_of_finite_projective
    {B : Type uP} [AddCommGroup B] [Module R B]
    [Module.Finite R B] [Module.Projective R B] :
    ∃ (Q : Type uR) (_ : AddCommGroup Q) (_ : Module R Q),
      Module.Finite R Q ∧ Module.Finite R (B × Q) ∧
        Module.Free R (B × Q) := by
  obtain ⟨n, Q, hQgroup, hQmodule, hQfinite, ⟨e⟩⟩ :=
    Projective.exists_finite_complement_linearEquiv (R := R) (P := B)
  let _ : AddCommGroup Q := hQgroup
  let _ : Module R Q := hQmodule
  let _ : Module.Finite R Q := hQfinite
  have hprodFinite : Module.Finite R (B × Q) := Module.Finite.equiv e.symm
  let _ : Module.Finite R (B × Q) := hprodFinite
  have hprodFree : Module.Free R (B × Q) := Module.Free.of_equiv e.symm
  exact ⟨Q, inferInstance, inferInstance, hQfinite, hprodFinite, hprodFree⟩

end Module
