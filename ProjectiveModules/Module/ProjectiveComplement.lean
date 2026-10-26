/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism, Iris
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Finiteness.Projective
public import StableRange.Module.SplitSurjective

/-!
# Complements of projective modules

This file packages the splitting of a surjection onto a projective module as
an explicit product equivalence.  As a finite-coordinate consequence, a
projective module has an `n`-element spanning family exactly when it has a
complement in the free module of rank `n`.  In particular, every finite
projective module over an arbitrary ring has a finite complement and an
explicit finite-standard-free product equivalence.

## References

* Mathlib, `Algebra.Module.Projective` and `Algebra.Category.ModuleCat.Biproducts`
  (projective lifting and right split exact sequences).
* Stable Range, `StableRange.Module.SplitSurjective`
  (kernel-product equivalences with a specified section).
-/

@[expose] public section

universe uR uF uP uA uM uB

open Function Set CategoryTheory CategoryTheory.Limits

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

/-- The projective splitting is the kernel-product equivalence for the section
chosen by the projective lifting property, after exchanging the two factors. -/
theorem prodKerEquivOfSurjective_eq_prodComm_trans [Module.Projective R P]
    (f : F →ₗ[R] P) (hf : Surjective f) :
    prodKerEquivOfSurjective f hf =
      (LinearEquiv.prodComm R P (LinearMap.ker f)).trans
        (LinearMap.kerProdEquivOfRightInverse f
          (Classical.choose (Module.projective_lifting_property
            f (LinearMap.id (R := R) (M := P)) hf))
          (Classical.choose_spec (Module.projective_lifting_property
            f (LinearMap.id (R := R) (M := P)) hf))) := by
  apply LinearEquiv.ext
  rintro ⟨p, k⟩
  simp only [prodKerEquivOfSurjective, LinearEquiv.trans_apply,
    LinearEquiv.prodComm_apply, Prod.swap_prod_mk,
    LinearMap.kerProdEquivOfRightInverse_apply]
  exact _root_.lequivProdOfRightSplitExact_apply
    (j := (LinearMap.ker f).subtype) (f := f)
    (g := Classical.choose (Module.projective_lifting_property
      f (LinearMap.id (R := R) (M := P)) hf))
    Subtype.val_injective (Submodule.range_subtype _)
    (Classical.choose_spec (Module.projective_lifting_property
      f (LinearMap.id (R := R) (M := P)) hf)) k p

/-- The projective splitting adds the kernel element to the image of the
section chosen by the projective lifting property. -/
@[simp] theorem prodKerEquivOfSurjective_apply [Module.Projective R P]
    (f : F →ₗ[R] P) (hf : Surjective f) (z : P × LinearMap.ker f) :
    prodKerEquivOfSurjective f hf z = (z.2 : F) +
      (Classical.choose (Module.projective_lifting_property
        f (LinearMap.id (R := R) (M := P)) hf)) z.1 := by
  rw [prodKerEquivOfSurjective_eq_prodComm_trans]
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodComm_apply,
    LinearMap.kerProdEquivOfRightInverse_apply, Prod.fst_swap, Prod.snd_swap]

/-- The kernel coordinate of the inverse splitting has underlying value equal
to the original element minus the chosen lift of its target coordinate. -/
@[simp] theorem prodKerEquivOfSurjective_symm_snd [Module.Projective R P]
    (f : F →ₗ[R] P) (hf : Surjective f) (x : F) :
    (((prodKerEquivOfSurjective f hf).symm x).2 : F) =
      x - (Classical.choose (Module.projective_lifting_property
        f (LinearMap.id (R := R) (M := P)) hf)) (f x) := by
  rw [prodKerEquivOfSurjective_eq_prodComm_trans]
  simp only [LinearEquiv.symm_trans_apply, LinearEquiv.symm_prodComm,
    LinearEquiv.prodComm_apply, Prod.snd_swap, LinearMap.kerProdEquivOfRightInverse_symm_fst]

/-- The target coordinate of the inverse splitting is the original surjection. -/
@[simp] theorem prodKerEquivOfSurjective_symm_fst [Module.Projective R P]
    (f : F →ₗ[R] P) (hf : Surjective f) (x : F) :
    ((prodKerEquivOfSurjective f hf).symm x).1 = f x := by
  rw [prodKerEquivOfSurjective_eq_prodComm_trans]
  simp only [LinearEquiv.symm_trans_apply, LinearEquiv.symm_prodComm,
    LinearEquiv.prodComm_apply, Prod.fst_swap, LinearMap.kerProdEquivOfRightInverse_symm_snd]

/-- Projecting a split element to the target recovers its target coordinate. -/
theorem prodKerEquivOfSurjective_apply_fst [Module.Projective R P]
    (f : F →ₗ[R] P) (hf : Surjective f) (p : P) (k : LinearMap.ker f) :
    f ((prodKerEquivOfSurjective f hf) (p, k)) = p := by
  have h := prodKerEquivOfSurjective_symm_fst f hf
    ((prodKerEquivOfSurjective f hf) (p, k))
  simpa only [LinearEquiv.symm_apply_apply] using h.symm

/-- The kernel factor embeds in the domain by its original subtype map. -/
theorem prodKerEquivOfSurjective_apply_zero_snd [Module.Projective R P]
    (f : F →ₗ[R] P) (hf : Surjective f) (k : LinearMap.ker f) :
    prodKerEquivOfSurjective f hf (0, k) = (k : F) := by
  rw [prodKerEquivOfSurjective_eq_prodComm_trans]
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodComm_apply, Prod.swap_prod_mk,
    LinearMap.kerProdEquivOfRightInverse_apply, map_zero, add_zero]

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
