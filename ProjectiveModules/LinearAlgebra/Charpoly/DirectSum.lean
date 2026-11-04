/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly
public import ProjectiveModules.Module.DirectSum

/-!
# Characteristic polynomials of internal sums

An endomorphism preserving a finite internal family of submodules has
characteristic polynomial equal to the product of those of its restrictions.
Only the ambient module is assumed finite projective; each summand inherits
these properties from its canonical splitting.
-/

@[expose] public section

open scoped BigOperators DirectSum

universe u v w

namespace Module

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]

open Classical in
/-- The characteristic polynomial factors over a finite invariant internal sum. -/
theorem charpoly_eq_finprod_restrict_of_isInternal {I : Type w} [_root_.Finite I]
    (A : I → Submodule R M) (hA : DirectSum.IsInternal A)
    (f : Module.End R M) (hf : ∀ i, ∀ x ∈ A i, f x ∈ A i) :
    charpoly R M f =
      ∏ᶠ i, @charpoly R _ (A i) _ _
        (hA.moduleFinite i) (hA.moduleProjective i) (f.restrict (hf i)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : ∀ i, Module.Finite R (A i) := fun i => hA.moduleFinite i
  let : ∀ i, Module.Projective R (A i) := fun i => hA.moduleProjective i
  let e : (⨁ i, A i) ≃ₗ[R] M :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA
  let q : (⨁ i, A i) ≃ₗ[R] (∀ i, A i) :=
    DirectSum.linearEquivFunOnFintype R I (fun i => A i)
  let E : M ≃ₗ[R] (∀ i, A i) := e.symm.trans q
  let g : ∀ i, Module.End R (A i) := fun i => f.restrict (hf i)
  have hE (i : I) (x : A i) : E (x : M) = Pi.single i x := by
    have hs : e.symm (x : M) = DirectSum.lof R I (fun i => A i) i x := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      exact (DirectSum.coeLinearMap_lof A i x).symm.trans
        (LinearEquiv.ofBijective_apply (DirectSum.coeLinearMap A)
          (hf := hA) (DirectSum.lof R I (fun i => A i) i x)).symm
    change q (e.symm (x : M)) = Pi.single i x
    rw [hs]
    simp only [q, DirectSum.linearEquivFunOnFintype_lof]
  have h : E.toLinearMap.comp f = (LinearMap.piMap g).comp E.toLinearMap := by
    have hs : (E.toLinearMap.comp f).comp (DirectSum.coeLinearMap A) =
        ((LinearMap.piMap g).comp E.toLinearMap).comp (DirectSum.coeLinearMap A) := by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      intro x
      funext j
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        DirectSum.coeLinearMap_lof]
      rw [show f (x : M) = (g i x : M) from rfl]
      rw [hE i (g i x), hE i x]
      simp only [LinearMap.coe_piMap]
      by_cases hij : i = j
      · subst j
        simp [Pi.map]
      · simp [Pi.map, Ne.symm hij]
    apply LinearMap.ext
    intro x
    obtain ⟨y, hy⟩ :=
      (show Function.Surjective (DirectSum.coeLinearMap A) from hA.2) x
    have hz := congrArg (fun k : (⨁ i, A i) →ₗ[R] (∀ i, A i) => k y) hs
    simpa only [LinearMap.comp_apply, hy] using hz
  exact (charpoly_eq_of_intertwining R M (∀ i, A i) f (LinearMap.piMap g) E h).trans
    (charpoly_piMap R (fun i => A i) g)

end Module
