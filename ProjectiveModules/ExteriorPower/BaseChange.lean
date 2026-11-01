/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Iris
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import ProjectiveModules.ExteriorAlgebra.BaseChange

/-!
# Homogeneous exterior powers under scalar extension

The compatibility statement in this file identifies the image of each homogeneous
exterior-power submodule under `ExteriorAlgebra.equivBaseChange` with the scalar extension
of the original submodule. The underlying exterior-algebra equivalence is due to Prism.

The rings and module have independent universes, and the degree can be zero. No finiteness,
projectivity, flatness, or nontriviality assumption is imposed. Scalar-action equations for
exterior-power maps are preserved by scalar extension. No equivalence between the
fixed-degree carriers is constructed in this file.
-/

@[expose] public section

open scoped TensorProduct

universe uR uS uM

variable {R : Type uR} {S : Type uS} {M : Type uM}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

private theorem span_range_one_tmul :
    Submodule.span S (Set.range (fun m : M ↦ (1 : S) ⊗ₜ[R] m)) = ⊤ := by
  suffices hspan : ∀ x : S ⊗[R] M,
      x ∈ Submodule.span S (Set.range (fun m : M ↦ (1 : S) ⊗ₜ[R] m)) by
    apply top_unique
    intro x _
    exact hspan x
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
      have hm : (1 : S) ⊗ₜ[R] m ∈
          Submodule.span S (Set.range (fun m : M ↦ (1 : S) ⊗ₜ[R] m)) :=
        Submodule.subset_span (Set.mem_range_self m)
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
        (Submodule.span S (Set.range (fun m : M ↦ (1 : S) ⊗ₜ[R] m))).smul_mem s hm
  | add x y hx hy => exact Submodule.add_mem _ hx hy

namespace ExteriorAlgebra

/-- On exterior products of pure tensors with coefficient one, the exterior-algebra
base-change equivalence tensors the original exterior product with one. -/
theorem equivBaseChange_ιMulti_one_tmul (n : ℕ) :
    ∀ v : Fin n → M,
      equivBaseChange (R := R) (S := S) (M := M)
          (ιMulti S n (fun i => (1 : S) ⊗ₜ[R] v i)) =
        (1 : S) ⊗ₜ[R] ιMulti R n v := by
  induction n with
  | zero =>
      intro v
      simp only [ιMulti_zero_apply, map_one, Algebra.TensorProduct.one_def]
  | succ n ih =>
      intro v
      rw [ιMulti_succ_apply, map_mul, equivBaseChange_apply_ι_tmul]
      change ((1 : S) ⊗ₜ[R] ι R (v 0)) *
          equivBaseChange (R := R) (S := S) (M := M)
            (ιMulti S n (fun i => (1 : S) ⊗ₜ[R] Matrix.vecTail v i)) =
        (1 : S) ⊗ₜ[R] ιMulti R (n + 1) v
      rw [ih, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ιMulti_succ_apply]

/-- The exterior-algebra scalar-extension equivalence carries the degree-`n` submodule
onto the scalar extension of the degree-`n` submodule. -/
theorem equivBaseChange_map_exteriorPower (n : ℕ) :
    (⋀[S]^n (S ⊗[R] M)).map
        (equivBaseChange (R := R) (S := S) (M := M)).toLinearEquiv.toLinearMap =
      (⋀[R]^n M).baseChange S := by
  classical
  let t : M → S ⊗[R] M := fun m => (1 : S) ⊗ₜ[R] m
  have ht : Submodule.span S (Set.range t) = ⊤ := span_range_one_tmul
  rw [← _root_.exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top
      S n (S ⊗[R] M) ht,
    ← ιMulti_span_fixedDegree R n, Submodule.baseChange_span, Submodule.map_span]
  apply congrArg (Submodule.span S)
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have hv' (i : Fin n) : ∃ m : M, t m = v i := hv (Set.mem_range_self i)
    choose w hw using hv'
    have hvec : v = fun i => (1 : S) ⊗ₜ[R] w i := funext fun i => (hw i).symm
    refine ⟨ιMulti R n w, ⟨w, rfl⟩, ?_⟩
    rw [hvec]
    exact (equivBaseChange_ιMulti_one_tmul n w).symm
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨ιMulti S n (fun i => (1 : S) ⊗ₜ[R] v i), ?_, ?_⟩
    · refine ⟨(fun i => (1 : S) ⊗ₜ[R] v i), ?_, rfl⟩
      rintro _ ⟨i, rfl⟩
      exact ⟨v i, rfl⟩
    · exact equivBaseChange_ιMulti_one_tmul n v

end ExteriorAlgebra

namespace exteriorPower

/-- A scalar-action equation for an exterior-power endomorphism remains valid after
arbitrary scalar extension. This includes degree zero and does not require flatness. -/
theorem map_baseChange_eq_smul (n : ℕ) (f : Module.End R M) (r : R)
    (h : ∀ x : ⋀[R]^n M, map n f x = r • x)
    (x : ⋀[S]^n (S ⊗[R] M)) :
    map n (f.baseChange S) x = algebraMap R S r • x := by
  classical
  have hmap : map n (f.baseChange S) =
      LinearMap.lsmul S (⋀[S]^n (S ⊗[R] M)) (algebraMap R S r) := by
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _
      (ιMulti_span_of_span S n (S ⊗[R] M)
        (span_range_one_tmul (R := R) (S := S) (M := M)))]
    rintro ⟨_, ⟨v, hv, rfl⟩⟩
    have hv' (i : Fin n) : ∃ m : M, (1 : S) ⊗ₜ[R] m = v i :=
      hv (Set.mem_range_self i)
    choose w hw using hv'
    have hvec : v = fun i ↦ (1 : S) ⊗ₜ[R] w i := funext fun i ↦ (hw i).symm
    simp only [hvec, map_apply_ιMulti, LinearMap.lsmul_apply]
    apply Subtype.val_injective
    apply (ExteriorAlgebra.equivBaseChange (R := R) (S := S) (M := M)).injective
    simp only [Function.comp_def, LinearMap.baseChange_tmul, ιMulti_apply_coe,
      Submodule.coe_smul, map_smul, ExteriorAlgebra.equivBaseChange_ιMulti_one_tmul]
    have hr := congrArg Subtype.val (h (ιMulti R n w))
    simp only [map_apply_ιMulti, ιMulti_apply_coe, Submodule.coe_smul] at hr
    change ExteriorAlgebra.ιMulti R n (fun i => f (w i)) =
      r • ExteriorAlgebra.ιMulti R n w at hr
    rw [hr, TensorProduct.tmul_smul]
    exact (IsScalarTower.algebraMap_smul S r
      ((1 : S) ⊗ₜ[R] ExteriorAlgebra.ιMulti R n w)).symm
  simpa only [LinearMap.lsmul_apply] using DFunLike.congr_fun hmap x

end exteriorPower
