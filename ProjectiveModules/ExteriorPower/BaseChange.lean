/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Iris
module

import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import ProjectiveModules.ExteriorAlgebra.BaseChange

/-!
# Homogeneous exterior powers under scalar extension

The compatibility statement in this file identifies the image of each homogeneous
exterior-power submodule under `ExteriorAlgebra.equivBaseChange` with the scalar extension
of the original submodule. The underlying exterior-algebra equivalence is due to Prism.

The rings and module have independent universes, and the degree can be zero. No finiteness,
projectivity, flatness, or nontriviality assumption is imposed. No equivalence between the
fixed-degree carriers is constructed in this file.
-/

@[expose] public section

open scoped TensorProduct

namespace ExteriorAlgebra

universe uR uS uM

variable {R : Type uR} {S : Type uS} {M : Type uM}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

private theorem equivBaseChange_ιMulti_one_tmul (n : ℕ) :
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
  have ht : Submodule.span S (Set.range t) = ⊤ := by
    suffices hspan : ∀ x : S ⊗[R] M, x ∈ Submodule.span S (Set.range t) by
      apply top_unique
      intro x _
      exact hspan x
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s m =>
        have hm : t m ∈ Submodule.span S (Set.range t) :=
          Submodule.subset_span (Set.mem_range_self m)
        simpa only [t, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
          (Submodule.span S (Set.range t)).smul_mem s hm
    | add x y hx hy => exact (Submodule.span S (Set.range t)).add_mem hx hy
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
