/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Free.FreeWordAugmentation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The kernel of the zero-generator free-word augmentation

For `A = MonoidAlgebra K (FreeMonoid α)`, the range of the `A`-linear combination
of letter monomials is the kernel of the zero-generator augmentation, viewed as a
semilinear map. The action on `A` is its left regular action: each polynomial
coordinate is multiplied by its letter on the right.

The proof separates the constant monomial from a finite sum of monomials ending
in letters. It uses addition and multiplication only, so it applies to arbitrary
coefficient semirings, including noncommutative and trivial semirings, and arbitrary
alphabets, including empty and infinite ones. The coefficient and alphabet universes
are independent.

## References

* Mathlib, `Mathlib.Algebra.FreeMonoid.Basic`: word reversal and word cases.
* Mathlib, `Mathlib.Algebra.MonoidAlgebra.Defs`: monomials and additive induction.
* Mathlib, `Mathlib.LinearAlgebra.Finsupp.LinearCombination`: finitely supported
  linear combinations and their range as a span.

Formal Frontier agents developed this module with AI assistance.
-/

@[expose] public section

universe u v

namespace MonoidAlgebra

variable {K : Type u} [Semiring K] {α : Type v}

private theorem exists_single_eq_constant_add_linearCombination (w : FreeMonoid α) (k : K) :
    ∃ f : α →₀ MonoidAlgebra K (FreeMonoid α),
      single w k = single 1 (freeMonoidAugmentation K α (single w k)) +
        Finsupp.linearCombination (MonoidAlgebra K (FreeMonoid α))
          (fun a : α ↦ single (FreeMonoid.of a) (1 : K)) f := by
  have h (z : FreeMonoid α) :
      ∃ f : α →₀ MonoidAlgebra K (FreeMonoid α),
        single z.reverse k = single 1 (freeMonoidAugmentation K α (single z.reverse k)) +
          Finsupp.linearCombination (MonoidAlgebra K (FreeMonoid α))
            (fun a : α ↦ single (FreeMonoid.of a) (1 : K)) f := by
    cases z using FreeMonoid.casesOn with
    | one =>
      have hreverse : FreeMonoid.reverse (1 : FreeMonoid α) = 1 := rfl
      exact ⟨0, by simp only [hreverse, freeMonoidAugmentation_single_one, map_zero, add_zero]⟩
    | of_mul a z =>
      refine ⟨Finsupp.single a (single z.reverse k), ?_⟩
      simp only [FreeMonoid.reverse_mul, FreeMonoid.reverse_of,
        freeMonoidAugmentation_single, map_mul, FreeMonoid.lift_eval_of, mul_zero,
        single_zero, zero_add, Finsupp.linearCombination_single, smul_eq_mul,
        single_mul_single, mul_one]
  simpa only [FreeMonoid.reverse_reverse] using h w.reverse

private theorem exists_eq_constant_add_linearCombination (x : MonoidAlgebra K (FreeMonoid α)) :
    ∃ f : α →₀ MonoidAlgebra K (FreeMonoid α),
      x = single 1 (freeMonoidAugmentation K α x) +
        Finsupp.linearCombination (MonoidAlgebra K (FreeMonoid α))
          (fun a : α ↦ single (FreeMonoid.of a) (1 : K)) f := by
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
    exact ⟨0, by simp only [map_zero, single_zero, add_zero]⟩
  | add x y hx hy =>
    obtain ⟨f, hf⟩ := hx
    obtain ⟨g, hg⟩ := hy
    refine ⟨f + g, ?_⟩
    calc
      x + y = (single 1 (freeMonoidAugmentation K α x) +
          Finsupp.linearCombination (MonoidAlgebra K (FreeMonoid α))
            (fun a : α ↦ single (FreeMonoid.of a) (1 : K)) f) +
        (single 1 (freeMonoidAugmentation K α y) +
          Finsupp.linearCombination (MonoidAlgebra K (FreeMonoid α))
            (fun a : α ↦ single (FreeMonoid.of a) (1 : K)) g) := by rw [← hf, ← hg]
      _ = _ := by simp only [map_add, single_add, add_add_add_comm]
  | single w k => exact exists_single_eq_constant_add_linearCombination w k

/-- The letter-monomial linear combination has range equal to the kernel of the
zero-generator augmentation as a semilinear map.

Both submodules use the canonical left regular action of the free-word semiring.
The coefficient semiring may be noncommutative or trivial, and the alphabet may be
empty or infinite. -/
theorem range_linearCombination_freeMonoid_of_eq_ker_freeMonoidAugmentation :
    LinearMap.range (Finsupp.linearCombination (MonoidAlgebra K (FreeMonoid α))
      (fun a : α ↦ single (FreeMonoid.of a) (1 : K))) =
      LinearMap.ker (freeMonoidAugmentation K α).toSemilinearMap := by
  apply le_antisymm
  · rw [Finsupp.range_linearCombination]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    exact LinearMap.mem_ker.mpr (freeMonoidAugmentation_single_of a (1 : K))
  · intro x hx
    have hx0 : freeMonoidAugmentation K α x = 0 := LinearMap.mem_ker.mp hx
    obtain ⟨f, hf⟩ := exists_eq_constant_add_linearCombination x
    exact LinearMap.mem_range.mpr ⟨f, by
      simpa only [hx0, single_zero, zero_add] using hf.symm⟩

end MonoidAlgebra
