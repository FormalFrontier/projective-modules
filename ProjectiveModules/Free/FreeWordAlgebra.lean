/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Pi

/-!
# A finite-free injection over a free-word semiring

For `A = MonoidAlgebra K (FreeMonoid ι)`, right multiplication by two letter monomials
combines two copies of the left regular module into one. Distinct letters give disjoint
suffixes: the coefficient at `w * FreeMonoid.of a` recovers the first input, and the
coefficient at `w * FreeMonoid.of b` recovers the second. This yields an obstruction to
the strong rank condition, in contrast to the rank condition and invariant basis number.

The coefficient semiring need not be commutative or nontrivial, and the alphabet need not
be finite. For a trivial coefficient semiring the free modules are singleton types, so
this case does not furnish a nonzero example. Distinct letters are essential for the
uniform statement: over nontrivial coefficients, repeating the same letter identifies
the two coordinate vectors.

## References

* Mathlib, `Mathlib.LinearAlgebra.InvariantBasisNumber`, counterexamples to converse
  results: the free-algebra contrast, attributed there to T. Y. Lam,
  *Lectures on Modules and Rings* (Springer, 1999).
* Mathlib, `Mathlib.Algebra.FreeMonoid.Basic` and `Mathlib.Algebra.MonoidAlgebra.Defs`:
  the word model, convolution multiplication and coefficient formulas used by the
  disjoint-suffix argument.
* Mathlib, `Mathlib.Algebra.Module.LinearMap.Defs` and `Mathlib.LinearAlgebra.Pi`:
  right multiplication as a left-linear map and coordinate projections.
-/

@[expose] public section

noncomputable section

universe u v

namespace MonoidAlgebra

variable {K : Type u} [Semiring K] {ι : Type v}

/-- Combine two left regular modules by appending the letters `a` and `b` on the right.

The map is linear over the possibly noncommutative semiring
`MonoidAlgebra K (FreeMonoid ι)` acting on the left. -/
def freeWordPairMap (a b : ι) :
    (Fin 2 → MonoidAlgebra K (FreeMonoid ι)) →ₗ[MonoidAlgebra K (FreeMonoid ι)]
      MonoidAlgebra K (FreeMonoid ι) :=
  (LinearMap.mulRight (MonoidAlgebra K (FreeMonoid ι))
      (single (FreeMonoid.of a) (1 : K))).comp
      (LinearMap.proj (R := MonoidAlgebra K (FreeMonoid ι))
        (φ := fun _ : Fin 2 ↦ MonoidAlgebra K (FreeMonoid ι)) 0) +
    (LinearMap.mulRight (MonoidAlgebra K (FreeMonoid ι))
      (single (FreeMonoid.of b) (1 : K))).comp
      (LinearMap.proj (R := MonoidAlgebra K (FreeMonoid ι))
        (φ := fun _ : Fin 2 ↦ MonoidAlgebra K (FreeMonoid ι)) 1)

/-- The two coordinates are multiplied by the corresponding letter monomials on the right. -/
@[simp]
theorem freeWordPairMap_apply (a b : ι) (x : Fin 2 → MonoidAlgebra K (FreeMonoid ι)) :
    freeWordPairMap a b x =
      x 0 * single (FreeMonoid.of a) 1 + x 1 * single (FreeMonoid.of b) 1 := by
  simp only [freeWordPairMap, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, LinearMap.proj_apply]

/-- Appending distinct letters embeds two finite-free left modules into one.

No nontriviality or commutativity assumption on the coefficient semiring is needed. -/
theorem freeWordPairMap_injective (a b : ι) (hab : a ≠ b) :
    Function.Injective (freeWordPairMap (K := K) a b) := by
  have suffix_ne (c d : ι) (hcd : c ≠ d) (p q : FreeMonoid ι) :
      p * FreeMonoid.of c ≠ q * FreeMonoid.of d := by
    intro hpq
    apply hcd
    have hlast := congrArg (fun w : FreeMonoid ι ↦ w.toList.getLast?) hpq
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of,
      List.getLast?_append_cons] at hlast
    exact Option.some.inj hlast
  have recover (c d : ι) (hcd : c ≠ d)
      (p q : MonoidAlgebra K (FreeMonoid ι)) (w : FreeMonoid ι) :
      (p * single (FreeMonoid.of c) 1 + q * single (FreeMonoid.of d) 1).coeff
        (w * FreeMonoid.of c) = p.coeff w := by
    rw [coeff_add, Finsupp.add_apply, coeff_mul_single_mul,
      coeff_mul_single_of_forall_mul_ne 1 q (fun v ↦ suffix_ne d c hcd.symm v w),
      mul_one, add_zero]
  have recover_zero (z : Fin 2 → MonoidAlgebra K (FreeMonoid ι)) (w : FreeMonoid ι) :
      (freeWordPairMap a b z).coeff (w * FreeMonoid.of a) = (z 0).coeff w := by
    rw [freeWordPairMap_apply, recover a b hab]
  have recover_one (z : Fin 2 → MonoidAlgebra K (FreeMonoid ι)) (w : FreeMonoid ι) :
      (freeWordPairMap a b z).coeff (w * FreeMonoid.of b) = (z 1).coeff w := by
    rw [freeWordPairMap_apply, add_comm, recover b a hab.symm]
  intro x y hxy
  apply funext
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · apply coeff_injective
    apply Finsupp.ext
    intro w
    simpa only [recover_zero] using
      congrArg (fun z : MonoidAlgebra K (FreeMonoid ι) ↦ z.coeff (w * FreeMonoid.of a)) hxy
  · apply coeff_injective
    apply Finsupp.ext
    intro w
    simpa only [recover_one] using
      congrArg (fun z : MonoidAlgebra K (FreeMonoid ι) ↦ z.coeff (w * FreeMonoid.of b)) hxy

/-- A free-word semiring on two distinct letters fails the strong rank condition.

This realizes the free-algebra contrast recorded in Mathlib's invariant-basis-number
module, using the finite-free left-module injection rather than an opposite-ring bridge. -/
theorem not_strongRankCondition_freeMonoid (a b : ι) (hab : a ≠ b) :
    ¬ StrongRankCondition (MonoidAlgebra K (FreeMonoid ι)) := by
  intro h
  let : StrongRankCondition (MonoidAlgebra K (FreeMonoid ι)) := h
  let e := LinearEquiv.piUnique (MonoidAlgebra K (FreeMonoid ι))
    (fun _ : Fin 1 ↦ MonoidAlgebra K (FreeMonoid ι))
  have hle : 2 ≤ 1 :=
    le_of_fin_injective (MonoidAlgebra K (FreeMonoid ι))
      (e.symm.toLinearMap.comp (freeWordPairMap (K := K) a b))
      (e.symm.injective.comp (freeWordPairMap_injective (K := K) a b hab))
  exact Nat.not_succ_le_self 1 hle

end MonoidAlgebra
