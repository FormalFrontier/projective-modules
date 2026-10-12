/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Pi

/-!
# Linear independence of free-word generators

For `A = MonoidAlgebra K (FreeMonoid ι)`, the family of letter monomials is linearly
independent over the left regular A-module. Mathlib's finitely supported linear
combination multiplies each polynomial coordinate by its letter on the right. The
coefficient at `w * FreeMonoid.of a` recovers the coefficient at `w` of the a-coordinate,
so distinct terminal letters separate all the inputs, including an infinite alphabet.

Reindexing along an injective letter map gives independent subfamilies. The two-letter
map agrees with the canonical linear combination through the finite coordinate
equivalence, and its injectivity is a corollary. This gives an obstruction to the strong
rank condition, in contrast to the rank condition and invariant basis number.

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
* Mathlib, `Mathlib.LinearAlgebra.LinearIndependent.Defs` and the finitely supported
  linear-combination interface: independence, injective reindexing and finite coordinates.
-/

@[expose] public section

noncomputable section

universe u v

namespace MonoidAlgebra

variable {K : Type u} [Semiring K] {ι : Type v}

private theorem freeMonoid_mul_of_ne_mul_of {a b : ι} (hab : a ≠ b)
    (p q : FreeMonoid ι) :
    p * FreeMonoid.of a ≠ q * FreeMonoid.of b := by
  intro hpq
  apply hab
  have hlast := congrArg (fun w : FreeMonoid ι ↦ w.toList.getLast?) hpq
  simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of,
    List.getLast?_append_cons] at hlast
  exact Option.some.inj hlast

/-- The coefficient at a word ending in `a` recovers the corresponding coordinate. -/
private theorem coeff_linearCombination_freeMonoid_of
    (f : ι →₀ MonoidAlgebra K (FreeMonoid ι)) (a : ι) (w : FreeMonoid ι) :
    (Finsupp.linearCombination (MonoidAlgebra K (FreeMonoid ι))
      (fun b : ι ↦ single (FreeMonoid.of b) (1 : K)) f).coeff
        (w * FreeMonoid.of a) = (f a).coeff w := by
  classical
  simp only [Finsupp.linearCombination_apply, smul_eq_mul, coeff_finsuppSum,
    Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single a]
  · rw [coeff_mul_single_mul, mul_one]
  · intro b _ hba
    exact coeff_mul_single_of_forall_mul_ne 1 (f b)
      (fun p ↦ freeMonoid_mul_of_ne_mul_of hba p w)
  · intro _
    simp only [zero_mul, coeff_zero, Finsupp.zero_apply]

/-- Letter monomials are linearly independent over the free-word semiring acting on the left.

The coefficients of a linear combination are themselves word polynomials, and multiplication
appends each family's letter on the right. No finiteness, commutativity or nontriviality
assumption is required. This is independence over the word semiring, not just over `K`. -/
theorem linearIndependent_freeMonoid_of :
    LinearIndependent (MonoidAlgebra K (FreeMonoid ι))
      (fun a : ι ↦ single (FreeMonoid.of a) (1 : K)) := by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  intro f g hfg
  apply Finsupp.ext
  intro a
  apply coeff_injective
  apply Finsupp.ext
  intro w
  simpa only [coeff_linearCombination_freeMonoid_of] using
    congrArg (fun z : MonoidAlgebra K (FreeMonoid ι) ↦ z.coeff (w * FreeMonoid.of a)) hfg

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

/-- The two-letter map is a finitely supported linear combination in finite coordinates. -/
theorem freeWordPairMap_eq_linearCombination (a b : ι) :
    freeWordPairMap (K := K) a b =
      (Finsupp.linearCombination (MonoidAlgebra K (FreeMonoid ι))
        (fun j : Fin 2 ↦ single (FreeMonoid.of (![a, b] j)) (1 : K))).comp
        (Finsupp.linearEquivFunOnFinite (MonoidAlgebra K (FreeMonoid ι))
          (MonoidAlgebra K (FreeMonoid ι)) (Fin 2)).symm.toLinearMap := by
  rw [Finsupp.linearCombination_eq_fintype_linearCombination]
  apply LinearMap.ext
  intro z
  simp [freeWordPairMap_apply, Fintype.linearCombination_apply,
    Fin.sum_univ_two, smul_eq_mul]

/-- Appending distinct letters embeds two finite-free left modules into one.

No nontriviality or commutativity assumption on the coefficient semiring is needed. -/
theorem freeWordPairMap_injective (a b : ι) (hab : a ≠ b) :
    Function.Injective (freeWordPairMap (K := K) a b) := by
  have hc : Function.Injective (![a, b] : Fin 2 → ι) := by
    simp only [Function.Injective, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    exact ⟨⟨fun _ ↦ True.intro, fun h ↦ (hab h).elim⟩,
      ⟨fun h ↦ (hab h.symm).elim, fun _ ↦ True.intro⟩⟩
  rw [freeWordPairMap_eq_linearCombination]
  exact ((linearIndependent_freeMonoid_of (K := K) (ι := ι)).comp
    (![a, b] : Fin 2 → ι) hc).finsuppLinearCombination_injective.comp
      (Finsupp.linearEquivFunOnFinite (MonoidAlgebra K (FreeMonoid ι))
        (MonoidAlgebra K (FreeMonoid ι)) (Fin 2)).symm.injective

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
