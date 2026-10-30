/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Int.Interval

/-!
# Parity sums of adjacent terms on integer intervals

For a function `z : ℤ → A` into an arbitrary additive commutative monoid, suppose that
`z a = 0` and `z (b + 1) = 0`. Summing `z i + z (i + 1)` over either the even or the odd
indices in `Finset.Icc a b` gives the sum of `z` over `Finset.Icc (a + 1) b`.
In particular, the two parity sums agree, without any cancellation assumption.

The proofs use Mathlib's finite-sum reindexing and complementary-filter partition lemmas:
the successor reindexing reverses parity, and the two zero endpoints can be omitted.
No ordering hypothesis on the endpoints is needed.
-/

@[expose] public section

open scoped BigOperators

namespace Int

universe u

variable {A : Type u} [AddCommMonoid A]

private theorem sum_Icc_filter_eq_of_zero_left (z : ℤ → A) (a b : ℤ)
    (p : ℤ → Prop) [DecidablePred p] (ha : z a = 0) :
    (∑ i ∈ Finset.Icc a b with p i, z i) =
      ∑ i ∈ Finset.Icc (a + 1) b with p i, z i := by
  symm
  refine Finset.sum_subset ?_ ?_
  · intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hi, hpi⟩
    rcases Finset.mem_Icc.mp hi with ⟨hai, hib⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hib⟩, hpi⟩
  · intro i hi hnot
    rcases Finset.mem_filter.mp hi with ⟨hi, hpi⟩
    rcases Finset.mem_Icc.mp hi with ⟨hai, hib⟩
    have hia : i = a := by
      by_contra hia
      exact hnot (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, hib⟩, hpi⟩)
    simpa only [hia] using ha

private theorem sum_Icc_filter_succ_eq (z : ℤ → A) (a b : ℤ)
    (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ i, p i ↔ q (i + 1)) (hb : z (b + 1) = 0) :
    (∑ i ∈ Finset.Icc a b with p i, z (i + 1)) =
      ∑ i ∈ Finset.Icc (a + 1) b with q i, z i := by
  classical
  refine Finset.sum_bij_ne_zero (fun i _ _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi hz
    rcases Finset.mem_filter.mp hi with ⟨hi, hpi⟩
    rcases Finset.mem_Icc.mp hi with ⟨hai, hib⟩
    have hib' : i ≠ b := by
      intro h
      apply hz
      simpa only [h] using hb
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, (hpq i).mp hpi⟩
  · intro i hi hzi j hj hzj hij
    omega
  · intro j hj hz
    rcases Finset.mem_filter.mp hj with ⟨hj, hqj⟩
    rcases Finset.mem_Icc.mp hj with ⟨haj, hjb⟩
    have hj' : j - 1 + 1 = j := by omega
    refine ⟨j - 1, ?_, ?_, hj'⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      exact (hpq (j - 1)).mpr (by simpa only [hj'] using hqj)
    · simpa only [hj'] using hz
  · intro i hi hz
    rfl

private theorem sum_Icc_filter_add_eq_of_toggle (z : ℤ → A) (a b : ℤ)
    (p : ℤ → Prop) [DecidablePred p] (hp : ∀ i, p (i + 1) ↔ ¬p i)
    (ha : z a = 0) (hb : z (b + 1) = 0) :
    (∑ i ∈ Finset.Icc a b with p i, (z i + z (i + 1))) =
      ∑ i ∈ Finset.Icc (a + 1) b, z i := by
  classical
  have hshift : ∀ i, p i ↔ ¬p (i + 1) := by
    intro i
    simp only [hp i, not_not]
  rw [Finset.sum_add_distrib, sum_Icc_filter_eq_of_zero_left z a b p ha,
    sum_Icc_filter_succ_eq z a b p (fun i => ¬p i) hshift hb]
  exact Finset.sum_filter_add_sum_filter_not (Finset.Icc (a + 1) b) p z

/-- With zero endpoint values, summing adjacent terms over the even indices of an integer
interval gives the sum over the interior interval. This holds in any additive commutative
monoid, including when the interval is empty. -/
theorem sum_Icc_even_add_eq_sum_Icc (z : ℤ → A) (a b : ℤ)
    (ha : z a = 0) (hb : z (b + 1) = 0) :
    (∑ i ∈ Finset.Icc a b with Even i, (z i + z (i + 1))) =
      ∑ i ∈ Finset.Icc (a + 1) b, z i :=
  sum_Icc_filter_add_eq_of_toggle z a b Even (fun _ => even_add_one) ha hb

/-- With zero endpoint values, summing adjacent terms over the odd indices of an integer
interval gives the sum over the interior interval. This holds in any additive commutative
monoid, including when the interval is empty. -/
theorem sum_Icc_odd_add_eq_sum_Icc (z : ℤ → A) (a b : ℤ)
    (ha : z a = 0) (hb : z (b + 1) = 0) :
    (∑ i ∈ Finset.Icc a b with Odd i, (z i + z (i + 1))) =
      ∑ i ∈ Finset.Icc (a + 1) b, z i :=
  sum_Icc_filter_add_eq_of_toggle z a b Odd
    (fun i => by simp only [← not_even_iff_odd, even_add_one, not_not]) ha hb

/-- The even and odd sums of adjacent terms agree when the two endpoint values vanish.
No cancellation or additive inverses in the target monoid are required. -/
theorem sum_Icc_even_add_eq_sum_Icc_odd_add (z : ℤ → A) (a b : ℤ)
    (ha : z a = 0) (hb : z (b + 1) = 0) :
    (∑ i ∈ Finset.Icc a b with Even i, (z i + z (i + 1))) =
      ∑ i ∈ Finset.Icc a b with Odd i, (z i + z (i + 1)) :=
  (sum_Icc_even_add_eq_sum_Icc z a b ha hb).trans
    (sum_Icc_odd_add_eq_sum_Icc z a b ha hb).symm

end Int
