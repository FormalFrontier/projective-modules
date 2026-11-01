/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Ring.Basic

/-!
# Centrality of idempotents in reduced rings

Every idempotent in a reduced ring is central. The two elements
`e * x * (1 - e)` and `(1 - e) * x * e` have square zero and hence vanish.
The proof uses Mathlib's idempotence and reduced-power APIs.
-/

@[expose] public section

universe u

namespace IsIdempotentElem

/-- An idempotent in a reduced ring commutes with every element. -/
public theorem commute {R : Type u} [Ring R] [IsReduced R] {e : R}
    (he : IsIdempotentElem e) (x : R) : Commute e x := by
  have hleft : e * x * (1 - e) = 0 := by
    apply (pow_eq_zero_iff (by simp : (2 : ℕ) ≠ 0)).mp
    rw [pow_two]
    calc
      (e * x * (1 - e)) * (e * x * (1 - e)) =
          e * x * ((1 - e) * e) * x * (1 - e) := by simp only [mul_assoc]
      _ = 0 := by
        rw [sub_mul, one_mul, he.eq, sub_self]
        simp only [mul_zero, zero_mul]
  have hright : (1 - e) * x * e = 0 := by
    apply (pow_eq_zero_iff (by simp : (2 : ℕ) ≠ 0)).mp
    rw [pow_two]
    calc
      ((1 - e) * x * e) * ((1 - e) * x * e) =
          (1 - e) * x * (e * (1 - e)) * x * e := by simp only [mul_assoc]
      _ = 0 := by
        rw [mul_sub, mul_one, he.eq, sub_self]
        simp only [mul_zero, zero_mul]
  have hex : e * x = e * x * e := by
    apply sub_eq_zero.mp
    simpa only [mul_sub, mul_one] using hleft
  have hxe : x * e = e * x * e := by
    apply sub_eq_zero.mp
    simpa only [sub_mul, one_mul] using hright
  exact (commute_iff_eq e x).mpr (hex.trans hxe.symm)

end IsIdempotentElem
