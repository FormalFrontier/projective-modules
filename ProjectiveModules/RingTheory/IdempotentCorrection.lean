/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.NoncommRing

/-!
# A cubic idempotent correction step

For an element `a` of a ring, `idempotentCorrection a` is the cubic `3 * a ^ 2 - 2 * a ^ 3`.
Its difference from `a` is a left multiple of `a * a - a`, and its idempotence error is
a multiple of the square of that error. In particular, square-zero error suffices for the
corrected element to be idempotent.

The correction commutes with ring homomorphisms and fixes idempotent elements. The ideal
closeness statement uses only left-ideal closure and does not require a two-sided ideal.
-/

@[expose] public section

universe u v

variable {R : Type u} [Ring R]

/-- The cubic correction step `3 * a ^ 2 - 2 * a ^ 3` for an element of a ring. -/
def idempotentCorrection (a : R) : R :=
  3 * a ^ 2 - 2 * a ^ 3

/-- The difference between the correction and its input is a left multiple of the
input's idempotence error. -/
theorem idempotentCorrection_sub_self (a : R) :
    idempotentCorrection a - a = (1 - 2 * a) * (a * a - a) := by
  unfold idempotentCorrection
  noncomm_ring

/-- The correction's idempotence error is a multiple of the square of the input's error. -/
theorem idempotentCorrection_mul_self_sub_self (a : R) :
    idempotentCorrection a * idempotentCorrection a - idempotentCorrection a =
      (4 * (a * a - a) - 3) * ((a * a - a) * (a * a - a)) := by
  unfold idempotentCorrection
  noncomm_ring

/-- Correcting an element with square-zero idempotence error gives an idempotent element. -/
theorem isIdempotentElem_idempotentCorrection (a : R)
    (h : (a * a - a) * (a * a - a) = 0) : IsIdempotentElem (idempotentCorrection a) := by
  apply isIdempotentElem_iff.mpr
  apply sub_eq_zero.mp
  rw [idempotentCorrection_mul_self_sub_self, h, mul_zero]

/-- If the input's idempotence error lies in a left ideal, so does the difference
between its correction and itself. -/
theorem idempotentCorrection_sub_self_mem (I : Ideal R) (a : R)
    (h : a * a - a ∈ I) : idempotentCorrection a - a ∈ I := by
  rw [idempotentCorrection_sub_self]
  exact I.mul_mem_left (1 - 2 * a) h

/-- Ring homomorphisms preserve the cubic correction step. -/
@[simp]
theorem RingHom.map_idempotentCorrection {S : Type v} [Ring S] (f : R →+* S) (a : R) :
    f (idempotentCorrection a) = idempotentCorrection (f a) := by
  have h := congrArg f (idempotentCorrection_sub_self a)
  simp only [map_sub, map_mul, map_one, map_ofNat] at h
  rw [← idempotentCorrection_sub_self (f a)] at h
  simpa only [sub_add_cancel] using congrArg (fun x : S => x + f a) h

/-- The correction step leaves an idempotent element unchanged. -/
@[simp]
theorem IsIdempotentElem.idempotentCorrection_eq {a : R} (h : IsIdempotentElem a) :
    idempotentCorrection a = a := by
  apply sub_eq_zero.mp
  rw [idempotentCorrection_sub_self, isIdempotentElem_iff.mp h, sub_self, mul_zero]
