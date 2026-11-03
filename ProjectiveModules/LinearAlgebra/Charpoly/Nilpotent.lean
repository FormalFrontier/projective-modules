/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly.CommutingNilpotent

/-!
# Characteristic polynomials of nilpotent endomorphisms

For a nilpotent endomorphism of a finite projective module over a commutative ring,
the difference between its intrinsic characteristic polynomial and that of zero is
nilpotent. Over a reduced ring the two characteristic polynomials are equal.

These are the zero-endomorphism specializations of the commuting nilpotent
perturbation theorems. The characteristic polynomial of zero accommodates varying
rank without a freeness or constant-rank hypothesis on the original module.
-/

@[expose] public section

universe u v

namespace Module

variable (R : Type u) (P : Type v)
variable [CommRing R] [AddCommGroup P] [Module R P]
variable [Module.Finite R P] [Module.Projective R P]

/-- The characteristic polynomial of a nilpotent endomorphism of a finite
projective module differs from the characteristic polynomial of zero by a
nilpotent polynomial. -/
theorem isNilpotent_charpoly_sub_charpoly_zero
    (f : Module.End R P) (hf : IsNilpotent f) :
    IsNilpotent (charpoly R P f - charpoly R P (0 : Module.End R P)) := by
  apply isNilpotent_charpoly_sub_charpoly_of_commute R P f 0
  · change f * 0 = 0 * f
    rw [mul_zero, zero_mul]
  · simpa only [sub_zero] using hf

/-- Over a reduced commutative ring, a nilpotent endomorphism of a finite
projective module has the same characteristic polynomial as zero. -/
theorem charpoly_eq_charpoly_zero_of_isNilpotent [IsReduced R]
    (f : Module.End R P) (hf : IsNilpotent f) :
    charpoly R P f = charpoly R P (0 : Module.End R P) := by
  apply charpoly_eq_charpoly_of_commute_of_isNilpotent_sub R P f 0
  · change f * 0 = 0 * f
    rw [mul_zero, zero_mul]
  · simpa only [sub_zero] using hf

end Module
