/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Characteristic polynomials of nilpotent endomorphisms

For a nilpotent endomorphism of a finite projective module over a commutative ring,
the difference between its intrinsic characteristic polynomial and that of zero is
nilpotent. Over a reduced ring the two characteristic polynomials are equal.

The proof passes to the fraction field of every prime quotient, using Mathlib's
`IsNilpotent.charpoly_eq_X_pow_finrank` for the finite-free comparison. The
characteristic polynomial of zero accommodates varying rank without a freeness
or constant-rank hypothesis on the original module.
-/

@[expose] public section

universe u v

open scoped TensorProduct
open Polynomial

namespace Module

variable (R : Type u) (P : Type v)
variable [CommRing R] [AddCommGroup P] [Module R P]
variable [Module.Finite R P] [Module.Projective R P]

private theorem charpoly_map_eq_charpoly_zero_of_isNilpotent
    (K : Type*) [Field K] [Algebra R K]
    (f : Module.End R P) (hf : IsNilpotent f) :
    (charpoly R P f).map (algebraMap R K) =
      (charpoly R P (0 : Module.End R P)).map (algebraMap R K) := by
  classical
  have hfK : IsNilpotent (f.baseChange K) := by
    obtain ⟨k, hk⟩ := hf
    refine ⟨k, ?_⟩
    rw [← LinearMap.baseChange_pow, hk, LinearMap.baseChange_zero]
  have hchar :
      charpoly K (K ⊗[R] P) (f.baseChange K) =
        charpoly K (K ⊗[R] P) ((0 : Module.End R P).baseChange K) := by
    rw [LinearMap.baseChange_zero, charpoly_eq_charpoly, charpoly_eq_charpoly]
    simpa using hfK.charpoly_eq_X_pow_finrank
  rwa [charpoly_baseChange, charpoly_baseChange] at hchar

/-- The characteristic polynomial of a nilpotent endomorphism of a finite
projective module differs from the characteristic polynomial of zero by a
nilpotent polynomial. -/
theorem isNilpotent_charpoly_sub_charpoly_zero
    (f : Module.End R P) (hf : IsNilpotent f) :
    IsNilpotent (charpoly R P f - charpoly R P (0 : Module.End R P)) := by
  classical
  apply Polynomial.isNilpotent_iff.mpr
  intro i
  apply nilpotent_iff_mem_prime.mpr
  intro p hp
  let : p.IsPrime := hp
  let K := FractionRing (R ⧸ p)
  -- Fix the field structure before using it to construct the composite algebra.
  let : Field K := inferInstance
  let : Algebra R K :=
    ((algebraMap (R ⧸ p) K).comp (Ideal.Quotient.mk p)).toAlgebra
  have hchar := charpoly_map_eq_charpoly_zero_of_isNilpotent R P K f hf
  have hcoeff :
      algebraMap R K ((charpoly R P f - charpoly R P 0).coeff i) = 0 := by
    have h := congrArg (fun q : K[X] => q.coeff i) hchar
    simp only [Polynomial.coeff_map] at h
    rw [Polynomial.coeff_sub, map_sub, sub_eq_zero]
    exact h
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply IsFractionRing.injective (R ⧸ p) K
  change algebraMap R K ((charpoly R P f - charpoly R P 0).coeff i) =
    algebraMap (R ⧸ p) K 0
  simpa only [map_zero] using hcoeff

/-- Over a reduced commutative ring, a nilpotent endomorphism of a finite
projective module has the same characteristic polynomial as zero. -/
theorem charpoly_eq_charpoly_zero_of_isNilpotent [IsReduced R]
    (f : Module.End R P) (hf : IsNilpotent f) :
    charpoly R P f = charpoly R P (0 : Module.End R P) := by
  apply sub_eq_zero.mp
  ext i
  simpa only [Polynomial.coeff_zero] using
    ((Polynomial.isNilpotent_iff.mp
      (isNilpotent_charpoly_sub_charpoly_zero R P f hf)) i).eq_zero

end Module
