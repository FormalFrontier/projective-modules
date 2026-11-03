/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly.CayleyHamilton
import ProjectiveModules.LinearAlgebra.Charpoly.MonicMultiple
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Nilpotence criteria from characteristic polynomials

For an endomorphism of a finite projective module over a commutative ring,
nilpotence of the difference between its characteristic polynomial and that of
zero implies nilpotence of the endomorphism. Equality of the two characteristic
polynomials is a special case.

The nilpotent-difference criterion also applies to nonzero nilpotent differences
over nonreduced rings, beyond the equality criterion. The module need not be
faithful or have constant rank, and its characteristic polynomial need not be
monic.

## References

* Mathlib's Cayley–Hamilton theory for finite free modules.
-/

@[expose] public section

universe uR uP

namespace Module

/-- An endomorphism of a finite projective module is nilpotent if the difference
between its characteristic polynomial and that of zero is nilpotent. This allows
nonzero nilpotent differences over nonreduced rings. -/
theorem isNilpotent_of_isNilpotent_charpoly_sub_charpoly_zero
    (R : Type uR) [CommRing R]
    (P : Type uP) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P)
    (h : IsNilpotent
      (Module.charpoly R P f - Module.charpoly R P (0 : Module.End R P))) :
    IsNilpotent f := by
  have hZero :
      IsNilpotent
        (Polynomial.aeval f (Module.charpoly R P (0 : Module.End R P))) := by
    have hEval := h.map (Polynomial.aeval f)
    rw [map_sub, Module.aeval_self_charpoly R P f, zero_sub] at hEval
    simpa only [neg_neg] using hEval.neg
  obtain ⟨k, hk⟩ := hZero
  obtain ⟨n, hn⟩ := Module.charpoly_zero_dvd_X_pow R P
  obtain ⟨q, hq⟩ := hn
  refine ⟨n * k, ?_⟩
  calc
    f ^ (n * k) =
        Polynomial.aeval f (((Polynomial.X : Polynomial R) ^ n) ^ k) := by
      simp only [map_pow, Polynomial.aeval_X, pow_mul]
    _ = Polynomial.aeval f
        ((Module.charpoly R P (0 : Module.End R P)) ^ k * q ^ k) := by
      -- Expand the product power in the commutative polynomial ring, not in End.
      rw [hq, mul_pow]
    _ = 0 := by
      rw [map_mul, map_pow, hk, zero_mul]

/-- An endomorphism of a finite projective module is nilpotent if its
characteristic polynomial equals that of zero. -/
theorem isNilpotent_of_charpoly_eq_charpoly_zero
    (R : Type uR) [CommRing R]
    (P : Type uP) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P)
    (h : Module.charpoly R P f = Module.charpoly R P (0 : Module.End R P)) :
    IsNilpotent f := by
  apply isNilpotent_of_isNilpotent_charpoly_sub_charpoly_zero R P f
  rw [h, sub_self]
  exact ⟨1, by simp⟩

end Module

namespace LinearMap

/-- A finite free endomorphism is nilpotent if the difference between its
Mathlib characteristic polynomial and that of zero is nilpotent. This is the
finite-free specialization of the finite-projective criterion. -/
theorem isNilpotent_of_isNilpotent_charpoly_sub_charpoly_zero
    (R : Type uR) [CommRing R]
    (P : Type uP) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Free R P]
    (f : Module.End R P)
    (h : IsNilpotent
      (LinearMap.charpoly f - LinearMap.charpoly (0 : Module.End R P))) :
    IsNilpotent f := by
  have : Module.Projective R P := inferInstance
  apply Module.isNilpotent_of_isNilpotent_charpoly_sub_charpoly_zero R P f
  simpa only [Module.charpoly_eq_charpoly R P] using h

end LinearMap
