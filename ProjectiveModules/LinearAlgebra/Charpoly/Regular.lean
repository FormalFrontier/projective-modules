/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly.MonicMultiple
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Regular.Basic

/-!
# Regularity of characteristic polynomials

The characteristic polynomial of an endomorphism of a finite projective module is
regular: multiplication by it is injective, including over the zero ring. It need
not be monic when the projective module has varying rank. Consequently an
intertwining equivalence after adding a common endomorphism allows cancellation
of the common characteristic-polynomial factor.

A monic multiple of the characteristic polynomial is regular, so the
characteristic polynomial itself is regular as a factor.
-/

@[expose] public section

universe uR uP uP' uQ

namespace Module

/-- The characteristic polynomial of an endomorphism of a finite projective module is a
non-zero-divisor, over an arbitrary commutative ring. -/
theorem charpoly_mem_nonZeroDivisors
    (R : Type uR) [CommRing R]
    (P : Type uP) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P) :
    Module.charpoly R P f ∈ nonZeroDivisors (Polynomial R) := by
  obtain ⟨g, hmonic, h, rfl⟩ := Module.charpoly_dvd_monic R P f
  exact IsRegular.mem_nonZeroDivisors (IsRegular.of_mul_left hmonic.isRegular)

/-- An intertwining equivalence after adding a common finite projective endomorphism
forces equality of characteristic polynomials. -/
theorem charpoly_eq_of_stable_intertwining
    (R : Type uR) [CommRing R]
    (P : Type uP) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (P' : Type uP') [AddCommGroup P'] [Module R P']
    [Module.Finite R P'] [Module.Projective R P']
    (Q : Type uQ) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q]
    (f : Module.End R P) (f' : Module.End R P')
    (g : Module.End R Q)
    (e : (P × Q) ≃ₗ[R] (P' × Q))
    (h : e.toLinearMap.comp (f.prodMap g) =
      (f'.prodMap g).comp e.toLinearMap) :
    Module.charpoly R P f = Module.charpoly R P' f' := by
  have hprod :
      Module.charpoly R P f * Module.charpoly R Q g =
        Module.charpoly R P' f' * Module.charpoly R Q g := by
    simpa only [Module.charpoly_prodMap] using
      (Module.charpoly_eq_of_intertwining R (P × Q) (P' × Q)
        (f.prodMap g) (f'.prodMap g) e h)
  have hzero :
      (Module.charpoly R P f - Module.charpoly R P' f') *
        Module.charpoly R Q g = 0 := by
    rw [sub_mul, hprod, sub_self]
  exact sub_eq_zero.mp
    ((mem_nonZeroDivisors_iff.mp
      (Module.charpoly_mem_nonZeroDivisors R Q g)).2 _ hzero)

end Module
