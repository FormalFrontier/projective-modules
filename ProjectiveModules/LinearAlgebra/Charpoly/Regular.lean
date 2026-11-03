/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import ProjectiveModules.Module.ProjectiveComplement
import Mathlib.LinearAlgebra.Charpoly.Basic
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

The proof combines the existing finite free complement, product formula and
finite-free comparison with Mathlib's monicity and polynomial-regularity APIs.
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
  classical
  have hAux :
      ∀ (Q : Type uR) [AddCommGroup Q] [Module R Q]
        [Module.Finite R Q] [Module.Finite R (P × Q)] [Module.Free R (P × Q)],
        Module.charpoly R P f ∈ nonZeroDivisors (Polynomial R) := by
    intro Q _ _ _ _ _
    have : Module.Projective R (P × Q) := inferInstance
    -- The complementary summand is a retract of the free product.
    have : Module.Projective R Q :=
      Module.Projective.of_split (LinearMap.inr R P Q) (LinearMap.snd R P Q)
        (by ext q; rfl)
    have hmonic :
        (Module.charpoly R P f * Module.charpoly R Q (0 : Module.End R Q)).Monic := by
      rw [← Module.charpoly_prodMap R P Q f (0 : Module.End R Q),
        Module.charpoly_eq_charpoly R (P × Q)]
      exact LinearMap.charpoly_monic _
    exact IsRegular.mem_nonZeroDivisors (IsRegular.of_mul_left hmonic.isRegular)
  obtain ⟨Q, hAdd, hModule, hFinite, hFiniteProd, hFreeProd⟩ :=
    Module.exists_finite_free_product_of_finite_projective (R := R) (B := P)
  exact @hAux Q hAdd hModule hFinite hFiniteProd hFreeProd

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
