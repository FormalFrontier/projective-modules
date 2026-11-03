/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly
import ProjectiveModules.Module.ProjectiveComplement
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Prod

/-!
# Monic multiples of characteristic polynomials

The characteristic polynomial of an endomorphism of a finite projective module
divides a monic polynomial over any commutative ring. A finite free complement
supplies such a polynomial through the product formula for characteristic
polynomials.

The module need not have constant rank, and its characteristic polynomial need
not itself be monic.
-/

@[expose] public section

universe uR uP

namespace Module

/-- The characteristic polynomial of a finite projective endomorphism divides a
monic polynomial. -/
theorem charpoly_dvd_monic
    (R : Type uR) [CommRing R]
    (P : Type uP) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P) :
    ∃ g : Polynomial R, g.Monic ∧ Module.charpoly R P f ∣ g := by
  classical
  have hAux :
      ∀ (Q : Type uR) [AddCommGroup Q] [Module R Q]
        [Module.Finite R Q] [Module.Finite R (P × Q)] [Module.Free R (P × Q)],
        ∃ g : Polynomial R, g.Monic ∧ Module.charpoly R P f ∣ g := by
    intro Q _ _ _ _ _
    have : Module.Projective R (P × Q) := inferInstance
    -- The complementary summand is a retract of the free product.
    have : Module.Projective R Q :=
      Module.Projective.of_split (LinearMap.inr R P Q) (LinearMap.snd R P Q)
        (by ext q; rfl)
    refine ⟨Module.charpoly R P f * Module.charpoly R Q (0 : Module.End R Q),
      ?_, ⟨Module.charpoly R Q (0 : Module.End R Q), rfl⟩⟩
    rw [← Module.charpoly_prodMap R P Q f (0 : Module.End R Q),
      Module.charpoly_eq_charpoly R (P × Q)]
    exact LinearMap.charpoly_monic _
  obtain ⟨Q, hAdd, hModule, hFinite, hFiniteProd, hFreeProd⟩ :=
    Module.exists_finite_free_product_of_finite_projective (R := R) (B := P)
  exact @hAux Q hAdd hModule hFinite hFiniteProd hFreeProd

end Module
