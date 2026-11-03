/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly.MonicMultiple
public import ProjectiveModules.Algebra.Polynomial.ContentIdeal

/-!
# Coefficients of characteristic polynomials

The coefficients of the characteristic polynomial of an endomorphism of a finite
projective module generate the unit ideal over any commutative ring. Equivalently,
its polynomial content ideal is the whole ring. A monic multiple has unit
content ideal, and this property passes to its factors.

The module need not have constant rank, and its characteristic polynomial need
not be monic or have any individual unit coefficient.
-/

@[expose] public section

universe uR uP

namespace Module

/-- The coefficients of a finite projective endomorphism's characteristic polynomial
collectively generate the unit ideal, even when its rank is not constant. -/
@[simp] theorem charpoly_contentIdeal
    (R : Type uR) [CommRing R]
    (P : Type uP) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P) :
    (Module.charpoly R P f).contentIdeal = ⊤ := by
  obtain ⟨g, hmonic, h, rfl⟩ := Module.charpoly_dvd_monic R P f
  have htop : (Module.charpoly R P f * h).contentIdeal = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    simpa only [hmonic.coeff_natDegree] using
      (Polynomial.coeff_mem_contentIdeal
        (Module.charpoly R P f * h) (Module.charpoly R P f * h).natDegree)
  exact Polynomial.contentIdeal_eq_top_of_contentIdeal_mul_eq_top htop

/-- The span of every coefficient value of a finite projective characteristic
polynomial is the unit ideal. -/
theorem span_range_coeff_charpoly
    (R : Type uR) [CommRing R]
    (P : Type uP) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P) :
    Ideal.span (Set.range (Polynomial.coeff (Module.charpoly R P f))) = ⊤ := by
  simpa only [Polynomial.contentIdeal_eq_span_range_coeff] using
    (Module.charpoly_contentIdeal R P f)

end Module
