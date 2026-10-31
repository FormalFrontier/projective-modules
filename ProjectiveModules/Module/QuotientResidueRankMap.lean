/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import ProjectiveModules.Module.QuotientResidueRank

/-!
# Quotient residue ranks under pullback

The residue-field rank of a quotient module is preserved under pullback along the map on prime
spectra induced by a ring homomorphism.
-/

@[expose] public section

open scoped TensorProduct

universe uR uS

namespace Module

/-- After lifting to a common universe, the residue-field rank of `S ⧸ I.map f` at `q` equals
that of `R ⧸ I` at `PrimeSpectrum.comap f q`. -/
theorem lift_rank_residueField_tensor_quotient_map
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (q : PrimeSpectrum S) :
    Cardinal.lift.{uR} (Module.rank q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[S] (S ⧸ I.map f))) =
    Cardinal.lift.{uS} (Module.rank (PrimeSpectrum.comap f q).asIdeal.ResidueField
      ((PrimeSpectrum.comap f q).asIdeal.ResidueField ⊗[R] (R ⧸ I))) := by
  have hmap : I.map f ≤ q.asIdeal ↔ I ≤ (PrimeSpectrum.comap f q).asIdeal := by
    rw [PrimeSpectrum.comap_asIdeal]
    exact Ideal.map_le_iff_le_comap
  by_cases h : I.map f ≤ q.asIdeal
  · simp only [rank_residueField_tensor_quotient_eq_one (I.map f) q h,
      rank_residueField_tensor_quotient_eq_one I (PrimeSpectrum.comap f q) (hmap.mp h),
      Cardinal.lift_one]
  · have hcomap : ¬ I ≤ (PrimeSpectrum.comap f q).asIdeal := fun hI => h (hmap.mpr hI)
    simp only [rank_residueField_tensor_quotient_eq_zero (I.map f) q h,
      rank_residueField_tensor_quotient_eq_zero I (PrimeSpectrum.comap f q) hcomap,
      Cardinal.lift_zero]

end Module
