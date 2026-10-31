/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.FiniteOfFiberRank
public import ProjectiveModules.Module.LocallyConstantResidueRank
public import ProjectiveModules.Module.ResidueRank
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Finite generation from locally constant finite residue rank

A projective module over a commutative ring is finitely generated if and only if its
residue fibers have finite rank and their Cardinal-valued rank is locally constant
on the prime spectrum. The local ranks need not have a common value.

Finite generation is deduced by applying the constant-rank finiteness theorem on
basic open neighborhoods and then using locality of finite generation. Allowing
the rank to vary locally generalizes the constant-rank case of the exercise below.

## References

* Charles A. Weibel, *The K-book*, Chapter I, §2, Exercise 2.14 (constant-rank case).
-/

@[expose] public section

universe uR v

open scoped TensorProduct

namespace Module.Projective

private theorem residue_rank_eq_of_ideal_eq
    {R : Type uR} [CommRing R]
    {P : Type v} [AddCommMonoid P] [Module R P]
    (I J : Ideal R) [I.IsPrime] [J.IsPrime] (hIJ : I = J) :
    Module.rank I.ResidueField (I.ResidueField ⊗[R] P) =
      Module.rank J.ResidueField (J.ResidueField ⊗[R] P) := by
  subst J
  rfl

private theorem finite_away_of_residue_rank_eq_nat
    {R : Type uR} [CommRing R]
    {P : Type v} [AddCommMonoid P] [Module R P] [Module.Projective R P]
    (f : R) (r : ℕ)
    (h : ∀ q : PrimeSpectrum R, q ∈ PrimeSpectrum.basicOpen f →
      Module.rank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[R] P) =
        (r : Cardinal)) :
    Module.Finite (Localization.Away f) (LocalizedModule.Away f P) := by
  have : Module.Finite (Localization.Away f) (Localization.Away f ⊗[R] P) := by
    apply finite_of_residue_rank_eq_nat r
    intro m hm
    obtain ⟨q, hq⟩ : ∃ q : PrimeSpectrum R, q.asIdeal = m.under R := by
      have hmem : m.under R ∈
          Set.range (PrimeSpectrum.asIdeal : PrimeSpectrum R → Ideal R) := by
        rw [PrimeSpectrum.range_asIdeal R]
        exact (inferInstance : (m.under R).IsPrime)
      exact hmem
    have hqopen : q ∈ PrimeSpectrum.basicOpen f := by
      rw [PrimeSpectrum.mem_basicOpen, hq, Ideal.mem_under]
      exact m.notMem_of_isUnit (IsLocalization.Away.algebraMap_isUnit f)
    have hbase :
        Module.rank (Localization.Away f ⧸ m)
            ((Localization.Away f ⧸ m) ⊗[Localization.Away f]
              (Localization.Away f ⊗[R] P)) =
          Module.rank (m.under R).ResidueField ((m.under R).ResidueField ⊗[R] P) := by
      exact Cardinal.lift_inj.mp
        (Module.lift_rank_quotient_baseChange (R := R) (S := Localization.Away f)
          (P := P) m)
    exact hbase.trans
      ((residue_rank_eq_of_ideal_eq (P := P) q.asIdeal (m.under R) hq).symm.trans
        (h q hqopen))
  exact Module.Finite.equiv
    (LocalizedModule.equivTensorProduct (Submonoid.powers f) P).symm

/-- A projective module with finite residue ranks and locally constant Cardinal-valued
residue rank on the prime spectrum is finitely generated. -/
theorem finite_of_isLocallyConstant_residue_rank
    {R : Type uR} [CommRing R]
    {P : Type v} [AddCommMonoid P] [Module R P] [Module.Projective R P]
    (hfinite : ∀ p : PrimeSpectrum R, ∃ r : ℕ,
      Module.rank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] P) = (r : Cardinal))
    (hloc : IsLocallyConstant (fun p : PrimeSpectrum R =>
      Module.rank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] P))) :
    Module.Finite R P := by
  classical
  let s : Set R := {f | Module.Finite (Localization.Away f) (LocalizedModule.Away f P)}
  have hcover : ∀ p : PrimeSpectrum R, ∃ f ∈ s, p ∈ PrimeSpectrum.basicOpen f := by
    intro p
    obtain ⟨r, hr⟩ := hfinite p
    obtain ⟨U, hU, hpU, hconst⟩ := hloc.exists_open p
    obtain ⟨V, hV, hpV, hVU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpU hU
    obtain ⟨f, rfl⟩ := hV
    refine ⟨f, ?_, hpV⟩
    exact finite_away_of_residue_rank_eq_nat f r
      (fun q hq => (hconst q (hVU hq)).trans hr)
  apply Module.Finite.of_localizationSpan s
  · apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
    apply top_unique
    intro p _
    obtain ⟨f, hf, hpf⟩ := hcover p
    exact (show PrimeSpectrum.basicOpen f ≤ ⨆ i ∈ s, PrimeSpectrum.basicOpen i from
      le_iSup_of_le f (le_iSup_of_le hf le_rfl)) hpf
  · intro f
    exact f.property

/-- A projective module is finitely generated exactly when every residue rank is finite
and the Cardinal-valued residue rank is locally constant on the prime spectrum. -/
theorem finite_iff_residue_rank_finite_and_isLocallyConstant
    {R : Type uR} [CommRing R]
    {P : Type v} [AddCommMonoid P] [Module R P] [Module.Projective R P] :
    Module.Finite R P ↔
      (∀ p : PrimeSpectrum R, ∃ r : ℕ,
        Module.rank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] P) = (r : Cardinal)) ∧
      IsLocallyConstant (fun p : PrimeSpectrum R =>
        Module.rank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] P)) := by
  constructor
  · intro hfinite
    let : Module.Finite R P := hfinite
    exact ⟨fun p => Module.Finite.exists_residue_rank_eq_nat p,
      Module.Projective.isLocallyConstant_residue_rank (R := R) (P := P)⟩
  · rintro ⟨hfinite, hloc⟩
    exact finite_of_isLocallyConstant_residue_rank hfinite hloc

end Module.Projective
