/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Subsingleton
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Residue-field ranks of quotient modules

The residue-field fibre of `R ⧸ I` has Cardinal rank one at primes containing `I`
and rank zero at all other primes. These calculations hold for every commutative
ring, with no finiteness or properness assumption on the ideal.

The proofs use the algebra equivalence between the fibre and the quotient of the
residue field by the extended ideal.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Module

variable {R : Type u} [CommRing R] (I : Ideal R) (p : PrimeSpectrum R)

/-- At a prime containing `I`, the residue-field fibre of `R ⧸ I` has Cardinal rank one. -/
theorem rank_residueField_tensor_quotient_eq_one (h : I ≤ p.asIdeal) :
    Module.rank p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] (R ⧸ I)) = 1 := by
  have hmap : I.map (algebraMap R p.asIdeal.ResidueField) = ⊥ := by
    apply (Ideal.map_eq_bot_iff_le_ker (algebraMap R p.asIdeal.ResidueField)).2
    simpa only [Ideal.ker_algebraMap_residueField] using h
  calc
    Module.rank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[R] (R ⧸ I)) =
        Module.rank p.asIdeal.ResidueField
          (p.asIdeal.ResidueField ⧸ I.map (algebraMap R p.asIdeal.ResidueField)) :=
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
        p.asIdeal.ResidueField I).toLinearEquiv.rank_eq.symm
    _ = Module.rank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⧸ (⊥ : Ideal p.asIdeal.ResidueField)) := by rw [hmap]
    _ = Module.rank p.asIdeal.ResidueField p.asIdeal.ResidueField :=
      (AlgEquiv.quotientBot p.asIdeal.ResidueField
        p.asIdeal.ResidueField).toLinearEquiv.rank_eq
    _ = 1 := Module.rank_self p.asIdeal.ResidueField

/-- At a prime not containing `I`, the residue-field fibre of `R ⧸ I` has Cardinal rank zero. -/
theorem rank_residueField_tensor_quotient_eq_zero (h : ¬ I ≤ p.asIdeal) :
    Module.rank p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] (R ⧸ I)) = 0 := by
  have hmap : I.map (algebraMap R p.asIdeal.ResidueField) = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top
        (I.map (algebraMap R p.asIdeal.ResidueField)) with hbot | htop
    · exfalso
      apply h
      have hker :=
        (Ideal.map_eq_bot_iff_le_ker (algebraMap R p.asIdeal.ResidueField)).1 hbot
      simpa only [Ideal.ker_algebraMap_residueField] using hker
    · exact htop
  have : Subsingleton
      (p.asIdeal.ResidueField ⧸ I.map (algebraMap R p.asIdeal.ResidueField)) :=
    Ideal.Quotient.subsingleton_iff.2 hmap
  calc
    Module.rank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[R] (R ⧸ I)) =
        Module.rank p.asIdeal.ResidueField
          (p.asIdeal.ResidueField ⧸ I.map (algebraMap R p.asIdeal.ResidueField)) :=
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
        p.asIdeal.ResidueField I).toLinearEquiv.rank_eq.symm
    _ = 0 := rank_subsingleton' p.asIdeal.ResidueField _

end Module
