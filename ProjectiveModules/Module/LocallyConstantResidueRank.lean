/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Residue-field ranks of finite projective modules

A finite module has finite cardinal rank after base change to every residue field.
For a finite projective module these cardinal ranks form a locally constant function
on the prime spectrum.
-/

@[expose] public section

universe uR v

open TensorProduct

namespace Module

variable {R : Type uR} [CommRing R]
variable {P : Type v} [AddCommMonoid P] [Module R P]

/-- Every residue-field fibre of a finite module has finite cardinal rank. -/
theorem Finite.exists_residue_rank_eq_nat [Module.Finite R P] (p : PrimeSpectrum R) :
    ∃ r : ℕ, Module.rank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] P) =
      (r : Cardinal) := by
  let : Module.Finite p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] P) :=
    Module.Finite.base_change R p.asIdeal.ResidueField P
  exact ⟨Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] P),
    (Module.finrank_eq_rank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] P)).symm⟩

/-- The cardinal ranks of the residue-field fibres of a finite projective module are
locally constant on the prime spectrum. -/
theorem Projective.isLocallyConstant_residue_rank [Module.Projective R P]
    [Module.Finite R P] :
    IsLocallyConstant (fun p : PrimeSpectrum R =>
      Module.rank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] P)) := by
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
  let : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
  have h := IsLocallyConstant.comp
    (Module.isLocallyConstant_rankAtStalk (R := R) (M := P))
    (fun n : ℕ => (n : Cardinal.{max uR v}))
  convert h using 1
  funext p
  let : Module.Finite p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] P) :=
    Module.Finite.base_change R p.asIdeal.ResidueField P
  have hp : Module.rankAtStalk P p =
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] P) :=
    Module.rankAtStalk_eq p
  exact (Module.finrank_eq_rank p.asIdeal.ResidueField
    (p.asIdeal.ResidueField ⊗[R] P)).symm.trans
      (congrArg (fun n : ℕ => (n : Cardinal.{max uR v})) hp.symm)

end Module
