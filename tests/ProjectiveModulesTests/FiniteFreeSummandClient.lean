/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Free.FiniteFreeSummand
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Ring.PUnit
import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis

/-!
# Direct-summand cancellation clients

Concrete product equivalences over the integers exercise endomorphism,
finite-free, finite-projective and basis-rank interfaces. A universe-lifted
zero complement tests that cancellation imposes no universe or finiteness
restriction on the complementary module. At the zero ring, the coordinate
modules of ranks zero and one are equivalent; stable finiteness still holds,
while rank condition and invariant basis number fail.
-/

@[expose] public section

set_option warningAsError true

namespace ProjectiveModulesTests.FiniteFreeSummandClient

private def integerZeroComplementEquiv :
    (Fin 1 → ℤ) ≃ₗ[ℤ] ((Fin 1 → ℤ) × (Fin 0 → ℤ)) :=
  (LinearEquiv.prodUnique (R := ℤ) (M := Fin 1 → ℤ) (M₂ := Fin 0 → ℤ)).symm

private theorem integerSource_nontrivial : (0 : Fin 1 → ℤ) ≠ (fun _ ↦ 1) := by
  intro h
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (congrFun h 0)

private theorem integerEnd_cancel : Subsingleton (Fin 0 → ℤ) :=
  Module.End.subsingleton_of_linearEquiv_prod ℤ integerZeroComplementEquiv

private theorem integerFiniteFree_cancel : Subsingleton (Fin 0 → ℤ) :=
  IsStablyFiniteRing.subsingleton_of_linearEquiv_prod ℤ integerZeroComplementEquiv

private theorem integerFiniteProjective_cancel : Subsingleton (Fin 0 → ℤ) :=
  IsStablyFiniteRing.subsingleton_of_finite_projective_linearEquiv_prod
    ℤ integerZeroComplementEquiv

private theorem integerRank_bound : (1 : ℕ) ≤ 1 :=
  RankCondition.card_le_of_linearEquiv_prod ℤ
    (Pi.basisFun ℤ (Fin 1)) (Pi.basisFun ℤ (Fin 1)) integerZeroComplementEquiv

private theorem integerNonzeroComplement_bound : (1 : ℕ) ≤ 2 :=
  RankCondition.card_le_of_linearEquiv_prod ℤ
    (Pi.basisFun ℤ (Fin 2)) (Module.Basis.singleton (Fin 1) ℤ)
      (LinearEquiv.finTwoArrow (R := ℤ) (M := ℤ))

private theorem integerComplement_nontrivial : ¬ Subsingleton ℤ := by
  intro h
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (@Subsingleton.elim ℤ h 0 1)

private def raisedZeroComplementEquiv :
    (Fin 1 → ℤ) ≃ₗ[ℤ] ((Fin 1 → ℤ) × ULift.{1} (Fin 0 → ℤ)) :=
  (LinearEquiv.prodUnique (R := ℤ) (M := Fin 1 → ℤ)
    (M₂ := ULift.{1} (Fin 0 → ℤ))).symm

private theorem raisedZeroComplement_cancel : Subsingleton (ULift.{1} (Fin 0 → ℤ)) :=
  IsStablyFiniteRing.subsingleton_of_linearEquiv_prod ℤ raisedZeroComplementEquiv

private def zeroRankEquiv :
    (Fin 0 → ℤ) ≃ₗ[ℤ] ((Fin 0 → ℤ) × (Fin 0 → ℤ)) :=
  (LinearEquiv.prodUnique (R := ℤ) (M := Fin 0 → ℤ) (M₂ := Fin 0 → ℤ)).symm

private theorem zeroRank_cancel : Subsingleton (Fin 0 → ℤ) :=
  IsStablyFiniteRing.subsingleton_of_linearEquiv_prod ℤ zeroRankEquiv

private theorem integerRank_characterization : (1 : ℕ) ≤ 1 :=
  (rankCondition_iff_le_of_fin_linearEquiv_fin_prod ℤ).mp inferInstance
    1 1 (Fin 0 → ℤ) integerZeroComplementEquiv

private theorem integerStable_characterization : Subsingleton (Fin 0 → ℤ) :=
  (isStablyFiniteRing_iff_subsingleton_of_fin_linearEquiv_fin_prod ℤ).mp
    inferInstance 1 (Fin 0 → ℤ) integerZeroComplementEquiv

private def zeroRingCoordinateEquiv :
    (Fin 0 → PUnit.{1}) ≃ₗ[PUnit.{1}]
      ((Fin 1 → PUnit.{1}) × (Fin 0 → PUnit.{1})) :=
  .ofSubsingleton _ _

private theorem zeroRing_stablyFinite : IsStablyFiniteRing PUnit.{1} := inferInstance

private theorem zeroRing_stable_characterization : Subsingleton (Fin 1 → PUnit.{1}) :=
  (isStablyFiniteRing_iff_subsingleton_of_fin_linearEquiv_fin_prod PUnit.{1}).mp
    inferInstance 0 (Fin 1 → PUnit.{1})
      (show (Fin 0 → PUnit.{1}) ≃ₗ[PUnit.{1}]
        ((Fin 0 → PUnit.{1}) × (Fin 1 → PUnit.{1})) from .ofSubsingleton _ _)

/-- The zero ring fails the rank condition despite satisfying stable finiteness. -/
theorem zeroRing_not_rankCondition : ¬ RankCondition PUnit.{1} := by
  intro condition
  let projection : (Fin 0 → PUnit.{1}) →ₗ[PUnit.{1}] (Fin 1 → PUnit.{1}) :=
    (LinearMap.fst PUnit.{1} (Fin 1 → PUnit.{1}) (Fin 0 → PUnit.{1})).comp
      zeroRingCoordinateEquiv.toLinearMap
  have hsurj : Function.Surjective projection :=
    fun value ↦ ⟨0, Subsingleton.elim _ value⟩
  have impossible : 1 ≤ 0 := condition.le_of_fin_surjective projection hsurj
  exact (by decide : ¬ (1 : ℕ) ≤ 0) impossible

private theorem zeroRing_not_invariantBasisNumber : ¬ InvariantBasisNumber PUnit.{1} := by
  intro condition
  have impossible : (0 : ℕ) = 1 :=
    condition.eq_of_fin_equiv
      (show (Fin 0 → PUnit.{1}) ≃ₗ[PUnit.{1}] (Fin 1 → PUnit.{1}) from
        .ofSubsingleton _ _)
  exact (by decide : (0 : ℕ) ≠ 1) impossible

end ProjectiveModulesTests.FiniteFreeSummandClient
