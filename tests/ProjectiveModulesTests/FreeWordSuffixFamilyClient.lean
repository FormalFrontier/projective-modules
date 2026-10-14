/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Free.FreeWordAlgebra
import ProjectiveModules.Free.InvariantBasisNumber
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Free-word linear combinations and suffix-family clients

Letter monomials use the left regular action of the word semiring, so a coordinate
polynomial multiplies its letter monomial on the right. The finitely supported domain
allows an infinite alphabet and an infinite index type without an infinite sum.

The examples are private importing clients, not a second public interface. The family
API applications are separated from the coefficient calculations and boundary examples.
The latter use the canonical linear-combination API, matrix units, or the two-letter map.
Sending every monoid element to `1` gives a coefficient-return homomorphism to `K`,
which transports the rank condition by the existing semiring-homomorphism pullback API.

## References

* Mathlib, `Mathlib.LinearAlgebra.Finsupp.LinearCombination` and
  `Mathlib.LinearAlgebra.LinearIndependent.Defs`: linear combinations and reindexing.
* Mathlib, `Mathlib.Data.Matrix.Basis`: matrix units and their multiplication.
* Mathlib, `Mathlib.Algebra.MonoidAlgebra.Lift`: the noncommutative lifting API.
* `ProjectiveModules.Free.FreeWordAlgebra`: the two-letter map and its application API.
* `ProjectiveModules.Free.InvariantBasisNumber`: rank-condition pullback.
-/

noncomputable section

universe u v w

-- Family API applications; these do not supply the independent calculations below.
section FamilyAPI

variable {K : Type u} [Semiring K] {ι : Type v} {κ : Type w}

example (c : κ → ι) (hc : Function.Injective c) :
    LinearIndependent (MonoidAlgebra K (FreeMonoid ι))
      (fun k : κ ↦ MonoidAlgebra.single (FreeMonoid.of (c k)) (1 : K)) :=
  (MonoidAlgebra.linearIndependent_freeMonoid_of (K := K) (ι := ι)).comp c hc

example (c : κ → ι) (hc : Function.Injective c) :
    Function.Injective
      (Finsupp.linearCombination (MonoidAlgebra K (FreeMonoid ι))
        (fun k : κ ↦ MonoidAlgebra.single (FreeMonoid.of (c k)) (1 : K))) := by
  have h := (MonoidAlgebra.linearIndependent_freeMonoid_of (K := K) (ι := ι)).comp c hc
  exact h.finsuppLinearCombination_injective

end FamilyAPI

-- All remaining declarations use Mathlib or existing semiring-map/two-letter APIs only.
section CoefficientReturn

variable {K : Type u} [Semiring K] {M : Type v} [Monoid M]

example (m : M) (k : K) :
    MonoidAlgebra.liftNCRingHom (RingHom.id K) (1 : M →* K)
      (fun k _ ↦ Commute.one_right k) (MonoidAlgebra.single m k) = k := by
  simp

example [RankCondition K] : RankCondition (MonoidAlgebra K M) :=
  (MonoidAlgebra.liftNCRingHom (RingHom.id K) (1 : M →* K)
    (fun k _ ↦ Commute.one_right k)).rankCondition

end CoefficientReturn

section CoordinateAPI

variable {K : Type u} [Semiring K] {ι : Type v} {κ : Type w}

private theorem linearCombination_single_letter (c : κ → ι) (k : κ)
    (p : MonoidAlgebra K (FreeMonoid ι)) :
    Finsupp.linearCombination (MonoidAlgebra K (FreeMonoid ι))
        (fun j : κ ↦ MonoidAlgebra.single (FreeMonoid.of (c j)) (1 : K))
        (Finsupp.single k p) =
      p * MonoidAlgebra.single (FreeMonoid.of (c k)) (1 : K) := by
  simp only [Finsupp.linearCombination_single, smul_eq_mul]

private theorem finite_linearCombination_injective (a b : ι) (hab : a ≠ b) :
    Function.Injective
      (Finsupp.linearCombination (MonoidAlgebra K (FreeMonoid ι))
        (fun j : Fin 2 ↦ MonoidAlgebra.single (FreeMonoid.of (![a, b] j)) (1 : K))) := by
  let e := Finsupp.linearEquivFunOnFinite (MonoidAlgebra K (FreeMonoid ι))
    (MonoidAlgebra K (FreeMonoid ι)) (Fin 2)
  intro z t hzt
  have hpair : MonoidAlgebra.freeWordPairMap a b (e z) =
      MonoidAlgebra.freeWordPairMap a b (e t) := by
    simpa [MonoidAlgebra.freeWordPairMap_eq_linearCombination, e] using hzt
  exact e.injective (MonoidAlgebra.freeWordPairMap_injective a b hab hpair)

private theorem finite_family_independent (a b : ι) (hab : a ≠ b) :
    LinearIndependent (MonoidAlgebra K (FreeMonoid ι))
      (fun j : Fin 2 ↦ MonoidAlgebra.single (FreeMonoid.of (![a, b] j)) (1 : K)) :=
  (linearIndependent_iff_injective_finsuppLinearCombination).mpr
    (finite_linearCombination_injective a b hab)

end CoordinateAPI

private abbrev RationalWords := MonoidAlgebra ℚ (FreeMonoid Bool)

private abbrev rationalLetter (a : Bool) : RationalWords :=
  MonoidAlgebra.single (FreeMonoid.of a) 1

local notation "rationalCombination" => Finsupp.linearCombination RationalWords rationalLetter

private theorem rational_single_output (a : Bool) :
    rationalCombination (Finsupp.single a 1) = rationalLetter a := by
  simpa only [one_mul] using
    (linearCombination_single_letter (K := ℚ) (fun b : Bool ↦ b) a (1 : RationalWords))

private theorem rational_single_output_nonzero (a : Bool) :
    rationalCombination (Finsupp.single a 1) ≠ 0 := by
  rw [rational_single_output]
  exact MonoidAlgebra.single_ne_zero.mpr one_ne_zero

example : rationalLetter false * rationalLetter true ≠
    rationalLetter true * rationalLetter false := by
  intro h
  have hwords : FreeMonoid.of false * FreeMonoid.of true =
      FreeMonoid.of true * FreeMonoid.of false :=
    MonoidAlgebra.single_left_injective (R := ℚ) (M := FreeMonoid Bool) one_ne_zero
      (by simpa only [rationalLetter, MonoidAlgebra.single_mul_single, one_mul] using h)
  have hlist := congrArg FreeMonoid.toList hwords
  simp at hlist

private theorem finite_zero_coordinate :
    (Finsupp.linearEquivFunOnFinite RationalWords RationalWords (Fin 2)).symm
        (![1, 0] : Fin 2 → RationalWords) = Finsupp.single 0 1 := by
  apply Finsupp.ext
  intro i
  fin_cases i <;> simp

private theorem finite_one_coordinate :
    (Finsupp.linearEquivFunOnFinite RationalWords RationalWords (Fin 2)).symm
        (![0, 1] : Fin 2 → RationalWords) = Finsupp.single 1 1 := by
  apply Finsupp.ext
  intro i
  fin_cases i <;> simp

-- The old finite vectors are transported through the same equivalence as the map.
example : MonoidAlgebra.freeWordPairMap false true (![1, 0] : Fin 2 → RationalWords) =
    (Finsupp.linearCombination RationalWords
      (fun j : Fin 2 ↦ rationalLetter (![false, true] j))) (Finsupp.single 0 1) := by
  rw [MonoidAlgebra.freeWordPairMap_eq_linearCombination]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, finite_zero_coordinate]

example : MonoidAlgebra.freeWordPairMap false true (![0, 1] : Fin 2 → RationalWords) =
    (Finsupp.linearCombination RationalWords
      (fun j : Fin 2 ↦ rationalLetter (![false, true] j))) (Finsupp.single 1 1) := by
  rw [MonoidAlgebra.freeWordPairMap_eq_linearCombination]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, finite_one_coordinate]

example : LinearIndependent RationalWords
    (fun j : Fin 2 ↦ rationalLetter (![false, true] j)) :=
  finite_family_independent false true (by intro h; cases h)

-- The coefficient semiring itself is noncommutative, independently of the word alphabet.
private abbrev MatrixCoefficients := Matrix (Fin 2) (Fin 2) ℚ

private abbrev P : MatrixCoefficients := Matrix.single 0 1 1

private abbrev Q : MatrixCoefficients := Matrix.single 1 0 1

private theorem QP_ne_PQ : Q * P ≠ P * Q := by
  intro h
  have hentry := congrArg (fun m : MatrixCoefficients ↦ m 0 0) h
  simp [P, Q] at hentry

private theorem P_nonzero : P ≠ 0 := by
  intro h
  have hentry := congrArg (fun m : MatrixCoefficients ↦ m 0 1) h
  simp [P] at hentry

private abbrev MatrixWords := MonoidAlgebra MatrixCoefficients (FreeMonoid Bool)

private abbrev matrixLetter (a : Bool) : MatrixWords :=
  MonoidAlgebra.single (FreeMonoid.of a) 1

private abbrev pWord : MatrixWords := MonoidAlgebra.single 1 P

private abbrev qWord : MatrixWords := MonoidAlgebra.single 1 Q

private abbrev matrixCoordinate : Bool →₀ MatrixWords := Finsupp.single false pWord

local notation "matrixCombination" => Finsupp.linearCombination MatrixWords matrixLetter

private theorem matrix_single_output :
    matrixCombination matrixCoordinate = MonoidAlgebra.single (FreeMonoid.of false) P := by
  simp [matrixCoordinate, pWord, matrixLetter, smul_eq_mul]

example : matrixCombination matrixCoordinate ≠ 0 := by
  rw [matrix_single_output]
  exact MonoidAlgebra.single_ne_zero.mpr P_nonzero

private theorem matrix_left_scalar_output :
    matrixCombination (qWord • matrixCoordinate) =
      MonoidAlgebra.single (FreeMonoid.of false) (Q * P) := by
  rw [map_smul, matrix_single_output]
  simp [qWord, smul_eq_mul]

private theorem matrix_left_scalar_coefficient :
    (matrixCombination (qWord • matrixCoordinate)).coeff (FreeMonoid.of false) = Q * P := by
  rw [matrix_left_scalar_output]
  simp

example : (matrixCombination (qWord • matrixCoordinate)).coeff (FreeMonoid.of false) ≠
    P * Q := by
  rw [matrix_left_scalar_coefficient]
  exact QP_ne_PQ

example : matrixCombination (qWord • matrixCoordinate) ≠ 0 := by
  intro h
  have hentry := congrArg
    (fun z : MatrixWords ↦ z.coeff (FreeMonoid.of false) 1 1) h
  simp [P, Q] at hentry

-- Both the alphabet and the Finsupp index below are genuinely infinite.
private abbrev NaturalWords := MonoidAlgebra ℚ (FreeMonoid ℕ)

private abbrev naturalLetter (n : ℕ) : NaturalWords :=
  MonoidAlgebra.single (FreeMonoid.of n) 1

private abbrev naturalCoordinates : ℕ →₀ NaturalWords :=
  Finsupp.single 7 (MonoidAlgebra.single 1 (2 : ℚ)) +
    Finsupp.single 42 (MonoidAlgebra.single 1 (3 : ℚ))

local notation "naturalCombination" => Finsupp.linearCombination NaturalWords naturalLetter

example : naturalCombination (Finsupp.single 7 1) = naturalLetter 7 := by
  simp [smul_eq_mul]

private theorem natural_combination_output :
    naturalCombination naturalCoordinates =
      MonoidAlgebra.single (FreeMonoid.of 7) (2 : ℚ) +
        MonoidAlgebra.single (FreeMonoid.of 42) (3 : ℚ) := by
  simp [naturalCoordinates, naturalLetter, smul_eq_mul]

private theorem natural_coefficient_seven :
    (naturalCombination naturalCoordinates).coeff (FreeMonoid.of 7) = 2 := by
  simp [natural_combination_output, FreeMonoid.of_injective.eq_iff]

example : (naturalCombination naturalCoordinates).coeff (FreeMonoid.of 42) = 3 := by
  simp [natural_combination_output, FreeMonoid.of_injective.eq_iff]

example : naturalCombination naturalCoordinates ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun z : NaturalWords ↦ z.coeff (FreeMonoid.of 7)) h
  rw [natural_coefficient_seven] at hcoeff
  norm_num at hcoeff

-- Zero coefficients give a singleton scalar semiring and singleton coordinate domain.
example : LinearIndependent (MonoidAlgebra PUnit (FreeMonoid ℕ))
    (fun n : ℕ ↦ MonoidAlgebra.single (FreeMonoid.of n) (1 : PUnit)) :=
  linearIndependent_of_subsingleton

example : Function.Injective
    (Finsupp.linearCombination (MonoidAlgebra PUnit (FreeMonoid Bool))
      (fun _ : Fin 2 ↦ MonoidAlgebra.single (FreeMonoid.of false) (1 : PUnit))) :=
  (linearIndependent_of_subsingleton).finsuppLinearCombination_injective

-- Empty coordinates give zero output without forcing a zero codomain.
example : LinearIndependent RationalWords (fun _ : PEmpty ↦ rationalLetter false) :=
  linearIndependent_empty_type

example (z : PEmpty →₀ RationalWords) :
    Finsupp.linearCombination RationalWords (fun _ : PEmpty ↦ rationalLetter false) z = 0 := by
  have hz : z = 0 := Subsingleton.elim _ _
  rw [hz, map_zero]

example : LinearIndependent (MonoidAlgebra ℚ (FreeMonoid PEmpty))
    (fun a : PEmpty ↦ MonoidAlgebra.single (FreeMonoid.of a) (1 : ℚ)) :=
  linearIndependent_empty_type

example : (1 : MonoidAlgebra ℚ (FreeMonoid PEmpty)) ≠ 0 := one_ne_zero

-- Equal letters collide on distinct Fin 2 coordinates over nontrivial coefficients.
private theorem repeated_coordinates_ne :
    (Finsupp.single 0 1 : Fin 2 →₀ RationalWords) ≠ Finsupp.single 1 1 := by
  intro h
  have hzero := congrArg (fun z : Fin 2 →₀ RationalWords ↦ z 0) h
  simp at hzero

private theorem repeated_family_not_injective :
    ¬ Function.Injective
      (Finsupp.linearCombination RationalWords (fun _ : Fin 2 ↦ rationalLetter false)) := by
  intro h
  apply repeated_coordinates_ne
  apply h
  simp [smul_eq_mul]

example : ¬ LinearIndependent RationalWords (fun _ : Fin 2 ↦ rationalLetter false) := by
  intro h
  exact repeated_family_not_injective h.finsuppLinearCombination_injective

-- Separately lifted coefficient, alphabet and index types retain independent universes.
private def liftedLetterEmbedding.{uι, uκ} : ULift.{uκ} ℕ → ULift.{uι} ℕ :=
  fun k ↦ ULift.up k.down

private theorem liftedLetterEmbedding_injective :
    Function.Injective (liftedLetterEmbedding.{v, w}) := by
  intro a b h
  have hab : a.down = b.down := congrArg (fun x : ULift.{v} ℕ ↦ x.down) h
  exact (Equiv.ulift : ULift.{w} ℕ ≃ ℕ).injective hab

private theorem lifted_coefficient_nonzero : (1 : ULift.{u} ℚ) ≠ 0 := one_ne_zero

private theorem lifted_coordinate_nonzero :
    (Finsupp.single (ULift.up 7 : ULift.{w} ℕ)
      (1 : MonoidAlgebra (ULift.{u} ℚ) (FreeMonoid (ULift.{v} ℕ)))) ≠ 0 :=
  Finsupp.single_ne_zero.mpr one_ne_zero

private theorem lifted_output_coefficient :
    (Finsupp.linearCombination (MonoidAlgebra (ULift.{u} ℚ) (FreeMonoid (ULift.{v} ℕ)))
      (fun k : ULift.{w} ℕ ↦ MonoidAlgebra.single
        (FreeMonoid.of (liftedLetterEmbedding.{v, w} k)) (1 : ULift.{u} ℚ))
      (Finsupp.single (ULift.up 7 : ULift.{w} ℕ) 1)).coeff
      (FreeMonoid.of (ULift.up 7 : ULift.{v} ℕ)) = 1 := by
  simp [liftedLetterEmbedding, smul_eq_mul]

private theorem lifted_output_nonzero :
    Finsupp.linearCombination (MonoidAlgebra (ULift.{u} ℚ) (FreeMonoid (ULift.{v} ℕ)))
        (fun k : ULift.{w} ℕ ↦ MonoidAlgebra.single
          (FreeMonoid.of (liftedLetterEmbedding.{v, w} k)) (1 : ULift.{u} ℚ))
        (Finsupp.single (ULift.up 7 : ULift.{w} ℕ) 1) ≠ 0 := by
  intro h
  have hcoeff := congrArg
    (fun z : MonoidAlgebra (ULift.{u} ℚ) (FreeMonoid (ULift.{v} ℕ)) ↦
      z.coeff (FreeMonoid.of (ULift.up 7 : ULift.{v} ℕ))) h
  rw [lifted_output_coefficient, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hcoeff
  exact lifted_coefficient_nonzero hcoeff

example : Function.Injective (liftedLetterEmbedding.{1, 2}) :=
  liftedLetterEmbedding_injective

example : (1 : ULift.{0} ℚ) ≠ 0 := lifted_coefficient_nonzero

example : (Finsupp.single (ULift.up 7 : ULift.{2} ℕ)
    (1 : MonoidAlgebra (ULift.{0} ℚ) (FreeMonoid (ULift.{1} ℕ)))) ≠ 0 :=
  lifted_coordinate_nonzero

example : Finsupp.linearCombination (MonoidAlgebra (ULift.{0} ℚ) (FreeMonoid (ULift.{1} ℕ)))
    (fun k : ULift.{2} ℕ ↦ MonoidAlgebra.single
      (FreeMonoid.of (liftedLetterEmbedding.{1, 2} k)) (1 : ULift.{0} ℚ))
    (Finsupp.single (ULift.up 7 : ULift.{2} ℕ) 1) ≠ 0 := lifted_output_nonzero

-- Coefficient height largest, and alphabet height largest, respectively.
example : Finsupp.linearCombination (MonoidAlgebra (ULift.{2} ℚ) (FreeMonoid (ULift.{0} ℕ)))
    (fun k : ULift.{1} ℕ ↦ MonoidAlgebra.single
      (FreeMonoid.of (liftedLetterEmbedding.{0, 1} k)) (1 : ULift.{2} ℚ))
    (Finsupp.single (ULift.up 7 : ULift.{1} ℕ) 1) ≠ 0 := lifted_output_nonzero

example : Finsupp.linearCombination (MonoidAlgebra (ULift.{1} ℚ) (FreeMonoid (ULift.{2} ℕ)))
    (fun k : ULift.{0} ℕ ↦ MonoidAlgebra.single
      (FreeMonoid.of (liftedLetterEmbedding.{2, 0} k)) (1 : ULift.{1} ℚ))
    (Finsupp.single (ULift.up 7 : ULift.{0} ℕ) 1) ≠ 0 := lifted_output_nonzero
