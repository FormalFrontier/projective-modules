/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Idempotents
public import GeneralLinearGroups.QuasiregularIdeal
public import ProjectiveModules.RingTheory.NilIdeal

import Mathlib.Tactic.NoncommRing

/-!
# Simultaneous conjugation of orthogonal idempotents

Two given finite orthogonal idempotent families congruent modulo a two-sided ideal in the
Jacobson radical are conjugate by one unit congruent to one. The unit's value is the sum of
`b i * a i`, together with the product of the two complementary idempotents. Neither family
has to sum to one. The ring may be noncommutative or zero, and the index type may be empty.

`OrthogonalIdempotents.conjugationCoeff` specifies the scalar coefficient without any ideal
or orthogonality hypotheses. `OrthogonalIdempotents.conjugatingUnit` constructs a unit from
it using only the first family's orthogonality, congruence, and the Jacobson-radical bound.
Orthogonality of both families is needed for the conjugation theorem. The kernel interfaces
apply to equal-image families without a surjectivity hypothesis.

## Implementation notes

The unit construction uses classical choice of a unit whose value is the specified
coefficient, not a new unit type.

## References

The definitions use Mathlib's orthogonal-idempotent, ideal, radical, and unit interfaces.
The arbitrary-ring unit criterion is supplied by General Linear Groups' quasiregular-ideal
API; the nil-kernel specialization uses this library's nil-ideal criterion.
-/

@[expose] public section

universe uR vS wι

open scoped BigOperators

namespace OrthogonalIdempotents

variable {R : Type uR} [Ring R] {ι : Type wι} [Fintype ι]

/-- The coefficient for finite idempotent conjugation, including the complementary summand. -/
def conjugationCoeff (a b : ι → R) : R :=
  (∑ i, b i * a i) + (1 - ∑ i, b i) * (1 - ∑ i, a i)

/-- The defining equation for the conjugation coefficient. -/
theorem conjugationCoeff_eq (a b : ι → R) :
    conjugationCoeff a b =
      (∑ i, b i * a i) + (1 - ∑ i, b i) * (1 - ∑ i, a i) :=
  rfl

variable {a b : ι → R}

/-- The coefficient intertwines the corresponding members of two orthogonal families. -/
theorem conjugationCoeff_mul (ha : OrthogonalIdempotents a)
    (hb : OrthogonalIdempotents b) (i : ι) :
    conjugationCoeff a b * a i = b i * conjugationCoeff a b := by
  classical
  have hleft : (∑ j, b j * a j) * a i = b i * a i := by
    rw [Finset.sum_mul]
    simp [mul_assoc, ha.mul_eq, mul_ite]
  have hright : b i * (∑ j, b j * a j) = b i * a i := by
    rw [Finset.mul_sum]
    simp [← mul_assoc, hb.mul_eq, ite_mul]
  have ha_sum : (∑ j, a j) * a i = a i := by
    rw [Finset.sum_mul]
    simp [ha.mul_eq]
  have hb_sum : b i * (∑ j, b j) = b i := by
    exact hb.mul_sum_of_mem (Finset.mem_univ i)
  have ha_compl : (1 - ∑ j, a j) * a i = 0 := by
    rw [sub_mul, one_mul, ha_sum, sub_self]
  have hb_compl : b i * (1 - ∑ j, b j) = 0 := by
    rw [mul_sub, mul_one, hb_sum, sub_self]
  calc
    conjugationCoeff a b * a i = b i * a i := by
      rw [conjugationCoeff_eq, add_mul, mul_assoc, ha_compl, mul_zero, add_zero, hleft]
    _ = b i * conjugationCoeff a b := by
      rw [conjugationCoeff_eq, mul_add, ← mul_assoc, hb_compl, zero_mul, add_zero, hright]

/-- Congruence to an orthogonal family makes the coefficient congruent to one. -/
theorem conjugationCoeff_sub_one_mem (ha : OrthogonalIdempotents a)
    (I : Ideal R) [I.IsTwoSided] (hab : ∀ i, b i - a i ∈ I) :
    conjugationCoeff a b - 1 ∈ I := by
  classical
  have ha_sum : (∑ i, a i) * (∑ i, a i) = ∑ i, a i := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    exact ha.mul_sum_of_mem (Finset.mem_univ i)
  have ha_diag : (∑ i, a i * a i) = ∑ i, a i := by
    simp [ha.mul_eq]
  have hdiff : (∑ i, b i) - (∑ i, a i) ∈ I := by
    rw [← Finset.sum_sub_distrib]
    exact I.sum_mem fun i _ ↦ hab i
  have hdiag : (∑ i, b i * a i) - (∑ i, a i) ∈ I := by
    have h : (∑ i, (b i - a i) * a i) ∈ I := by
      exact I.sum_mem fun i _ ↦ I.mul_mem_right (a i) (hab i)
    simpa only [sub_mul, Finset.sum_sub_distrib, ha_diag] using h
  have hcoeff : conjugationCoeff a b - 1 =
      ((∑ i, b i * a i) - ∑ i, a i) -
        ((∑ i, b i) - ∑ i, a i) * (1 - ∑ i, a i) := by
    calc
      conjugationCoeff a b - 1 =
          (((∑ i, b i * a i) - ∑ i, a i) -
            ((∑ i, b i) - ∑ i, a i) * (1 - ∑ i, a i)) +
            ((∑ i, a i) * (∑ i, a i) - ∑ i, a i) := by
        rw [conjugationCoeff_eq]
        noncomm_ring
      _ = _ := by rw [ha_sum, sub_self, add_zero]
  rw [hcoeff]
  exact I.sub_mem hdiag (I.mul_mem_right (1 - ∑ i, a i) hdiff)

/-- The coefficient is a unit when the congruence ideal lies in the Jacobson radical. -/
theorem isUnit_conjugationCoeff (ha : OrthogonalIdempotents a)
    (I : Ideal R) [I.IsTwoSided] (hI : I ≤ Ring.jacobson R)
    (hab : ∀ i, b i - a i ∈ I) : IsUnit (conjugationCoeff a b) := by
  have hmem : conjugationCoeff a b - 1 ∈ Ring.jacobson R :=
    hI (conjugationCoeff_sub_one_mem ha I hab)
  have hunit : IsUnit (1 + (conjugationCoeff a b - 1)) :=
    (TwoSidedIdeal.isQuasiregular_iff_forall_isUnit_one_add
      (Ring.jacobson R).toTwoSided).mp
      TwoSidedIdeal.ringJacobson_isQuasiregular
      (conjugationCoeff a b - 1) (by simpa using hmem)
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hunit

/-- The unit whose value is the finite idempotent-conjugation coefficient. -/
noncomputable def conjugatingUnit (ha : OrthogonalIdempotents a)
    (I : Ideal R) [I.IsTwoSided] (hI : I ≤ Ring.jacobson R)
    (hab : ∀ i, b i - a i ∈ I) : Rˣ :=
  Classical.choose (isUnit_conjugationCoeff ha I hI hab)

/-- The constructed unit has the specified coefficient as its value. -/
@[simp] theorem coe_conjugatingUnit (ha : OrthogonalIdempotents a)
    (I : Ideal R) [I.IsTwoSided] (hI : I ≤ Ring.jacobson R)
    (hab : ∀ i, b i - a i ∈ I) :
    (conjugatingUnit ha I hI hab : R) = conjugationCoeff a b := by
  exact Classical.choose_spec (isUnit_conjugationCoeff ha I hI hab)

/-- The constructed unit is congruent to one modulo the given ideal. -/
theorem conjugatingUnit_sub_one_mem (ha : OrthogonalIdempotents a)
    (I : Ideal R) [I.IsTwoSided] (hI : I ≤ Ring.jacobson R)
    (hab : ∀ i, b i - a i ∈ I) :
    (conjugatingUnit ha I hI hab : R) - 1 ∈ I := by
  simpa only [coe_conjugatingUnit] using conjugationCoeff_sub_one_mem ha I hab

/-- One unit congruent to one simultaneously conjugates the two given orthogonal families. -/
theorem conjugatingUnit_mul_inv (ha : OrthogonalIdempotents a)
    (hb : OrthogonalIdempotents b)
    (I : Ideal R) [I.IsTwoSided] (hI : I ≤ Ring.jacobson R)
    (hab : ∀ i, b i - a i ∈ I) (i : ι) :
    (conjugatingUnit ha I hI hab : R) * a i *
      (((conjugatingUnit ha I hI hab)⁻¹ : Rˣ) : R) = b i := by
  have hintertwine :
      (conjugatingUnit ha I hI hab : R) * a i =
        b i * (conjugatingUnit ha I hI hab : R) := by
    simpa only [coe_conjugatingUnit] using conjugationCoeff_mul ha hb i
  calc
    (conjugatingUnit ha I hI hab : R) * a i *
        (((conjugatingUnit ha I hI hab)⁻¹ : Rˣ) : R) =
      (b i * (conjugatingUnit ha I hI hab : R)) *
        (((conjugatingUnit ha I hI hab)⁻¹ : Rˣ) : R) := by
          rw [hintertwine]
    _ = b i := by
      -- Keep the unit value intact so its inverse cancels.
      simp [-coe_conjugatingUnit, mul_assoc]

/-- If the first family sums to one, the complementary summand vanishes. -/
theorem conjugationCoeff_eq_sum (a b : ι → R) (hsum : ∑ i, a i = 1) :
    conjugationCoeff a b = ∑ i, b i * a i := by
  simp [conjugationCoeff_eq, hsum]

/-- For a singleton index, the coefficient is the two-idempotent expression. -/
theorem conjugationCoeff_unique [Unique ι] (a b : ι → R) :
    conjugationCoeff a b =
      b default * a default + (1 - b default) * (1 - a default) := by
  classical
  simp [conjugationCoeff_eq]

/-- The empty-family coefficient is one. -/
@[simp] theorem conjugationCoeff_of_isEmpty [IsEmpty ι] (a b : ι → R) :
    conjugationCoeff a b = 1 := by
  simp [conjugationCoeff_eq]

/-- The construction gives the identity unit for an empty family. -/
@[simp] theorem conjugatingUnit_of_isEmpty [IsEmpty ι]
    (ha : OrthogonalIdempotents a)
    (I : Ideal R) [I.IsTwoSided] (hI : I ≤ Ring.jacobson R)
    (hab : ∀ i, b i - a i ∈ I) :
    conjugatingUnit ha I hI hab = 1 := by
  ext
  simp

section RingHom

variable {S : Type vS} [Ring S]

/-- Equal-image orthogonal families are conjugate by a unit mapping to one, with the
specified coefficient as its value. No surjectivity of the homomorphism is required. -/
theorem exists_conjugatingUnit_of_ker_le_jacobson
    (f : R →+* S) (hf : RingHom.ker f ≤ Ring.jacobson R)
    (ha : OrthogonalIdempotents a) (hb : OrthogonalIdempotents b)
    (hab : ∀ i, f (a i) = f (b i)) :
    ∃ u : Rˣ, (u : R) = conjugationCoeff a b ∧
      f (u : R) = 1 ∧ (u : R) - 1 ∈ RingHom.ker f ∧
      ∀ i, (u : R) * a i * ((u⁻¹ : Rˣ) : R) = b i := by
  have hker : ∀ i, b i - a i ∈ RingHom.ker f := by
    intro i
    exact (RingHom.sub_mem_ker_iff f).2 (hab i).symm
  refine ⟨conjugatingUnit ha (RingHom.ker f) hf hker,
    coe_conjugatingUnit ha (RingHom.ker f) hf hker, ?_,
    conjugatingUnit_sub_one_mem ha (RingHom.ker f) hf hker, ?_⟩
  · have hmem := conjugatingUnit_sub_one_mem ha (RingHom.ker f) hf hker
    simpa using (RingHom.sub_mem_ker_iff f).1 hmem
  · intro i
    exact conjugatingUnit_mul_inv ha hb (RingHom.ker f) hf hker i

/-- The equal-image conjugacy criterion when every element of the whole kernel is
nilpotent; no common nilpotence exponent is assumed. -/
theorem exists_conjugatingUnit_of_isNilpotent_ker
    (f : R →+* S) (hnil : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    (ha : OrthogonalIdempotents a) (hb : OrthogonalIdempotents b)
    (hab : ∀ i, f (a i) = f (b i)) :
    ∃ u : Rˣ, (u : R) = conjugationCoeff a b ∧
      f (u : R) = 1 ∧ (u : R) - 1 ∈ RingHom.ker f ∧
      ∀ i, (u : R) * a i * ((u⁻¹ : Rˣ) : R) = b i := by
  apply exists_conjugatingUnit_of_ker_le_jacobson f ?_ ha hb hab
  simpa only [Ideal.jacobson_bot] using
    Ideal.le_jacobson_bot_of_isNilpotent_mem (RingHom.ker f) hnil

end RingHom

end OrthogonalIdempotents
