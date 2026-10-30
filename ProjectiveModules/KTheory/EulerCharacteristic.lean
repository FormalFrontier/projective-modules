/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Algebra.Ring.Parity

/-!
# Euler characteristics of graded finite-projective right modules

For an integer-graded family of finite-projective right modules, its Euler
characteristic on a finite set of degrees is the sum of the even term classes
minus the sum of the odd term classes in `KTheory.K0 R`.

The family retains its original carriers and module structures. The scalar
universe and the term-carrier universe are independent. No differential is
part of this definition.
-/

@[expose] public section

universe u v w

open scoped BigOperators

namespace KTheory.K0

/-- The alternating class sum of an integer-graded family of finite-projective
right `R`-modules over the finite set `S`.

This is a finite truncation for an arbitrary `S`. When the original modules are
zero outside `S`, it is the Euler characteristic of the supported family. -/
noncomputable def eulerCharacteristic (R : Type u) [Ring R]
    (P : ℤ → Type v) [∀ i, AddCommGroup (P i)] [∀ i, Module Rᵐᵒᵖ (P i)]
    [∀ i, Module.Finite Rᵐᵒᵖ (P i)] [∀ i, Module.Projective Rᵐᵒᵖ (P i)]
    (S : Finset ℤ) : K0 R :=
  letI : DecidablePred (Even : ℤ → Prop) := fun i => Classical.propDecidable (Even i)
  letI : DecidablePred (Odd : ℤ → Prop) := fun i => Classical.propDecidable (Odd i)
  (S.filter Even).sum (fun i => KTheory.K0.of R (P i)) -
    (S.filter Odd).sum (fun i => KTheory.K0.of R (P i))

section Graded

variable (R : Type u) [Ring R]
    (P : ℤ → Type v) [∀ i, AddCommGroup (P i)] [∀ i, Module Rᵐᵒᵖ (P i)]
    [∀ i, Module.Finite Rᵐᵒᵖ (P i)] [∀ i, Module.Projective Rᵐᵒᵖ (P i)]

/-- The Euler characteristic is the even class sum minus the odd class sum. -/
theorem eulerCharacteristic_eq_sum_sub_sum (S : Finset ℤ)
    [DecidablePred (Even : ℤ → Prop)] [DecidablePred (Odd : ℤ → Prop)] :
    eulerCharacteristic R P S =
      (S.filter Even).sum (fun i => KTheory.K0.of R (P i)) -
        (S.filter Odd).sum (fun i => KTheory.K0.of R (P i)) := by
  unfold eulerCharacteristic
  congr

/-- The Euler characteristic is the sum of the signed term classes. -/
theorem eulerCharacteristic_eq_sum (S : Finset ℤ) :
    eulerCharacteristic R P S =
      ∑ i ∈ S, if Even i then KTheory.K0.of R (P i) else -KTheory.K0.of R (P i) := by
  classical
  rw [eulerCharacteristic_eq_sum_sub_sum, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Even i
  · have hi' : ¬Odd i := Int.not_odd_iff_even.mpr hi
    simp [hi, hi']
  · have hi' : Odd i := Int.not_even_iff_odd.mp hi
    simp [hi, hi']

/-- The Euler characteristic over no degrees is zero. -/
@[simp]
theorem eulerCharacteristic_empty : eulerCharacteristic R P ∅ = 0 := by
  simp [eulerCharacteristic_eq_sum]

/-- Enlarging the set of degrees does not change the Euler characteristic
when every newly included module is zero. -/
theorem eulerCharacteristic_eq_of_subset {S T : Finset ℤ} (hST : S ⊆ T)
    (hP : ∀ i ∈ T, i ∉ S → Subsingleton (P i)) :
    eulerCharacteristic R P S = eulerCharacteristic R P T := by
  classical
  rw [eulerCharacteristic_eq_sum, eulerCharacteristic_eq_sum]
  apply Finset.sum_subset hST
  intro i hi hiS
  have : Subsingleton (P i) := hP i hi hiS
  simp

/-- Any two finite supports of a graded family give the same Euler
characteristic. The support conditions refer to zero modules. -/
theorem eulerCharacteristic_eq_of_support (S T : Finset ℤ)
    (hS : ∀ i, i ∉ S → Subsingleton (P i))
    (hT : ∀ i, i ∉ T → Subsingleton (P i)) :
    eulerCharacteristic R P S = eulerCharacteristic R P T := by
  calc
    eulerCharacteristic R P S = eulerCharacteristic R P (S ∪ T) :=
      eulerCharacteristic_eq_of_subset R P Finset.subset_union_left
        (fun i _ hi => hS i hi)
    _ = eulerCharacteristic R P T :=
      (eulerCharacteristic_eq_of_subset R P Finset.subset_union_right
        (fun i _ hi => hT i hi)).symm

/-- A graded family of zero modules has zero Euler characteristic. -/
theorem eulerCharacteristic_eq_zero (S : Finset ℤ) (hP : ∀ i, Subsingleton (P i)) :
    eulerCharacteristic R P S = 0 := by
  calc
    eulerCharacteristic R P S = eulerCharacteristic R P ∅ :=
      (eulerCharacteristic_eq_of_subset R P (Finset.empty_subset S)
        (fun i _ _ => hP i)).symm
    _ = 0 := eulerCharacteristic_empty R P

/-- Truncation to one degree gives its term class in even degree and the
negative of its term class in odd degree. -/
@[simp]
theorem eulerCharacteristic_singleton (j : ℤ) :
    eulerCharacteristic R P {j} =
      if Even j then KTheory.K0.of R (P j) else -KTheory.K0.of R (P j) := by
  simp [eulerCharacteristic_eq_sum]

/-- A family supported in one degree has the same Euler characteristic on
any finite support containing that degree as on the singleton. -/
theorem eulerCharacteristic_eq_singleton {j : ℤ} {S : Finset ℤ} (hj : j ∈ S)
    (hP : ∀ i, i ≠ j → Subsingleton (P i)) :
    eulerCharacteristic R P S = eulerCharacteristic R P {j} := by
  symm
  apply eulerCharacteristic_eq_of_subset R P (Finset.singleton_subset_iff.mpr hj)
  intro i _ hi
  exact hP i (Finset.notMem_singleton.mp hi)

variable (Q : ℤ → Type w) [∀ i, AddCommGroup (Q i)] [∀ i, Module Rᵐᵒᵖ (Q i)]
    [∀ i, Module.Finite Rᵐᵒᵖ (Q i)] [∀ i, Module.Projective Rᵐᵒᵖ (Q i)]

/-- The Euler characteristic of the degreewise product is additive on any
common finite set of degrees, without support assumptions. -/
@[simp]
theorem eulerCharacteristic_prod (S : Finset ℤ) :
    eulerCharacteristic R (fun i => P i × Q i) S =
      eulerCharacteristic R P S + eulerCharacteristic R Q S := by
  classical
  simp_rw [eulerCharacteristic_eq_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Even i
  · simpa only [ite_eq_left hi] using of_prod R (P i) (Q i)
  · simp only [ite_eq_right hi, of_prod, neg_add_rev]
    exact add_comm _ _

/-- For separately supported families, the Euler characteristic of their
product on the union of their supports is the sum of their Euler characteristics. -/
theorem eulerCharacteristic_prod_union (S T : Finset ℤ)
    (hP : ∀ i, i ∉ S → Subsingleton (P i))
    (hQ : ∀ i, i ∉ T → Subsingleton (Q i)) :
    eulerCharacteristic R (fun i => P i × Q i) (S ∪ T) =
      eulerCharacteristic R P S + eulerCharacteristic R Q T := by
  rw [eulerCharacteristic_prod]
  congr 1
  · exact (eulerCharacteristic_eq_of_subset R P Finset.subset_union_left
      (fun i _ hi => hP i hi)).symm
  · exact (eulerCharacteristic_eq_of_subset R Q Finset.subset_union_right
      (fun i _ hi => hQ i hi)).symm

end Graded

end KTheory.K0
