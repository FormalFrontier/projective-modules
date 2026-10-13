/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Free.FreeWordAlgebra
import ProjectiveModules.Free.FreeWordAugmentation
import ProjectiveModules.Free.FreeWordAugmentationKernel
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Zero-generator augmentation clients

These private clients compute with the canonical augmentation and with Mathlib's
linear-combination map. Direct finite-support and matrix-order calculations check trivial
coefficients, right-appending word order, left multiplication of matrix coefficients, and
omitted or repeated indexing. Separate consumers use the terminal-coefficient rules and
output characterization, including the empty-alphabet case and reconstruction of a
matrix-word output from independently computed coefficients.

Further computations use the augmentation's coefficient API and full-letter range
criterion: matrix products retain their ordered constant coefficient, a nonzero matrix
polynomial has uniquely determined letter coordinates, and an infinite alphabet has a
full-range element excluded by a restricted indexing. The coordinate uniqueness uses
linear independence over the left regular word algebra. The terminal-coefficient API
also computes outputs with a moving terminal letter in an infinite alphabet and a
nonconstant word-algebra scalar with ordered matrix coefficients. Independently lifted
coefficient and alphabet carriers retain nonzero outputs in the augmentation kernel.

The private proposition definitions specify the coefficient, range, independence and
linear-equivalence questions. They are statement data, not proofs of those questions.
Their lifted uses keep coefficient, alphabet and indexing universes independent.

## References

* Mathlib, `Mathlib.Algebra.MonoidAlgebra.Lift`: the noncommutative ring-homomorphism lift.
* Mathlib, `Mathlib.LinearAlgebra.Finsupp.LinearCombination`: finite linear combinations.
* Mathlib, `Mathlib.Data.Matrix.Basis`: multiplication of matrix units.
* Mathlib, `Mathlib.Algebra.FreeMonoid.Basic` and `Mathlib.Data.List.Basic`: words and
  terminal letters.
* `ProjectiveModules.Free.FreeWordAlgebra`: independence of letter monomials over the
  left regular word algebra.

Formal Frontier agents developed these clients with AI assistance.
-/

noncomputable section

universe u v w u' v' w'

private abbrev WordAlgebra (K : Type u) (α : Type v) [Semiring K] :=
  MonoidAlgebra K (FreeMonoid α)

private def letterCombination {K : Type u} [Semiring K] {α : Type v} {I : Type w}
    (c : I → α) : (I →₀ WordAlgebra K α) →ₗ[WordAlgebra K α] WordAlgebra K α :=
  Finsupp.linearCombination (WordAlgebra K α)
    (fun i ↦ MonoidAlgebra.single (FreeMonoid.of (c i)) (1 : K))

-- These definitions record propositions only; none supplies a proof of its value.
private def coefficientStatement (K : Type u) (α : Type v) [Semiring K] : Prop :=
  ∀ x : WordAlgebra K α, MonoidAlgebra.freeMonoidAugmentation K α x = x.coeff 1

private def fullRangeStatement (K : Type u) (α : Type v) [Semiring K] : Prop :=
  LinearMap.range (letterCombination (K := K) (id : α → α)) =
    LinearMap.ker (MonoidAlgebra.freeMonoidAugmentation K α).toSemilinearMap

private def membershipStatement (K : Type u) (α : Type v) [Semiring K] : Prop :=
  ∀ x : WordAlgebra K α, MonoidAlgebra.freeMonoidAugmentation K α x = 0 ↔
    ∃ a : α →₀ WordAlgebra K α, letterCombination id a = x

private def reindexedRangeStatement {K : Type u} [Semiring K] {α : Type v}
    {I : Type w} (c : I → α) : Prop :=
  Function.Surjective c → LinearMap.range (letterCombination (K := K) c) =
    LinearMap.ker (MonoidAlgebra.freeMonoidAugmentation K α).toSemilinearMap

private def independenceStatement {K : Type u} [Semiring K] {α : Type v}
    {I : Type w} (c : I → α) : Prop :=
  Function.Injective c →
    LinearIndependent (WordAlgebra K α)
      (fun i ↦ MonoidAlgebra.single (FreeMonoid.of (c i)) (1 : K)) ∧
    Function.Injective (letterCombination (K := K) c)

private def equivalenceStatement {K : Type u} [Semiring K] {α : Type v}
    {I : Type w} (c : I → α) : Prop :=
  Function.Bijective c →
    ∃ e : (I →₀ WordAlgebra K α) ≃ₗ[WordAlgebra K α]
      LinearMap.ker (MonoidAlgebra.freeMonoidAugmentation K α).toSemilinearMap,
      ∀ a, (e a : WordAlgebra K α) = letterCombination c a

section LiftedStatements

variable (K : Type u) (α : Type v) (I : Type w) [Semiring K] (c : I → α)

#check coefficientStatement (ULift.{u'} K) (ULift.{v'} α)
#check fullRangeStatement (ULift.{w'} K) (ULift.{u'} α)
#check membershipStatement (ULift.{v'} K) (ULift.{w'} α)
#check reindexedRangeStatement (K := ULift.{u'} K)
  (fun i : ULift.{w'} I ↦ (ULift.up (c i.down) : ULift.{v'} α))
#check independenceStatement (K := ULift.{w'} K)
  (fun i : ULift.{v'} I ↦ (ULift.up (c i.down) : ULift.{u'} α))
#check equivalenceStatement (K := ULift.{v'} K)
  (fun i : ULift.{u'} I ↦ (ULift.up (c i.down) : ULift.{w'} α))

end LiftedStatements

section SemiringCalculations

variable {K : Type u} [Semiring K] {α : Type v} {I : Type w}

example (k : K) :
    MonoidAlgebra.freeMonoidAugmentation K α (MonoidAlgebra.single 1 k) = k := by
  simp only [MonoidAlgebra.freeMonoidAugmentation_single_one]

example (i : α) (k : K) :
    MonoidAlgebra.freeMonoidAugmentation K α
      (MonoidAlgebra.single (FreeMonoid.of i) k) = 0 := by
  simp only [MonoidAlgebra.freeMonoidAugmentation_single_of]

example (i : α) :
    MonoidAlgebra.freeMonoidAugmentation K α
      (MonoidAlgebra.single (FreeMonoid.of i) (1 : K) *
        MonoidAlgebra.single (FreeMonoid.of i) 1) = 0 := by
  simp only [map_mul, MonoidAlgebra.freeMonoidAugmentation_single_of, zero_mul]

example : letterCombination (K := K) (id : Unit → Unit)
    (Finsupp.single () (MonoidAlgebra.single (FreeMonoid.of ()) (1 : K))) =
      MonoidAlgebra.single (FreeMonoid.of () * FreeMonoid.of ()) 1 := by
  simp [letterCombination, smul_eq_mul, MonoidAlgebra.single_mul_single]

-- Nontriviality is local to properness, not a hypothesis of the proposition data.
example [Nontrivial K] : (1 : WordAlgebra K α) ∉
    LinearMap.ker (MonoidAlgebra.freeMonoidAugmentation K α).toSemilinearMap := by
  simp [LinearMap.mem_ker]

-- With zero coefficients, every input, output and coordinate vector is zero.
example [Subsingleton K] (x : WordAlgebra K α) :
    MonoidAlgebra.freeMonoidAugmentation K α x = 0 := Subsingleton.elim _ _

example [Subsingleton K] (c : I → α) (a : I →₀ WordAlgebra K α) :
    a = 0 ∧ letterCombination c a = 0 :=
  ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

example [Subsingleton K] (c : I → α) :
    Function.Injective (letterCombination (K := K) c) := by
  intro a b _
  exact Subsingleton.elim a b

end SemiringCalculations

example : (MonoidAlgebra.single (FreeMonoid.of ()) 1 : WordAlgebra ℕ Unit) ≠ 0 ∧
    MonoidAlgebra.freeMonoidAugmentation ℕ Unit
      (MonoidAlgebra.single (FreeMonoid.of ()) 1) = 0 := by
  constructor
  · exact MonoidAlgebra.single_ne_zero.mpr one_ne_zero
  · simp only [MonoidAlgebra.freeMonoidAugmentation_single_of]

private theorem empty_word (w : FreeMonoid Empty) : w = 1 := by
  apply FreeMonoid.toList.injective
  cases w.toList with
  | nil => rfl
  | cons a _ => exact Empty.elim a

private theorem empty_element {K : Type u} [Semiring K] (x : WordAlgebra K Empty) :
    x = MonoidAlgebra.single 1 (x.coeff 1) := by
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro w
  rw [empty_word w]
  simp

-- Under the canonical coefficient identification, augmentation on an empty alphabet is identity.
private theorem empty_augmentation {K : Type u} [Semiring K] (x : WordAlgebra K Empty) :
    MonoidAlgebra.freeMonoidAugmentation K Empty x = x.coeff 1 := by
  calc
    MonoidAlgebra.freeMonoidAugmentation K Empty x =
        MonoidAlgebra.freeMonoidAugmentation K Empty
          (MonoidAlgebra.single 1 (x.coeff 1)) :=
      congrArg (MonoidAlgebra.freeMonoidAugmentation K Empty) (empty_element x)
    _ = x.coeff 1 := by simp only [MonoidAlgebra.freeMonoidAugmentation_single_one]

example {K : Type u} [Semiring K] (x : WordAlgebra K Empty)
    (hx : x ∈ LinearMap.ker
      (MonoidAlgebra.freeMonoidAugmentation K Empty).toSemilinearMap) : x = 0 := by
  have hx0 : MonoidAlgebra.freeMonoidAugmentation K Empty x = 0 :=
    LinearMap.mem_ker.mp hx
  have hx1 : x.coeff 1 = 0 := by simpa only [empty_augmentation] using hx0
  calc
    x = MonoidAlgebra.single 1 (x.coeff 1) := empty_element x
    _ = 0 := by simp [hx1]

example {K : Type u} [Semiring K] (a : Empty →₀ WordAlgebra K Empty) :
    letterCombination (id : Empty → Empty) a = 0 := by
  simp only [letterCombination, id_eq]
  apply (MonoidAlgebra.linearCombination_freeMonoid_of_eq_iff a 0).mpr
  refine ⟨by simp, ?_⟩
  intro i
  exact Empty.elim i

private def constantOne (K : Type u) (α : Type v) [Semiring K] :
    WordAlgebra K α →+* K :=
  MonoidAlgebra.liftNCRingHom (RingHom.id K) (1 : FreeMonoid α →* K)
    (fun k _ ↦ Commute.one_right k)

private theorem constantOne_single {K : Type u} [Semiring K] {α : Type v}
    (w : FreeMonoid α) (k : K) : constantOne K α (MonoidAlgebra.single w k) = k := by
  simp [constantOne]

example {K : Type u} [Semiring K] [Nontrivial K] {α : Type v} (i : α) :
    constantOne K α ≠ MonoidAlgebra.freeMonoidAugmentation K α := by
  intro h
  have hi := DFunLike.congr_fun h (MonoidAlgebra.single (FreeMonoid.of i) (1 : K))
  simp only [constantOne_single, MonoidAlgebra.freeMonoidAugmentation_single_of] at hi
  exact one_ne_zero hi

-- Empty alphabets and trivial coefficients give agreement, not separation.
example {K : Type u} [Semiring K] :
    constantOne K Empty = MonoidAlgebra.freeMonoidAugmentation K Empty := by
  apply DFunLike.ext _ _
  intro x
  rw [empty_element x]
  simp only [constantOne_single, MonoidAlgebra.freeMonoidAugmentation_single_one]

example {K : Type u} [Semiring K] [Subsingleton K] {α : Type v} :
    constantOne K α = MonoidAlgebra.freeMonoidAugmentation K α := by
  apply DFunLike.ext _ _
  intro x
  exact Subsingleton.elim _ _

private theorem bool_words_ne : FreeMonoid.of false * FreeMonoid.of true ≠
    FreeMonoid.of true * FreeMonoid.of false := by
  intro h
  have hl := congrArg FreeMonoid.toList h
  simp at hl

private theorem bool_append : letterCombination (K := ℕ) (id : Bool → Bool)
    (Finsupp.single true (MonoidAlgebra.single (FreeMonoid.of false) 1)) =
      MonoidAlgebra.single (FreeMonoid.of false * FreeMonoid.of true) 1 := by
  simp [letterCombination, smul_eq_mul, MonoidAlgebra.single_mul_single]

example : letterCombination (K := ℕ) (id : Bool → Bool)
    (Finsupp.single true (MonoidAlgebra.single (FreeMonoid.of false) 1)) ≠
      MonoidAlgebra.single (FreeMonoid.of true * FreeMonoid.of false) 1 := by
  rw [bool_append]
  intro h
  exact bool_words_ne (MonoidAlgebra.single_left_injective
    (R := ℕ) (M := FreeMonoid Bool) one_ne_zero h)

example : (MonoidAlgebra.single (FreeMonoid.of false) 1 : WordAlgebra ℕ Bool) ≠
    MonoidAlgebra.single (FreeMonoid.of true) 1 := by
  intro h
  have hw := MonoidAlgebra.single_left_injective
    (R := ℕ) (M := FreeMonoid Bool) one_ne_zero h
  have hb := FreeMonoid.of_injective hw
  cases hb

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℕ

private abbrev matrixUnit (i j : Fin 2) : Mat := Matrix.single i j 1

private theorem matrix_left_order : letterCombination (K := Mat) (id : Bool → Bool)
    ((MonoidAlgebra.single 1 (matrixUnit 0 1) : WordAlgebra Mat Bool) •
      Finsupp.single true (MonoidAlgebra.single (FreeMonoid.of false) (matrixUnit 1 0))) =
    MonoidAlgebra.single (FreeMonoid.of false * FreeMonoid.of true) (matrixUnit 0 0) := by
  rw [map_smul]
  simp [letterCombination, smul_eq_mul, MonoidAlgebra.single_mul_single, matrixUnit]

private theorem matrix_reverse_order : letterCombination (K := Mat) (id : Bool → Bool)
    ((MonoidAlgebra.single 1 (matrixUnit 1 0) : WordAlgebra Mat Bool) •
      Finsupp.single true (MonoidAlgebra.single (FreeMonoid.of false) (matrixUnit 0 1))) =
    MonoidAlgebra.single (FreeMonoid.of false * FreeMonoid.of true) (matrixUnit 1 1) := by
  rw [map_smul]
  simp [letterCombination, smul_eq_mul, MonoidAlgebra.single_mul_single, matrixUnit]

example : (letterCombination (K := Mat) (id : Bool → Bool)
    ((MonoidAlgebra.single 1 (matrixUnit 0 1) : WordAlgebra Mat Bool) •
      Finsupp.single true (MonoidAlgebra.single (FreeMonoid.of false) (matrixUnit 1 0)))).coeff
      (FreeMonoid.of false * FreeMonoid.of true) = matrixUnit 0 0 := by
  simp only [letterCombination, id_eq,
    MonoidAlgebra.coeff_linearCombination_freeMonoid_of]
  simp [smul_eq_mul, MonoidAlgebra.single_mul_single, matrixUnit]

-- Reconstruct a matrix-word output from its independently computed coefficients.
example : letterCombination (K := Mat) (id : Bool → Bool)
    ((MonoidAlgebra.single 1 (matrixUnit 0 1) : WordAlgebra Mat Bool) •
      Finsupp.single true (MonoidAlgebra.single (FreeMonoid.of false) (matrixUnit 1 0))) =
    MonoidAlgebra.single (FreeMonoid.of false * FreeMonoid.of true) (matrixUnit 0 0) := by
  simp only [letterCombination, id_eq]
  apply (MonoidAlgebra.linearCombination_freeMonoid_of_eq_iff _ _).mpr
  constructor
  · simpa only [letterCombination, id_eq,
      MonoidAlgebra.coeff_linearCombination_freeMonoid_of_one] using
      (congrArg (fun y : WordAlgebra Mat Bool ↦ y.coeff 1) matrix_left_order).symm
  · intro a w
    simpa only [letterCombination, id_eq,
      MonoidAlgebra.coeff_linearCombination_freeMonoid_of] using
      (congrArg (fun y : WordAlgebra Mat Bool ↦ y.coeff (w * FreeMonoid.of a))
        matrix_left_order).symm

example : (letterCombination (K := Mat) (id : Bool → Bool)
    ((MonoidAlgebra.single 1 (matrixUnit 1 0) : WordAlgebra Mat Bool) •
      Finsupp.single true (MonoidAlgebra.single (FreeMonoid.of false) (matrixUnit 0 1)))).coeff
      (FreeMonoid.of false * FreeMonoid.of true) ≠ matrixUnit 0 0 := by
  rw [matrix_reverse_order]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  intro h
  have h00 := congrArg (fun m : Mat ↦ m 0 0) h
  simp [matrixUnit, Matrix.single] at h00

-- Terminal-coefficient vanishing is proved directly, without any range/kernel headline.
private theorem omitted_terminal {K : Type u} [Semiring K] {α : Type v} {I : Type w}
    (c : I → α) (j : α) (hc : ∀ i, c i ≠ j) (a : I →₀ WordAlgebra K α)
    (w : FreeMonoid α) : (letterCombination c a).coeff (w * FreeMonoid.of j) = 0 := by
  classical
  have ht (i : I) (p : FreeMonoid α) :
      p * FreeMonoid.of (c i) ≠ w * FreeMonoid.of j := by
    intro h
    apply hc i
    have hl := congrArg (fun q : FreeMonoid α ↦ q.toList.getLast?) h
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of,
      List.getLast?_append_cons] at hl
    exact Option.some.inj hl
  simp only [letterCombination, Finsupp.linearCombination_apply, smul_eq_mul,
    MonoidAlgebra.coeff_finsuppSum, Finsupp.sum_apply]
  exact Finset.sum_eq_zero fun i _ ↦
    MonoidAlgebra.coeff_mul_single_of_forall_mul_ne 1 (a i) (ht i)

example : Function.Injective (Fin.castSucc : Fin 2 → Fin 3) := Fin.castSucc_injective 2

example (a : Fin 2 →₀ WordAlgebra ℕ (Fin 3)) (w : FreeMonoid (Fin 3)) :
    (letterCombination Fin.castSucc a).coeff (w * FreeMonoid.of (Fin.last 2)) = 0 :=
  omitted_terminal Fin.castSucc (Fin.last 2) Fin.castSucc_ne_last a w

private theorem omitted_letter_not_mem :
    (MonoidAlgebra.single (FreeMonoid.of (Fin.last 2)) 1 : WordAlgebra ℕ (Fin 3)) ∉
      LinearMap.range (letterCombination (K := ℕ) (Fin.castSucc : Fin 2 → Fin 3)) := by
  rintro ⟨a, ha⟩
  have h0 := omitted_terminal Fin.castSucc (Fin.last 2) Fin.castSucc_ne_last a 1
  rw [one_mul, ha] at h0
  simp at h0

example : (MonoidAlgebra.single (FreeMonoid.of (Fin.last 2)) 1 : WordAlgebra ℕ (Fin 3)) ∈
    LinearMap.ker (MonoidAlgebra.freeMonoidAugmentation ℕ (Fin 3)).toSemilinearMap := by
  simp only [LinearMap.mem_ker, RingHom.coe_toSemilinearMap,
    MonoidAlgebra.freeMonoidAugmentation_single_of]

example : LinearMap.range (letterCombination (K := ℕ) (Fin.castSucc : Fin 2 → Fin 3)) ≠
    LinearMap.ker (MonoidAlgebra.freeMonoidAugmentation ℕ (Fin 3)).toSemilinearMap := by
  intro h
  apply omitted_letter_not_mem
  rw [h]
  simp only [LinearMap.mem_ker, RingHom.coe_toSemilinearMap,
    MonoidAlgebra.freeMonoidAugmentation_single_of]

-- The indexing is surjective, but two distinct coordinate vectors have the same image.
example : Function.Surjective (fun _ : Bool ↦ ()) := by
  intro i
  cases i
  exact ⟨false, rfl⟩

private theorem repeated_coordinate_images :
    letterCombination (K := ℕ) (fun _ : Bool ↦ ()) (Finsupp.single false 1) =
      letterCombination (K := ℕ) (fun _ : Bool ↦ ()) (Finsupp.single true 1) := by
  simp [letterCombination]

example : ¬ Function.Injective (letterCombination (K := ℕ) (fun _ : Bool ↦ ())) := by
  intro h
  have heq := h repeated_coordinate_images
  have h10 : (1 : WordAlgebra ℕ Unit) = 0 := by
    simpa using congrArg (fun a : Bool →₀ WordAlgebra ℕ Unit ↦ a false) heq
  exact one_ne_zero h10

example {K : Type u} [Semiring K] [Subsingleton K] :
    Function.Injective (letterCombination (K := K) (fun _ : Bool ↦ ())) := by
  intro a b _
  exact Subsingleton.elim a b

-- The constant coefficient of a product remembers the order of matrix multiplication.
example :
    MonoidAlgebra.freeMonoidAugmentation Mat Bool
      ((MonoidAlgebra.single 1 (matrixUnit 0 1) +
          MonoidAlgebra.single (FreeMonoid.of false) (matrixUnit 1 0)) *
        (MonoidAlgebra.single 1 (matrixUnit 1 0) +
          MonoidAlgebra.single (FreeMonoid.of true) (matrixUnit 0 1))) = matrixUnit 0 0 ∧
    MonoidAlgebra.freeMonoidAugmentation Mat Bool
      ((MonoidAlgebra.single 1 (matrixUnit 1 0) +
          MonoidAlgebra.single (FreeMonoid.of false) (matrixUnit 0 1)) *
        (MonoidAlgebra.single 1 (matrixUnit 0 1) +
          MonoidAlgebra.single (FreeMonoid.of true) (matrixUnit 1 0))) = matrixUnit 1 1 := by
  have hword : FreeMonoid.of false * FreeMonoid.of true ≠ 1 := by
    intro h
    have hl := congrArg FreeMonoid.toList h
    simp at hl
  constructor <;> rw [MonoidAlgebra.freeMonoidAugmentation_apply] <;>
    simp [mul_add, add_mul, MonoidAlgebra.single_mul_single, matrixUnit, hword]

-- Range supplies a preimage; independence identifies its coordinates, not just its image.
example :
    (MonoidAlgebra.single (FreeMonoid.of false * FreeMonoid.of true) (matrixUnit 0 0) :
      WordAlgebra Mat Bool) ≠ 0 ∧
    ∃! a : Bool →₀ WordAlgebra Mat Bool,
      letterCombination id a =
        MonoidAlgebra.single (FreeMonoid.of false * FreeMonoid.of true) (matrixUnit 0 0) ∧
      a true = MonoidAlgebra.single (FreeMonoid.of false) (matrixUnit 0 0) ∧ a false = 0 := by
  have hinj : Function.Injective (letterCombination (K := Mat) (id : Bool → Bool)) := by
    simpa only [letterCombination, id_eq] using
      (MonoidAlgebra.linearIndependent_freeMonoid_of
        (K := Mat) (ι := Bool)).finsuppLinearCombination_injective
  have hfull : LinearMap.range (letterCombination (K := Mat) (id : Bool → Bool)) =
      LinearMap.ker (MonoidAlgebra.freeMonoidAugmentation Mat Bool).toSemilinearMap := by
    simpa only [letterCombination, id_eq] using
      (MonoidAlgebra.range_linearCombination_freeMonoid_of_eq_ker_freeMonoidAugmentation
        (K := Mat) (α := Bool))
  have hp : (MonoidAlgebra.single (FreeMonoid.of false * FreeMonoid.of true)
      (matrixUnit 0 0) : WordAlgebra Mat Bool) ∈
      LinearMap.range (letterCombination (K := Mat) (id : Bool → Bool)) := by
    rw [hfull, LinearMap.mem_ker, RingHom.coe_toSemilinearMap,
      MonoidAlgebra.freeMonoidAugmentation_apply]
    have hword : FreeMonoid.of false * FreeMonoid.of true ≠ 1 := by
      intro h
      have hl := congrArg FreeMonoid.toList h
      simp at hl
    simp [hword]
  constructor
  · apply MonoidAlgebra.single_ne_zero.mpr
    intro h
    have h00 := congrArg (fun m : Mat ↦ m 0 0) h
    simp [matrixUnit, Matrix.single] at h00
  · obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hp
    have ha' : a = (MonoidAlgebra.single 1 (matrixUnit 0 1) : WordAlgebra Mat Bool) •
        Finsupp.single true (MonoidAlgebra.single (FreeMonoid.of false) (matrixUnit 1 0)) :=
      hinj (ha.trans matrix_left_order.symm)
    refine ⟨a, ⟨ha, ?_, ?_⟩, ?_⟩
    · rw [ha']
      simp [smul_eq_mul, MonoidAlgebra.single_mul_single, matrixUnit]
    · rw [ha']
      simp
    · intro b hb
      exact hinj (hb.1.trans ha.symm)

-- Coefficients and indices may be independently lifted while the alphabet is infinite.
example :
    (MonoidAlgebra.single (FreeMonoid.of 2) 1 : WordAlgebra (ULift.{u'} ℕ) ℕ) ∈
      LinearMap.range (letterCombination (id : ℕ → ℕ)) ∧
    (MonoidAlgebra.single (FreeMonoid.of 2) 1 : WordAlgebra (ULift.{u'} ℕ) ℕ) ∉
      LinearMap.range (letterCombination (fun i : ULift.{v'} (Fin 2) ↦ i.down.val)) := by
  constructor
  · have hfull : LinearMap.range (letterCombination (K := ULift.{u'} ℕ) (id : ℕ → ℕ)) =
        LinearMap.ker
          (MonoidAlgebra.freeMonoidAugmentation (ULift.{u'} ℕ) ℕ).toSemilinearMap := by
      simpa only [letterCombination, id_eq] using
        (MonoidAlgebra.range_linearCombination_freeMonoid_of_eq_ker_freeMonoidAugmentation
          (K := ULift.{u'} ℕ) (α := ℕ))
    rw [hfull]
    simp only [LinearMap.mem_ker, RingHom.coe_toSemilinearMap,
      MonoidAlgebra.freeMonoidAugmentation_single_of]
  · rintro ⟨a, ha⟩
    have h0 := omitted_terminal (K := ULift.{u'} ℕ)
      (fun i : ULift.{v'} (Fin 2) ↦ i.down.val) 2
      (fun i ↦ Nat.ne_of_lt i.down.isLt) a 1
    rw [one_mul, ha] at h0
    have h10 : (1 : ULift.{u'} ℕ) = 0 := by simp at h0
    exact one_ne_zero h10

-- The terminal letter moves through an infinite alphabet; the scalar is a word polynomial.
example (j : ℕ) :
    let f : ℕ →₀ WordAlgebra Mat ℕ :=
      (MonoidAlgebra.single (FreeMonoid.of 13) (matrixUnit 0 1) : WordAlgebra Mat ℕ) •
        Finsupp.single j
          (MonoidAlgebra.single (FreeMonoid.of 3 * FreeMonoid.of 5) (matrixUnit 1 0))
    let x := letterCombination id f
    x.coeff ((FreeMonoid.of 13 * (FreeMonoid.of 3 * FreeMonoid.of 5)) * FreeMonoid.of j) =
        matrixUnit 0 0 ∧ x ≠ 0 ∧
      x ∈ LinearMap.ker (MonoidAlgebra.freeMonoidAugmentation Mat ℕ).toSemilinearMap := by
  let f : ℕ →₀ WordAlgebra Mat ℕ :=
    (MonoidAlgebra.single (FreeMonoid.of 13) (matrixUnit 0 1) : WordAlgebra Mat ℕ) •
      Finsupp.single j
        (MonoidAlgebra.single (FreeMonoid.of 3 * FreeMonoid.of 5) (matrixUnit 1 0))
  let x := letterCombination id f
  have hchar := (MonoidAlgebra.linearCombination_freeMonoid_of_eq_iff f x).mp rfl
  have hc : x.coeff
      ((FreeMonoid.of 13 * (FreeMonoid.of 3 * FreeMonoid.of 5)) * FreeMonoid.of j) =
        matrixUnit 0 0 := by
    rw [hchar.2 j (FreeMonoid.of 13 * (FreeMonoid.of 3 * FreeMonoid.of 5))]
    simp [f, smul_eq_mul, MonoidAlgebra.single_mul_single, matrixUnit]
  refine ⟨hc, ?_, ?_⟩
  · intro hx
    have hxcoeff : x.coeff
        ((FreeMonoid.of 13 * (FreeMonoid.of 3 * FreeMonoid.of 5)) * FreeMonoid.of j) = 0 := by
      simpa only [MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
        congrArg (fun y : WordAlgebra Mat ℕ ↦ y.coeff
          ((FreeMonoid.of 13 * (FreeMonoid.of 3 * FreeMonoid.of 5)) * FreeMonoid.of j)) hx
    have hz : matrixUnit 0 0 = 0 := hc.symm.trans hxcoeff
    have h00 := congrArg (fun m : Mat ↦ m 0 0) hz
    simp [matrixUnit, Matrix.single] at h00
  · simpa only [LinearMap.mem_ker, RingHom.coe_toSemilinearMap,
      MonoidAlgebra.freeMonoidAugmentation_apply] using hchar.1

-- These are independent carrier lifts, not a reindexing of the letter family.
example (a : ULift.{v'} ℕ) (w : FreeMonoid (ULift.{v'} ℕ)) :
    let x : WordAlgebra (ULift.{u'} ℕ) (ULift.{v'} ℕ) :=
      letterCombination id (Finsupp.single a (MonoidAlgebra.single w 1))
    x.coeff (w * FreeMonoid.of a) = 1 ∧ x ≠ 0 ∧
      x ∈ LinearMap.ker
        (MonoidAlgebra.freeMonoidAugmentation (ULift.{u'} ℕ) (ULift.{v'} ℕ)).toSemilinearMap := by
  let x : WordAlgebra (ULift.{u'} ℕ) (ULift.{v'} ℕ) :=
    letterCombination id (Finsupp.single a (MonoidAlgebra.single w 1))
  have hc : x.coeff (w * FreeMonoid.of a) = 1 := by
    simp only [x, letterCombination, id_eq,
      MonoidAlgebra.coeff_linearCombination_freeMonoid_of,
      Finsupp.single_eq_same, MonoidAlgebra.coeff_single]
  refine ⟨hc, ?_, ?_⟩
  · intro hx
    have hxcoeff : x.coeff (w * FreeMonoid.of a) = 0 := by
      simpa only [MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
        congrArg (fun y : WordAlgebra (ULift.{u'} ℕ) (ULift.{v'} ℕ) ↦
          y.coeff (w * FreeMonoid.of a)) hx
    exact one_ne_zero (hc.symm.trans hxcoeff)
  · simp only [LinearMap.mem_ker, RingHom.coe_toSemilinearMap,
      MonoidAlgebra.freeMonoidAugmentation_apply, letterCombination, id_eq,
      MonoidAlgebra.coeff_linearCombination_freeMonoid_of_one]
