/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.RightRegularDefect
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.Int.Basic
import Mathlib.LinearAlgebra.Pi

/-!
# Right regular defect clients

On all integer sequences, the backward shift has the zero-inserting shift as a
right inverse but not as a left inverse. Evaluation at coordinate zero of
`Pi.single 0 (1 : ℤ)` proves that the reverse composite is not the identity.
The same evaluation and Mathlib's singleton-span theorem independently show
that its defect span is nonzero. Multiplication of the defect on the left by
the zero-inserting shift leaves that span, showing the handedness boundary.

The product equivalence is exercised through its coordinate and inverse APIs,
including the canonical opposite-ring action. The identity pair over the
integers, the zero ring, and commutative rings give zero-defect boundaries.
All sequence endomorphisms in this file are private fixtures.
-/

@[expose] public section

universe v

namespace ProjectiveModulesTests.RightRegularDefectClient

private abbrev SequenceEnd := Module.End ℤ (ℕ → ℤ)

private def backwardShift : SequenceEnd :=
  LinearMap.pi fun n => LinearMap.proj (n + 1)

private def insertZero : SequenceEnd :=
  LinearMap.pi fun n => match n with
    | 0 => 0
    | m + 1 => LinearMap.proj m

private theorem backwardShift_apply (v : ℕ → ℤ) (n : ℕ) :
    backwardShift v n = v (n + 1) := rfl

private theorem insertZero_apply_zero (v : ℕ → ℤ) :
    insertZero v 0 = 0 := rfl

private theorem insertZero_apply_succ (v : ℕ → ℤ) (n : ℕ) :
    insertZero v (n + 1) = v n := rfl

private theorem sequence_mul_eq_one : backwardShift * insertZero = 1 := by
  apply LinearMap.ext
  intro v
  funext n
  simp only [Module.End.mul_apply, Module.End.one_apply,
    backwardShift_apply, insertZero_apply_succ]

private theorem sequence_reverse_ne_one : insertZero * backwardShift ≠ 1 := by
  intro h
  have hzero := congrArg (fun f : SequenceEnd => f (Pi.single 0 (1 : ℤ)) 0) h
  have impossible : (0 : ℤ) = 1 := by
    simpa only [Module.End.mul_apply, Module.End.one_apply,
      insertZero_apply_zero, Pi.single_eq_same] using hzero
  exact zero_ne_one impossible

private theorem sequence_defect_at_zero :
    (1 - insertZero * backwardShift : SequenceEnd) (Pi.single 0 (1 : ℤ)) 0 = 1 := by
  simp [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply,
    insertZero_apply_zero]

private theorem sequence_defect_ne_zero :
    (1 - insertZero * backwardShift : SequenceEnd) ≠ 0 := by
  intro h
  have hzero := congrArg (fun f : SequenceEnd => f (Pi.single 0 (1 : ℤ)) 0) h
  have impossible : (1 : ℤ) = 0 := by
    simpa only [sequence_defect_at_zero, LinearMap.zero_apply, Pi.zero_apply] using hzero
  exact one_ne_zero impossible

private abbrev sequenceDefectSpan : Submodule SequenceEndᵐᵒᵖ SequenceEnd :=
  Submodule.span SequenceEndᵐᵒᵖ ({1 - insertZero * backwardShift} : Set SequenceEnd)

private theorem sequence_span_ne_bot_independent : sequenceDefectSpan ≠ ⊥ := by
  intro h
  exact sequence_defect_ne_zero (Submodule.span_singleton_eq_bot.mp h)

private abbrev sequenceDefectGenerator : sequenceDefectSpan :=
  ⟨1 - insertZero * backwardShift, Submodule.mem_span_singleton_self _⟩

private theorem sequence_generator_ne_zero : sequenceDefectGenerator ≠ 0 := by
  intro h
  exact sequence_defect_ne_zero
    (congrArg (fun p : sequenceDefectSpan => (p : SequenceEnd)) h)

private theorem sequence_right_action (a b : SequenceEnd) :
    MulOpposite.op a • b = b * a :=
  op_smul_eq_mul a b

private theorem sequence_right_action_not_left :
    MulOpposite.op backwardShift • insertZero ≠ backwardShift * insertZero := by
  rw [op_smul_eq_mul, sequence_mul_eq_one]
  exact sequence_reverse_ne_one

private theorem sequence_left_multiple_not_mem :
    insertZero * (1 - insertZero * backwardShift) ∉ sequenceDefectSpan := by
  intro hm
  have hz := (Submodule.mem_span_one_sub_mul_iff_of_mul_eq_one sequence_mul_eq_one
    (insertZero * (1 - insertZero * backwardShift))).mp hm
  exact sequence_defect_ne_zero
    (by simpa only [← mul_assoc, sequence_mul_eq_one, one_mul] using hz)

private noncomputable abbrev sequenceDecomposition :
    SequenceEnd ≃ₗ[SequenceEndᵐᵒᵖ] (SequenceEnd × sequenceDefectSpan) :=
  LinearEquiv.rightRegularEquivProdOfMulEqOne sequence_mul_eq_one

private theorem sequence_nonzero_product :
    Nonempty (SequenceEnd ≃ₗ[SequenceEndᵐᵒᵖ] (SequenceEnd × sequenceDefectSpan)) ∧
      sequenceDefectSpan ≠ ⊥ :=
  ⟨⟨sequenceDecomposition⟩, Submodule.span_one_sub_mul_ne_bot sequence_reverse_ne_one⟩

private theorem sequence_generator_mem_kernel :
    (sequenceDefectGenerator : SequenceEnd) ∈
      LinearMap.ker (LinearMap.mulLeft SequenceEndᵐᵒᵖ backwardShift) := by
  rw [LinearMap.ker_mulLeft_eq_span_one_sub_mul_of_mul_eq_one sequence_mul_eq_one]
  exact sequenceDefectGenerator.property

private theorem sequence_generator_annihilated :
    backwardShift * (sequenceDefectGenerator : SequenceEnd) = 0 :=
  (Submodule.mem_span_one_sub_mul_iff_of_mul_eq_one sequence_mul_eq_one
    (sequenceDefectGenerator : SequenceEnd)).mp sequenceDefectGenerator.property

private theorem sequence_first_coordinate_of_one :
    (sequenceDecomposition 1).1 = backwardShift := by
  simpa only [mul_one] using
    (LinearEquiv.rightRegularEquivProdOfMulEqOne_apply_fst sequence_mul_eq_one (1 : SequenceEnd))

private theorem sequence_second_coordinate_of_one :
    ((sequenceDecomposition 1).2 : SequenceEnd) = 1 - insertZero * backwardShift := by
  simpa only [mul_one] using
    (LinearEquiv.rightRegularEquivProdOfMulEqOne_apply_snd_coe
      sequence_mul_eq_one (1 : SequenceEnd))

private theorem sequence_inverse_on_section_and_defect :
    sequenceDecomposition.symm (1, sequenceDefectGenerator) =
      insertZero + (1 - insertZero * backwardShift) := by
  simpa only [mul_one] using
    (LinearEquiv.rightRegularEquivProdOfMulEqOne_symm_apply
      sequence_mul_eq_one (1 : SequenceEnd) sequenceDefectGenerator)

private theorem sequence_generator_coordinates :
    sequenceDecomposition (sequenceDefectGenerator : SequenceEnd) =
      (0, sequenceDefectGenerator) := by
  apply sequenceDecomposition.symm.injective
  calc
    sequenceDecomposition.symm
        (sequenceDecomposition (sequenceDefectGenerator : SequenceEnd)) =
        (sequenceDefectGenerator : SequenceEnd) :=
      sequenceDecomposition.symm_apply_apply _
    _ = sequenceDecomposition.symm (0, sequenceDefectGenerator) := by
      simpa only [mul_zero, zero_add] using
        (LinearEquiv.rightRegularEquivProdOfMulEqOne_symm_apply
          sequence_mul_eq_one (0 : SequenceEnd) sequenceDefectGenerator).symm

private theorem sequence_reconstruction (r : SequenceEnd) :
    insertZero * (sequenceDecomposition r).1 +
      ((sequenceDecomposition r).2 : SequenceEnd) = r := by
  calc
    insertZero * (sequenceDecomposition r).1 +
        ((sequenceDecomposition r).2 : SequenceEnd) =
        sequenceDecomposition.symm (sequenceDecomposition r) :=
      (LinearEquiv.rightRegularEquivProdOfMulEqOne_symm_apply sequence_mul_eq_one
        (sequenceDecomposition r).1 (sequenceDecomposition r).2).symm
    _ = r := sequenceDecomposition.symm_apply_apply r

private theorem sequence_linear_right_action (r t : SequenceEnd) :
    sequenceDecomposition (r * t) = MulOpposite.op t • sequenceDecomposition r := by
  simpa only [op_smul_eq_mul] using
    sequenceDecomposition.map_smul (MulOpposite.op t) r

private theorem integer_mul_eq_one : (1 : ℤ) * 1 = 1 := by simp

private noncomputable abbrev integerDecomposition :
    ℤ ≃ₗ[ℤᵐᵒᵖ] (ℤ × Submodule.span ℤᵐᵒᵖ ({1 - (1 : ℤ) * 1} : Set ℤ)) :=
  LinearEquiv.rightRegularEquivProdOfMulEqOne integer_mul_eq_one

private theorem integer_zero_defect :
    Submodule.span ℤᵐᵒᵖ ({1 - (1 : ℤ) * 1} : Set ℤ) = ⊥ :=
  (Submodule.span_one_sub_mul_eq_bot_iff (1 : ℤ) 1).mpr (by simp)

private theorem integer_coordinates (r : ℤ) :
    (integerDecomposition r).1 = r ∧ ((integerDecomposition r).2 : ℤ) = 0 := by
  constructor
  · simpa only [one_mul] using
      (LinearEquiv.rightRegularEquivProdOfMulEqOne_apply_fst integer_mul_eq_one r)
  · simpa only [one_mul, sub_self, zero_mul] using
      (LinearEquiv.rightRegularEquivProdOfMulEqOne_apply_snd_coe integer_mul_eq_one r)

private theorem integer_inverse (s : ℤ) : integerDecomposition.symm (s, 0) = s := by
  simpa only [one_mul, Submodule.coe_zero, add_zero] using
    (LinearEquiv.rightRegularEquivProdOfMulEqOne_symm_apply integer_mul_eq_one s 0)

private theorem zero_ring_mul_eq_one (x y : PUnit.{1}) : x * y = 1 :=
  Subsingleton.elim _ _

private theorem zero_ring_boundary (x y : PUnit.{1}) :
    Nonempty (PUnit.{1} ≃ₗ[PUnit.{1}ᵐᵒᵖ]
      (PUnit.{1} × Submodule.span PUnit.{1}ᵐᵒᵖ ({1 - y * x} : Set PUnit.{1}))) ∧
      Submodule.span PUnit.{1}ᵐᵒᵖ ({1 - y * x} : Set PUnit.{1}) = ⊥ :=
  ⟨⟨LinearEquiv.rightRegularEquivProdOfMulEqOne (zero_ring_mul_eq_one x y)⟩,
    (Submodule.span_one_sub_mul_eq_bot_iff x y).mpr (Subsingleton.elim _ _)⟩

private theorem zero_ring_inverse (x y : PUnit.{1}) :
    (LinearEquiv.rightRegularEquivProdOfMulEqOne (zero_ring_mul_eq_one x y)).symm (0, 0) = 0 := by
  simp

private theorem commutative_zero_defect {A : Type v} [CommRing A]
    {x y : A} (hxy : x * y = 1) :
    Submodule.span Aᵐᵒᵖ ({1 - y * x} : Set A) = ⊥ :=
  (Submodule.span_one_sub_mul_eq_bot_iff x y).mpr ((mul_comm y x).trans hxy)

/-- In a commutative ring, a specified right inverse has zero defect coordinate. -/
theorem commutative_second_coordinate_zero {A : Type v} [CommRing A]
    {x y : A} (hxy : x * y = 1) (r : A) :
    ((LinearEquiv.rightRegularEquivProdOfMulEqOne hxy r).2 : A) = 0 := by
  have hyx : y * x = 1 := (mul_comm y x).trans hxy
  calc
    ((LinearEquiv.rightRegularEquivProdOfMulEqOne hxy r).2 : A) = (1 - y * x) * r :=
      LinearEquiv.rightRegularEquivProdOfMulEqOne_apply_snd_coe hxy r
    _ = 0 := by rw [hyx, sub_self, zero_mul]

end ProjectiveModulesTests.RightRegularDefectClient
