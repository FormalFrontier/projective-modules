/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules
import Mathlib.Data.ZMod.Basic

/-!
# Cyclic additive trace clients

Identity traces on rational scalars and ordinary traces on rational matrices
meet the cyclicity and unit-multiple conditions. The matrix trace is not
multiplicative, and the zero ring shows why the unit-multiple hypothesis matters.
-/

set_option warningAsError true

namespace ProjectiveModulesTests.CyclicTraceClient

universe uR uA

private theorem rational_invariantBasisNumber_from_cyclic : InvariantBasisNumber ℚ := by
  let τ : ℚ →+ ℚ := AddMonoidHom.id ℚ
  have hcyc : ∀ x y : ℚ, τ (x * y) = τ (y * x) := by
    intro x y
    exact congrArg τ (mul_comm x y)
  have hinj : Function.Injective (fun n : ℕ => n • τ (1 : ℚ)) := by
    simpa [τ] using (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℚ)))
  exact τ.invariantBasisNumber_of_cyclic hcyc hinj

private def rationalMatrixTrace : Matrix (Fin 2) (Fin 2) ℚ →+ ℚ :=
  Matrix.traceAddMonoidHom (Fin 2) ℚ

private theorem rationalMatrixTrace_cyclic :
    ∀ X Y : Matrix (Fin 2) (Fin 2) ℚ,
      rationalMatrixTrace (X * Y) = rationalMatrixTrace (Y * X) := by
  intro X Y
  exact Matrix.trace_mul_comm X Y

private theorem rationalMatrixTrace_one :
    rationalMatrixTrace (1 : Matrix (Fin 2) (Fin 2) ℚ) = 2 := by
  norm_num [rationalMatrixTrace]

private theorem rationalMatrixTrace_nsmul_injective :
    Function.Injective (fun n : ℕ =>
      n • rationalMatrixTrace (1 : Matrix (Fin 2) (Fin 2) ℚ)) := by
  intro m n h
  apply (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℚ)))
  rw [rationalMatrixTrace_one] at h
  have h' : (m : ℚ) * 2 = (n : ℚ) * 2 := by
    simpa only [nsmul_eq_mul] using h
  exact mul_right_cancel₀ (by norm_num : (2 : ℚ) ≠ 0) h'

private theorem rationalMatrixTrace_not_multiplicative :
    ¬ ∀ X Y : Matrix (Fin 2) (Fin 2) ℚ,
      rationalMatrixTrace (X * Y) = rationalMatrixTrace X * rationalMatrixTrace Y := by
  intro h
  have hxy := h (Matrix.single 0 1 (1 : ℚ)) (Matrix.single 1 0 (1 : ℚ))
  norm_num [rationalMatrixTrace, Matrix.single_mul_single_same] at hxy

private theorem rationalMatrixTrace_rectangular
    (X : Matrix (Fin 1) (Fin 2) (Matrix (Fin 2) (Fin 2) ℚ))
    (Y : Matrix (Fin 2) (Fin 1) (Matrix (Fin 2) (Fin 2) ℚ)) :
    rationalMatrixTrace (Matrix.trace (X * Y)) =
      rationalMatrixTrace (Matrix.trace (Y * X)) :=
  Matrix.trace_mul_comm_of_addMonoidHom rationalMatrixTrace rationalMatrixTrace_cyclic X Y

/-- Ordinary rational matrix trace applies the cyclic additive trace criterion to
a noncommutative matrix semiring. -/
public theorem rationalMatrix_invariantBasisNumber_from_cyclic :
    InvariantBasisNumber (Matrix (Fin 2) (Fin 2) ℚ) :=
  rationalMatrixTrace.invariantBasisNumber_of_cyclic
    rationalMatrixTrace_cyclic rationalMatrixTrace_nsmul_injective

private theorem empty_rectangular_trace {R : Type uR} {A : Type uA}
    [AddCommMonoid R] [Mul R] [AddCommMonoid A]
    (τ : R →+ A) (hcyc : ∀ x y : R, τ (x * y) = τ (y * x))
    (X : Matrix (Fin 0) (Fin 2) R) (Y : Matrix (Fin 2) (Fin 0) R) :
    τ (Matrix.trace (X * Y)) = 0 := by
  calc
    τ (Matrix.trace (X * Y)) = τ (Matrix.trace (Y * X)) :=
      Matrix.trace_mul_comm_of_addMonoidHom τ hcyc X Y
    _ = 0 := by simp [Matrix.trace, Matrix.mul_apply]

private theorem zero_trace_not_injective :
    ¬ Function.Injective (fun n : ℕ => n • (0 : ℚ →+ ℚ) (1 : ℚ)) := by
  intro hinj
  have h : (0 : ℕ) = 1 := hinj (by simp)
  exact Nat.zero_ne_one h

private theorem zero_target_not_injective :
    ¬ Function.Injective (fun n : ℕ =>
      n • (0 : ℚ →+ (Fin 0 → ℚ)) (1 : ℚ)) := by
  intro hinj
  have h : (0 : ℕ) = 1 := hinj (by funext i; exact Fin.elim0 i)
  exact Nat.zero_ne_one h

private theorem zero_ring_zero_trace_cyclic :
    ∀ x y : ZMod 1, (0 : ZMod 1 →+ ℚ) (x * y) = (0 : ZMod 1 →+ ℚ) (y * x) := by
  simp

private theorem zero_ring_zero_trace_not_injective :
    ¬ Function.Injective (fun n : ℕ => n • (0 : ZMod 1 →+ ℚ) (1 : ZMod 1)) := by
  intro hinj
  have h : (0 : ℕ) = 1 := hinj (by simp)
  exact Nat.zero_ne_one h

private theorem zero_ring_not_invariantBasisNumber : ¬ InvariantBasisNumber (ZMod 1) := by
  intro h
  exact (ZMod.nontrivial_iff.mp
    (@nontrivial_of_invariantBasisNumber (ZMod 1) _ h)) rfl

end ProjectiveModulesTests.CyclicTraceClient
