/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Trace.Comparison
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A mixed three-coordinate endomorphism over the natural numbers

The canonical module `Fin 3 → ℕ` is finite free, hence projective. The matrix
with diagonal entries `(2, 3, 6)` and all six off-diagonal entries equal to `1`
defines an endomorphism with finite-projective trace `11`. This is computed
using finite-free comparison with the finite-basis trace and the standard
basis, over the commutative semiring `ℕ`.

Its three diagonal projected maps have traces `2`, `3` and `6`, as follows
independently from the rank-one trace formula on the regular module. Every
off-diagonal projected map takes `1` to `1` and is therefore nonzero. The
canonical addition has vectors without additive inverses.

## References

The matrix and finite-basis trace interfaces are from the Mathlib formalization
by Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen and Antoine Labelle.
The standard-basis and coordinate-map interfaces are from the formalization by
Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov and Eric Wieser.
The rank-one trace formula uses the contraction formalization by Oliver Nash
and Antoine Labelle.
-/

noncomputable section

namespace ProjectiveModulesTests.FiniteProjectiveTracePiNatClient

private abbrev P := Fin 3 → ℕ

private instance : Module.Finite ℕ P :=
  Module.Finite.of_basis (Pi.basisFun ℕ (Fin 3))

private instance : Module.Free ℕ P :=
  Module.Free.of_basis (Pi.basisFun ℕ (Fin 3))

private theorem finiteProjectivePi :
    Module.Finite ℕ P ∧ Module.Free ℕ P ∧ Module.Projective ℕ P :=
  ⟨inferInstance, inferInstance, Module.Projective.of_free⟩

private def matrix : Matrix (Fin 3) (Fin 3) ℕ :=
  !![2, 1, 1; 1, 3, 1; 1, 1, 6]

private def F : P →ₗ[ℕ] P :=
  Matrix.toLin' matrix

private theorem F_single_apply (i j : Fin 3) (n : ℕ) :
    F (Pi.single j n) i = matrix i j * n := by
  change Matrix.mulVec matrix (Pi.single j n) i = matrix i j * n
  exact dotProduct_single (matrix i) n j

private theorem standardMatrix :
    LinearMap.toMatrix (Pi.basisFun ℕ (Fin 3)) (Pi.basisFun ℕ (Fin 3)) F = matrix := by
  ext i j
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr ℕ (Fin 3),
    Pi.basisFun_apply, F_single_apply, mul_one]

private theorem matrix_offDiagonal (i j : Fin 3) (h : i ≠ j) :
    matrix i j = 1 := by
  fin_cases i <;> fin_cases j <;> norm_num [matrix] at *

private theorem trace_F : LinearMap.traceOfFiniteProjective ℕ P F = 11 := by
  calc
    LinearMap.traceOfFiniteProjective ℕ P F = Matrix.trace matrix := by
      rw [LinearMap.traceOfFiniteProjective_eq_trace,
        LinearMap.trace_eq_matrix_trace ℕ (Pi.basisFun ℕ (Fin 3)), standardMatrix]
    _ = 11 := by
      norm_num [Matrix.trace, Matrix.diag, matrix, Fin.sum_univ_succ]

private theorem projectedBlock_apply (i j : Fin 3) (n : ℕ) :
    ((LinearMap.proj i : P →ₗ[ℕ] ℕ).comp
      (F.comp (LinearMap.single ℕ (fun _ : Fin 3 => ℕ) j))) n =
        matrix i j * n := by
  exact F_single_apply i j n

private theorem projectedBlock_eq_rankOne (i j : Fin 3) :
    (LinearMap.proj i : P →ₗ[ℕ] ℕ).comp
      (F.comp (LinearMap.single ℕ (fun _ : Fin 3 => ℕ) j)) =
        (LinearMap.id : ℕ →ₗ[ℕ] ℕ).smulRight (matrix i j) := by
  apply LinearMap.ext
  intro n
  rw [projectedBlock_apply]
  simp only [LinearMap.smulRight_apply, LinearMap.id_apply, smul_eq_mul]
  exact mul_comm _ _

private theorem trace_projectedBlock (i j : Fin 3) :
    LinearMap.traceOfFiniteProjective ℕ ℕ
      ((LinearMap.proj i : P →ₗ[ℕ] ℕ).comp
        (F.comp (LinearMap.single ℕ (fun _ : Fin 3 => ℕ) j))) = matrix i j := by
  rw [projectedBlock_eq_rankOne, LinearMap.traceOfFiniteProjective_smulRight,
    LinearMap.id_apply]

private theorem trace_component_zero :
    LinearMap.traceOfFiniteProjective ℕ ℕ
      ((LinearMap.proj (0 : Fin 3) : P →ₗ[ℕ] ℕ).comp
        (F.comp (LinearMap.single ℕ (fun _ : Fin 3 => ℕ) 0))) = 2 := by
  simpa [matrix] using trace_projectedBlock (0 : Fin 3) 0

private theorem trace_component_one :
    LinearMap.traceOfFiniteProjective ℕ ℕ
      ((LinearMap.proj (1 : Fin 3) : P →ₗ[ℕ] ℕ).comp
        (F.comp (LinearMap.single ℕ (fun _ : Fin 3 => ℕ) 1))) = 3 := by
  simpa [matrix] using trace_projectedBlock (1 : Fin 3) 1

private theorem trace_component_two :
    LinearMap.traceOfFiniteProjective ℕ ℕ
      ((LinearMap.proj (2 : Fin 3) : P →ₗ[ℕ] ℕ).comp
        (F.comp (LinearMap.single ℕ (fun _ : Fin 3 => ℕ) 2))) = 6 := by
  simpa [matrix] using trace_projectedBlock (2 : Fin 3) 2

private theorem trace_F_eq_component_traces :
    LinearMap.traceOfFiniteProjective ℕ P F =
      LinearMap.traceOfFiniteProjective ℕ ℕ
        ((LinearMap.proj (0 : Fin 3) : P →ₗ[ℕ] ℕ).comp
          (F.comp (LinearMap.single ℕ (fun _ : Fin 3 => ℕ) 0))) +
      LinearMap.traceOfFiniteProjective ℕ ℕ
        ((LinearMap.proj (1 : Fin 3) : P →ₗ[ℕ] ℕ).comp
          (F.comp (LinearMap.single ℕ (fun _ : Fin 3 => ℕ) 1))) +
      LinearMap.traceOfFiniteProjective ℕ ℕ
        ((LinearMap.proj (2 : Fin 3) : P →ₗ[ℕ] ℕ).comp
          (F.comp (LinearMap.single ℕ (fun _ : Fin 3 => ℕ) 2))) := by
  norm_num only [trace_F, trace_component_zero, trace_component_one, trace_component_two]

private theorem offDiagonalBlock_apply_one (i j : Fin 3) (h : i ≠ j) :
    ((LinearMap.proj i : P →ₗ[ℕ] ℕ).comp
      (F.comp (LinearMap.single ℕ (fun _ : Fin 3 => ℕ) j))) 1 = 1 := by
  rw [projectedBlock_apply, matrix_offDiagonal i j h, mul_one]

private theorem offDiagonalBlock_ne_zero (i j : Fin 3) (h : i ≠ j) :
    (LinearMap.proj i : P →ₗ[ℕ] ℕ).comp
      (F.comp (LinearMap.single ℕ (fun _ : Fin 3 => ℕ) j)) ≠ 0 := by
  intro hz
  have hone := offDiagonalBlock_apply_one i j h
  rw [hz, LinearMap.zero_apply] at hone
  exact zero_ne_one hone

private theorem F_ne_zero : F ≠ 0 := by
  intro h
  have htrace : (0 : ℕ) = 11 := by
    simpa only [h, map_zero] using trace_F
  norm_num at htrace

private theorem nat_one_has_no_additive_inverse : ¬ ∃ n : ℕ, 1 + n = 0 := by
  rintro ⟨n, hn⟩
  norm_num at hn

private theorem basisVector_has_no_additive_inverse :
    ¬ ∃ x : P, Pi.single (0 : Fin 3) (1 : ℕ) + x = 0 := by
  rintro ⟨x, hx⟩
  apply nat_one_has_no_additive_inverse
  refine ⟨x 0, ?_⟩
  simpa using congrArg (fun y : P => y 0) hx

example : Module.Finite ℕ P ∧ Module.Free ℕ P ∧ Module.Projective ℕ P :=
  finiteProjectivePi

example : LinearMap.traceOfFiniteProjective ℕ P F = 11 := trace_F

example : F ≠ 0 := F_ne_zero

example : ∀ i j : Fin 3, i ≠ j →
    (LinearMap.proj i : P →ₗ[ℕ] ℕ).comp
      (F.comp (LinearMap.single ℕ (fun _ : Fin 3 => ℕ) j)) ≠ 0 :=
  offDiagonalBlock_ne_zero

example : ¬ ∃ x : P, Pi.single (0 : Fin 3) (1 : ℕ) + x = 0 :=
  basisVector_has_no_additive_inverse

end ProjectiveModulesTests.FiniteProjectiveTracePiNatClient
