/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Trace.Pi
public import Mathlib.LinearAlgebra.Matrix.ToLin

import Mathlib.Tactic.NormNum

/-!
# Computing a mixed three-coordinate trace over the natural numbers

The matrix with diagonal entries `(2, 3, 6)` and all six off-diagonal entries
`1` acts on the canonical module `Fin 3 → ℕ` through `Matrix.toLin'`.
The finite-dependent-product trace formula computes its finite-projective
trace as `11`: each coordinate endomorphism of the regular module has its
trace computed by the rank-one formula, and the resulting finite sum is
`2 + 3 + 6`.

No comparison with the finite-basis trace is needed. All module structures
are the usual pointwise structures over the commutative semiring `ℕ`.

## References

The matrix interface is from the Mathlib formalization by Johannes Hölzl,
Patrick Massot, Casper Putz, Anne Baanen and Antoine Labelle. Coordinate maps
are from the formalization by Johannes Hölzl, Mario Carneiro, Kevin Buzzard,
Yury Kudryashov and Eric Wieser. The rank-one formula uses the contraction
formalization by Oliver Nash and Antoine Labelle.
-/

noncomputable section

namespace ProjectiveModulesTests.FiniteProjectiveTracePiClient

private abbrev P := Fin 3 → ℕ

private def matrix : Matrix (Fin 3) (Fin 3) ℕ :=
  !![2, 1, 1; 1, 3, 1; 1, 1, 6]

private def F : P →ₗ[ℕ] P :=
  Matrix.toLin' matrix

private theorem trace_coordinate (i j : Fin 3) :
    LinearMap.traceOfFiniteProjective ℕ ℕ
      ((LinearMap.proj i : P →ₗ[ℕ] ℕ).comp
        (F.comp (@LinearMap.single ℕ (Fin 3) _ (fun _ => ℕ) _ _
          (Classical.decEq (Fin 3)) j))) = matrix i j := by
  let : DecidableEq (Fin 3) := Classical.decEq (Fin 3)
  have h :
      (LinearMap.proj i : P →ₗ[ℕ] ℕ).comp
        (F.comp (LinearMap.single ℕ (fun _ : Fin 3 => ℕ) j)) =
          (LinearMap.id : ℕ →ₗ[ℕ] ℕ).smulRight (matrix i j) := by
    apply LinearMap.ext
    intro n
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply,
      F, Matrix.toLin'_apply, Matrix.mulVec, dotProduct_single,
      LinearMap.smulRight_apply, LinearMap.id_apply, smul_eq_mul]
    exact mul_comm _ _
  rw [h, LinearMap.traceOfFiniteProjective_smulRight, LinearMap.id_apply]

/-- The dependent-product trace formula evaluates this mixed endomorphism to `11`. -/
private theorem trace_F : LinearMap.traceOfFiniteProjective ℕ P F = 11 := by
  rw [LinearMap.traceOfFiniteProjective_pi ℕ (fun _ : Fin 3 => ℕ) F,
    finsum_eq_sum_of_fintype]
  simp only [trace_coordinate]
  norm_num [matrix, Fin.sum_univ_succ]

example : LinearMap.traceOfFiniteProjective ℕ P F = 11 := trace_F

end ProjectiveModulesTests.FiniteProjectiveTracePiClient
