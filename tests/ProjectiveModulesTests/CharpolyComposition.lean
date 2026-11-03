/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.LinearAlgebra.Charpoly.Composition
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Matrix characteristic polynomials from composition formulas

The intrinsic composition formula recovers Mathlib's rectangular identity
`Matrix.charpoly_mul_comm'` over an arbitrary commutative ring. Its rank-one
consequence similarly recovers `Matrix.charpoly_vecMulVec`, including empty
index types. Only the polynomial indeterminate is cancelled in the latter
comparison.

## References

The matrix statements and finite-free comparison API are from Mathlib's
`LinearAlgebra.Matrix.Charpoly.Basic` and `LinearAlgebra.Charpoly.ToMatrix`.
-/

open Matrix Polynomial

universe u v w

namespace Matrix

variable {R : Type u} [CommRing R]
variable {m : Type v} {n : Type w}
variable [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

private theorem charpoly_toLin'_intrinsic (A : Matrix n n R) :
    Module.charpoly R (n → R) A.toLin' = A.charpoly := by
  rw [Module.charpoly_eq_charpoly, Matrix.charpoly_toLin']

/-- The intrinsic composition identity specializes to `Matrix.charpoly_mul_comm'`
with its original independent index types and commutative-ring hypotheses. -/
private theorem charpoly_mul_comm'_of_charpoly_comp
    (A : Matrix m n R) (B : Matrix n m R) :
    X ^ Fintype.card n * (A * B).charpoly =
      X ^ Fintype.card m * (B * A).charpoly := by
  have hm := charpoly_toLin'_intrinsic (0 : Matrix m m R)
  have hn := charpoly_toLin'_intrinsic (0 : Matrix n n R)
  simp only [map_zero, Matrix.charpoly_zero] at hm hn
  have h := Module.charpoly_comp_mul_charpoly_zero R (m → R) (n → R)
    B.toLin' A.toLin'
  simp only [← Matrix.toLin'_mul, charpoly_toLin'_intrinsic, hm, hn] at h
  simpa only [mul_comm] using h

/-- The intrinsic rank-one formula specializes to `Matrix.charpoly_vecMulVec`.
The empty case is separate; otherwise cancellation uses only regularity of `X`. -/
private theorem charpoly_vecMulVec_of_charpoly_smulRight (u v : n → R) :
    (vecMulVec u v).charpoly =
      X ^ Fintype.card n - (u ⬝ᵥ v) • X ^ (Fintype.card n - 1) := by
  cases isEmpty_or_nonempty n
  · simp
  · have hcard : 1 ≤ Fintype.card n := NeZero.one_le
    let φ : Module.Dual R (n → R) := (dotProductBilin R R).flip v
    have hφ : φ.smulRight u = (vecMulVec u v).toLin' := by
      ext z i
      simp [φ, dotProductBilin, Matrix.toLin'_apply,
        Matrix.mulVec, dotProduct, vecMulVec, Finset.mul_sum,
        mul_comm, mul_assoc]
    have hzero := charpoly_toLin'_intrinsic (0 : Matrix n n R)
    simp only [map_zero, Matrix.charpoly_zero] at hzero
    have h := Module.charpoly_smulRight_mul_X R (n → R) φ u
    rw [hφ, charpoly_toLin'_intrinsic, hzero] at h
    change (vecMulVec u v).charpoly * X =
      X ^ Fintype.card n * (X - C (u ⬝ᵥ v)) at h
    have hpow : (X : R[X]) ^ (Fintype.card n - 1) * X =
        X ^ Fintype.card n := by
      rw [← pow_succ, Nat.sub_add_cancel hcard]
    apply (isRegular_X (R := R)).right.eq_iff.mp
    calc
      (vecMulVec u v).charpoly * X =
          X ^ Fintype.card n * (X - C (u ⬝ᵥ v)) := h
      _ = (X ^ Fintype.card n - (u ⬝ᵥ v) • X ^ (Fintype.card n - 1)) * X := by
        rw [smul_eq_C_mul, sub_mul, mul_assoc, hpow]
        ring

end Matrix
