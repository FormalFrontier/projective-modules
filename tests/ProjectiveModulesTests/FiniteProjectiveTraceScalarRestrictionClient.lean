/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.Trace.Prod
import Mathlib.Algebra.Algebra.Bilinear
import ProjectiveModules.Module.Trace.ScalarRestriction

/-!
# Diagonal endomorphisms over a product semiring

For `A = ℕ × ℕ` and `M = A × A`, the diagonal `A`-linear endomorphism with
weights `(2, 3)` and `(5, 7)` has `A`-trace `(7, 10)`. Multiplication on `A` by
`(7, 10)` has `ℕ`-trace `17`. These two traces are computed independently
using products and rank-one maps. The restriction-of-scalars identity then
shows that the diagonal endomorphism restricted to `ℕ` also has trace `17`.
Restriction retains its values on the same product module. The same identity
gives trace zero for the restricted zero endomorphism on this module. The
finite-free comparison recovers the algebra-element trace identity in the
integer product-ring tower `ℤ → ℤ × ℤ → (ℤ × ℤ) × (ℤ × ℤ)`.

## References

The rank-one calculation uses the contraction formalization by Oliver Nash
and Antoine Labelle in `Mathlib.LinearAlgebra.Contraction`. The product-map
interface is formalized by Johannes Hölzl, Mario Carneiro, Kevin Buzzard,
Yury Kudryashov and Eric Wieser in `Mathlib.LinearAlgebra.Prod`. Multiplication
as a linear map uses the formalization by Kenny Lau and Yury Kudryashov in
`Mathlib.Algebra.Algebra.Bilinear`. The restriction-of-scalars identity is
provided by `ProjectiveModules.Module.Trace.ScalarRestriction`.
-/

noncomputable section

namespace ProjectiveModulesTests.FiniteProjectiveTraceScalarRestrictionClient

private abbrev A := ℕ × ℕ
private abbrev M := A × A

private def towerDiagonal : M →ₗ[A] M :=
  LinearMap.prodMap (Algebra.lmul A A (2, 3)) (Algebra.lmul A A (5, 7))

private def towerDiagonalRestrict : M →ₗ[ℕ] M :=
  towerDiagonal.restrictScalars ℕ

private theorem towerDiagonal_apply (x y : A) :
    towerDiagonal (x, y) = ((2, 3) * x, (5, 7) * y) := by
  simp only [towerDiagonal, LinearMap.prodMap_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']

private theorem towerDiagonalRestrict_apply (x y : A) :
    towerDiagonalRestrict (x, y) = ((2, 3) * x, (5, 7) * y) := by
  simp only [towerDiagonalRestrict, LinearMap.restrictScalars_apply, towerDiagonal_apply]

private theorem trace_towerDiagonal :
    LinearMap.traceOfFiniteProjective A M towerDiagonal = (7, 10) := by
  have h₂ : Algebra.lmul A A (2, 3) =
      (LinearMap.id : A →ₗ[A] A).smulRight (2, 3) := by
    apply LinearMap.ext
    intro x
    change (2, 3) * x = x * (2, 3)
    exact mul_comm _ _
  have h₅ : Algebra.lmul A A (5, 7) =
      (LinearMap.id : A →ₗ[A] A).smulRight (5, 7) := by
    apply LinearMap.ext
    intro x
    change (5, 7) * x = x * (5, 7)
    exact mul_comm _ _
  change LinearMap.traceOfFiniteProjective A (A × A)
    (LinearMap.prodMap (Algebra.lmul A A (2, 3)) (Algebra.lmul A A (5, 7))) = (7, 10)
  rw [LinearMap.traceOfFiniteProjective_prodMap, h₂, h₅,
    LinearMap.traceOfFiniteProjective_smulRight, LinearMap.traceOfFiniteProjective_smulRight]
  rfl

private theorem trace_lmul_trace_towerDiagonal :
    LinearMap.traceOfFiniteProjective ℕ A (Algebra.lmul ℕ A (7, 10)) = 17 := by
  have hmul : Algebra.lmul ℕ A (7, 10) =
      LinearMap.prodMap
        ((LinearMap.id : ℕ →ₗ[ℕ] ℕ).smulRight 7)
        ((LinearMap.id : ℕ →ₗ[ℕ] ℕ).smulRight 10) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;>
      simp [Algebra.coe_lmul_eq_mul, LinearMap.prodMap_apply,
        LinearMap.smulRight_apply, smul_eq_mul, mul_comm]
  rw [hmul, LinearMap.traceOfFiniteProjective_prodMap,
    LinearMap.traceOfFiniteProjective_smulRight, LinearMap.traceOfFiniteProjective_smulRight]
  rfl

private theorem trace_towerDiagonalRestrict :
    LinearMap.traceOfFiniteProjective ℕ M towerDiagonalRestrict = 17 := by
  exact
    (LinearMap.traceOfFiniteProjective_restrictScalars ℕ A M towerDiagonal).trans
      (by rw [trace_towerDiagonal, trace_lmul_trace_towerDiagonal])

private theorem trace_zero_restrictScalars :
    LinearMap.traceOfFiniteProjective ℕ M
      ((0 : M →ₗ[A] M).restrictScalars ℕ) = 0 := by
  exact
    (LinearMap.traceOfFiniteProjective_restrictScalars ℕ A M
      (0 : M →ₗ[A] M)).trans (by simp)

private theorem algebraTrace_integerProductTower :
    Algebra.trace ℤ ((ℤ × ℤ) × (ℤ × ℤ)) ((2, 3), (5, 7)) =
      Algebra.trace ℤ (ℤ × ℤ)
        (Algebra.trace (ℤ × ℤ) ((ℤ × ℤ) × (ℤ × ℤ)) ((2, 3), (5, 7))) := by
  exact
    (LinearMap.traceOfFiniteProjective_restrictScalars_lmul_iff_trace_trace
      ℤ (ℤ × ℤ) ((ℤ × ℤ) × (ℤ × ℤ)) ((2, 3), (5, 7))).1
      (LinearMap.traceOfFiniteProjective_restrictScalars
        ℤ (ℤ × ℤ) ((ℤ × ℤ) × (ℤ × ℤ))
        (Algebra.lmul (ℤ × ℤ) ((ℤ × ℤ) × (ℤ × ℤ)) ((2, 3), (5, 7))))

end ProjectiveModulesTests.FiniteProjectiveTraceScalarRestrictionClient
