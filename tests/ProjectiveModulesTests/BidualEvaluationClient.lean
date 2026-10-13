/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules
public import Mathlib.LinearAlgebra.Pi

/-!
# Semiring and finite-product bidual evaluation

The natural-number regular module tests evaluation without additive inverses.
The scalar `2` changes a nonzero evaluated value. A two-coordinate module
supplies a nonzero coordinate evaluation, while the empty product checks that
no nonempty basis hypothesis is required. Inverse evaluation uses the
characteristic API rather than an unfolded inverse.

## References

The scalar actions, coordinate projections and finite-product module instances
are Mathlib's. Mixed-scalar evaluation is `LinearMap.flip` of the identity.
-/

namespace ProjectiveModulesTests.BidualEvaluationClient

example :
    LinearMap.flip (LinearMap.id :
      (ℕ →ₗ[ℕ] ℕ) →ₗ[ℕᵐᵒᵖ] (ℕ →ₗ[ℕ] ℕ)) 1
      (LinearMap.id : ℕ →ₗ[ℕ] ℕ) ≠ 0 := by
  exact Nat.one_ne_zero

example :
    ((2 : ℕ) • (LinearMap.flip (LinearMap.id :
      (ℕ →ₗ[ℕ] ℕ) →ₗ[ℕᵐᵒᵖ] (ℕ →ₗ[ℕ] ℕ)) 1))
      (LinearMap.id : ℕ →ₗ[ℕ] ℕ) = 2 := rfl

example :
    LinearMap.bidualEvalEquiv ℕ ℕ 1 (LinearMap.id : ℕ →ₗ[ℕ] ℕ) = 1 := by
  simp only [LinearMap.bidualEvalEquiv_apply, LinearMap.id_apply]

example :
    LinearMap.bidualEvalEquiv ℕ (Fin 2 → ℕ) (Pi.single 0 1)
      (LinearMap.proj 0) = 1 := by
  simp

example (Φ : (ℕ →ₗ[ℕ] ℕ) →ₗ[ℕᵐᵒᵖ] ℕ) :
    (LinearMap.id : ℕ →ₗ[ℕ] ℕ) ((LinearMap.bidualEvalEquiv ℕ ℕ).symm Φ) =
      Φ (LinearMap.id : ℕ →ₗ[ℕ] ℕ) :=
  LinearMap.apply_bidualEvalEquiv_symm ℕ ℕ Φ LinearMap.id

noncomputable example : (Fin 0 → ℕ) ≃ₗ[ℕ]
    (((Fin 0 → ℕ) →ₗ[ℕ] ℕ) →ₗ[ℕᵐᵒᵖ] ℕ) :=
  LinearMap.bidualEvalEquiv ℕ (Fin 0 → ℕ)

end ProjectiveModulesTests.BidualEvaluationClient
