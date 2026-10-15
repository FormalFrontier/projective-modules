/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Dual.TensorProduct

/-!
# Tensor dual separation over the natural numbers

The identity dual forms on the standard modules `ℕ` evaluate to `1` on `1 ⊗ₜ 1`.
This directly establishes that this tensor is nonzero, independently of the
separation criterion. The criterion then gives failure of universal vanishing.
Every rank-one dual form vanishes on the zero tensor by linearity.
-/

open scoped TensorProduct

namespace ProjectiveModulesTests

theorem nat_one_tmul_one_dual_separation :
    ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ≠ (0 : ℕ ⊗[ℕ] ℕ) ∧
      TensorProduct.dualDistrib ℕ ℕ ℕ
        ((LinearMap.id : Module.Dual ℕ ℕ) ⊗ₜ[ℕ] (LinearMap.id : Module.Dual ℕ ℕ))
        ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) = 1 ∧
      ¬ (∀ f : Module.Dual ℕ ℕ, ∀ g : Module.Dual ℕ ℕ,
        TensorProduct.dualDistrib ℕ ℕ ℕ (f ⊗ₜ[ℕ] g)
          ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) = 0) := by
  have hEval : TensorProduct.dualDistrib ℕ ℕ ℕ
      ((LinearMap.id : Module.Dual ℕ ℕ) ⊗ₜ[ℕ] (LinearMap.id : Module.Dual ℕ ℕ))
      ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) = 1 := by
    simp only [TensorProduct.dualDistrib_apply, LinearMap.id_apply, one_mul]
  have hEvalNe : TensorProduct.dualDistrib ℕ ℕ ℕ
      ((LinearMap.id : Module.Dual ℕ ℕ) ⊗ₜ[ℕ] (LinearMap.id : Module.Dual ℕ ℕ))
      ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ≠ 0 := by
    rw [hEval]
    exact Nat.one_ne_zero
  have ht : ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ≠ (0 : ℕ ⊗[ℕ] ℕ) := by
    intro hzero
    apply hEvalNe
    rw [hzero, map_zero]
  have hNotAll : ¬ (∀ f : Module.Dual ℕ ℕ, ∀ g : Module.Dual ℕ ℕ,
      TensorProduct.dualDistrib ℕ ℕ ℕ (f ⊗ₜ[ℕ] g)
        ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) = 0) := by
    intro h
    exact ht ((TensorProduct.forall_dualDistrib_apply_eq_zero_iff
      ℕ ℕ ℕ ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ))).mp h)
  exact ⟨ht, hEval, hNotAll⟩

theorem dualDistrib_nat_zero : ∀ f : Module.Dual ℕ ℕ, ∀ g : Module.Dual ℕ ℕ,
    TensorProduct.dualDistrib ℕ ℕ ℕ (f ⊗ₜ[ℕ] g) (0 : ℕ ⊗[ℕ] ℕ) = 0 := by
  intro f g
  exact map_zero _

end ProjectiveModulesTests
