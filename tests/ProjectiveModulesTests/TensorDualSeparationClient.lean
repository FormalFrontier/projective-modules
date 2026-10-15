/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Dual.TensorProduct

/-!
# Tensor dual separation with scalar submodules

For any scalar submodule `I : Submodule R R`, the tensor `1 ⊗ₜ[R] x` is nonzero
whenever `x : I` is nonzero, as witnessed by the left unitor. The scalar-submodule
separation theorem then shows that not all rank-one dual forms vanish on it,
without assuming that `I` is projective.

The identity dual forms on `ℕ` evaluate to `1` on `1 ⊗ₜ[ℕ] 1`, independently
establishing nonvanishing before using the two-projective separation theorem.
Every rank-one dual form vanishes on the zero tensor with a scalar-submodule
factor by linearity.
-/

open scoped TensorProduct

universe uR uM

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

theorem one_tmul_submodule_dual_separation
    (R : Type uR) [CommSemiring R] (I : Submodule R R)
    (x : I) (hx : x ≠ 0) :
    ((1 : R) ⊗ₜ[R] x) ≠ (0 : R ⊗[R] I) ∧
      ¬ (∀ f : Module.Dual R R, ∀ g : Module.Dual R I,
        TensorProduct.dualDistrib R R I (f ⊗ₜ[R] g) ((1 : R) ⊗ₜ[R] x) = 0) := by
  have ht : ((1 : R) ⊗ₜ[R] x) ≠ (0 : R ⊗[R] I) := by
    intro hzero
    apply hx
    have h := congrArg (TensorProduct.lid R I) hzero
    simpa only [TensorProduct.lid_tmul, one_smul, map_zero] using h
  refine ⟨ht, ?_⟩
  intro h
  exact ht ((TensorProduct.forall_dualDistrib_apply_eq_zero_iff_submodule
    R R I ((1 : R) ⊗ₜ[R] x)).mp h)

theorem dualDistrib_submodule_zero
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    (I : Submodule R R) :
    ∀ f : Module.Dual R M, ∀ g : Module.Dual R I,
      TensorProduct.dualDistrib R M I (f ⊗ₜ[R] g) (0 : M ⊗[R] I) = 0 := by
  intro f g
  exact map_zero _

end ProjectiveModulesTests
