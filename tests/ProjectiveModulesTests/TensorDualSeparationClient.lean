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

The scalar model over `ℕ` instantiates point equality with one projective factor and
injective dual evaluation. The countably generated free model `ℕ →₀ ℕ` instantiates
the both-projective point-equality criterion. Coordinate forms distinguish the
basis tensors at `(0, 0)` and `(1, 0)` independently of the point-equality criterion.
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

/-- The scalar semimodule over `ℕ` satisfies the one-projective point-equality
hypotheses, and its tensor square has the independently witnessed nonzero point
`1 ⊗ₜ[ℕ] 1`. -/
theorem nat_tensor_point_equality_model :
    Module.Projective ℕ ℕ ∧
      Function.Injective (Module.Dual.eval ℕ ℕ) ∧
      (∀ t u : ℕ ⊗[ℕ] ℕ,
        (∀ f : Module.Dual ℕ ℕ, ∀ g : Module.Dual ℕ ℕ,
          TensorProduct.dualDistrib ℕ ℕ ℕ (f ⊗ₜ[ℕ] g) t =
            TensorProduct.dualDistrib ℕ ℕ ℕ (f ⊗ₜ[ℕ] g) u) ↔ t = u) ∧
      ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) ≠ (0 : ℕ ⊗[ℕ] ℕ) := by
  refine ⟨inferInstance, Module.eval_apply_injective ℕ (V := ℕ), ?_,
    nat_one_tmul_one_dual_separation.1⟩
  intro t u
  exact TensorProduct.forall_dualDistrib_apply_eq_iff_of_eval_injective
    ℕ ℕ ℕ (Module.eval_apply_injective ℕ (V := ℕ)) t u

/-- The standard countably generated free semimodule over `ℕ` satisfies the
both-projective point-equality hypotheses. Its basis tensors at `(0, 0)` and `(1, 0)`
are distinct by explicit coordinate evaluation, without using point equality. -/
theorem nat_finsupp_tensor_point_equality_model :
    Module.Projective ℕ (ℕ →₀ ℕ) ∧
      Function.Injective (Module.Dual.eval ℕ (ℕ →₀ ℕ)) ∧
      (∀ t u : (ℕ →₀ ℕ) ⊗[ℕ] (ℕ →₀ ℕ),
        (∀ f : Module.Dual ℕ (ℕ →₀ ℕ), ∀ g : Module.Dual ℕ (ℕ →₀ ℕ),
          TensorProduct.dualDistrib ℕ (ℕ →₀ ℕ) (ℕ →₀ ℕ) (f ⊗ₜ[ℕ] g) t =
            TensorProduct.dualDistrib ℕ (ℕ →₀ ℕ) (ℕ →₀ ℕ) (f ⊗ₜ[ℕ] g) u) ↔ t = u) ∧
      ((Finsupp.single 0 1 : ℕ →₀ ℕ) ⊗ₜ[ℕ] (Finsupp.single 0 1 : ℕ →₀ ℕ)) ≠
        ((Finsupp.single 1 1 : ℕ →₀ ℕ) ⊗ₜ[ℕ] (Finsupp.single 0 1 : ℕ →₀ ℕ)) := by
  have : Module.Projective ℕ (ℕ →₀ ℕ) :=
    Module.Projective.of_basis (Finsupp.basisSingleOne : Module.Basis ℕ ℕ (ℕ →₀ ℕ))
  have hpoints :
      ((Finsupp.single 0 1 : ℕ →₀ ℕ) ⊗ₜ[ℕ] (Finsupp.single 0 1 : ℕ →₀ ℕ)) ≠
        ((Finsupp.single 1 1 : ℕ →₀ ℕ) ⊗ₜ[ℕ] (Finsupp.single 0 1 : ℕ →₀ ℕ)) := by
    intro h
    have hcoord := congrArg
      (TensorProduct.dualDistrib ℕ (ℕ →₀ ℕ) (ℕ →₀ ℕ)
        ((Finsupp.lapply 0 : Module.Dual ℕ (ℕ →₀ ℕ)) ⊗ₜ[ℕ]
          (Finsupp.lapply 0 : Module.Dual ℕ (ℕ →₀ ℕ)))) h
    have hbad : (1 : ℕ) = 0 := by
      simp [TensorProduct.dualDistrib_apply, Finsupp.lapply_apply] at hcoord
    exact Nat.one_ne_zero hbad
  refine ⟨inferInstance, Module.eval_apply_injective ℕ (V := ℕ →₀ ℕ), ?_, hpoints⟩
  intro t u
  exact TensorProduct.forall_dualDistrib_apply_eq_iff ℕ (ℕ →₀ ℕ) (ℕ →₀ ℕ) t u

end ProjectiveModulesTests

namespace ProjectiveModulesTests.TensorHom


/-- A rank-one operator with Finsupp output has a unique tensor preimage,
without any projectivity assumption on its source. -/
private theorem tensorHom_rankOne_unique
    (M : Type uM) [AddCommMonoid M] [Module ℕ M]
    (φ : Module.Dual ℕ M) (n : ℕ →₀ ℕ)
    (t : Module.Dual ℕ M ⊗[ℕ] (ℕ →₀ ℕ))
    (h : ∀ m : M, dualTensorHom ℕ M (ℕ →₀ ℕ) t m = φ m • n) :
    t = φ ⊗ₜ[ℕ] n := by
  apply dualTensorHom_injective_of_projective_right ℕ M (ℕ →₀ ℕ)
  apply LinearMap.ext
  intro m
  rw [dualTensorHom_apply]
  exact h m

/-- The coordinate rank-one operator on the standard natural-number Finsupp
module is nonzero and has a unique tensor preimage. The nonzero tensor and
operator are established directly by evaluation. -/
private theorem nat_finsupp_rankOne_nonzero_unique :
    let φ : Module.Dual ℕ (ℕ →₀ ℕ) := Finsupp.lapply 0
    let n : ℕ →₀ ℕ := Finsupp.single 1 1
    let m : ℕ →₀ ℕ := Finsupp.single 0 1
    let t : Module.Dual ℕ (ℕ →₀ ℕ) ⊗[ℕ] (ℕ →₀ ℕ) := φ ⊗ₜ[ℕ] n
    dualTensorHom ℕ (ℕ →₀ ℕ) (ℕ →₀ ℕ) t m = n ∧
      dualTensorHom ℕ (ℕ →₀ ℕ) (ℕ →₀ ℕ) t ≠ 0 ∧ t ≠ 0 ∧
      ∀ t' : Module.Dual ℕ (ℕ →₀ ℕ) ⊗[ℕ] (ℕ →₀ ℕ),
        (∀ m' : ℕ →₀ ℕ,
          dualTensorHom ℕ (ℕ →₀ ℕ) (ℕ →₀ ℕ) t' m' = φ m' • n) → t' = t := by
  let φ : Module.Dual ℕ (ℕ →₀ ℕ) := Finsupp.lapply 0
  let n : ℕ →₀ ℕ := Finsupp.single 1 1
  let m : ℕ →₀ ℕ := Finsupp.single 0 1
  let t : Module.Dual ℕ (ℕ →₀ ℕ) ⊗[ℕ] (ℕ →₀ ℕ) := φ ⊗ₜ[ℕ] n
  have hEval : dualTensorHom ℕ (ℕ →₀ ℕ) (ℕ →₀ ℕ) t m = n := by
    simp only [t, φ, m, dualTensorHom_apply, Finsupp.lapply_apply,
      Finsupp.single_eq_same, one_smul]
  have hn : n ≠ 0 := Finsupp.single_ne_zero.mpr Nat.one_ne_zero
  have hImageNe : dualTensorHom ℕ (ℕ →₀ ℕ) (ℕ →₀ ℕ) t ≠ 0 := by
    intro hz
    apply hn
    calc
      n = dualTensorHom ℕ (ℕ →₀ ℕ) (ℕ →₀ ℕ) t m := hEval.symm
      _ = 0 := by rw [hz, LinearMap.zero_apply]
  have ht : t ≠ 0 := by
    intro hzero
    apply hImageNe
    rw [hzero, map_zero]
  refine ⟨hEval, hImageNe, ht, ?_⟩
  intro t' h
  exact tensorHom_rankOne_unique (ℕ →₀ ℕ) φ n t' h

end ProjectiveModulesTests.TensorHom
