/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Rank-one dual forms detect zero in tensors

Over a commutative semiring, products of linear forms detect zero in `M ⊗[R] N`
when `M` is projective and the canonical evaluation pairing `Module.Dual.eval R N`
is left-separating. The factors may have arbitrary rank, their additive structures
need only be commutative monoids, and the scalar and carrier universes are independent.
Left separation here means detection of zero, not separation of arbitrary pairs of
points in semimodules.

The two-projective criterion `TensorProduct.forall_dualDistrib_apply_eq_zero_iff`
is a corollary. The scalar-submodule application
`TensorProduct.forall_dualDistrib_apply_eq_zero_iff_submodule` applies to every
`I : Submodule R R`, including ideals, without assuming projectivity of `I`.

The proof generalizes the projective-factor splitting argument, using Mathlib's
projective splitting, finitely supported tensor coordinates and dual evaluation APIs.
-/

@[expose] public section

open scoped TensorProduct

universe uR uM uN

namespace TensorProduct

/-- A tensor with projective first factor vanishes exactly when every rank-one product
of linear forms vanishes on it, provided the canonical dual evaluation on the second
factor detects zero. No finite-generation or second-factor projectivity is required. -/
theorem forall_dualDistrib_apply_eq_zero_iff_of_eval_separatingLeft
    (R : Type uR) [CommSemiring R]
    (M : Type uM) (N : Type uN)
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    [Module.Projective R M]
    (hN : (Module.Dual.eval R N).SeparatingLeft)
    (t : M ⊗[R] N) :
    (∀ f : Module.Dual R M, ∀ g : Module.Dual R N,
      TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) t = 0) ↔ t = 0 := by
  constructor
  · intro h
    classical
    obtain ⟨sM, hsM⟩ :=
      Module.projective_def'.mp (inferInstance : Module.Projective R M)
    -- Testing an N-valued coordinate gives a product with a pulled-back coordinate form.
    have hcoord (i : M) (g : Module.Dual R N) :
        g.comp ((Finsupp.lapply i).comp
            ((TensorProduct.finsuppScalarLeft R N M).toLinearMap.comp (sM.rTensor N))) =
          TensorProduct.dualDistrib R M N ((Finsupp.lapply i).comp sM ⊗ₜ[R] g) := by
      apply TensorProduct.ext'
      intro m n
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
        Finsupp.lapply_apply, TensorProduct.finsuppScalarLeft_apply_tmul_apply, map_smul,
        TensorProduct.dualDistrib_apply, smul_eq_mul]
    have hzero : sM.rTensor N t = 0 := by
      apply (TensorProduct.finsuppScalarLeft R N M).map_eq_zero_iff.mp
      apply Finsupp.ext
      intro i
      change TensorProduct.finsuppScalarLeft R N M (sM.rTensor N t) i = 0
      apply hN
      intro g
      exact (LinearMap.congr_fun (hcoord i g) t).trans (h ((Finsupp.lapply i).comp sM) g)
    -- Tensoring the sole projective splitting with the identity gives a retraction.
    calc
      t = (Finsupp.linearCombination R (id : M → M)).rTensor N (sM.rTensor N t) := by
        rw [← LinearMap.rTensor_comp_apply, hsM, LinearMap.rTensor_id, LinearMap.id_apply]
      _ = 0 := by rw [hzero, map_zero]
  · intro ht f g
    rw [ht, map_zero]

/-- A tensor of two projective modules vanishes exactly when every rank-one product of
linear forms vanishes on it. No finite-generation assumption is required. -/
theorem forall_dualDistrib_apply_eq_zero_iff
    (R : Type uR) [CommSemiring R]
    (M : Type uM) (N : Type uN)
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    [Module.Projective R M] [Module.Projective R N]
    (t : M ⊗[R] N) :
    (∀ f : Module.Dual R M, ∀ g : Module.Dual R N,
      TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) t = 0) ↔ t = 0 := by
  exact forall_dualDistrib_apply_eq_zero_iff_of_eval_separatingLeft R M N
    LinearMap.SeparatingLeft.eval t

/-- Products of linear forms detect zero in the tensor product of a projective module
with any scalar submodule. No projectivity of the scalar submodule is assumed. -/
theorem forall_dualDistrib_apply_eq_zero_iff_submodule
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    [Module.Projective R M]
    (I : Submodule R R) (t : M ⊗[R] I) :
    (∀ f : Module.Dual R M, ∀ g : Module.Dual R I,
      TensorProduct.dualDistrib R M I (f ⊗ₜ[R] g) t = 0) ↔ t = 0 := by
  exact forall_dualDistrib_apply_eq_zero_iff_of_eval_separatingLeft R M I
    (fun x hx => Subtype.ext (hx I.subtype)) t

end TensorProduct
