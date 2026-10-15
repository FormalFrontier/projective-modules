/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dual forms separate tensors of projective modules

For projective modules over a commutative semiring, products of dual forms separate
points of their tensor product. The factors may have arbitrary rank, and their
additive structures need only be commutative monoids.
-/

@[expose] public section

open scoped TensorProduct

universe uR uM uN

namespace TensorProduct

/-- A tensor of projective modules vanishes exactly when every rank-one product of
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
  constructor
  · intro h
    obtain ⟨sM, hsM⟩ :=
      Module.projective_def'.mp (inferInstance : Module.Projective R M)
    obtain ⟨sN, hsN⟩ :=
      Module.projective_def'.mp (inferInstance : Module.Projective R N)
    let bM : Module.Basis M R (M →₀ R) := Finsupp.basisSingleOne
    let bN : Module.Basis N R (N →₀ R) := Finsupp.basisSingleOne
    -- Tensor-basis coordinates are products of the two coordinate forms.
    have hcoord (i : M) (j : N) :
        ((bM.tensorProduct bN).coord (i, j)).comp (TensorProduct.map sM sN) =
          TensorProduct.dualDistrib R M N
            ((bM.coord i).comp sM ⊗ₜ[R] (bN.coord j).comp sN) := by
      apply TensorProduct.ext'
      intro m n
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, Module.Basis.coord_apply,
        Module.Basis.tensorProduct_repr_tmul_apply, TensorProduct.dualDistrib_apply,
        smul_eq_mul, mul_comm]
    have hzero : TensorProduct.map sM sN t = 0 := by
      apply (bM.tensorProduct bN).forall_coord_eq_zero_iff.mp
      rintro ⟨i, j⟩
      exact (LinearMap.congr_fun (hcoord i j) t).trans
        (h ((bM.coord i).comp sM) ((bN.coord j).comp sN))
    -- The two free-module splittings give a retraction on tensor products.
    calc
      t = TensorProduct.map (Finsupp.linearCombination R (id : M → M))
          (Finsupp.linearCombination R (id : N → N))
          (TensorProduct.map sM sN t) := by
        rw [TensorProduct.map_map, hsM, hsN, TensorProduct.map_id, LinearMap.id_apply]
      _ = 0 := by rw [hzero, map_zero]
  · intro ht f g
    rw [ht, map_zero]

end TensorProduct
