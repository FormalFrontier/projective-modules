/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.LinearAlgebra.Basis.VectorSpace
import ProjectiveModules.TensorProduct.Submodule

/-!
# Tensor membership in the first coordinate line

The two coordinate projections on `Fin 2 → k` jointly detect zero, although neither
is injective. For the proper nonzero first coordinate line, tensor-image membership
is equivalent to the vanishing of the second coordinate of both columns, computed
using the right unitor. The quotient is a vector space, hence projective.
-/

open scoped TensorProduct

universe uR uV uK

namespace ProjectiveModulesTests

private theorem mem_range_subtype_rTensor_iff_rid
    {R : Type uR} [CommSemiring R]
    {V : Type uV} [AddCommMonoid V] [Module R V]
    (W : Submodule R V) (t : V ⊗[R] R) :
    t ∈ LinearMap.range (W.subtype.rTensor R) ↔ TensorProduct.rid R V t ∈ W := by
  have hnat :
      (TensorProduct.rid R V).toLinearMap.comp (W.subtype.rTensor R) =
        W.subtype.comp (TensorProduct.rid R W).toLinearMap := by
    apply TensorProduct.ext'
    intro w r
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
      TensorProduct.rid_tmul, LinearMap.map_smul]
  constructor
  · intro ht
    obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp ht
    have hs : TensorProduct.rid R V (W.subtype.rTensor R s) =
        (TensorProduct.rid R W s : V) := LinearMap.congr_fun hnat s
    exact hs.symm ▸ (TensorProduct.rid R W s).property
  · intro ht
    refine LinearMap.mem_range.mpr
      ⟨(TensorProduct.rid R W).symm ⟨TensorProduct.rid R V t, ht⟩, ?_⟩
    apply (TensorProduct.rid R V).injective
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, Submodule.subtype_apply] using
      LinearMap.congr_fun hnat
        ((TensorProduct.rid R W).symm ⟨TensorProduct.rid R V t, ht⟩)

example (k : Type uK) [Field k] (x : (Fin 2 → k) ⊗[k] (Fin 2 → k)) :
    x ∈ LinearMap.range
      ((LinearMap.ker (LinearMap.proj (1 : Fin 2) : (Fin 2 → k) →ₗ[k] k)).subtype.rTensor
        (Fin 2 → k)) ↔
      ∀ i : Fin 2,
        (TensorProduct.rid k (Fin 2 → k)
          (TensorProduct.map (LinearMap.id : (Fin 2 → k) →ₗ[k] (Fin 2 → k))
            (LinearMap.proj i : (Fin 2 → k) →ₗ[k] k) x)) 1 = 0 := by
  have hf : ∀ a : Fin 2 → k,
      (∀ i : Fin 2, (LinearMap.proj i : (Fin 2 → k) →ₗ[k] k) a = 0) → a = 0 := by
    intro a ha
    funext i
    exact ha i
  simpa only [mem_range_subtype_rTensor_iff_rid, LinearMap.mem_ker,
    LinearMap.proj_apply] using
    (Submodule.mem_range_subtype_rTensor_iff_of_projective
      (LinearMap.ker (LinearMap.proj (1 : Fin 2) : (Fin 2 → k) →ₗ[k] k))
      (fun i : Fin 2 => (LinearMap.proj i : (Fin 2 → k) →ₗ[k] k)) hf x)

end ProjectiveModulesTests
