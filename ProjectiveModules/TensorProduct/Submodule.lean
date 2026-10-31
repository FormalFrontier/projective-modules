/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Dual.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tensor-image membership detected by a family of maps

Let `W` be a submodule of `V` with projective quotient `V ⧸ W`. A jointly
zero-detecting family `f i : A →ₗ[R] B i` detects membership in the image of
`W ⊗[R] A → V ⊗[R] A`: a tensor belongs to this image if and only if all its
images under `TensorProduct.map LinearMap.id (f i)` belong to the corresponding
images of `W ⊗[R] B i`. The source and dependent targets of the family are
arbitrary modules, and the index type need not be finite or nonempty.

The proof uses the canonical quotient map `W.mkQ`, tensor right exactness,
naturality and projective-factor zero detection. The image is also expressed
as the infimum of the comaps of the target images.

## References

- Mathlib's tensor right-exactness formalization by Antoine Chambert-Loir
  (`Mathlib.LinearAlgebra.TensorProduct.RightExactness`).
- Mathlib's tensor-map formalization by Kenny Lau and Mario Carneiro
  (`Mathlib.LinearAlgebra.TensorProduct.Map`).
- Projective Modules' projective-factor tensor-family zero detection
  (`ProjectiveModules.Dual.TensorProduct`).
-/

@[expose] public section

open scoped TensorProduct

universe uR uV uA uI uB

variable {R : Type uR} [CommRing R]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {A : Type uA} [AddCommGroup A] [Module R A]
  {I : Type uI} {B : I → Type uB}
  [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]

/-- A jointly zero-detecting family detects membership in the tensor image of a
submodule whose quotient is projective. Only the quotient `V ⧸ W` is assumed
projective. This combines Mathlib's tensor right exactness with projective-factor
tensor-family zero detection. -/
theorem Submodule.mem_range_subtype_rTensor_iff_of_projective
    (W : Submodule R V) [Module.Projective R (V ⧸ W)]
    (f : ∀ i, A →ₗ[R] B i)
    (hf : ∀ a : A, (∀ i, f i a = 0) → a = 0)
    (x : V ⊗[R] A) :
    x ∈ LinearMap.range (W.subtype.rTensor A) ↔
      ∀ i, TensorProduct.map (LinearMap.id : V →ₗ[R] V) (f i) x ∈
        LinearMap.range (W.subtype.rTensor (B i)) := by
  simp_rw [← rTensor_mkQ, LinearMap.mem_ker, LinearMap.rTensor_map,
    LinearMap.comp_id]
  simpa only [LinearMap.map_rTensor, LinearMap.id_comp] using
    (TensorProduct.forall_map_id_left_apply_eq_zero_iff_of_projective
      (V ⧸ W) f hf (W.mkQ.rTensor A x)).symm

/-- The tensor image of a submodule with projective quotient is the infimum of
the comaps of its tensor images along a jointly zero-detecting family. This is
the submodule equality corresponding to
`Submodule.mem_range_subtype_rTensor_iff_of_projective`. -/
theorem Submodule.range_subtype_rTensor_eq_iInf_comap_of_projective
    (W : Submodule R V) [Module.Projective R (V ⧸ W)]
    (f : ∀ i, A →ₗ[R] B i)
    (hf : ∀ a : A, (∀ i, f i a = 0) → a = 0) :
    LinearMap.range (W.subtype.rTensor A) =
      ⨅ i, (LinearMap.range (W.subtype.rTensor (B i))).comap
        (TensorProduct.map (LinearMap.id : V →ₗ[R] V) (f i)) := by
  ext x
  simpa only [Submodule.mem_iInf, Submodule.mem_comap] using
    W.mem_range_subtype_rTensor_iff_of_projective f hf x
