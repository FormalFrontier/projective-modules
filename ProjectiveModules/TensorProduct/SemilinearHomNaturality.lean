/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.TensorProduct.SemilinearHom

/-!
# Source naturality of the semilinear Hom–tensor comparison

Precomposition by a linear map commutes with the canonical comparison from
semilinear Hom tensored with a module to semilinear Hom into a tensor product.
The source semiring is arbitrary, and the two source modules may lie in
independent universes.
-/

@[expose] public section

universe uR uS uM uM' uN uP

namespace TensorProduct

variable {R : Type uR} {S : Type uS}
variable [Semiring R] [CommSemiring S]
variable (σ : R →+* S)
variable {M : Type uM} {M' : Type uM'} {N : Type uN} {P : Type uP}
variable [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module R M'] [Module S N] [Module S P]

/-- The semilinear Hom–tensor comparison commutes with precomposition in its source. -/
theorem semilinearHomTensorMap_natural_source (g : M' →ₗ[R] M) :
    (semilinearHomTensorMap (M := M') (N := N) (P := P) σ).comp
        ((LinearMap.lcompₛₗ S N σ g).rTensor P) =
      (LinearMap.lcompₛₗ S (N ⊗[S] P) σ g).comp
        (semilinearHomTensorMap (M := M) (N := N) (P := P) σ) := by
  apply TensorProduct.ext'
  intro f p
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul,
    semilinearHomTensorMap_tmul, LinearMap.lcompₛₗ_apply]

/-- Evaluation of source naturality at an arbitrary tensor and source element. -/
theorem semilinearHomTensorMap_natural_source_apply (g : M' →ₗ[R] M)
    (t : (M →ₛₗ[σ] N) ⊗[S] P) (m' : M') :
    semilinearHomTensorMap (M := M') (N := N) (P := P) σ
        ((LinearMap.lcompₛₗ S N σ g).rTensor P t) m' =
      semilinearHomTensorMap σ t (g m') := by
  exact congrArg
    (fun F : (M →ₛₗ[σ] N) ⊗[S] P →ₗ[S] (M' →ₛₗ[σ] (N ⊗[S] P)) => F t m')
    (semilinearHomTensorMap_natural_source (N := N) (P := P) σ g)

end TensorProduct
