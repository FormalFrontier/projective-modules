/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import ProjectiveModules.Dual.TensorProduct

/-!
# Tensor products and dependent products

`TensorProduct.piRightHom_apply` describes each coordinate of Mathlib's comparison
`TensorProduct.piRightHom`. If the tensor factor is projective over the base semiring,
`TensorProduct.piRightHom_injective_of_projective` proves that this comparison is injective
for an arbitrary dependent family of modules. The auxiliary scalar semiring controls the
linearity of the comparison; projectivity is required only over the tensor-base semiring.

For a finite index type with `Fintype` and `DecidableEq` instances, Mathlib's existing
`TensorProduct.piRight` is an equivalence, and `TensorProduct.piRight_apply` identifies its
forward map with `TensorProduct.piRightHom`. This finite equivalence requires neither
projectivity nor finite generation of the tensor factor.

## References

The comparison, its pure-tensor formula and the finite-product equivalence are from Mathlib's
`Mathlib.LinearAlgebra.TensorProduct.Pi`, by Judith Ludwig and Christian Merten. The injectivity
proof uses the projective tensor family API of `ProjectiveModules.Dual.TensorProduct`.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

universe uR uS uP uI uB

/-- Each coordinate of the tensor-product comparison is obtained by tensoring the corresponding
projection with the identity on the first factor. -/
@[simp]
theorem piRightHom_apply
    (R : Type uR) (S : Type uS)
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    (P : Type uP) [AddCommMonoid P]
    [Module R P] [Module S P] [IsScalarTower R S P]
    {I : Type uI} (B : I → Type uB)
    [∀ i, AddCommMonoid (B i)] [∀ i, Module R (B i)]
    (x : P ⊗[R] (∀ i, B i)) (i : I) :
    TensorProduct.piRightHom R S P B x i =
      TensorProduct.map (LinearMap.id : P →ₗ[R] P) (LinearMap.proj i) x := by
  have h :
      (LinearMap.proj i : (∀ j, P ⊗[R] B j) →ₗ[R] P ⊗[R] B i).comp
          ((piRightHom R S P B).restrictScalars R) =
        TensorProduct.map (LinearMap.id : P →ₗ[R] P) (LinearMap.proj i) := by
    apply TensorProduct.ext'
    intro p b
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, piRightHom_tmul,
      LinearMap.proj_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  exact LinearMap.congr_fun h x

/-- Tensoring an arbitrary dependent product with a projective module gives an injective
comparison to the product of the tensor products. Projectivity is needed only over the
base semiring, not over the auxiliary semiring governing the comparison's linearity. -/
theorem piRightHom_injective_of_projective
    (R : Type uR) (S : Type uS)
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    (P : Type uP) [AddCommMonoid P]
    [Module R P] [Module S P] [IsScalarTower R S P]
    {I : Type uI} (B : I → Type uB)
    [∀ i, AddCommMonoid (B i)] [∀ i, Module R (B i)]
    [Module.Projective R P] :
    Function.Injective (TensorProduct.piRightHom R S P B) := by
  intro x y hxy
  apply (forall_map_id_left_apply_eq_iff_of_projective (R := R) (P := P)
    (fun i : I => (LinearMap.proj i : (∀ j, B j) →ₗ[R] B i))
    (fun _ _ h => funext h) x y).mp
  intro i
  simpa only [piRightHom_apply] using congrFun hxy i

end TensorProduct
