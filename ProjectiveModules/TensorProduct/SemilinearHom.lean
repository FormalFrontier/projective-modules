/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import ProjectiveModules.TensorProduct.RightModule

/-!
# Semilinear Hom and tensor products

`TensorProduct.semilinearHomTensorMap` is the canonical comparison for an
arbitrary source semiring and arbitrary right tensor factor. On pure tensors,
it sends `f ⊗ₜ[S] p` to the semilinear map `m ↦ f m ⊗ₜ[S] p`. Under Mathlib's
commutative-source hypotheses it agrees with `rTensorHomToHomRTensor`.

After evaluation at a source element, the comparison intertwines the chosen
right-factor actions `TensorProduct.rightModule` on its source tensor product
and on the output tensor product.
-/

@[expose] public section

universe uR uS uT uM uN uP

namespace TensorProduct

section Comparison

variable {R : Type uR} {S : Type uS}
variable [Semiring R] [CommSemiring S]
variable (σ : R →+* S)
variable {M : Type uM} {N : Type uN} {P : Type uP}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module S N] [Module S P]

/-- The canonical comparison from tensoring semilinear Hom to semilinear Hom
into a tensor product. The source semiring need not be commutative and the
right tensor factor is any base module. -/
def semilinearHomTensorMap :
    (M →ₛₗ[σ] N) ⊗[S] P →ₗ[S] (M →ₛₗ[σ] (N ⊗[S] P)) :=
  TensorProduct.lift
    { toFun := fun f =>
        (LinearMap.lcompₛₗ S (N ⊗[S] P) (RingHom.id S) f).comp
          (TensorProduct.mk S N P).flip
      map_add' := by
        intro f g
        ext p m
        simp
      map_smul' := by
        intro s f
        ext p m
        simp }

/-- Evaluation of the comparison on a pure tensor. -/
@[simp]
theorem semilinearHomTensorMap_tmul (f : M →ₛₗ[σ] N) (p : P) (m : M) :
    semilinearHomTensorMap σ (f ⊗ₜ[S] p) m = f m ⊗ₜ[S] p :=
  rfl

/-- After evaluation at any source element, the comparison intertwines the
chosen action `rightModule S T (M →ₛₗ[σ] N) P` on its source with the chosen
action `rightModule S T N P` on the output tensor. This evaluation formula
does not require a `T`-module structure on the semilinear-map carrier. -/
theorem semilinearHomTensorMap_rightModule_smul_apply
    {T : Type uT} [Semiring T] [Module T P] [SMulCommClass S T P]
    (t : T) (x : (M →ₛₗ[σ] N) ⊗[S] P) (m : M) :
    semilinearHomTensorMap σ
        (@SMul.smul T _ (rightModule S T (M →ₛₗ[σ] N) P).toSMul t x) m =
      @SMul.smul T _ (rightModule S T N P).toSMul t
        (semilinearHomTensorMap σ x m) := by
  induction x using TensorProduct.inductionOn with
  | tmul f p =>
      simp only [rightModule_smul_tmul, semilinearHomTensorMap_tmul]
  | add x y hx hy =>
      simp only [rightModule_smul_add, map_add, LinearMap.add_apply, hx, hy]

end Comparison

section CommutativeSource

variable {R : Type uR} {S : Type uS}
variable [CommSemiring R] [CommSemiring S]
variable (σ : R →+* S)
variable {M : Type uM} {N : Type uN} {P : Type uP}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module S N] [Module S P]

/-- The arbitrary-source comparison agrees with Mathlib's comparison when
the latter is available. -/
theorem semilinearHomTensorMap_eq_rTensorHomToHomRTensor :
    semilinearHomTensorMap (M := M) (N := N) (P := P) σ =
      rTensorHomToHomRTensor σ M N P := by
  ext f p
  rfl

end CommutativeSource

end TensorProduct
