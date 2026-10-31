/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Algebra.Basic

/-!
# A module structure from the right tensor factor

`TensorProduct.rightModule` transports the stock left-factor module structure
through the tensor commutor. It is a non-instance: the usual tensor action may
act on the left factor, even when a different right-factor action is available.

For an algebra `T` over `S`, restriction of this right-factor `T`-action on
`N ⊗[S] T` agrees with the usual `S`-action by tensor balance. The agreement is
an equality of module structures, not a definitional equality.
-/

@[expose] public section

universe uR uS uT uN uP

namespace TensorProduct

section RightFactor

variable (S : Type uS) (T : Type uT) (N : Type uN) (P : Type uP)
variable [CommSemiring S] [Semiring T]
variable [AddCommMonoid N] [AddCommMonoid P]
variable [Module S N] [Module S P] [Module T P] [SMulCommClass S T P]

/-- The module structure on a tensor product obtained from the right factor.
It is transported from the stock left-factor action by the tensor commutor,
and is deliberately not a global instance. -/
@[instance_reducible]
def rightModule : Module T (N ⊗[S] P) :=
  (TensorProduct.comm S N P).toAddEquiv.module T

/-- The right-factor action on a pure tensor. -/
@[simp]
theorem rightModule_smul_tmul (t : T) (n : N) (p : P) :
    @SMul.smul T (N ⊗[S] P) (rightModule S T N P).toSMul t (n ⊗ₜ[S] p) =
      n ⊗ₜ[S] (t • p) := by
  change (TensorProduct.comm S N P).symm
    (t • (TensorProduct.comm S N P) (n ⊗ₜ[S] p)) = _
  simp only [TensorProduct.comm_tmul, smul_tmul', TensorProduct.comm_symm_tmul]

/-- The right-factor action distributes over tensor addition. -/
theorem rightModule_smul_add (t : T) (x y : N ⊗[S] P) :
    @SMul.smul T (N ⊗[S] P) (rightModule S T N P).toSMul t (x + y) =
      @SMul.smul T (N ⊗[S] P) (rightModule S T N P).toSMul t x +
        @SMul.smul T (N ⊗[S] P) (rightModule S T N P).toSMul t y := by
  exact @DistribMulAction.smul_add T (N ⊗[S] P) _ _
    (rightModule S T N P).toDistribMulAction t x y

end RightFactor

section Algebra

variable (S : Type uS) (T : Type uT) (N : Type uN)
variable [CommSemiring S] [Semiring T] [Algebra S T]
variable [AddCommMonoid N] [Module S N]

/-- Tensor balance identifies the restricted right-factor action with the
usual base action. -/
theorem rightModule_algebraMap_smul (s : S) (x : N ⊗[S] T) :
    @SMul.smul T (N ⊗[S] T) (rightModule S T N T).toSMul (algebraMap S T s) x =
      s • x := by
  let : Module T (N ⊗[S] T) := rightModule S T N T
  induction x using TensorProduct.inductionOn with
  | tmul n t =>
      rw [rightModule_smul_tmul]
      change n ⊗ₜ[S] (algebraMap S T s * t) = s • (n ⊗ₜ[S] t)
      rw [← Algebra.smul_def, tmul_smul]
  | add x y hx hy =>
      simpa only [rightModule_smul_add, _root_.smul_add] using congrArg₂ (· + ·) hx hy

/-- Restricting the chosen right-factor action along the algebra map gives
exactly the stock base module structure. -/
theorem rightModule_compHom :
    @Module.compHom (R := T) (S := S) (M := N ⊗[S] T)
      _ _ (rightModule S T N T) _ (algebraMap S T) =
      (inferInstance : Module S (N ⊗[S] T)) := by
  apply Module.ext'
  intro s x
  exact rightModule_algebraMap_smul S T N s x

variable {R : Type uR} [Semiring R]

/-- Only the image of the scalar homomorphism must commute with the
right-factor coefficient action. No commutativity of `T` is required. -/
theorem rightModule_compHom_smulCommClass (σ : R →+* S) :
    @SMulCommClass R T (N ⊗[S] T)
      (@Module.compHom (R := T) (S := R) (M := N ⊗[S] T)
        _ _ (rightModule S T N T) _ ((algebraMap S T).comp σ)).toSMul
      (rightModule S T N T).toSMul := by
  let : Module T (N ⊗[S] T) := rightModule S T N T
  let : Module R (N ⊗[S] T) :=
    Module.compHom (N ⊗[S] T) ((algebraMap S T).comp σ)
  refine ⟨fun r t x => ?_⟩
  change algebraMap S T (σ r) • (t • x) = t • (algebraMap S T (σ r) • x)
  rw [← mul_smul, ← mul_smul, Algebra.commutes (σ r) t]

end Algebra

end TensorProduct
