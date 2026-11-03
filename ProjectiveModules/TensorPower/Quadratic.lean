/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.TensorPower.BaseChange
import Mathlib.Tactic.FinCases

/-!
# Binary and indexed tensor squares

The binary tensor square of a module is linearly equivalent to its indexed second
tensor power. The equivalence uses the singleton tensor-product equivalence followed
by the append-one equivalence, and sends a pure tensor to the indexed pure tensor
with the same two entries.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe uR uM

namespace TensorPower

variable (R : Type uR) [CommSemiring R]
variable (M : Type uM) [AddCommMonoid M] [Module R M]

/-- The binary tensor square is the indexed second tensor power. -/
def tensorSquareEquiv : (M ⊗[R] M) ≃ₗ[R] (⨂[R]^2 M) :=
  let e1 : (⨂[R]^1 M) ≃ₗ[R] M :=
    PiTensorProduct.subsingletonEquiv (R := R) (0 : Fin 1)
  (TensorProduct.congr e1.symm (LinearEquiv.refl R M)).trans
    (TensorPower.appendEquiv R M 1)

/-- The binary/indexed comparison sends a pure binary tensor to the
corresponding indexed pure tensor. -/
@[simp] theorem tensorSquareEquiv_tmul (x y : M) :
    tensorSquareEquiv R M (x ⊗ₜ[R] y) =
      PiTensorProduct.tprod R ![x, y] := by
  let e1 : (⨂[R]^1 M) ≃ₗ[R] M :=
    PiTensorProduct.subsingletonEquiv (R := R) (0 : Fin 1)
  have he1 (z : M) : e1.symm z =
      PiTensorProduct.tprod R (fun _ : Fin 1 => z) := by
    apply e1.injective
    simp only [e1, LinearEquiv.apply_symm_apply,
      PiTensorProduct.subsingletonEquiv_apply_tprod]
  change (TensorPower.appendEquiv R M 1)
      ((TensorProduct.congr e1.symm (LinearEquiv.refl R M))
        (x ⊗ₜ[R] y)) = PiTensorProduct.tprod R ![x, y]
  rw [TensorProduct.congr_tmul]
  change (TensorPower.appendEquiv R M 1)
      (e1.symm x ⊗ₜ[R] y) = PiTensorProduct.tprod R ![x, y]
  rw [he1, TensorPower.appendEquiv_tprod]
  congr 1
  funext i
  fin_cases i
  · rfl
  · change (Fin.snoc (fun _ : Fin 1 => x) y : Fin 2 → M) (Fin.last 1) = y
    rw [Fin.snoc_last]

end TensorPower
