/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Ring
public import ProjectiveModules.Module.PiTensorProduct
public import ProjectiveModules.TensorPower.Projective

/-!
# Classes of tensor powers

For a finite projective right module, the class of its tensor power is the
corresponding power of its class in K₀. The empty tensor product represents the
multiplicative unit, including when the input module is zero.
-/

@[expose] public section

open scoped TensorProduct

universe uR uM

namespace KTheory.K0

variable (R : Type uR) [CommRing R]
variable (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]

/-- The class of a tensor power is the corresponding power of the module class. -/
@[simp] theorem of_tensorPower (n : ℕ) :
    of R (TensorPower Rᵐᵒᵖ n M) = (of R M) ^ n := by
  induction n with
  | zero =>
      calc
        of R (TensorPower Rᵐᵒᵖ 0 M) = of R Rᵐᵒᵖ :=
          of_eq_of_equiv R _
            (PiTensorProduct.isEmptyEquiv (R := Rᵐᵒᵖ)
              (s := fun _ : Fin 0 => M) (Fin 0))
        _ = 1 := of_self R
        _ = (of R M) ^ 0 := (pow_zero _).symm
  | succ n ih =>
      calc
        of R (TensorPower Rᵐᵒᵖ (n + 1) M) =
            of R (TensorPower Rᵐᵒᵖ n M ⊗[Rᵐᵒᵖ] M) :=
          of_eq_of_equiv R _ (TensorPower.appendEquiv Rᵐᵒᵖ M n).symm
        _ = of R (TensorPower Rᵐᵒᵖ n M) * of R M :=
          (of_mul R (TensorPower Rᵐᵒᵖ n M) M).symm
        _ = (of R M) ^ n * of R M := by rw [ih]
        _ = (of R M) ^ (n + 1) := (pow_succ _ _).symm

end KTheory.K0
