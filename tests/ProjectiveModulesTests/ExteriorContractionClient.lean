/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.ExteriorAlgebra.Contraction
import ProjectiveModules.ExteriorPower.Contraction
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# A unit-pairing contraction over the integers

The degree-one generator contracts to the nonzero scalar one. Cartan's identity
then gives a contracting identity for the same functional and generator.
-/

@[expose] public section

example :
    (1 : ExteriorAlgebra ℤ ℤ) ≠ 0 ∧
      ((exteriorPower.contractLeft 0 (LinearMap.id : Module.Dual ℤ ℤ)
        (exteriorPower.ιMulti ℤ 1 (fun _ => (1 : ℤ)))) : ExteriorAlgebra ℤ ℤ) = 1 ∧
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℤ ℤ))
        (LinearMap.id : Module.Dual ℤ ℤ)).comp
          (LinearMap.mulLeft ℤ (ExteriorAlgebra.ι ℤ 1)) +
        (LinearMap.mulLeft ℤ (ExteriorAlgebra.ι ℤ 1)).comp
          (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℤ ℤ))
            (LinearMap.id : Module.Dual ℤ ℤ)) =
        (LinearMap.id : ExteriorAlgebra ℤ ℤ →ₗ[ℤ] ExteriorAlgebra ℤ ℤ) := by
  refine ⟨one_ne_zero, ?_, ?_⟩
  · simp [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply]
  · apply CliffordAlgebra.contractLeft_comp_mulLeft_add_mulLeft_comp_of_eq_one
    rfl
