/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.SemisimpleRegularClass
public import Mathlib.Algebra.Module.Equiv.Opposite

/-!
# Regular module carriers

The opposite-ring-linear op/unop equivalence preserves the regular class and its
integer multiples.
-/

@[expose] public section

universe u

namespace ProjectiveModulesTests

open KTheory KTheory.K0

/-- Op/unop preserves integer multiples of the regular module class. -/
theorem regularClass_integer_multiples (R : Type u) [Ring R] (n : ℤ) :
    zmultiplesHom (K0 R) (of R Rᵐᵒᵖ) n = n • of R R := by
  let e : Rᵐᵒᵖ ≃ₗ[Rᵐᵒᵖ] R := (MulOpposite.opLinearEquiv (Rᵐᵒᵖ)).symm
  have hregular : of R Rᵐᵒᵖ = of R R := by
    apply KTheory.K0.of_eq_of_equiv
    exact e
  exact congrArg (fun x : K0 R => n • x) hregular

end ProjectiveModulesTests
