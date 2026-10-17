/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.TensorProduct
import ProjectiveModules.KTheory.Rank
import ProjectiveModules.KTheory.ZeroRing
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Ring.PUnit
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Tensor products of regular projective classes

The rational regular class tensors with itself to give the same class, whose
dimension proves it is nonzero. Over the one-element scalar ring the tensor
class is zero, using this library's zero-ring class API. The tensor comparison
is Mathlib's left unit equivalence.
-/

public section

namespace KTheory.ProjectiveClass

example :
    tensorMul ℚ (of ℚ ℚᵐᵒᵖ) (of ℚ ℚᵐᵒᵖ) = of ℚ ℚᵐᵒᵖ ∧
      of ℚ ℚᵐᵒᵖ ≠ 0 := by
  constructor
  · rw [tensorMul_of_module]
    exact of_eq_of_equiv ℚ _ (TensorProduct.lid ℚᵐᵒᵖ ℚᵐᵒᵖ)
  · intro h
    have h' : (1 : ℕ) = 0 := by
      simpa only [finrankHom_of_self, map_zero] using congrArg (finrankHom ℚ) h
    exact one_ne_zero h'

section

attribute [local instance] Module.Finite.of_finite

example :
    tensorMul PUnit.{1} (of PUnit.{1} PUnit.{1}ᵐᵒᵖ)
      (of PUnit.{1} PUnit.{1}ᵐᵒᵖ) = 0 := by
  rw [tensorMul_of_module, of_eq_zero_of_subsingleton]

end

end KTheory.ProjectiveClass
