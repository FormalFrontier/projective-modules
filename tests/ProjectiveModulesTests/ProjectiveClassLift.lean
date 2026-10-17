/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.Rank
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Module.PUnit

/-!
# Function descent on projective module classes

Dimension detects the rational regular-module class. Over the zero ring, the
predicate of being isomorphic to the zero module descends to the zero class
without any additive structure on the target. These examples use this library's
finite-projective representatives and dimension map, and Mathlib's linear equivalences.
-/

public section

namespace KTheory.ProjectiveClass

example :
    liftFunction ℚ
      (fun X : ModuleCat.FiniteProjective.{0, 0} ℚᵐᵒᵖ ↦ Module.finrank ℚᵐᵒᵖ X)
      (fun e ↦ (ModuleCat.FiniteProjective.isoToLinearEquiv e).finrank_eq)
      (of ℚ ℚᵐᵒᵖ) = 1 := by
  have h := liftFunction_unique ℚ
    (fun X : ModuleCat.FiniteProjective.{0, 0} ℚᵐᵒᵖ ↦ Module.finrank ℚᵐᵒᵖ X)
    (fun e ↦ (ModuleCat.FiniteProjective.isoToLinearEquiv e).finrank_eq)
    (finrankHom ℚ) (finrankHom_of ℚ)
  exact (congrFun h (of ℚ ℚᵐᵒᵖ)).symm.trans (finrankHom_of_self ℚ)

example :
    liftFunction PUnit.{1}
      (fun X : ModuleCat.FiniteProjective.{0, 0} PUnit.{1}ᵐᵒᵖ ↦
        Nonempty (X ≃ₗ[PUnit.{1}ᵐᵒᵖ] PUnit.{1}))
      (fun e ↦ propext
        ⟨fun ⟨g⟩ ↦ ⟨(ModuleCat.FiniteProjective.isoToLinearEquiv e).symm.trans g⟩,
          fun ⟨g⟩ ↦ ⟨(ModuleCat.FiniteProjective.isoToLinearEquiv e).trans g⟩⟩)
      0 := by
  letI : Module.Finite PUnit.{1}ᵐᵒᵖ PUnit.{1} := Module.Finite.of_finite
  rw [← of_zero PUnit.{1} PUnit.{1},
    liftFunction_of_module PUnit.{1} PUnit.{1}
      (fun X : ModuleCat.FiniteProjective.{0, 0} PUnit.{1}ᵐᵒᵖ ↦
        Nonempty (X ≃ₗ[PUnit.{1}ᵐᵒᵖ] PUnit.{1}))
      (fun e ↦ propext
        ⟨fun ⟨g⟩ ↦ ⟨(ModuleCat.FiniteProjective.isoToLinearEquiv e).symm.trans g⟩,
          fun ⟨g⟩ ↦ ⟨(ModuleCat.FiniteProjective.isoToLinearEquiv e).trans g⟩⟩)]
  exact ⟨ModuleCat.FiniteProjective.reprEquiv PUnit.{1}ᵐᵒᵖ PUnit.{1}⟩

end KTheory.ProjectiveClass
