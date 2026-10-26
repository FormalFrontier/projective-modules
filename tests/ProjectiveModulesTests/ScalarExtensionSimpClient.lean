/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.RightExtensionFree
import ProjectiveModules.KTheory.ScalarExtension

/-!
# Scalar-extension and representative simplification

Free-coordinate reassembly, regular-module classes, and projective-class
representatives simplify without restricting scalar rings to be commutative.
-/

universe uR uS uI uM

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

example (f : R →+* S) (ι : Type uI) [Fintype ι] [DecidableEq ι]
    (z : ModuleCat.RightExtension.Obj f (ι → R)) :
    ModuleCat.RightExtension.rightFreeFrom f ι
      (ModuleCat.RightExtension.rightFreeTo f ι z) = z := by
  simp

example (f : R →+* S) :
    KTheory.ProjectiveClass.map f (KTheory.ProjectiveClass.of R Rᵐᵒᵖ) =
      KTheory.ProjectiveClass.of S Sᵐᵒᵖ := by
  simp

example (f : R →+* S) :
    KTheory.K0.map f (KTheory.K0.of R Rᵐᵒᵖ) = KTheory.K0.of S Sᵐᵒᵖ := by
  simp

section

local instance (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    Module.Projective Rᵐᵒᵖ (Module.Finite.repr Rᵐᵒᵖ M) :=
  Module.Projective.of_equiv' (Module.Finite.reprEquiv Rᵐᵒᵖ M).symm

example (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    KTheory.ProjectiveClass.of R (Module.Finite.repr Rᵐᵒᵖ M) =
      KTheory.ProjectiveClass.of R M := by
  simp

end
