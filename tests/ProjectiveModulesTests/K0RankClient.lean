/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Rank

/-!
# Clients of the dimension maps on right-module K₀

The scalar-self regular module over a division ring has dimension one, its
binary direct sum has dimension two, and the zero module has dimension zero.
Independent carrier lifts leave these computations unchanged. The integer
map also evaluates negative generators and differences, so it is not merely
a natural-valued invariant on positive generators.

The examples use only the public class, completion and dimension APIs. The
module formulas allow arbitrary carrier universes and obtain projectivity
from the division-ring instances.
-/

@[expose] public section

universe u v w

open KTheory

namespace ProjectiveModulesTests.K0RankClient

variable (K : Type u) [DivisionRing K]

-- The regular right module, zero space and plane have distinct dimensions.
example : ProjectiveClass.finrankHom K (ProjectiveClass.of K Kᵐᵒᵖ) = 1 := by
  simp

example : ProjectiveClass.finrankHom K (ProjectiveClass.of K PUnit.{v + 1}) = 0 := by
  simp

example :
    ProjectiveClass.finrankHom K (ProjectiveClass.of K (Kᵐᵒᵖ × Kᵐᵒᵖ)) = 2 := by
  simp

example :
    ProjectiveClass.finrankHom K (ProjectiveClass.of K (ULift.{v} Kᵐᵒᵖ)) = 1 := by
  simp

example :
    ProjectiveClass.finrankHom K
      (ProjectiveClass.of K (ULift.{v} Kᵐᵒᵖ × PUnit.{w + 1})) = 1 := by
  simp

example : K0.finrankHom K (K0.of K Kᵐᵒᵖ) = 1 := by
  simp

example : K0.finrankHom K (K0.of K PUnit.{v + 1}) = 0 := by
  simp

example : K0.finrankHom K (K0.of K (Kᵐᵒᵖ × Kᵐᵒᵖ)) = 2 := by
  simp

example : K0.finrankHom K (K0.of K (ULift.{v} Kᵐᵒᵖ)) = 1 := by
  simp

example : K0.finrankHom K (-(K0.of K Kᵐᵒᵖ)) = -1 := by
  simp

-- Subtraction is evaluated by the group homomorphism, not by a class quotient.
example :
    K0.finrankHom K
      (K0.of K (ULift.{v} Kᵐᵒᵖ × ULift.{w} Kᵐᵒᵖ) - K0.of K Kᵐᵒᵖ) = 1 := by
  rw [map_sub]
  simp

example (a : ProjectiveClass K) :
    K0.finrankHom K (K0.ofClass K a - K0.of K Kᵐᵒᵖ) =
      (ProjectiveClass.finrankHom K a : ℤ) - 1 := by
  rw [map_sub, K0.finrankHom_ofClass, K0.finrankHom_of_self]

-- The universal extension agrees with the dimension map on negative inputs.
example :
    K0.lift K ((Int.ofNatHom : ℕ →+ ℤ).comp (ProjectiveClass.finrankHom K))
      (-(K0.of K (ULift.{v} Kᵐᵒᵖ))) = -1 := by
  rw [← K0.finrankHom_eq_lift]
  simp

-- Reference objects retain module dimension as the simp normal form.
example (X : ModuleCat.FiniteProjective.{u, u} Kᵐᵒᵖ) :
    ProjectiveClass.finrankHom K (ProjectiveClass.of K (X × PUnit.{v + 1})) =
      Module.finrank Kᵐᵒᵖ X := by
  simp

example (X : ModuleCat.FiniteProjective.{u, u} Kᵐᵒᵖ) :
    K0.finrankHom K (K0.of K (X × PUnit.{v + 1})) =
      (Module.finrank Kᵐᵒᵖ X : ℤ) := by
  simp

section FiniteModules

variable (M : Type v) (N : Type w)
  [AddCommGroup M] [Module Kᵐᵒᵖ M] [Module.Finite Kᵐᵒᵖ M]
  [AddCommGroup N] [Module Kᵐᵒᵖ N] [Module.Finite Kᵐᵒᵖ N]

-- These modules need not be bundled reference objects or share a carrier universe.
example :
    ProjectiveClass.finrankHom K
      (ProjectiveClass.of K (ULift.{w} M × (N × PUnit.{u + 1}))) =
        Module.finrank Kᵐᵒᵖ M + Module.finrank Kᵐᵒᵖ N := by
  simp only [ProjectiveClass.of_prod, ProjectiveClass.of_ulift,
    ProjectiveClass.of_zero, map_add, add_zero,
    ProjectiveClass.finrankHom_of_module]

example :
    K0.finrankHom K (K0.of K (ULift.{w} M × (N × PUnit.{u + 1}))) =
      (Module.finrank Kᵐᵒᵖ M : ℤ) + (Module.finrank Kᵐᵒᵖ N : ℤ) := by
  simp only [K0.of_prod, K0.of_ulift, K0.of_zero, map_add, add_zero,
    K0.finrankHom_of_module]

-- Restriction of the integer map recovers class dimension on arbitrary modules.
example :
    ((K0.finrankHom K).comp (K0.ofClass K))
      (ProjectiveClass.of K (ULift.{w} M × PUnit.{u + 1})) =
        (Module.finrank Kᵐᵒᵖ M : ℤ) := by
  rw [AddMonoidHom.comp_apply, K0.finrankHom_ofClass]
  simp only [ProjectiveClass.of_prod, ProjectiveClass.of_ulift,
    ProjectiveClass.of_zero, add_zero,
    ProjectiveClass.finrankHom_of_module]

end FiniteModules

end ProjectiveModulesTests.K0RankClient
