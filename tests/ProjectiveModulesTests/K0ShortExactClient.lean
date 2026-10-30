/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.ShortExact
import Mathlib.Algebra.Exact.Basic

/-!
# A canonical short exact sequence in K₀

The inclusion into the first factor and projection onto the second factor
satisfy the short-exact hypotheses over any ring, with independent carrier
universes. This client obtains the product relation through the exact-sequence
API rather than the product formula.
-/

@[expose] public section

universe u v w

open KTheory

namespace ProjectiveModulesTests.K0ShortExactClient

example (R : Type u) [Ring R]
    (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]
    (Q : Type w) [AddCommGroup Q] [Module Rᵐᵒᵖ Q]
    [Module.Finite Rᵐᵒᵖ Q] [Module.Projective Rᵐᵒᵖ Q] :
    K0.of R (P × Q) = K0.of R P + K0.of R Q := by
  apply K0.of_eq_add_of_exact R P (P × Q) Q
    (LinearMap.inl Rᵐᵒᵖ P Q) (LinearMap.snd Rᵐᵒᵖ P Q)
  · intro p p' h
    exact congrArg Prod.fst h
  · intro q
    exact ⟨(0, q), rfl⟩
  · exact (Function.Exact.inl_snd (R := Rᵐᵒᵖ) (M := P) (N := Q)).linearMap_ker_eq.symm

end ProjectiveModulesTests.K0ShortExactClient
