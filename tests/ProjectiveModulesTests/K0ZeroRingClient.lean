/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.ZeroRing
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Zero-ring clients for right-module K₀

These examples use the zero-ring class and K₀ instances across independent
carrier universes. An arbitrary right module over a subsingleton ring obtains
its finite projective ring-universe representative from the existing module
instances, without finite generation or projectivity as extra hypotheses.

The one-element ring provides concrete regular, zero and finite-free inputs.
All their generators vanish, while Mathlib's finrank convention gives one on
these modules, even for the empty coordinate type. Thus finrank is not an
additive K₀ invariant over the zero ring.

## References and credits

These clients reuse the finite-projective representative API in this library
and Mathlib's subsingleton module equivalences and `Module.finrank_subsingleton`.
-/

@[expose] public section

universe u v w

open KTheory ModuleCat

namespace ProjectiveModulesTests.K0ZeroRingClient

-- The whole group is trivial, without a representative or generator hypothesis.
example (R : Type u) [Ring R] [Subsingleton R] (z z' : K0 R) : z = z' :=
  Subsingleton.elim _ _

-- Arbitrary unital right modules acquire finite projective representatives.
example (R : Type u) [Ring R] [Subsingleton R]
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    ∃ P : FiniteProjective.{u, u} Rᵐᵒᵖ,
      Nonempty (P ≃ₗ[Rᵐᵒᵖ] M) ∧ K0.of R P = 0 := by
  let _ : Subsingleton M := Module.subsingleton Rᵐᵒᵖ M
  exact ⟨FiniteProjective.repr Rᵐᵒᵖ M,
    ⟨FiniteProjective.reprEquiv Rᵐᵒᵖ M⟩, by simp⟩

-- Class and generator normalization accepts independent input universes.
example (R : Type u) [Ring R] [Subsingleton R]
    (P : FiniteProjective.{u, v} Rᵐᵒᵖ) (Q : FiniteProjective.{u, w} Rᵐᵒᵖ) :
    ProjectiveClass.of R (ULift.{w} P × Q) = 0 ∧
      K0.of R (ULift.{w} P × Q) - K0.of R Q = 0 := by
  simp

-- Every pair of displayed free ranks is right-linearly equivalent.
example (R : Type u) [Ring R] [Subsingleton R] (n m : ℕ) :
    Nonempty ((Fin n → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (Fin m → Rᵐᵒᵖ)) :=
  ⟨LinearEquiv.ofSubsingleton _ _⟩

-- The regular self-opposite carrier, zero module and arbitrary free ranks
-- instantiate generator normalization over the one-element ring.
example (n m : ℕ) :
    K0.of PUnit.{u + 1} PUnit.{u + 1}ᵐᵒᵖ = 0 ∧
      K0.of PUnit.{u + 1} PUnit.{v + 1} = 0 ∧
      K0.of PUnit.{u + 1} (Fin n → PUnit.{u + 1}ᵐᵒᵖ) -
        K0.of PUnit.{u + 1} (ULift.{w} (Fin m → PUnit.{u + 1}ᵐᵒᵖ)) = 0 := by
  simp

-- The existing finrank convention gives one, including at n = 0.
example (n : ℕ) :
    K0.of PUnit.{u + 1} (Fin n → PUnit.{u + 1}ᵐᵒᵖ) = 0 ∧
      Module.finrank PUnit.{u + 1}ᵐᵒᵖ (Fin n → PUnit.{u + 1}ᵐᵒᵖ) = 1 := by
  simp

end ProjectiveModulesTests.K0ZeroRingClient
