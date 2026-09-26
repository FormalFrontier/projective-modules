/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Projectivity of exterior powers

This file proves that every exterior power of a projective module over a
commutative ring is projective. The proof applies the exterior-power functor
to the canonical splitting of the projective module from a free module.
-/

@[expose] public section

namespace exteriorPower

universe u v

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Every exterior power of a projective module is projective. -/
instance instProjective (n : ℕ) [Module.Projective R M] :
    Module.Projective R (⋀[R]^n M) := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective R M).out
  let π : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  have hs' : π ∘ₗ s = LinearMap.id := LinearMap.ext fun x ↦ hs x
  exact Module.Projective.of_split (map n s) (map n π) (by
    rw [← map_comp, hs', map_id])

end exteriorPower
