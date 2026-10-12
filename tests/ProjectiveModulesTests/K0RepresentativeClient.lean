/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.Stabilization

/-!
# Clients of K₀ difference representatives and projective stabilization

A universal additive invariant evaluates an arbitrary K₀ element using its
chosen module pair, without unfolding the representative. The pair chosen for
zero has a common projective stabilizer, even though its two modules need not
be zero or be isomorphic before stabilization. A lifted regular module and a
regular module with an adjoined zero illustrate the generator criterion across
independent carrier universes.

These examples use the difference and stabilization descriptions of K₀ from
Weibel's *The K-book*, Chapter II, through the public Projective Modules and
Mathlib additive-map APIs.
-/

@[expose] public section

universe u v w x

open KTheory ModuleCat

namespace ProjectiveModulesTests.K0RepresentativeClient

example (R : Type u) [Ring R] (z : K0 R)
    (G : Type x) [AddCommGroup G] (f : ProjectiveClass R →+ G) :
    K0.lift R f z =
      f (ProjectiveClass.of R (K0.representative R z).1) -
        f (ProjectiveClass.of R (K0.representative R z).2) := by
  calc
    K0.lift R f z = K0.lift R f
        (K0.of R (K0.representative R z).1 -
          K0.of R (K0.representative R z).2) :=
      congrArg (K0.lift R f) (K0.representative_spec R z)
    _ = _ := by simp only [map_sub, K0.lift_of]

example (R : Type u) [Ring R] :
    ∃ T : FiniteProjective.{u, u} Rᵐᵒᵖ,
      Nonempty (((K0.representative R 0).1 × T) ≃ₗ[Rᵐᵒᵖ]
        ((K0.representative R 0).2 × T)) := by
  apply (K0.of_eq_iff_exists_projective_stabilizer R
    (K0.representative R 0).1 (K0.representative R 0).2).mp
  exact sub_eq_zero.mp (K0.representative_spec R 0).symm

example (R : Type u) [Ring R] :
    ∃ T : FiniteProjective.{u, u} Rᵐᵒᵖ,
      Nonempty ((ULift.{v} Rᵐᵒᵖ × T) ≃ₗ[Rᵐᵒᵖ]
        ((Rᵐᵒᵖ × PUnit.{w + 1}) × T)) := by
  apply (K0.of_eq_iff_exists_projective_stabilizer R
    (ULift.{v} Rᵐᵒᵖ) (Rᵐᵒᵖ × PUnit.{w + 1})).mp
  simp only [K0.of_ulift, K0.of_prod, K0.of_zero, add_zero]

end ProjectiveModulesTests.K0RepresentativeClient
