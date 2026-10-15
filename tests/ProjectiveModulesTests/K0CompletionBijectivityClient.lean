/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.Rank
import ProjectiveModules.KTheory.ScalarExtension
import ProjectiveModules.KTheory.ZeroRing
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Algebra.Ring.Rat

/-!
# Clients of bijectivity transport from projective classes to K₀

The identity on the rational field has a bijective class map by the public
identity contract. Transport to K₀ uses the class-map bijectivity theorem.
The independent integer dimension equivalence detects a nonzero image of
the regular rank-one generator. The identity of the one-element ring gives
the subsingleton boundary, without a nontrivial-ring premise.
-/

@[expose] public section

open KTheory

namespace ProjectiveModulesTests.K0CompletionBijectivityClient

private theorem rational_identity_bijective_and_nonzero :
    Function.Bijective (K0.map (RingHom.id ℚ)) ∧
      K0.map (RingHom.id ℚ) (K0.of ℚ ℚᵐᵒᵖ) ≠ 0 := by
  constructor
  · apply K0.map_bijective_of_projectiveClass_map_bijective
    rw [ProjectiveClass.map_id]
    exact Function.bijective_id
  · intro equality
    have dimensions := congrArg (K0.finrankEquiv ℚ) equality
    have impossible : (1 : ℤ) = 0 := by
      simpa only [K0.map_id, AddMonoidHom.id_apply,
        K0.finrankEquiv_of_self, map_zero] using dimensions
    exact one_ne_zero impossible

private theorem zero_ring_identity_boundary :
    Function.Bijective (K0.map (RingHom.id PUnit.{1})) ∧
      ∀ x : K0 PUnit.{1}, K0.map (RingHom.id PUnit.{1}) x = 0 := by
  constructor
  · apply K0.map_bijective_of_projectiveClass_map_bijective
    rw [ProjectiveClass.map_id]
    exact Function.bijective_id
  · intro x
    exact Subsingleton.elim _ _

end ProjectiveModulesTests.K0CompletionBijectivityClient
