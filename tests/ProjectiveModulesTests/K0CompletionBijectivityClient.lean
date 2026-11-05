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
# Clients of completion transport from projective classes to K₀

The projection from `ℤ × ℤ` onto its first factor uses the surjectivity-only
class-map criterion, with the diagonal as a section. The second projective
factor is forgotten, so class-map bijectivity is not required.

The identity on the rational field has a bijective class map by the public
identity contract. Transport to K₀ uses the class-map bijectivity theorem.
The independent integer dimension equivalence detects a nonzero image of
the regular rank-one generator. The identity of the one-element ring gives
the subsingleton boundary, without a nontrivial-ring premise.
-/

@[expose] public section

open KTheory

namespace ProjectiveModulesTests.K0CompletionBijectivityClient

private theorem first_projection_surjective :
    Function.Surjective (K0.map (RingHom.fst ℤ ℤ)) := by
  apply K0.map_surjective_of_projectiveClass_map_surjective
  have h : (RingHom.fst ℤ ℤ).comp ((RingHom.id ℤ).prod (RingHom.id ℤ)) =
      RingHom.id ℤ := by
    ext x
    rfl
  intro x
  refine ⟨ProjectiveClass.map ((RingHom.id ℤ).prod (RingHom.id ℤ)) x, ?_⟩
  rw [← AddMonoidHom.comp_apply, ← ProjectiveClass.map_comp, h,
    ProjectiveClass.map_id, AddMonoidHom.id_apply]

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
