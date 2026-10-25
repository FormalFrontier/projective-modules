/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Continuous lifting from projective modules

Algebraic projectivity supplies a linear lift along a surjection. When the
source has its module topology and the target of the lift has continuous
addition and scalar multiplication, that lift is continuous for the given
topologies. This yields a factorization of continuous linear maps without
requiring continuous operations on their common codomain.

## References

* Mathlib, `Module.projective_lifting_property`, for algebraic lifting.
* Mathlib, `IsModuleTopology.continuous_of_linearMap`, for continuity from the
  module topology.
-/

@[expose] public section

universe uR uP uM uN

namespace ContinuousLinearMap

/-- A continuous linear map from a projective module with its module topology
lifts along a surjective continuous linear map. The target of the lift has
continuous addition and scalar multiplication; the common codomain needs no
continuity of its algebraic operations. -/
theorem projective_lifting_property
    {R : Type uR} [Semiring R] [TopologicalSpace R]
    {P : Type uP} [AddCommMonoid P] [Module R P]
    [TopologicalSpace P] [Module.Projective R P] [IsModuleTopology R P]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul R M]
    {N : Type uN} [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (f : M →L[R] N) (g : P →L[R] N)
    (hf : Function.Surjective f) :
    ∃ l : P →L[R] M, f.comp l = g := by
  obtain ⟨l, hl⟩ := Module.projective_lifting_property f.toLinearMap g.toLinearMap hf
  refine ⟨{ toLinearMap := l, cont := IsModuleTopology.continuous_of_linearMap l }, ?_⟩
  ext x
  exact DFunLike.congr_fun hl x

end ContinuousLinearMap
