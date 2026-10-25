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

Conversely, testing continuous lifting with sufficiently large lift targets
characterizes algebraic projectivity. The converse preserves any fixed topology
on the original source; the equivalence uses its given module topology.

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

/-- Continuous lifting detects algebraic projectivity without a module-topology
assumption on the original source. Lift targets in `Type (max uR uP)` and common
codomains in `Type uP` suffice. -/
theorem Module.Projective.of_continuous_lifting_property
    {R : Type uR} [Semiring R] [tR : TopologicalSpace R]
    {P : Type uP} [AddCommMonoid P] [Module R P]
    [tP : TopologicalSpace P]
    (h : ∀ (M : Type (max uR uP)) (N : Type uP)
      [AddCommMonoid M] [Module R M] [tM : TopologicalSpace M]
      [ContinuousAdd M] [ContinuousSMul R M]
      [AddCommMonoid N] [Module R N] [tN : TopologicalSpace N]
      (f : M →L[R] N) (g : P →L[R] N),
      Function.Surjective f →
        ∃ l : P →L[R] M, f.comp l = g) :
    Module.Projective R P := by
  apply Module.Projective.of_lifting_property''
  intro f hf
  -- Only fresh copies receive indiscrete topologies; original R and P stay fixed.
  letI tM : TopologicalSpace (ULift.{0} (P →₀ R)) := ⊤
  letI tN : TopologicalSpace (ULift.{0} P) := ⊤
  letI cM : ContinuousAdd (ULift.{0} (P →₀ R)) := ⟨continuous_top⟩
  letI sM : ContinuousSMul R (ULift.{0} (P →₀ R)) := ⟨continuous_top⟩
  let eM : ULift.{0} (P →₀ R) ≃ₗ[R] (P →₀ R) := ULift.moduleEquiv
  let eN : ULift.{0} P ≃ₗ[R] P := ULift.moduleEquiv
  let f' : ULift.{0} (P →₀ R) →L[R] ULift.{0} P :=
    { toLinearMap := eN.symm.toLinearMap.comp (f.comp eM.toLinearMap)
      cont := continuous_top }
  let g' : P →L[R] ULift.{0} P :=
    { toLinearMap := eN.symm.toLinearMap
      cont := continuous_top }
  have hf' : Function.Surjective f' := by
    intro y
    obtain ⟨x, hx⟩ := hf (eN y)
    refine ⟨eM.symm x, ?_⟩
    change eN.symm (f (eM (eM.symm x))) = y
    rw [eM.apply_symm_apply, hx, eN.symm_apply_apply]
  obtain ⟨l, hl⟩ := @h (ULift.{0} (P →₀ R)) (ULift.{0} P)
    _ _ tM cM sM _ _ tN f' g' hf'
  refine ⟨eM.toLinearMap.comp l.toLinearMap, ?_⟩
  ext x
  apply eN.symm.injective
  exact DFunLike.congr_fun hl x

/-- For the given module topology on the original source, algebraic projectivity
is equivalent to continuous lifting along all surjections in the indicated
lift-target and common-codomain universes. -/
theorem Module.projective_iff_continuous_lifting_property
    {R : Type uR} [Semiring R] [tR : TopologicalSpace R]
    {P : Type uP} [AddCommMonoid P] [Module R P]
    [tP : TopologicalSpace P] [IsModuleTopology R P] :
    Module.Projective R P ↔
      ∀ (M : Type (max uR uP)) (N : Type uP)
        [AddCommMonoid M] [Module R M] [tM : TopologicalSpace M]
        [ContinuousAdd M] [ContinuousSMul R M]
        [AddCommMonoid N] [Module R N] [tN : TopologicalSpace N]
        (f : M →L[R] N) (g : P →L[R] N),
        Function.Surjective f →
          ∃ l : P →L[R] M, f.comp l = g := by
  constructor
  · intro hP
    letI : Module.Projective R P := hP
    intro M N _ _ _ _ _ _ _ _ f g hf
    exact ContinuousLinearMap.projective_lifting_property f g hf
  · intro h
    exact Module.Projective.of_continuous_lifting_property h
