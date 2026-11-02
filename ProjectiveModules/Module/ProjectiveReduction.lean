/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Reduction

/-!
# Lifting maps from reductions of projective modules

Every map from the reduction of a projective module lifts to a linear map.
Neither nilpotence of the ideal nor projectivity of the target is required.
-/

@[expose] public section

universe u v p q w

namespace Module

variable {R : Type u} [Ring R] (I : Ideal R) [I.IsTwoSided]

/-- A map between reductions lifts to a linear map when its source is projective.
No nilpotence hypothesis or projectivity of the target is needed. -/
theorem exists_reductionMap_eq_of_projective
    {P : Type p} {Q : Type q}
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup Q] [Module R Q]
    (g : Reduction I P →ₗ[R ⧸ I] Reduction I Q) :
    ∃ f : P →ₗ[R] Q, reductionMap I f = g := by
  let g' : P →ₗ[R] Reduction I Q :=
    (g.restrictScalars R).comp (reductionMk I P)
  obtain ⟨f, hf⟩ : ∃ f : P →ₗ[R] Q, (reductionMk I Q).comp f = g' := by
    have hq : Function.Surjective (reductionMk I Q) := reductionMk_surjective I
    exact projective_lifting_property (reductionMk I Q) g' hq
  refine ⟨f, ?_⟩
  apply reduction_hom_ext I
  intro p
  rw [reductionMap_mk]
  exact LinearMap.congr_fun hf p

end Module
