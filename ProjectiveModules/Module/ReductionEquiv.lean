/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.ReductionBijective

/-!
# Lifting specified equivalences of reduced projective modules

Every given equivalence between the canonical reductions of two projective
modules modulo a nilpotent two-sided ideal lifts to an equivalence of the
original modules. The lift has exactly the prescribed reduced linear map.
-/

@[expose] public section

universe u p q

namespace Module

variable {R : Type u} [Ring R] (I : Ideal R) [I.IsTwoSided]

/-- Every specified equivalence of reductions of projective modules modulo a
nilpotent two-sided ideal lifts to a linear equivalence with that exact reduced
linear map. No finite-generation hypothesis is needed. -/
theorem exists_linearEquiv_lift (hI : IsNilpotent I)
    {P : Type p} {Q : Type q}
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    (e₀ : Reduction I P ≃ₗ[R ⧸ I] Reduction I Q) :
    ∃ e : P ≃ₗ[R] Q, reductionMap I e.toLinearMap = e₀.toLinearMap := by
  obtain ⟨f, hf⟩ := exists_reductionMap_eq_of_projective I e₀.toLinearMap
  have hfb : Function.Bijective (reductionMap I f) := by
    rw [hf]
    exact e₀.bijective
  refine ⟨LinearEquiv.ofBijective f (bijective_of_reduction_bijective I hI f hfb), ?_⟩
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun hf x

end Module
