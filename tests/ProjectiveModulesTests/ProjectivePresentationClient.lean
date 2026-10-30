/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Presentation

/-!
# Augmenting a projective presentation by a regular generator

Starting with a finite projective source and a finite projective kernel, add a
regular summand to the source and ignore it in the presentation map. The new
kernel is finite projective by the public kernel-property comparison, and its
K₀ class increases by the regular-module class. No property of the target beyond
its original semimodule structure is required.
-/

@[expose] public section

universe uR uP uM

namespace ProjectiveModulesTests.ProjectivePresentationClient

open KTheory

variable (R : Type uR) [Ring R]
variable {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P]
  [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]
variable {M : Type uM} [AddCommMonoid M] [Module Rᵐᵒᵖ M]

/-- Adding an unused regular generator adds its class to the kernel class.
The witnesses of finite generation and projectivity of the augmented kernel
are conclusions, not hypotheses. -/
theorem augmented_presentation_kernel_class
    (p : P →ₗ[Rᵐᵒᵖ] M)
    [Module.Finite Rᵐᵒᵖ p.ker] [Module.Projective Rᵐᵒᵖ p.ker]
    (hp : Function.Surjective p) :
    ∃ (hfin : Module.Finite Rᵐᵒᵖ
        (p.comp (LinearMap.fst Rᵐᵒᵖ P Rᵐᵒᵖ)).ker)
      (hproj : Module.Projective Rᵐᵒᵖ
        (p.comp (LinearMap.fst Rᵐᵒᵖ P Rᵐᵒᵖ)).ker),
      @K0.of R _ (p.comp (LinearMap.fst Rᵐᵒᵖ P Rᵐᵒᵖ)).ker _ _ hfin hproj =
        K0.of R p.ker + K0.of R Rᵐᵒᵖ := by
  let q : P × Rᵐᵒᵖ →ₗ[Rᵐᵒᵖ] M := p.comp (LinearMap.fst Rᵐᵒᵖ P Rᵐᵒᵖ)
  have hq : Function.Surjective q := by
    intro m
    obtain ⟨x, hx⟩ := hp m
    exact ⟨(x, 0), hx⟩
  have : Module.Finite Rᵐᵒᵖ q.ker :=
    LinearMap.finite_ker_of_surjective_of_finite_ker p q hp hq
  have : Module.Projective Rᵐᵒᵖ q.ker :=
    LinearMap.projective_ker_of_surjective_of_projective_ker p q hp hq
  refine ⟨inferInstance, inferInstance, ?_⟩
  have h := K0.sub_ker_eq_sub_ker_of_surjective R p q hp hq
  have hclass : K0.of R P + K0.of R q.ker =
      K0.of R P + (K0.of R p.ker + K0.of R Rᵐᵒᵖ) := by
    calc
      K0.of R P + K0.of R q.ker = K0.of R (P × Rᵐᵒᵖ) + K0.of R p.ker :=
        sub_eq_sub_iff_add_eq_add.mp h
      _ = (K0.of R P + K0.of R Rᵐᵒᵖ) + K0.of R p.ker := by rw [K0.of_prod]
      _ = K0.of R P + (K0.of R p.ker + K0.of R Rᵐᵒᵖ) := by
        rw [add_assoc, add_comm (K0.of R Rᵐᵒᵖ) (K0.of R p.ker)]
  exact add_left_cancel hclass

end ProjectiveModulesTests.ProjectivePresentationClient
