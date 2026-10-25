/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Topology.Projective
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuous projective lifting over the reals

The first-coordinate projection from the real plane has a continuous linear
right inverse `x ↦ (x, 0)` even though it is not injective. The full lifting
hypothesis comes from stock projectivity and the generic forward theorem, and
exercises both characterization statements. In contrast, the identity on the
real line cannot factor through the zero map, so surjectivity cannot be omitted.
-/

example :
    (∃ l : ℝ →L[ℝ] ℝ × ℝ,
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp l = ContinuousLinearMap.id ℝ ℝ) ∧
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)) =
      ContinuousLinearMap.id ℝ ℝ ∧
    ¬ Function.Injective (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
  have h : ∀ (M N : Type)
      [AddCommMonoid M] [Module ℝ M] [TopologicalSpace M]
      [ContinuousAdd M] [ContinuousSMul ℝ M]
      [AddCommMonoid N] [Module ℝ N] [TopologicalSpace N]
      (f : M →L[ℝ] N) (g : ℝ →L[ℝ] N),
      Function.Surjective f → ∃ l : ℝ →L[ℝ] M, f.comp l = g := by
    intro M N _ _ _ _ _ _ _ _ f g hf
    exact ContinuousLinearMap.projective_lifting_property f g hf
  have hP : Module.Projective ℝ ℝ :=
    Module.Projective.of_continuous_lifting_property h
  have h' := (Module.projective_iff_continuous_lifting_property
    (R := ℝ) (P := ℝ)).mp hP
  constructor
  · exact h' (ℝ × ℝ) ℝ
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ)
      (fun x ↦ ⟨(x, 0), rfl⟩)
  · constructor
    · ext x
      rfl
    · intro hi
      have h01 : ((0, 0) : ℝ × ℝ) = (0, 1) := hi rfl
      exact zero_ne_one (congrArg Prod.snd h01)

example :
    ¬ ∃ l : ℝ →L[ℝ] ℝ,
      (0 : ℝ →L[ℝ] ℝ).comp l = ContinuousLinearMap.id ℝ ℝ := by
  intro h
  obtain ⟨l, hl⟩ := h
  exact zero_ne_one (DFunLike.congr_fun hl 1)
