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
right inverse even though it is not injective. In contrast, the identity on the
real line cannot factor through the zero map, so surjectivity cannot be omitted.
-/

example :
    (∃ l : ℝ →L[ℝ] ℝ × ℝ,
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp l = ContinuousLinearMap.id ℝ ℝ) ∧
    ¬ Function.Injective (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
  constructor
  · exact ContinuousLinearMap.projective_lifting_property
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ)
      (fun x ↦ ⟨(x, 0), rfl⟩)
  · intro h
    have h01 : ((0, 0) : ℝ × ℝ) = (0, 1) := h rfl
    exact zero_ne_one (congrArg Prod.snd h01)

example :
    ¬ ∃ l : ℝ →L[ℝ] ℝ,
      (0 : ℝ →L[ℝ] ℝ).comp l = ContinuousLinearMap.id ℝ ℝ := by
  intro h
  obtain ⟨l, hl⟩ := h
  exact zero_ne_one (DFunLike.congr_fun hl 1)
