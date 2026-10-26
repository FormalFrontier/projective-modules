/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Topology.Splitting
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuous projective lifting and splitting on real spaces

The first-coordinate projection from the real plane has a continuous linear
right inverse despite its nonzero kernel; the standard section `x ↦ (x, 0)` is
also checked directly. The full lifting hypothesis comes from the real line's
standard projectivity through the generic forward theorem, and exercises both
characterization statements. The projection splits as its kernel times the real
line, while the identity gives a zero-kernel boundary. In contrast, the identity
on the real line cannot factor through zero, so surjectivity cannot be omitted.

The splitting formulas are also evaluated over ℕ on the real plane and line,
using the standard section.
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
    · ext
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

-- The original real topologies and module structures are inferred throughout.
example :
    ∃ e : (ℝ × ℝ) ≃L[ℝ] ((ContinuousLinearMap.fst ℝ ℝ ℝ).ker × ℝ),
      ∀ x, (e x).2 = x.1 :=
  ContinuousLinearMap.exists_equiv_ker_prod (ContinuousLinearMap.fst ℝ ℝ ℝ)
    (fun x ↦ ⟨(x, 0), rfl⟩)

example : ∃ k : (ContinuousLinearMap.fst ℝ ℝ ℝ).ker, k ≠ 0 := by
  refine ⟨⟨(0, 1), rfl⟩, ?_⟩
  intro h
  have h' := congrArg
    (fun k : (ContinuousLinearMap.fst ℝ ℝ ℝ).ker ↦ (k : ℝ × ℝ).2) h
  exact one_ne_zero h'

example :
    ∃ e : ℝ ≃L[ℝ] ((ContinuousLinearMap.id ℝ ℝ).ker × ℝ),
      ∀ x, (e x).2 = x :=
  ContinuousLinearMap.exists_equiv_ker_prod (ContinuousLinearMap.id ℝ ℝ)
    Function.surjective_id

-- A nonring scalar semiring, with the standard continuous section.
example (a b : ℝ) :
    let f := ContinuousLinearMap.fst ℕ ℝ ℝ
    ∃ e : (ℝ × ℝ) ≃L[ℕ] (ℝ × f.ker),
      (e (a, b)).1 = a ∧ ((e (a, b)).2 : ℝ × ℝ) = (0, b) ∧
        e.symm (a, (⟨(0, b), by simp [f]⟩ : f.ker)) = (a, b) := by
  intro f
  let s := (ContinuousLinearMap.id ℕ ℝ).prod (0 : ℝ →L[ℕ] ℝ)
  have hs : Function.RightInverse s f := by
    intro x
    simp [f, s]
  let e := f.equivProdKerOfRightInverse s hs
  refine ⟨e, ?_, ?_, ?_⟩
  · exact ContinuousLinearMap.fst_equivProdKerOfRightInverse f s hs (a, b)
  · simpa [e, f, s] using
      (ContinuousLinearMap.coe_snd_equivProdKerOfRightInverse f s hs (a, b))
  · dsimp only [e]
    rw [ContinuousLinearMap.equivProdKerOfRightInverse_symm_apply]
    simp [s]

-- The headline keeps the original data and independent universes under the weaker hypotheses.
universe uR uM uN

example {R : Type uR} {M : Type uM} {N : Type uN}
    [Semiring R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [ContinuousAdd M] [ContinuousSMul R M]
    [Module.Projective R N] [IsModuleTopology R N]
    (f : M →L[R] N) (hf : Function.Surjective f) :
    ∃ e : M ≃L[R] (f.ker × N), ∀ x, (e x).2 = f x :=
  ContinuousLinearMap.exists_equiv_ker_prod f hf
