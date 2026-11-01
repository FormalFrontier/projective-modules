/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Topology.KernelComparison
import Mathlib.Topology.Instances.Int

/-!
# A nontrivial kernel comparison over natural-number scalars

The diagonal section of the two coordinate projections on `ℤ × ℤ` gives a
continuous `ℕ`-linear comparison of their kernels. All topological, additive,
and module structures are the canonical ones. The restricted corrections are
continuous because their domains are discrete subspaces of `ℤ × ℤ`.

The comparison sends `(0, 1)` to `(-1, 0)`, and its inverse sends `(-1, 0)`
back to `(0, 1)`. Thus the comparison changes the ambient vector even though
the scalars form only the semiring `ℕ`: the negative correction belongs to
the ambient additive group, not to the scalar semiring.
-/

namespace KernelComparisonSemiring

private def Γ : ℤ →ₗ[ℕ] ℤ × ℤ where
  toFun h := (h, h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def r : (ℤ × ℤ) →ₗ[ℕ] ℤ where
  toFun a := a.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def s : (ℤ × ℤ) →ₗ[ℕ] ℤ where
  toFun a := a.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem hr (h : ℤ) : r (Γ h) = h := rfl

private theorem hs (h : ℤ) : s (Γ h) = h := rfl

private theorem correction_continuous_on_ker_r :
    Continuous (fun a : LinearMap.ker r =>
      Γ (r (a : ℤ × ℤ)) - Γ (s (a : ℤ × ℤ))) :=
  continuous_of_discreteTopology

private theorem correction_continuous_on_ker_s :
    Continuous (fun b : LinearMap.ker s =>
      Γ (r (b : ℤ × ℤ)) - Γ (s (b : ℤ × ℤ))) :=
  continuous_of_discreteTopology

private noncomputable def comparison : LinearMap.ker r ≃L[ℕ] LinearMap.ker s :=
  LinearMap.kerContinuousLinearEquivOfCommonRightInverse Γ r s hr hs
    correction_continuous_on_ker_r correction_continuous_on_ker_s

private def source : LinearMap.ker r := ⟨(0, 1), rfl⟩

private def target : LinearMap.ker s := ⟨(-1, 0), rfl⟩

example : comparison source = target ∧ comparison.symm target = source ∧
    (comparison source : ℤ × ℤ) ≠ (source : ℤ × ℤ) := by
  have hforward : comparison source = target := by
    apply Subtype.ext
    calc
      (comparison source : ℤ × ℤ) =
          (source : ℤ × ℤ) - Γ (s (source : ℤ × ℤ)) :=
        LinearMap.coe_kerContinuousLinearEquivOfCommonRightInverse_apply
          Γ r s hr hs correction_continuous_on_ker_r correction_continuous_on_ker_s source
      _ = (target : ℤ × ℤ) := by
        change ((0 : ℤ) - 1, (1 : ℤ) - 1) = (-1, 0)
        rw [zero_sub, sub_self]
  have hinverse : comparison.symm target = source := by
    apply Subtype.ext
    calc
      (comparison.symm target : ℤ × ℤ) =
          (target : ℤ × ℤ) - Γ (r (target : ℤ × ℤ)) :=
        LinearMap.coe_kerContinuousLinearEquivOfCommonRightInverse_symm_apply
          Γ r s hr hs correction_continuous_on_ker_r correction_continuous_on_ker_s target
      _ = (source : ℤ × ℤ) := by
        change ((-1 : ℤ) - (-1), (0 : ℤ) - (-1)) = (0, 1)
        rw [sub_self, zero_sub, neg_neg]
  refine ⟨hforward, hinverse, ?_⟩
  intro h
  rw [hforward] at h
  have hfirst := congrArg Prod.fst h
  change (-1 : ℤ) = 0 at hfirst
  exact (neg_ne_zero.mpr (one_ne_zero : (1 : ℤ) ≠ 0)) hfirst

end KernelComparisonSemiring
