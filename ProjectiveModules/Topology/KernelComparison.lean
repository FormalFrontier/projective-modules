/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Topology.Splitting
import Mathlib.Tactic.Abel

/-!
# Comparing kernels with a common section

For continuous linear maps `r, s : A →L[K] H` with a common right inverse
`Γ : H →L[K] A`, `ContinuousLinearMap.kerEquivOfCommonRightInverse` identifies
`ker r` with `ker s`. Its ambient formula is `a ↦ a - Γ (s a)`, and the inverse
has formula `b ↦ b - Γ (r b)`. These equivalences satisfy identity, symmetry,
and composition laws.

The construction uses the second coordinate of
`ContinuousLinearMap.equivProdKerOfRightInverse`. Kernels carry the subspace
topology from the given topology on `A`. The scalar semiring needs no topology,
and `H` needs only its given additive commutative monoid and module structures:
all subtraction takes place in `A`.
-/

@[expose] public section

universe uK uH uA

private theorem commonSectionResidual
    {K : Type uK} {H : Type uH} {A : Type uA}
    [Semiring K] [AddCommMonoid H] [Module K H]
    [AddCommGroup A] [Module K A]
    (Γ : H →ₗ[K] A) (u v : A →ₗ[K] H)
    (hu : ∀ h : H, u (Γ h) = h) (a : A) :
    ((a - Γ (v a)) - Γ (u (a - Γ (v a)))) = a - Γ (u a) := by
  let P : A →ₗ[K] A := Γ.comp u
  have hP : P (a - Γ (v a)) = Γ (u a) - Γ (v a) := by
    rw [map_sub]
    change Γ (u a) - Γ (u (Γ (v a))) = Γ (u a) - Γ (v a)
    rw [hu]
  change (a - Γ (v a)) - P (a - Γ (v a)) = a - Γ (u a)
  rw [hP]
  abel

namespace ContinuousLinearMap

variable {K : Type uK} [Semiring K]
variable {H : Type uH} [AddCommMonoid H] [Module K H] [TopologicalSpace H]
variable {A : Type uA} [AddCommGroup A] [Module K A] [TopologicalSpace A]

private theorem residual_residual (Γ : H →L[K] A) (u v : A →L[K] H)
    (hu : u.comp Γ = ContinuousLinearMap.id K H) (a : A) :
    (a - Γ (v a)) - Γ (u (a - Γ (v a))) = a - Γ (u a) :=
  commonSectionResidual Γ.toLinearMap u.toLinearMap v.toLinearMap
    (fun h => congrArg (fun f : H →L[K] H => f h) hu) a

variable [IsTopologicalAddGroup A]

private theorem coe_splittingCoordinate_apply (Γ : H →L[K] A) (u : A →L[K] H)
    (hu : u.comp Γ = ContinuousLinearMap.id K H) (a : A) :
    ((ContinuousLinearMap.equivProdKerOfRightInverse u Γ
      (fun h => congrArg (fun f : H →L[K] H => f h) hu) a).2 : A) = a - Γ (u a) := by
  apply ContinuousLinearMap.coe_snd_equivProdKerOfRightInverse

/-- The continuous linear equivalence between kernels of two maps with a common
right inverse. In the ambient module it sends `a` to `a - Γ (s a)`. -/
noncomputable def kerEquivOfCommonRightInverse (Γ : H →L[K] A) (r s : A →L[K] H)
    (hr : r.comp Γ = ContinuousLinearMap.id K H)
    (hs : s.comp Γ = ContinuousLinearMap.id K H) :
    LinearMap.ker r.toLinearMap ≃L[K] LinearMap.ker s.toLinearMap :=
  let er := ContinuousLinearMap.equivProdKerOfRightInverse r Γ
    (fun h => congrArg (fun f : H →L[K] H => f h) hr)
  let es := ContinuousLinearMap.equivProdKerOfRightInverse s Γ
    (fun h => congrArg (fun f : H →L[K] H => f h) hs)
  { toLinearEquiv :=
      { toFun := fun a => (es (a : A)).2
        invFun := fun b => (er (b : A)).2
        left_inv := by
          intro a
          apply Subtype.ext
          rw [coe_splittingCoordinate_apply Γ r hr, coe_splittingCoordinate_apply Γ s hs]
          have ha : r (a : A) = 0 := a.property
          simpa only [ha, map_zero, sub_zero] using residual_residual Γ r s hr (a : A)
        right_inv := by
          intro b
          apply Subtype.ext
          rw [coe_splittingCoordinate_apply Γ s hs, coe_splittingCoordinate_apply Γ r hr]
          have hb : s (b : A) = 0 := b.property
          simpa only [hb, map_zero, sub_zero] using residual_residual Γ s r hs (b : A)
        map_add' := by
          intro a b
          exact congrArg Prod.snd (map_add es (a : A) (b : A))
        map_smul' := by
          intro c a
          exact congrArg Prod.snd (map_smul es c (a : A)) }
    continuous_toFun := es.continuous.snd.comp continuous_subtype_val
    continuous_invFun := er.continuous.snd.comp continuous_subtype_val }

/-- The ambient formula for the common-section comparison. -/
@[simp]
theorem coe_kerEquivOfCommonRightInverse_apply (Γ : H →L[K] A) (r s : A →L[K] H)
    (hr : r.comp Γ = ContinuousLinearMap.id K H)
    (hs : s.comp Γ = ContinuousLinearMap.id K H) (a : LinearMap.ker r.toLinearMap) :
    (kerEquivOfCommonRightInverse Γ r s hr hs a : A) = (a : A) - Γ (s (a : A)) :=
  coe_splittingCoordinate_apply Γ s hs (a : A)

/-- The ambient formula for the inverse common-section comparison. -/
theorem coe_kerEquivOfCommonRightInverse_symm_apply (Γ : H →L[K] A)
    (r s : A →L[K] H) (hr : r.comp Γ = ContinuousLinearMap.id K H)
    (hs : s.comp Γ = ContinuousLinearMap.id K H) (b : LinearMap.ker s.toLinearMap) :
    ((kerEquivOfCommonRightInverse Γ r s hr hs).symm b : A) =
      (b : A) - Γ (r (b : A)) :=
  coe_splittingCoordinate_apply Γ r hr (b : A)

/-- Comparing a kernel with itself is the identity equivalence. -/
@[simp]
theorem kerEquivOfCommonRightInverse_refl (Γ : H →L[K] A) (r : A →L[K] H)
    (hr : r.comp Γ = ContinuousLinearMap.id K H) :
    kerEquivOfCommonRightInverse Γ r r hr hr =
      ContinuousLinearEquiv.refl K (LinearMap.ker r.toLinearMap) := by
  apply ContinuousLinearEquiv.ext
  funext a
  apply Subtype.ext
  have ha : r (a : A) = 0 := a.property
  rw [coe_kerEquivOfCommonRightInverse_apply Γ r r hr hr, ha, map_zero, sub_zero,
    ContinuousLinearEquiv.refl_apply]

/-- Reversing the pair of maps gives the inverse comparison. -/
@[simp]
theorem kerEquivOfCommonRightInverse_symm (Γ : H →L[K] A) (r s : A →L[K] H)
    (hr : r.comp Γ = ContinuousLinearMap.id K H)
    (hs : s.comp Γ = ContinuousLinearMap.id K H) :
    (kerEquivOfCommonRightInverse Γ r s hr hs).symm =
      kerEquivOfCommonRightInverse Γ s r hs hr := by
  apply ContinuousLinearEquiv.ext
  funext b
  apply Subtype.ext
  rw [coe_kerEquivOfCommonRightInverse_symm_apply Γ r s hr hs,
    coe_kerEquivOfCommonRightInverse_apply Γ s r hs hr]

/-- Kernel comparisons with a fixed common section compose in the expected order. -/
@[simp]
theorem kerEquivOfCommonRightInverse_trans (Γ : H →L[K] A) (r s t : A →L[K] H)
    (hr : r.comp Γ = ContinuousLinearMap.id K H)
    (hs : s.comp Γ = ContinuousLinearMap.id K H)
    (ht : t.comp Γ = ContinuousLinearMap.id K H) :
    (kerEquivOfCommonRightInverse Γ r s hr hs).trans
        (kerEquivOfCommonRightInverse Γ s t hs ht) =
      kerEquivOfCommonRightInverse Γ r t hr ht := by
  apply ContinuousLinearEquiv.ext
  funext a
  apply Subtype.ext
  simpa only [ContinuousLinearEquiv.trans_apply,
    coe_kerEquivOfCommonRightInverse_apply Γ s t hs ht,
    coe_kerEquivOfCommonRightInverse_apply Γ r s hr hs,
    coe_kerEquivOfCommonRightInverse_apply Γ r t hr ht] using
    residual_residual Γ t s ht (a : A)

end ContinuousLinearMap
