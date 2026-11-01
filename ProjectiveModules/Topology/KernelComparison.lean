/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Topology.Splitting
public import ProjectiveModules.Module.KernelComparison
import Mathlib.Tactic.Abel

/-!
# Comparing kernels with a common section

For linear retractions `r, s : A →ₗ[K] H` with a common section `Γ : H →ₗ[K] A`,
`LinearMap.kerContinuousLinearEquivOfCommonRightInverse` equips the shared
algebraic kernel comparison with continuity. It requires only that the ambient
correction `Δ a = Γ (r a) - Γ (s a)` be continuous on each kernel. The forward
and inverse continuity criteria characterize these two restrictions exactly.
The ambient formulas are `a ↦ a - Γ (s a) = a + Δ a` on `ker r` and
`b ↦ b - Γ (r b) = b - Δ b` on `ker s`.

Global continuity of `Δ` supplies a convenient specialization. For continuous
linear input data, `ContinuousLinearMap.kerEquivOfCommonRightInverse` delegates
to it. The comparisons satisfy identity, symmetry, and composition laws, and
preserve continuity of ambient-valued kernel parametrizations.

The algebraic kernel comparison is also shared with
`LinearMap.kerFamilyHomeomorphOfCommonRightInverse`. The latter compares the
original product-subtype total spaces of kernels for varying fibres `H t`.
Only the ambient difference `Γ t (r t a) - Γ t (q t a)` must be jointly
continuous; none of the individual linear maps needs to be continuous.

Kernels carry the subspace topology from the given topology on `A`. The scalar
semiring needs no topology, and the fibres need only their given additive
commutative monoid and module structures: all subtraction takes place in `A`.
-/

@[expose] public section

universe uT uK uH uA uX

namespace LinearMap

variable {K : Type uK} [Semiring K]
variable {H : Type uH} [AddCommMonoid H] [Module K H]
variable {A : Type uA} [AddCommGroup A] [Module K A]
variable [TopologicalSpace A]

/-- Continuity of the algebraic forward comparison is equivalent to continuity
of the ambient correction restricted to its source kernel. -/
theorem continuous_kerEquivOfCommonRightInverse_iff
    [IsTopologicalAddGroup A]
    (Γ : H →ₗ[K] A) (r s : A →ₗ[K] H)
    (hr : ∀ h : H, r (Γ h) = h) (hs : ∀ h : H, s (Γ h) = h) :
    Continuous (fun a : LinearMap.ker r =>
      LinearMap.kerEquivOfCommonRightInverse Γ r s hr hs a) ↔
      Continuous (fun a : LinearMap.ker r => Γ (r (a : A)) - Γ (s (a : A))) := by
  constructor
  · intro he
    have hc : Continuous (fun a : LinearMap.ker r =>
        (kerEquivOfCommonRightInverse Γ r s hr hs a : A) - (a : A)) :=
      (continuous_subtype_val.comp he).sub continuous_subtype_val
    convert hc using 1
    funext a
    have ha : r (a : A) = 0 := a.property
    rw [coe_kerEquivOfCommonRightInverse_apply, ha, map_zero, zero_sub]
    abel
  · intro hΔr
    apply Continuous.subtype_mk
    have hc : Continuous (fun a : LinearMap.ker r =>
        (a : A) + (Γ (r (a : A)) - Γ (s (a : A)))) :=
      continuous_subtype_val.add hΔr
    convert hc using 1
    funext a
    have ha : r (a : A) = 0 := a.property
    simp only [ha, map_zero, sub_eq_add_neg, zero_add]

/-- Continuity of the algebraic inverse comparison is equivalent to continuity
of the same ambient correction restricted to the target kernel. -/
theorem continuous_kerEquivOfCommonRightInverse_symm_iff
    [IsTopologicalAddGroup A]
    (Γ : H →ₗ[K] A) (r s : A →ₗ[K] H)
    (hr : ∀ h : H, r (Γ h) = h) (hs : ∀ h : H, s (Γ h) = h) :
    Continuous (fun b : LinearMap.ker s =>
      (LinearMap.kerEquivOfCommonRightInverse Γ r s hr hs).symm b) ↔
      Continuous (fun b : LinearMap.ker s => Γ (r (b : A)) - Γ (s (b : A))) := by
  constructor
  · intro he
    have hc : Continuous (fun b : LinearMap.ker s =>
        (b : A) - ((kerEquivOfCommonRightInverse Γ r s hr hs).symm b : A)) :=
      continuous_subtype_val.sub (continuous_subtype_val.comp he)
    convert hc using 1
    funext b
    have hb : s (b : A) = 0 := b.property
    rw [coe_kerEquivOfCommonRightInverse_symm_apply, hb, map_zero, sub_zero]
    abel
  · intro hΔs
    apply Continuous.subtype_mk
    have hc : Continuous (fun b : LinearMap.ker s =>
        (b : A) - (Γ (r (b : A)) - Γ (s (b : A)))) :=
      continuous_subtype_val.sub hΔs
    convert hc using 1
    funext b
    have hb : s (b : A) = 0 := b.property
    simp only [hb, map_zero, sub_zero]

/-- The continuous linear equivalence between kernels of two linear retractions
with a common section. It uses the algebraic common-section comparison and only
requires continuity of the ambient correction restricted to the two kernels. -/
noncomputable def kerContinuousLinearEquivOfCommonRightInverse
    [IsTopologicalAddGroup A]
    (Γ : H →ₗ[K] A) (r s : A →ₗ[K] H)
    (hr : ∀ h : H, r (Γ h) = h) (hs : ∀ h : H, s (Γ h) = h)
    (hΔr : Continuous (fun a : LinearMap.ker r =>
      Γ (r (a : A)) - Γ (s (a : A))))
    (hΔs : Continuous (fun b : LinearMap.ker s =>
      Γ (r (b : A)) - Γ (s (b : A)))) :
    LinearMap.ker r ≃L[K] LinearMap.ker s where
  toLinearEquiv := LinearMap.kerEquivOfCommonRightInverse Γ r s hr hs
  continuous_toFun :=
    (continuous_kerEquivOfCommonRightInverse_iff Γ r s hr hs).2 hΔr
  continuous_invFun :=
    (continuous_kerEquivOfCommonRightInverse_symm_iff Γ r s hr hs).2 hΔs

variable (Γ : H →ₗ[K] A) (r s : A →ₗ[K] H)
variable (hr : ∀ h : H, r (Γ h) = h) (hs : ∀ h : H, s (Γ h) = h)
variable (hΔr : Continuous (fun a : LinearMap.ker r =>
  Γ (r (a : A)) - Γ (s (a : A))))
variable (hΔs : Continuous (fun b : LinearMap.ker s =>
  Γ (r (b : A)) - Γ (s (b : A))))

/-- Forgetting continuity recovers the shared algebraic comparison. -/
@[simp]
theorem kerContinuousLinearEquivOfCommonRightInverse_toLinearEquiv
    [IsTopologicalAddGroup A] :
    (kerContinuousLinearEquivOfCommonRightInverse Γ r s hr hs hΔr hΔs).toLinearEquiv =
      LinearMap.kerEquivOfCommonRightInverse Γ r s hr hs := by
  rfl

/-- The forward comparison has the common-section residual as ambient value. -/
@[simp]
theorem coe_kerContinuousLinearEquivOfCommonRightInverse_apply
    [IsTopologicalAddGroup A]
    (a : LinearMap.ker r) :
    (kerContinuousLinearEquivOfCommonRightInverse Γ r s hr hs hΔr hΔs a : A) =
      (a : A) - Γ (s (a : A)) := by
  exact coe_kerEquivOfCommonRightInverse_apply Γ r s hr hs a

/-- The inverse comparison has the reverse residual as ambient value. -/
theorem coe_kerContinuousLinearEquivOfCommonRightInverse_symm_apply
    [IsTopologicalAddGroup A]
    (b : LinearMap.ker s) :
    ((kerContinuousLinearEquivOfCommonRightInverse Γ r s hr hs hΔr hΔs).symm b : A) =
      (b : A) - Γ (r (b : A)) := by
  exact coe_kerEquivOfCommonRightInverse_symm_apply Γ r s hr hs b

/-- On the source kernel the forward comparison adds the ambient correction. -/
theorem coe_kerContinuousLinearEquivOfCommonRightInverse_apply_eq_add
    [IsTopologicalAddGroup A]
    (a : LinearMap.ker r) :
    (kerContinuousLinearEquivOfCommonRightInverse Γ r s hr hs hΔr hΔs a : A) =
      (a : A) + (Γ (r (a : A)) - Γ (s (a : A))) := by
  rw [coe_kerContinuousLinearEquivOfCommonRightInverse_apply]
  have ha : r (a : A) = 0 := a.property
  rw [ha, map_zero, zero_sub, sub_eq_add_neg]

/-- On the target kernel the inverse comparison subtracts the ambient correction. -/
theorem coe_kerContinuousLinearEquivOfCommonRightInverse_symm_apply_eq_sub
    [IsTopologicalAddGroup A]
    (b : LinearMap.ker s) :
    ((kerContinuousLinearEquivOfCommonRightInverse Γ r s hr hs hΔr hΔs).symm b : A) =
      (b : A) - (Γ (r (b : A)) - Γ (s (b : A))) := by
  rw [coe_kerContinuousLinearEquivOfCommonRightInverse_symm_apply]
  have hb : s (b : A) = 0 := b.property
  rw [hb, map_zero, sub_zero]

/-- Comparing a kernel with itself gives the identity continuous linear equivalence. -/
@[simp]
theorem kerContinuousLinearEquivOfCommonRightInverse_refl
    [IsTopologicalAddGroup A]
    (hΔrr : Continuous (fun a : LinearMap.ker r =>
      Γ (r (a : A)) - Γ (r (a : A)))) :
    kerContinuousLinearEquivOfCommonRightInverse Γ r r hr hr hΔrr hΔrr =
      ContinuousLinearEquiv.refl K (LinearMap.ker r) := by
  apply DFunLike.ext
  intro a
  exact congrArg (fun e : LinearMap.ker r ≃ₗ[K] LinearMap.ker r => e a)
    (kerEquivOfCommonRightInverse_refl Γ r hr)

/-- Reversing the retractions gives the inverse comparison, independently of
which continuity witnesses are supplied for the reversed correction. -/
theorem kerContinuousLinearEquivOfCommonRightInverse_symm
    [IsTopologicalAddGroup A]
    (hΔsr_s : Continuous (fun b : LinearMap.ker s =>
      Γ (s (b : A)) - Γ (r (b : A))))
    (hΔsr_r : Continuous (fun a : LinearMap.ker r =>
      Γ (s (a : A)) - Γ (r (a : A)))) :
    (kerContinuousLinearEquivOfCommonRightInverse Γ r s hr hs hΔr hΔs).symm =
      kerContinuousLinearEquivOfCommonRightInverse Γ s r hs hr hΔsr_s hΔsr_r := by
  apply DFunLike.ext
  intro b
  exact congrArg (fun e : LinearMap.ker s ≃ₗ[K] LinearMap.ker r => e b)
    (kerEquivOfCommonRightInverse_symm Γ r s hr hs)

/-- Comparisons with a fixed common section compose in order. The equality holds
for any continuity witnesses specifying the three comparisons. -/
theorem kerContinuousLinearEquivOfCommonRightInverse_trans
    [IsTopologicalAddGroup A]
    (t : A →ₗ[K] H) (ht : ∀ h : H, t (Γ h) = h)
    (hΔst_s : Continuous (fun b : LinearMap.ker s =>
      Γ (s (b : A)) - Γ (t (b : A))))
    (hΔst_t : Continuous (fun c : LinearMap.ker t =>
      Γ (s (c : A)) - Γ (t (c : A))))
    (hΔrt_r : Continuous (fun a : LinearMap.ker r =>
      Γ (r (a : A)) - Γ (t (a : A))))
    (hΔrt_t : Continuous (fun c : LinearMap.ker t =>
      Γ (r (c : A)) - Γ (t (c : A)))) :
    (kerContinuousLinearEquivOfCommonRightInverse Γ r s hr hs hΔr hΔs).trans
        (kerContinuousLinearEquivOfCommonRightInverse Γ s t hs ht hΔst_s hΔst_t) =
      kerContinuousLinearEquivOfCommonRightInverse Γ r t hr ht hΔrt_r hΔrt_t := by
  apply DFunLike.ext
  intro a
  exact congrArg (fun e : LinearMap.ker r ≃ₗ[K] LinearMap.ker t => e a)
    (kerEquivOfCommonRightInverse_trans Γ r s t hr hs ht)

/-- Global continuity of the ambient correction supplies its two kernel
restrictions. This is a sufficient caller convenience, not an additional
requirement of the restricted-continuity construction. -/
noncomputable def kerContinuousLinearEquivOfCommonRightInverseOfContinuous
    [IsTopologicalAddGroup A]
    (hΔ : Continuous (fun a : A => Γ (r a) - Γ (s a))) :
    LinearMap.ker r ≃L[K] LinearMap.ker s :=
  kerContinuousLinearEquivOfCommonRightInverse Γ r s hr hs
    (hΔ.comp continuous_subtype_val) (hΔ.comp continuous_subtype_val)

variable (hΔ : Continuous (fun a : A => Γ (r a) - Γ (s a)))

/-- The globally continuous construction forgets to the same algebraic comparison. -/
@[simp]
theorem kerContinuousLinearEquivOfCommonRightInverseOfContinuous_toLinearEquiv
    [IsTopologicalAddGroup A] :
    (kerContinuousLinearEquivOfCommonRightInverseOfContinuous Γ r s hr hs hΔ).toLinearEquiv =
      LinearMap.kerEquivOfCommonRightInverse Γ r s hr hs := by
  rfl

/-- Restricting a global continuity certificate gives the restricted construction. -/
theorem kerContinuousLinearEquivOfCommonRightInverseOfContinuous_eq
    [IsTopologicalAddGroup A] :
    kerContinuousLinearEquivOfCommonRightInverseOfContinuous Γ r s hr hs hΔ =
      kerContinuousLinearEquivOfCommonRightInverse Γ r s hr hs
        (hΔ.comp continuous_subtype_val) (hΔ.comp continuous_subtype_val) := by
  rfl

/-- The global-continuity specialization has the same forward residual formula. -/
@[simp]
theorem coe_kerContinuousLinearEquivOfCommonRightInverseOfContinuous_apply
    [IsTopologicalAddGroup A]
    (a : LinearMap.ker r) :
    (kerContinuousLinearEquivOfCommonRightInverseOfContinuous Γ r s hr hs hΔ a : A) =
      (a : A) - Γ (s (a : A)) := by
  exact coe_kerContinuousLinearEquivOfCommonRightInverse_apply Γ r s hr hs
    (hΔ.comp continuous_subtype_val) (hΔ.comp continuous_subtype_val) a

/-- The global-continuity specialization has the same inverse residual formula. -/
theorem coe_kerContinuousLinearEquivOfCommonRightInverseOfContinuous_symm_apply
    [IsTopologicalAddGroup A]
    (b : LinearMap.ker s) :
    ((kerContinuousLinearEquivOfCommonRightInverseOfContinuous Γ r s hr hs hΔ).symm b : A) =
      (b : A) - Γ (r (b : A)) := by
  exact coe_kerContinuousLinearEquivOfCommonRightInverse_symm_apply Γ r s hr hs
    (hΔ.comp continuous_subtype_val) (hΔ.comp continuous_subtype_val) b

/-- A kernel-valued parametrization is ambient-continuous exactly when its
common-section residual is. Only the ambient correction must be globally
continuous; the individual retractions and section need not be continuous. -/
theorem continuous_sub_commonRightInverse_iff
    [IsTopologicalAddGroup A]
    (hr : ∀ h : H, r (Γ h) = h) (hs : ∀ h : H, s (Γ h) = h)
    (hΔ : Continuous (fun a : A => Γ (r a) - Γ (s a)))
    {X : Type uX} [TopologicalSpace X] (f : X → LinearMap.ker r) :
    Continuous (fun x : X => (f x : A) - Γ (s (f x : A))) ↔
      Continuous (fun x : X => (f x : A)) := by
  let e := kerContinuousLinearEquivOfCommonRightInverseOfContinuous Γ r s hr hs hΔ
  have he (a : LinearMap.ker r) : (e a : A) = (a : A) - Γ (s (a : A)) :=
    coe_kerContinuousLinearEquivOfCommonRightInverseOfContinuous_apply Γ r s hr hs hΔ a
  constructor
  · intro h
    have h' : Continuous (fun x : X => e (f x)) := by
      apply Continuous.subtype_mk
      simpa only [he] using h
    have h'' := continuous_subtype_val.comp (e.symm.continuous.comp h')
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using h''
  · intro h
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      exact h
    have h' := continuous_subtype_val.comp (e.continuous.comp hf)
    simpa only [Function.comp_def, he] using h'

end LinearMap

namespace ContinuousLinearMap

variable {K : Type uK} [Semiring K]
variable {H : Type uH} [AddCommMonoid H] [Module K H] [TopologicalSpace H]
variable {A : Type uA} [AddCommGroup A] [Module K A] [TopologicalSpace A]

/-- The continuous linear equivalence between kernels of two continuous linear
maps with a common right inverse. It specializes the ambient-correction
construction, with the same algebraic kernel comparison. -/
noncomputable def kerEquivOfCommonRightInverse
    [IsTopologicalAddGroup A]
    (Γ : H →L[K] A) (r s : A →L[K] H)
    (hr : r.comp Γ = ContinuousLinearMap.id K H)
    (hs : s.comp Γ = ContinuousLinearMap.id K H) :
    LinearMap.ker r.toLinearMap ≃L[K] LinearMap.ker s.toLinearMap :=
  LinearMap.kerContinuousLinearEquivOfCommonRightInverseOfContinuous
    Γ.toLinearMap r.toLinearMap s.toLinearMap
    (fun h => congrArg (fun f : H →L[K] H => f h) hr)
    (fun h => congrArg (fun f : H →L[K] H => f h) hs)
    ((Γ.continuous.comp r.continuous).sub (Γ.continuous.comp s.continuous))

/-- Continuous linear input data agree with the global ambient-correction
specialization on their underlying linear maps. -/
theorem kerEquivOfCommonRightInverse_eq_kerContinuousLinearEquiv
    [IsTopologicalAddGroup A]
    (Γ : H →L[K] A) (r s : A →L[K] H)
    (hr : r.comp Γ = ContinuousLinearMap.id K H)
    (hs : s.comp Γ = ContinuousLinearMap.id K H) :
    kerEquivOfCommonRightInverse Γ r s hr hs =
      LinearMap.kerContinuousLinearEquivOfCommonRightInverseOfContinuous
        Γ.toLinearMap r.toLinearMap s.toLinearMap
        (fun h => congrArg (fun f : H →L[K] H => f h) hr)
        (fun h => congrArg (fun f : H →L[K] H => f h) hs)
        ((Γ.continuous.comp r.continuous).sub (Γ.continuous.comp s.continuous)) := by
  rfl

/-- The ambient formula for the common-section comparison. -/
@[simp]
theorem coe_kerEquivOfCommonRightInverse_apply
    [IsTopologicalAddGroup A]
    (Γ : H →L[K] A) (r s : A →L[K] H)
    (hr : r.comp Γ = ContinuousLinearMap.id K H)
    (hs : s.comp Γ = ContinuousLinearMap.id K H) (a : LinearMap.ker r.toLinearMap) :
    (kerEquivOfCommonRightInverse Γ r s hr hs a : A) = (a : A) - Γ (s (a : A)) := by
  exact LinearMap.coe_kerContinuousLinearEquivOfCommonRightInverseOfContinuous_apply
    Γ.toLinearMap r.toLinearMap s.toLinearMap
    (fun h => congrArg (fun f : H →L[K] H => f h) hr)
    (fun h => congrArg (fun f : H →L[K] H => f h) hs)
    ((Γ.continuous.comp r.continuous).sub (Γ.continuous.comp s.continuous)) a

/-- The ambient formula for the inverse common-section comparison. -/
theorem coe_kerEquivOfCommonRightInverse_symm_apply
    [IsTopologicalAddGroup A]
    (Γ : H →L[K] A)
    (r s : A →L[K] H) (hr : r.comp Γ = ContinuousLinearMap.id K H)
    (hs : s.comp Γ = ContinuousLinearMap.id K H) (b : LinearMap.ker s.toLinearMap) :
    ((kerEquivOfCommonRightInverse Γ r s hr hs).symm b : A) =
      (b : A) - Γ (r (b : A)) := by
  exact LinearMap.coe_kerContinuousLinearEquivOfCommonRightInverseOfContinuous_symm_apply
    Γ.toLinearMap r.toLinearMap s.toLinearMap
    (fun h => congrArg (fun f : H →L[K] H => f h) hr)
    (fun h => congrArg (fun f : H →L[K] H => f h) hs)
    ((Γ.continuous.comp r.continuous).sub (Γ.continuous.comp s.continuous)) b

/-- Comparing a kernel with itself is the identity equivalence. -/
@[simp]
theorem kerEquivOfCommonRightInverse_refl
    [IsTopologicalAddGroup A]
    (Γ : H →L[K] A) (r : A →L[K] H)
    (hr : r.comp Γ = ContinuousLinearMap.id K H) :
    kerEquivOfCommonRightInverse Γ r r hr hr =
      ContinuousLinearEquiv.refl K (LinearMap.ker r.toLinearMap) := by
  apply DFunLike.ext
  intro a
  exact congrArg
    (fun e : LinearMap.ker r.toLinearMap ≃ₗ[K] LinearMap.ker r.toLinearMap => e a)
    (LinearMap.kerEquivOfCommonRightInverse_refl Γ.toLinearMap r.toLinearMap
      (fun h => congrArg (fun f : H →L[K] H => f h) hr))

/-- Reversing the pair of maps gives the inverse comparison. -/
@[simp]
theorem kerEquivOfCommonRightInverse_symm
    [IsTopologicalAddGroup A]
    (Γ : H →L[K] A) (r s : A →L[K] H)
    (hr : r.comp Γ = ContinuousLinearMap.id K H)
    (hs : s.comp Γ = ContinuousLinearMap.id K H) :
    (kerEquivOfCommonRightInverse Γ r s hr hs).symm =
      kerEquivOfCommonRightInverse Γ s r hs hr := by
  apply DFunLike.ext
  intro b
  exact congrArg
    (fun e : LinearMap.ker s.toLinearMap ≃ₗ[K] LinearMap.ker r.toLinearMap => e b)
    (LinearMap.kerEquivOfCommonRightInverse_symm Γ.toLinearMap r.toLinearMap s.toLinearMap
      (fun h => congrArg (fun f : H →L[K] H => f h) hr)
      (fun h => congrArg (fun f : H →L[K] H => f h) hs))

/-- Kernel comparisons with a fixed common section compose in order. -/
@[simp]
theorem kerEquivOfCommonRightInverse_trans
    [IsTopologicalAddGroup A]
    (Γ : H →L[K] A) (r s t : A →L[K] H)
    (hr : r.comp Γ = ContinuousLinearMap.id K H)
    (hs : s.comp Γ = ContinuousLinearMap.id K H)
    (ht : t.comp Γ = ContinuousLinearMap.id K H) :
    (kerEquivOfCommonRightInverse Γ r s hr hs).trans
        (kerEquivOfCommonRightInverse Γ s t hs ht) =
      kerEquivOfCommonRightInverse Γ r t hr ht := by
  apply DFunLike.ext
  intro a
  exact congrArg
    (fun e : LinearMap.ker r.toLinearMap ≃ₗ[K] LinearMap.ker t.toLinearMap => e a)
    (LinearMap.kerEquivOfCommonRightInverse_trans Γ.toLinearMap
      r.toLinearMap s.toLinearMap t.toLinearMap
      (fun h => congrArg (fun f : H →L[K] H => f h) hr)
      (fun h => congrArg (fun f : H →L[K] H => f h) hs)
      (fun h => congrArg (fun f : H →L[K] H => f h) ht))

end ContinuousLinearMap

namespace LinearMap

variable {T : Type uT} [TopologicalSpace T]
variable {K : Type uK} [Semiring K]
variable {H : T → Type uH} [∀ t, AddCommMonoid (H t)] [∀ t, Module K (H t)]
variable {A : Type uA} [AddCommGroup A] [Module K A]
variable [TopologicalSpace A] [IsTopologicalAddGroup A]

variable (Γ : ∀ t, H t →ₗ[K] A) (r q : ∀ t, A →ₗ[K] H t)
variable (hr : ∀ t h, r t (Γ t h) = h) (hq : ∀ t h, q t (Γ t h) = h)
variable (hΔ : Continuous (fun p : T × A => Γ p.1 (r p.1 p.2) - Γ p.1 (q p.1 p.2)))

/-- Compare the original product-subtype total spaces of two kernel families
with a common section. Only the difference of the two ambient projections must
be jointly continuous. The forward ambient formula is `(t, a + Δ t a)` and the
inverse is `(t, a - Δ t a)`, where `Δ t a = Γ t (r t a) - Γ t (q t a)`.
The fibres `H t` need neither topologies nor additive group structures. -/
noncomputable def kerFamilyHomeomorphOfCommonRightInverse :
    {p : T × A // r p.1 p.2 = 0} ≃ₜ {p : T × A // q p.1 p.2 = 0} where
  toFun p :=
    let e := LinearMap.kerEquivOfCommonRightInverse
      (Γ p.val.1) (r p.val.1) (q p.val.1) (hr p.val.1) (hq p.val.1)
    ⟨(p.val.1, (e ⟨p.val.2, p.property⟩ : A)), (e ⟨p.val.2, p.property⟩).property⟩
  invFun p :=
    let e := LinearMap.kerEquivOfCommonRightInverse
      (Γ p.val.1) (r p.val.1) (q p.val.1) (hr p.val.1) (hq p.val.1)
    ⟨(p.val.1, (e.symm ⟨p.val.2, p.property⟩ : A)),
      (e.symm ⟨p.val.2, p.property⟩).property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        ((LinearMap.kerEquivOfCommonRightInverse (Γ p.val.1) (r p.val.1) (q p.val.1)
          (hr p.val.1) (hq p.val.1)).left_inv ⟨p.val.2, p.property⟩)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        ((LinearMap.kerEquivOfCommonRightInverse (Γ p.val.1) (r p.val.1) (q p.val.1)
          (hr p.val.1) (hq p.val.1)).right_inv ⟨p.val.2, p.property⟩)
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun p : {p : T × A // r p.1 p.2 = 0} =>
        (p.val.1, p.val.2 + (Γ p.val.1 (r p.val.1 p.val.2) -
          Γ p.val.1 (q p.val.1 p.val.2)))) :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).add (hΔ.comp continuous_subtype_val))
    convert hc using 1
    funext p
    apply Prod.ext
    · rfl
    · rw [LinearMap.coe_kerEquivOfCommonRightInverse_apply,
        p.property, map_zero, zero_sub, sub_eq_add_neg]
  continuous_invFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun p : {p : T × A // q p.1 p.2 = 0} =>
        (p.val.1, p.val.2 - (Γ p.val.1 (r p.val.1 p.val.2) -
          Γ p.val.1 (q p.val.1 p.val.2)))) :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).sub (hΔ.comp continuous_subtype_val))
    convert hc using 1
    funext p
    apply Prod.ext
    · rfl
    · rw [LinearMap.coe_kerEquivOfCommonRightInverse_symm_apply,
        p.property, map_zero, sub_zero]

/-- Kernel-family comparison preserves the base point. -/
@[simp]
theorem kerFamilyHomeomorphOfCommonRightInverse_apply_fst
    (p : {p : T × A // r p.1 p.2 = 0}) :
    (kerFamilyHomeomorphOfCommonRightInverse Γ r q hr hq hΔ p).val.1 = p.val.1 :=
  rfl

/-- The inverse comparison also preserves the base point. -/
theorem kerFamilyHomeomorphOfCommonRightInverse_symm_apply_fst
    (p : {p : T × A // q p.1 p.2 = 0}) :
    ((kerFamilyHomeomorphOfCommonRightInverse Γ r q hr hq hΔ).symm p).val.1 = p.val.1 :=
  rfl

/-- On a kernel the forward ambient value is the usual residual. -/
@[simp]
theorem kerFamilyHomeomorphOfCommonRightInverse_apply_snd
    (p : {p : T × A // r p.1 p.2 = 0}) :
    (kerFamilyHomeomorphOfCommonRightInverse Γ r q hr hq hΔ p).val.2 =
      p.val.2 - Γ p.val.1 (q p.val.1 p.val.2) :=
  rfl

/-- On a kernel the inverse ambient value is the reverse residual. -/
theorem kerFamilyHomeomorphOfCommonRightInverse_symm_apply_snd
    (p : {p : T × A // q p.1 p.2 = 0}) :
    ((kerFamilyHomeomorphOfCommonRightInverse Γ r q hr hq hΔ).symm p).val.2 =
      p.val.2 - Γ p.val.1 (r p.val.1 p.val.2) :=
  rfl

/-- The jointly continuous ambient formula for the forward comparison. -/
theorem kerFamilyHomeomorphOfCommonRightInverse_apply_val
    (p : {p : T × A // r p.1 p.2 = 0}) :
    (kerFamilyHomeomorphOfCommonRightInverse Γ r q hr hq hΔ p).val =
      (p.val.1, p.val.2 + (Γ p.val.1 (r p.val.1 p.val.2) -
        Γ p.val.1 (q p.val.1 p.val.2))) := by
  apply Prod.ext
  · rfl
  · rw [kerFamilyHomeomorphOfCommonRightInverse_apply_snd,
      p.property, map_zero, zero_sub, sub_eq_add_neg]

/-- The jointly continuous ambient formula for the inverse comparison. -/
theorem kerFamilyHomeomorphOfCommonRightInverse_symm_apply_val
    (p : {p : T × A // q p.1 p.2 = 0}) :
    ((kerFamilyHomeomorphOfCommonRightInverse Γ r q hr hq hΔ).symm p).val =
      (p.val.1, p.val.2 - (Γ p.val.1 (r p.val.1 p.val.2) -
        Γ p.val.1 (q p.val.1 p.val.2))) := by
  apply Prod.ext
  · rfl
  · rw [kerFamilyHomeomorphOfCommonRightInverse_symm_apply_snd,
      p.property, map_zero, sub_zero]

/-- Comparing a kernel family with itself gives the identity homeomorphism. -/
@[simp]
theorem kerFamilyHomeomorphOfCommonRightInverse_refl
    (hrr : Continuous (fun p : T × A => Γ p.1 (r p.1 p.2) - Γ p.1 (r p.1 p.2))) :
    kerFamilyHomeomorphOfCommonRightInverse Γ r r hr hr hrr = Homeomorph.refl _ := by
  ext p : 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change p.val.2 - Γ p.val.1 (r p.val.1 p.val.2) = p.val.2
    rw [p.property, map_zero, sub_zero]

/-- Reversing the two families gives the inverse homeomorphism. -/
@[simp]
theorem kerFamilyHomeomorphOfCommonRightInverse_symm :
    (kerFamilyHomeomorphOfCommonRightInverse Γ r q hr hq hΔ).symm =
      kerFamilyHomeomorphOfCommonRightInverse Γ q r hq hr (by
        convert hΔ.neg using 1
        funext p
        change Γ p.1 (q p.1 p.2) - Γ p.1 (r p.1 p.2) =
          -(Γ p.1 (r p.1 p.2) - Γ p.1 (q p.1 p.2))
        rw [neg_sub]) := by
  ext p : 1
  rfl

/-- Kernel-family comparisons with a fixed common section compose in order.
Continuity of the composite ambient difference follows by addition. -/
@[simp]
theorem kerFamilyHomeomorphOfCommonRightInverse_trans
    (s : ∀ t, A →ₗ[K] H t) (hs : ∀ t h, s t (Γ t h) = h)
    (hqs : Continuous (fun p : T × A => Γ p.1 (q p.1 p.2) - Γ p.1 (s p.1 p.2))) :
    (kerFamilyHomeomorphOfCommonRightInverse Γ r q hr hq hΔ).trans
        (kerFamilyHomeomorphOfCommonRightInverse Γ q s hq hs hqs) =
      kerFamilyHomeomorphOfCommonRightInverse Γ r s hr hs (by
        convert hΔ.add hqs using 1
        funext p
        change Γ p.1 (r p.1 p.2) - Γ p.1 (s p.1 p.2) =
          (Γ p.1 (r p.1 p.2) - Γ p.1 (q p.1 p.2)) +
            (Γ p.1 (q p.1 p.2) - Γ p.1 (s p.1 p.2))
        abel) := by
  ext p : 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact congrArg
      (fun e : LinearMap.ker (r p.val.1) ≃ₗ[K] LinearMap.ker (s p.val.1) =>
        (e ⟨p.val.2, p.property⟩ : A))
      (LinearMap.kerEquivOfCommonRightInverse_trans (Γ p.val.1)
        (r p.val.1) (q p.val.1) (s p.val.1) (hr p.val.1) (hq p.val.1) (hs p.val.1))

end LinearMap

namespace ContinuousLinearMap

variable {T : Type uT} [TopologicalSpace T]
variable {K : Type uK} [Semiring K]
variable {H : T → Type uH} [∀ t, AddCommMonoid (H t)] [∀ t, Module K (H t)]
variable [∀ t, TopologicalSpace (H t)]
variable {A : Type uA} [AddCommGroup A] [Module K A]
variable [TopologicalSpace A] [IsTopologicalAddGroup A]

/-- For compatible continuous linear data, the family comparison restricts at
each base point to the pointwise continuous linear kernel comparison. These fibre
topologies are required to specify the continuous linear data. -/
theorem kerFamilyHomeomorphOfCommonRightInverse_apply_eq
    (Γ : ∀ t, H t →L[K] A) (r q : ∀ t, A →L[K] H t)
    (hr : ∀ t, (r t).comp (Γ t) = ContinuousLinearMap.id K (H t))
    (hq : ∀ t, (q t).comp (Γ t) = ContinuousLinearMap.id K (H t))
    (hΔ : Continuous (fun p : T × A => Γ p.1 (r p.1 p.2) - Γ p.1 (q p.1 p.2)))
    (t : T) (a : LinearMap.ker (r t).toLinearMap) :
    (LinearMap.kerFamilyHomeomorphOfCommonRightInverse
      (fun t => (Γ t).toLinearMap) (fun t => (r t).toLinearMap)
      (fun t => (q t).toLinearMap)
      (fun t h => congrArg (fun f : H t →L[K] H t => f h) (hr t))
      (fun t h => congrArg (fun f : H t →L[K] H t => f h) (hq t)) hΔ
      ⟨(t, (a : A)), a.property⟩).val =
        (t, (kerEquivOfCommonRightInverse (Γ t) (r t) (q t) (hr t) (hq t) a : A)) :=
  rfl

end ContinuousLinearMap

namespace LinearMap

variable {T : Type uT} [TopologicalSpace T]
variable {K : Type uK} [Semiring K]
variable {H : T → Type uH} [∀ t, AddCommMonoid (H t)] [∀ t, Module K (H t)]
variable {A : Type uA} [AddCommGroup A] [Module K A] [TopologicalSpace A]

/-- The kernel-family comparison acts at each base point by the continuous linear
kernel comparison on that fibre. Joint continuity of the ambient correction
supplies its global continuity on the fibre, without topologies on `H t`. -/
theorem kerFamilyHomeomorphOfCommonRightInverse_apply_eq_kerContinuousLinearEquiv
    [IsTopologicalAddGroup A]
    (Γ : ∀ t, H t →ₗ[K] A) (r q : ∀ t, A →ₗ[K] H t)
    (hr : ∀ t h, r t (Γ t h) = h) (hq : ∀ t h, q t (Γ t h) = h)
    (hΔ : Continuous (fun p : T × A => Γ p.1 (r p.1 p.2) - Γ p.1 (q p.1 p.2)))
    (t : T) (a : LinearMap.ker (r t)) :
    (kerFamilyHomeomorphOfCommonRightInverse Γ r q hr hq hΔ
      ⟨(t, (a : A)), a.property⟩).val =
        (t, (kerContinuousLinearEquivOfCommonRightInverseOfContinuous
          (Γ t) (r t) (q t) (hr t) (hq t)
          (hΔ.comp ((continuous_const : Continuous (fun _ : A => t)).prodMk continuous_id))
          a : A)) := by
  apply Prod.ext
  · exact kerFamilyHomeomorphOfCommonRightInverse_apply_fst Γ r q hr hq hΔ
      ⟨(t, (a : A)), a.property⟩
  · rw [kerFamilyHomeomorphOfCommonRightInverse_apply_snd,
      coe_kerContinuousLinearEquivOfCommonRightInverseOfContinuous_apply]

end LinearMap
