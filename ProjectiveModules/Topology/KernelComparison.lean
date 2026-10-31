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

For continuous linear maps `r, s : A →L[K] H` with a common right inverse
`Γ : H →L[K] A`, `ContinuousLinearMap.kerEquivOfCommonRightInverse` identifies
`ker r` with `ker s`. Its ambient formula is `a ↦ a - Γ (s a)`, and the inverse
has formula `b ↦ b - Γ (r b)`. These equivalences satisfy identity, symmetry,
and composition laws.

The algebraic kernel comparison is shared with
`LinearMap.kerFamilyHomeomorphOfCommonRightInverse`. The latter compares the
original product-subtype total spaces of kernels for varying fibres `H t`.
Only the ambient difference `Γ t (r t a) - Γ t (q t a)` must be jointly
continuous; none of the individual linear maps needs to be continuous.

Kernels carry the subspace topology from the given topology on `A`. The scalar
semiring needs no topology, and the fibres need only their given additive
commutative monoid and module structures: all subtraction takes place in `A`.
-/

@[expose] public section

universe uT uK uH uA

namespace ContinuousLinearMap

variable {K : Type uK} [Semiring K]
variable {H : Type uH} [AddCommMonoid H] [Module K H] [TopologicalSpace H]
variable {A : Type uA} [AddCommGroup A] [Module K A] [TopologicalSpace A]

variable [IsTopologicalAddGroup A]

/-- The continuous linear equivalence between kernels of two maps with a common
right inverse. In the ambient module it sends `a` to `a - Γ (s a)`. -/
noncomputable def kerEquivOfCommonRightInverse (Γ : H →L[K] A) (r s : A →L[K] H)
    (hr : r.comp Γ = ContinuousLinearMap.id K H)
    (hs : s.comp Γ = ContinuousLinearMap.id K H) :
    LinearMap.ker r.toLinearMap ≃L[K] LinearMap.ker s.toLinearMap :=
  { toLinearEquiv := LinearMap.kerEquivOfCommonRightInverse
      Γ.toLinearMap r.toLinearMap s.toLinearMap
      (fun h => congrArg (fun f : H →L[K] H => f h) hr)
      (fun h => congrArg (fun f : H →L[K] H => f h) hs)
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.sub
        (Γ.continuous.comp (s.continuous.comp continuous_subtype_val))
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.sub
        (Γ.continuous.comp (r.continuous.comp continuous_subtype_val)) }

/-- The ambient formula for the common-section comparison. -/
@[simp]
theorem coe_kerEquivOfCommonRightInverse_apply (Γ : H →L[K] A) (r s : A →L[K] H)
    (hr : r.comp Γ = ContinuousLinearMap.id K H)
    (hs : s.comp Γ = ContinuousLinearMap.id K H) (a : LinearMap.ker r.toLinearMap) :
    (kerEquivOfCommonRightInverse Γ r s hr hs a : A) = (a : A) - Γ (s (a : A)) :=
  rfl

/-- The ambient formula for the inverse common-section comparison. -/
theorem coe_kerEquivOfCommonRightInverse_symm_apply (Γ : H →L[K] A)
    (r s : A →L[K] H) (hr : r.comp Γ = ContinuousLinearMap.id K H)
    (hs : s.comp Γ = ContinuousLinearMap.id K H) (b : LinearMap.ker s.toLinearMap) :
    ((kerEquivOfCommonRightInverse Γ r s hr hs).symm b : A) =
      (b : A) - Γ (r (b : A)) :=
  rfl

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
  exact congrArg
    (fun e : LinearMap.ker r.toLinearMap ≃ₗ[K] LinearMap.ker t.toLinearMap => (e a : A))
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
