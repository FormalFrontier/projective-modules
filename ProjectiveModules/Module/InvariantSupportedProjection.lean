/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import ProjectiveModules.Module.CountablyGenerated
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Projection

/-!
# Invariant coordinate supports of an idempotent endomorphism

This file studies the part of the range of an idempotent endomorphism that is
supported on a chosen invariant set of coordinates.  Nested invariant supports
give split inclusions of these range pieces.  If the coordinate increment is
countable, the complementary kernel is countably generated as well as
projective.
-/

@[expose] public section

noncomputable section

open Set Submodule

namespace LinearMap

universe uR uI

variable {R : Type uR} [Ring R] {ι : Type uI}

attribute [local instance] Classical.propDecidable

/-- The elements in the range of `p` whose coordinates are supported on `s`. -/
def supportedRange (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) (s : Set ι) :
    Submodule R (ι →₀ R) :=
  LinearMap.range p ⊓ Finsupp.supported R R s

/-- Supported range pieces are monotone in their coordinate set. -/
theorem supportedRange_mono (p : (ι →₀ R) →ₗ[R] (ι →₀ R))
    {s t : Set ι} (hst : s ⊆ t) :
    p.supportedRange s ≤ p.supportedRange t :=
  fun _ hx ↦ ⟨hx.1, Finsupp.supported_mono hst hx.2⟩

/-- The natural inclusion between nested supported range pieces. -/
def supportedRangeInclusion (p : (ι →₀ R) →ₗ[R] (ι →₀ R))
    {s t : Set ι} (hst : s ⊆ t) :
    p.supportedRange s →ₗ[R] p.supportedRange t :=
  Submodule.inclusion (p.supportedRange_mono hst)

/-- On an invariant coordinate set, applying `p` lands in its supported
range. -/
def supportedRangeProjection (p : (ι →₀ R) →ₗ[R] (ι →₀ R))
    (s : Set ι)
    (hinv : Finsupp.supported R R s ≤
      (Finsupp.supported R R s).comap p) :
    Finsupp.supported R R s →ₗ[R] p.supportedRange s :=
  LinearMap.codRestrict (p.supportedRange s)
    (p.domRestrict (Finsupp.supported R R s)) fun x ↦
      ⟨⟨x, rfl⟩, hinv x.2⟩

/-- The supported range piece includes into its supported standard free
module. -/
def supportedRangeToSupported (p : (ι →₀ R) →ₗ[R] (ι →₀ R))
    (s : Set ι) :
    p.supportedRange s →ₗ[R] Finsupp.supported R R s :=
  Submodule.inclusion inf_le_right

/-- For an idempotent endomorphism, supported range projection retracts the
natural inclusion. -/
theorem supportedRangeProjection_comp_toSupported
    (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) (hp : IsIdempotentElem p)
    (s : Set ι)
    (hinv : Finsupp.supported R R s ≤
      (Finsupp.supported R R s).comap p) :
    (p.supportedRangeProjection s hinv).comp
      (p.supportedRangeToSupported s) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact (IsIdempotentElem.mem_range_iff hp).mp x.2.1

/-- An invariant supported piece of the range of an idempotent endomorphism
is projective. -/
theorem supportedRange_projective
    (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) (hp : IsIdempotentElem p)
    (s : Set ι)
    (hinv : Finsupp.supported R R s ≤
      (Finsupp.supported R R s).comap p) :
    Module.Projective R (p.supportedRange s) := by
  let _ : Module.Projective R (Finsupp.supported R R s) :=
    Module.Projective.of_equiv'
      (Finsupp.supportedEquivFinsupp (R := R) s).symm
  exact Module.Projective.of_split
    (p.supportedRangeToSupported s)
    (p.supportedRangeProjection s hinv)
    (p.supportedRangeProjection_comp_toSupported hp s hinv)

/-- Restriction to `s`, followed by `p`, retracts a later supported range piece
onto the earlier one. -/
def supportedRangeRetraction (p : (ι →₀ R) →ₗ[R] (ι →₀ R))
    (s t : Set ι)
    (hinv : Finsupp.supported R R s ≤
      (Finsupp.supported R R s).comap p) :
    p.supportedRange t →ₗ[R] p.supportedRange s :=
  by
    classical
    exact (p.supportedRangeProjection s hinv).comp <|
      (Finsupp.restrictDom R R s).comp (p.supportedRange t).subtype

/-- The retraction of a nested supported range piece is a right inverse to its
natural inclusion. -/
theorem supportedRangeRetraction_comp_inclusion
    (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) (hp : IsIdempotentElem p)
    {s t : Set ι} (hst : s ⊆ t)
    (hinv : Finsupp.supported R R s ≤
      (Finsupp.supported R R s).comap p) :
    (p.supportedRangeRetraction s t hinv).comp
      (p.supportedRangeInclusion hst) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change p (Finsupp.filter (· ∈ s) (x : ι →₀ R)) = x
  have hfilter : Finsupp.filter (· ∈ s) (x : ι →₀ R) = x :=
    (Finsupp.filter_eq_self_iff _ _).2 fun i hi ↦
      x.2.2 (Finsupp.mem_support_iff.mpr hi)
  rw [hfilter]
  exact (IsIdempotentElem.mem_range_iff hp).mp x.2.1

/-- A later supported range piece is the product of an earlier piece and the
kernel of the canonical retraction. -/
noncomputable def supportedRangeProdComplementEquiv
    (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) (hp : IsIdempotentElem p)
    {s t : Set ι} (hst : s ⊆ t)
    (hinv : Finsupp.supported R R s ≤
      (Finsupp.supported R R s).comap p) :
    (LinearMap.ker (p.supportedRangeRetraction s t hinv) ×
      p.supportedRange s) ≃ₗ[R] p.supportedRange t :=
  by
    let i : p.supportedRange s →ₗ[R] p.supportedRange t :=
      p.supportedRangeInclusion hst
    let r : p.supportedRange t →ₗ[R] p.supportedRange s :=
      p.supportedRangeRetraction s t hinv
    have hsplit : r.comp i = LinearMap.id :=
      p.supportedRangeRetraction_comp_inclusion hp hst hinv
    let _ : AddCommGroup (p.supportedRange s) := inferInstance
    let _ : AddCommGroup (p.supportedRange t) := inferInstance
    let _ : AddCommGroup (LinearMap.ker r) := inferInstance
    change (LinearMap.ker r × p.supportedRange s) ≃ₗ[R]
      p.supportedRange t
    exact lequivProdOfRightSplitExact (R := R)
      (A := LinearMap.ker r) (M := p.supportedRange t)
      (B := p.supportedRange s) (j := (LinearMap.ker r).subtype)
      (g := r) (f := i) Subtype.val_injective
      (Submodule.range_subtype _) hsplit

/-- Projection from a split module onto the kernel of its retraction. -/
def splitKernelProjection {A M : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M]
    (i : A →ₗ[R] M) (r : M →ₗ[R] A)
    (h : r.comp i = LinearMap.id) : M →ₗ[R] LinearMap.ker r :=
  LinearMap.codRestrict (LinearMap.ker r)
    (LinearMap.id - i.comp r) fun x ↦ by
      rw [LinearMap.mem_ker]
      change r (x - i (r x)) = 0
      rw [map_sub, show r (i (r x)) = r x by
        rw [← LinearMap.comp_apply, h, LinearMap.id_apply], sub_self]

/-- The split-kernel projection retracts the kernel subtype. -/
theorem splitKernelProjection_comp_subtype {A M : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M]
    (i : A →ₗ[R] M) (r : M →ₗ[R] A)
    (h : r.comp i = LinearMap.id) :
    (splitKernelProjection i r h).comp (LinearMap.ker r).subtype =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change x - i (r x) = x
  rw [LinearMap.mem_ker.mp x.2, map_zero, sub_zero]

/-- The kernel of a retraction from a projective module is projective. -/
theorem projective_splitKernel {A M : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M]
    [Module.Projective R M]
    (i : A →ₗ[R] M) (r : M →ₗ[R] A)
    (h : r.comp i = LinearMap.id) :
    Module.Projective R (LinearMap.ker r) :=
  Module.Projective.of_split (LinearMap.ker r).subtype
    (splitKernelProjection i r h)
    (splitKernelProjection_comp_subtype i r h)

/-- The complement of an earlier invariant supported range piece in a later
one is projective. -/
theorem supportedRangeComplement_projective
    (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) (hp : IsIdempotentElem p)
    {s t : Set ι} (hst : s ⊆ t)
    (hs : Finsupp.supported R R s ≤
      (Finsupp.supported R R s).comap p)
    (ht : Finsupp.supported R R t ≤
      (Finsupp.supported R R t).comap p) :
    Module.Projective R (LinearMap.ker
      (p.supportedRangeRetraction s t hs)) := by
  let _ : Module.Projective R (p.supportedRange t) :=
    p.supportedRange_projective hp t ht
  let i : p.supportedRange s →ₗ[R] p.supportedRange t :=
    p.supportedRangeInclusion hst
  let r : p.supportedRange t →ₗ[R] p.supportedRange s :=
    p.supportedRangeRetraction s t hs
  have h : r.comp i = LinearMap.id :=
    p.supportedRangeRetraction_comp_inclusion hp hst hs
  change Module.Projective R (LinearMap.ker r)
  exact projective_splitKernel (R := R)
    (A := p.supportedRange s) (M := p.supportedRange t) i r h

private theorem filter_add_filter_diff_of_mem_supported
    {s t : Set ι} {x : ι →₀ R}
    (hx : x ∈ Finsupp.supported R R t) :
    Finsupp.filter (· ∈ s) x + Finsupp.filter (· ∈ t \ s) x = x := by
  classical
  ext i
  by_cases his : i ∈ s
  · simp [his]
  by_cases hit : i ∈ t
  · simp [his, hit]
  · have hxi : x i = 0 := (Finsupp.mem_supported' R x).mp hx i hit
    simp [his, hit, hxi]

/-- The coordinate difference maps onto the complement of an earlier
invariant supported range piece. -/
def supportedDifferenceToComplement
    (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) (hp : IsIdempotentElem p)
    {s t : Set ι} (hst : s ⊆ t)
    (hs : Finsupp.supported R R s ≤
      (Finsupp.supported R R s).comap p)
    (ht : Finsupp.supported R R t ≤
      (Finsupp.supported R R t).comap p) :
    Finsupp.supported R R (t \ s) →ₗ[R]
      LinearMap.ker (p.supportedRangeRetraction s t hs) :=
  (splitKernelProjection (R := R)
    (A := p.supportedRange s) (M := p.supportedRange t)
    (p.supportedRangeInclusion hst)
    (p.supportedRangeRetraction s t hs)
    (p.supportedRangeRetraction_comp_inclusion hp hst hs)).comp <|
    (p.supportedRangeProjection t ht).comp <|
      Submodule.inclusion (Finsupp.supported_mono Set.sdiff_subset)

/-- The coordinate-difference map onto the split complement is surjective. -/
theorem supportedDifferenceToComplement_surjective
    (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) (hp : IsIdempotentElem p)
    {s t : Set ι} (hst : s ⊆ t)
    (hs : Finsupp.supported R R s ≤
      (Finsupp.supported R R s).comap p)
    (ht : Finsupp.supported R R t ≤
      (Finsupp.supported R R t).comap p) :
    Function.Surjective
      (p.supportedDifferenceToComplement hp hst hs ht) := by
  classical
  let i : p.supportedRange s →ₗ[R] p.supportedRange t :=
    p.supportedRangeInclusion hst
  let r : p.supportedRange t →ₗ[R] p.supportedRange s :=
    p.supportedRangeRetraction s t hs
  have hsplit : r.comp i = LinearMap.id :=
    p.supportedRangeRetraction_comp_inclusion hp hst hs
  intro y
  let z : Finsupp.supported R R (t \ s) :=
    Finsupp.restrictDom R R (t \ s) ((y : LinearMap.ker r) : ι →₀ R)
  have hker : r (y : LinearMap.ker r) = 0 :=
    LinearMap.mem_ker.mp y.2
  have hs_zero :
      p (Finsupp.filter (· ∈ s) ((y : LinearMap.ker r) : ι →₀ R)) = 0 := by
    have h := congrArg
      (fun x : p.supportedRange s ↦ (x : ι →₀ R)) hker
    change p (Finsupp.filter (· ∈ s)
      ((y : LinearMap.ker r) : ι →₀ R)) = 0 at h
    exact h
  have hy_fixed : p ((y : LinearMap.ker r) : ι →₀ R) = y :=
    (IsIdempotentElem.mem_range_iff hp).mp y.1.2.1
  have hdecomp := filter_add_filter_diff_of_mem_supported
    (s := s) (t := t) (x := ((y : LinearMap.ker r) : ι →₀ R)) y.1.2.2
  have hz_fixed : p (z : ι →₀ R) = y := by
    change p (Finsupp.filter (· ∈ t \ s)
      ((y : LinearMap.ker r) : ι →₀ R)) = y
    calc
      p (Finsupp.filter (· ∈ t \ s)
          ((y : LinearMap.ker r) : ι →₀ R)) =
          0 + p (Finsupp.filter (· ∈ t \ s)
            ((y : LinearMap.ker r) : ι →₀ R)) := by rw [zero_add]
      _ = p (Finsupp.filter (· ∈ s)
            ((y : LinearMap.ker r) : ι →₀ R)) +
          p (Finsupp.filter (· ∈ t \ s)
            ((y : LinearMap.ker r) : ι →₀ R)) := by rw [hs_zero]
      _ = p (Finsupp.filter (· ∈ s)
            ((y : LinearMap.ker r) : ι →₀ R) +
          Finsupp.filter (· ∈ t \ s)
            ((y : LinearMap.ker r) : ι →₀ R)) := by rw [map_add]
      _ = p ((y : LinearMap.ker r) : ι →₀ R) := by rw [hdecomp]
      _ = y := hy_fixed
  have htoRange :
      (p.supportedRangeProjection t ht)
        (Submodule.inclusion
          (Finsupp.supported_mono Set.sdiff_subset) z) =
        (y : LinearMap.ker r) := by
    apply Subtype.ext
    exact hz_fixed
  refine ⟨z, ?_⟩
  simp only [supportedDifferenceToComplement, LinearMap.comp_apply]
  rw [htoRange]
  apply Subtype.ext
  change (y : p.supportedRange t) -
      p.supportedRangeInclusion hst
        (p.supportedRangeRetraction s t hs (y : p.supportedRange t)) =
    (y : p.supportedRange t)
  rw [LinearMap.mem_ker.mp y.2, map_zero]
  exact sub_zero (y : p.supportedRange t)

/-- If the coordinate increment is countable, the complement of the earlier
supported range piece is countably generated. -/
theorem supportedRangeComplement_countablyGenerated
    (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) (hp : IsIdempotentElem p)
    {s t : Set ι} (hst : s ⊆ t)
    (hs : Finsupp.supported R R s ≤
      (Finsupp.supported R R s).comap p)
    (ht : Finsupp.supported R R t ≤
      (Finsupp.supported R R t).comap p)
    (hcount : (t \ s).Countable) :
    Module.CountablyGenerated R (LinearMap.ker
      (p.supportedRangeRetraction s t hs)) :=
  (Module.CountablyGenerated.supported (R := R) (t \ s) hcount).of_surjective
    (p.supportedDifferenceToComplement hp hst hs ht)
    (p.supportedDifferenceToComplement_surjective hp hst hs ht)

end LinearMap
