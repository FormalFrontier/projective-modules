/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import ProjectiveModules.Module.TransfiniteCoordinateFiltration
public import Mathlib.Data.Finset.Max
public import Mathlib.LinearAlgebra.DirectSum.Basis

/-!
# Bases assembled from a transfinite split filtration

This file assembles free split increments along a well-ordered invariant
coordinate filtration.  The result is source-independent: it concerns only an
idempotent endomorphism of a standard free module and the freeness of the
canonical increment at each stage.
-/

@[expose] public section

noncomputable section

open Set Submodule

attribute [local instance] Classical.decEq

namespace LinearMap.CountableInvariantCoordinateFiltration

universe uS uJ

variable {S : Type uS} [Ring S] {κ : Type uJ}
variable {q : (κ →₀ S) →ₗ[S] (κ →₀ S)}

/-- The canonical split increment at a filtration stage. -/
abbrev increment
    (F : LinearMap.CountableInvariantCoordinateFiltration q) (i : κ) :=
  LinearMap.ker (q.supportedRangeRetraction
    (F.before i) (F.through i) (F.before_invariant i))

/-- A split increment, included in the full range of the idempotent. -/
def incrementToRange
    (F : LinearMap.CountableInvariantCoordinateFiltration q) (i : κ) :
    F.increment i →ₗ[S] LinearMap.range q where
  toFun x := ⟨x.1.1, x.1.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Inclusion of a split increment in the full range is injective. -/
theorem incrementToRange_injective
    (F : LinearMap.CountableInvariantCoordinateFiltration q) (i : κ) :
    Function.Injective (F.incrementToRange i) := by
  intro x y hxy
  have hval : ((F.incrementToRange i x : LinearMap.range q) : κ →₀ S) =
      ((F.incrementToRange i y : LinearMap.range q) : κ →₀ S) :=
    congrArg (fun z : LinearMap.range q ↦ (z : κ →₀ S)) hxy
  exact Subtype.ext (Subtype.ext hval)

/-- The copy of a split increment inside the full range of the idempotent. -/
def incrementInRange
    (F : LinearMap.CountableInvariantCoordinateFiltration q) (i : κ) :
    Submodule S (LinearMap.range q) :=
  LinearMap.range (F.incrementToRange i)

/-- A split increment is linearly equivalent to its copy in the full range. -/
noncomputable def incrementEquivInRange
    (F : LinearMap.CountableInvariantCoordinateFiltration q) (i : κ) :
    F.increment i ≃ₗ[S] F.incrementInRange i :=
  LinearEquiv.ofInjective (F.incrementToRange i)
    (F.incrementToRange_injective i)

/-- Elements of the full range supported on a chosen coordinate set. -/
def rangeSupported
    (_F : LinearMap.CountableInvariantCoordinateFiltration q) (s : Set κ) :
    Submodule S (LinearMap.range q) :=
  (Finsupp.supported S S s).comap (LinearMap.range q).subtype

@[simp]
theorem mem_rangeSupported
    (F : LinearMap.CountableInvariantCoordinateFiltration q)
    (s : Set κ) (x : LinearMap.range q) :
    x ∈ F.rangeSupported s ↔ (x : κ →₀ S) ∈ Finsupp.supported S S s :=
  Iff.rfl

/-- Supported pieces of the full range are monotone in the coordinate set. -/
theorem rangeSupported_mono
    (F : LinearMap.CountableInvariantCoordinateFiltration q)
    {s t : Set κ} (hst : s ⊆ t) :
    F.rangeSupported s ≤ F.rangeSupported t :=
  Submodule.comap_mono (Finsupp.supported_mono hst)

/-- Every increment is supported on its completed filtration stage. -/
theorem incrementInRange_le_rangeSupported_through
    (F : LinearMap.CountableInvariantCoordinateFiltration q) (i : κ) :
    F.incrementInRange i ≤ F.rangeSupported (F.through i) := by
  rintro _ ⟨x, rfl⟩
  exact x.1.2.2

/-- An earlier increment is supported before every later stage. -/
theorem incrementInRange_le_rangeSupported_before_of_rel
    (F : LinearMap.CountableInvariantCoordinateFiltration q)
    {i j : κ} (hji : F.r j i) :
    F.incrementInRange j ≤ F.rangeSupported (F.before i) :=
  (F.incrementInRange_le_rangeSupported_through j).trans <|
    F.rangeSupported_mono (F.through_subset_before_of_rel hji)

/-- A split increment meets the preceding supported range only in zero. -/
theorem disjoint_incrementInRange_rangeSupported_before
    (F : LinearMap.CountableInvariantCoordinateFiltration q)
    (hq : IsIdempotentElem q) (i : κ) :
    Disjoint (F.incrementInRange i) (F.rangeSupported (F.before i)) := by
  rw [Submodule.disjoint_def]
  intro y hyinc hybefore
  obtain ⟨x, rfl⟩ := hyinc
  let a : q.supportedRange (F.before i) :=
    ⟨x.1.1, x.1.2.1, hybefore⟩
  have hsplit := q.supportedRangeRetraction_comp_inclusion hq
    (F.before_subset_through i) (F.before_invariant i)
  have hret : q.supportedRangeRetraction
      (F.before i) (F.through i) (F.before_invariant i)
      (q.supportedRangeInclusion (F.before_subset_through i) a) = a := by
    rw [← LinearMap.comp_apply, hsplit, LinearMap.id_apply]
  have hinclusion : q.supportedRangeInclusion
      (F.before_subset_through i) a = x.1 := by
    apply Subtype.ext
    rfl
  have ha : a = 0 := by
    rw [hinclusion, LinearMap.mem_ker.mp x.2] at hret
    exact hret.symm
  apply Subtype.ext
  change (x.1.1 : κ →₀ S) = 0
  exact congrArg Subtype.val ha

/-- Freeness of an increment passes to its copy in the full range. -/
theorem incrementInRange_free
    (F : LinearMap.CountableInvariantCoordinateFiltration q) (i : κ)
    (hfree : Module.Free S (F.increment i)) :
    Module.Free S (F.incrementInRange i) :=
  Module.Free.of_equiv' hfree (F.incrementEquivInRange i)

/-- The split increments form an independent family inside the full range. -/
theorem incrementInRange_iSupIndep
    (F : LinearMap.CountableInvariantCoordinateFiltration q)
    (hq : IsIdempotentElem q) :
    iSupIndep F.incrementInRange := by
  classical
  let _ : LinearOrder κ := F.isWellOrder.linearOrder F.r
  change iSupIndep (fun i ↦ F.incrementInRange i)
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero
    (R := S) (N := LinearMap.range q)
    (fun i ↦ F.incrementInRange i)).2
  intro s
  induction s using Finset.induction_on_max_value (f := fun i : κ ↦ i) with
  | empty => simp
  | @insert a s ha hmax ih =>
      intro v hv hsum i hi
      have hsum_before :
          (∑ j ∈ s, v j) ∈ F.rangeSupported (F.before a) := by
        apply Submodule.sum_mem
        intro j hj
        have hja : j ≠ a := by
          intro hja
          subst j
          exact ha hj
        have hle : j ≤ a := hmax j hj
        apply F.incrementInRange_le_rangeSupported_before_of_rel
          (show F.r j a from lt_of_le_of_ne hle hja)
        exact hv j (Finset.mem_insert_of_mem hj)
      have hva_before : v a ∈ F.rangeSupported (F.before a) := by
        change (v a : κ →₀ S) ∈ Finsupp.supported S S (F.before a)
        change (∑ j ∈ insert a s, v j) = 0 at hsum
        rw [Finset.sum_insert ha] at hsum
        have hsum_val := congrArg
          (fun z : LinearMap.range q ↦ (z : κ →₀ S)) hsum
        have hva_val : (v a : κ →₀ S) =
            -(((∑ j ∈ s, v j) : LinearMap.range q) : κ →₀ S) :=
          add_eq_zero_iff_eq_neg.mp hsum_val
        rw [hva_val]
        apply (Finsupp.supported S S (F.before a)).neg_mem
        exact hsum_before
      have hva_zero : v a = 0 :=
        Submodule.disjoint_def.mp
          (F.disjoint_incrementInRange_rangeSupported_before hq a)
          (v a) (hv a (Finset.mem_insert_self a s)) hva_before
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hva_zero
      · apply ih v (fun j hj ↦ hv j (Finset.mem_insert_of_mem hj))
        · simpa [Finset.sum_insert ha, hva_zero] using hsum
        · exact hi

/-- A nonzero range element supported before a stage is already supported
through one strictly earlier stage.  Finite coordinate support is essential
here: it lets us take the greatest of the finitely many witness stages. -/
theorem eq_zero_or_exists_rel_mem_rangeSupported_through
    (F : LinearMap.CountableInvariantCoordinateFiltration q)
    (i : κ) (x : LinearMap.range q)
    (hx : x ∈ F.rangeSupported (F.before i)) :
    x = 0 ∨ ∃ j, F.r j i ∧ x ∈ F.rangeSupported (F.through j) := by
  classical
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  right
  let _ : LinearOrder κ := F.isWellOrder.linearOrder F.r
  have hxval0 : (x : κ →₀ S) ≠ 0 := fun h ↦ hx0 (Subtype.ext h)
  have hsupp : (x : κ →₀ S).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr hxval0
  have hstage (k : κ) (hk : k ∈ (x : κ →₀ S).support) :
      ∃ j, F.r j i ∧ k ∈ F.through j := by
    have hkbefore : k ∈ F.before i :=
      (Finsupp.mem_supported (R := S) (x : κ →₀ S)).mp hx hk
    rw [F.before_eq_iUnion_through i] at hkbefore
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hkbefore
    obtain ⟨hji, hkthrough⟩ := Set.mem_iUnion.mp hj
    exact ⟨j, hji, hkthrough⟩
  let stage (k : κ) : κ :=
    if hk : k ∈ (x : κ →₀ S).support then (hstage k hk).choose else i
  have stage_rel (k : κ) (hk : k ∈ (x : κ →₀ S).support) :
      F.r (stage k) i := by
    simp only [stage, dite_eq_left hk]
    exact (hstage k hk).choose_spec.1
  have mem_through_stage (k : κ) (hk : k ∈ (x : κ →₀ S).support) :
      k ∈ F.through (stage k) := by
    simp only [stage, dite_eq_left hk]
    exact (hstage k hk).choose_spec.2
  obtain ⟨k, hk, hkmax⟩ :=
    Finset.exists_max_image (x : κ →₀ S).support stage hsupp
  refine ⟨stage k, stage_rel k hk, ?_⟩
  rw [F.mem_rangeSupported, Finsupp.mem_supported]
  intro j hj
  have hjstage : j ∈ F.through (stage j) := mem_through_stage j hj
  rcases (hkmax j hj).eq_or_lt with hstageeq | hstagelt
  · simpa [hstageeq] using hjstage
  · exact F.through_subset_through_of_rel
      (show F.r (stage j) (stage k) from hstagelt) hjstage

/-- Every completed supported range stage is generated by the split
increments up to that stage. -/
theorem rangeSupported_through_le_iSup_incrementInRange
    (F : LinearMap.CountableInvariantCoordinateFiltration q)
    (hq : IsIdempotentElem q) (i : κ) :
    F.rangeSupported (F.through i) ≤ ⨆ j, F.incrementInRange j := by
  induction i using F.isWellOrder.wf.induction with
  | h i ih =>
      intro x hx
      let inc : q.supportedRange (F.before i) →ₗ[S]
          q.supportedRange (F.through i) :=
        q.supportedRangeInclusion (F.before_subset_through i)
      let ret : q.supportedRange (F.through i) →ₗ[S]
          q.supportedRange (F.before i) :=
        q.supportedRangeRetraction
          (F.before i) (F.through i) (F.before_invariant i)
      have hsplit : ret.comp inc = LinearMap.id :=
        q.supportedRangeRetraction_comp_inclusion hq
          (F.before_subset_through i) (F.before_invariant i)
      let xt : q.supportedRange (F.through i) :=
        ⟨x.1, x.2, hx⟩
      let a : q.supportedRange (F.before i) := ret xt
      let ar : LinearMap.range q := ⟨a.1, a.2.1⟩
      let k : F.increment i := ⟨xt - inc a, by
        rw [LinearMap.mem_ker]
        change ret (xt - inc a) = 0
        calc
          ret (xt - inc a) = ret xt - ret (inc a) := map_sub ret xt (inc a)
          _ = ret xt - (ret.comp inc) a := rfl
          _ = ret xt - a := by rw [hsplit, LinearMap.id_apply]
          _ = 0 := sub_self (ret xt)⟩
      have hk : F.incrementToRange i k ∈ ⨆ j, F.incrementInRange j :=
        le_iSup (fun j ↦ F.incrementInRange j) i
          (LinearMap.mem_range_self (F.incrementToRange i) k)
      have har_before : ar ∈ F.rangeSupported (F.before i) := a.2.2
      have har : ar ∈ ⨆ j, F.incrementInRange j := by
        rcases F.eq_zero_or_exists_rel_mem_rangeSupported_through i ar har_before with
          har0 | ⟨j, hji, harj⟩
        · rw [har0]
          exact Submodule.zero_mem _
        · exact ih j hji harj
      have hdecomp : F.incrementToRange i k + ar = x := by
        apply Subtype.ext
        change ((xt : κ →₀ S) - (inc a : κ →₀ S)) +
            (a : κ →₀ S) = (xt : κ →₀ S)
        have hinc : (inc a : κ →₀ S) = (a : κ →₀ S) := rfl
        rw [hinc, sub_add_cancel]
      rw [← hdecomp]
      exact Submodule.add_mem _ hk har

/-- The split increments span the full range of the idempotent. -/
theorem iSup_incrementInRange_eq_top
    (F : LinearMap.CountableInvariantCoordinateFiltration q)
    (hq : IsIdempotentElem q) :
    ⨆ i, F.incrementInRange i = ⊤ := by
  apply top_unique
  intro x _
  by_cases hx0 : x = 0
  · rw [hx0]
    exact Submodule.zero_mem _
  have hsupp : (x : κ →₀ S).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr fun hx ↦ hx0 (Subtype.ext hx)
  let _ : LinearOrder κ := F.isWellOrder.linearOrder F.r
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image
    (x : κ →₀ S).support (fun j : κ ↦ j) hsupp
  apply F.rangeSupported_through_le_iSup_incrementInRange hq i
  rw [F.mem_rangeSupported, Finsupp.mem_supported]
  intro j hj
  rcases (himax j hj).eq_or_lt with hji | hji
  · subst i
    exact F.mem_through j
  · exact F.through_subset_through_of_rel
      (show F.r j i from hji) (F.mem_through j)

/-- The range of an idempotent endomorphism is free when every split
increment in an invariant coordinate filtration is free. -/
theorem range_free_of_free_increments
    (F : LinearMap.CountableInvariantCoordinateFiltration q)
    (hq : IsIdempotentElem q)
    (hfree : ∀ i, Module.Free S (F.increment i)) :
    Module.Free S (LinearMap.range q) := by
  classical
  let _ : ∀ i, Module.Free S (F.increment i) := hfree
  let _ : ∀ i, Module.Free S (F.incrementInRange i) :=
    fun i ↦ F.incrementInRange_free i (hfree i)
  have hind : iSupIndep (fun i : κ ↦ F.incrementInRange i) := by
    change iSupIndep F.incrementInRange
    exact F.incrementInRange_iSupIndep hq
  have htop : ⨆ i : κ, F.incrementInRange i = ⊤ :=
    F.iSup_incrementInRange_eq_top hq
  let e : (Π₀ i, F.incrementInRange i) ≃ₗ[S] LinearMap.range q :=
    iSupIndep.linearEquiv (R := S) (N := LinearMap.range q)
      (p := fun i : κ ↦ F.incrementInRange i) hind htop
  exact Module.Free.of_equiv e

end LinearMap.CountableInvariantCoordinateFiltration
