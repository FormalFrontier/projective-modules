/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import ProjectiveModules.Module.CountableCoordinateClosure
public import ProjectiveModules.Module.InvariantSupportedProjection
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Well-ordered invariant coordinate filtrations

This file packages an arbitrary standard free module as a well-ordered union
of coordinate-supported submodules preserved by a chosen linear endomorphism,
with a countable coordinate increment at every stage.

The construction chooses a countable invariant coordinate closure around each
single basis coordinate.  A well-order of the full index type then turns unions
of those closures into a continuous filtration.  In particular, no
countability assumption is made on the ambient basis index type.
-/

@[expose] public section

noncomputable section

open Set Submodule

namespace LinearMap

universe uR uI

variable {R : Type uR} [Semiring R] {ι : Type uI}

/-- A well-ordered family of countable coordinate sets, each containing its
index and each supporting a submodule preserved by `p`.  The sets may overlap;
their well-ordered unions form the associated filtration. -/
structure CountableInvariantCoordinateFiltration
    (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) where
  /-- The well-order used to assemble the filtration. -/
  r : ι → ι → Prop
  /-- The chosen relation is a well-order. -/
  isWellOrder : IsWellOrder ι r
  /-- A countable invariant coordinate closure around each index. -/
  block : ι → Set ι
  /-- Each index belongs to its chosen closure. -/
  mem_block : ∀ i, i ∈ block i
  /-- Every chosen closure is countable. -/
  block_countable : ∀ i, (block i).Countable
  /-- Every chosen closure supports a submodule preserved by `p`. -/
  block_invariant : ∀ i,
    Finsupp.supported R R (block i) ≤
      (Finsupp.supported R R (block i)).comap p

namespace CountableInvariantCoordinateFiltration

variable {p : (ι →₀ R) →ₗ[R] (ι →₀ R)}

/-- The coordinates strictly before `i` in the filtration. -/
def before (F : CountableInvariantCoordinateFiltration p) (i : ι) : Set ι :=
  ⋃ j, ⋃ (_ : F.r j i), F.block j

/-- The coordinates through `i` in the filtration. -/
def through (F : CountableInvariantCoordinateFiltration p) (i : ι) : Set ι :=
  F.before i ∪ F.block i

/-- The submodule supported on the coordinates before a stage is preserved by
the endomorphism. -/
theorem before_invariant (F : CountableInvariantCoordinateFiltration p)
    (i : ι) :
    Finsupp.supported R R (F.before i) ≤
      (Finsupp.supported R R (F.before i)).comap p := by
  rw [before, Finsupp.supported_iUnion]
  refine iSup_le fun j ↦ ?_
  by_cases hji : F.r j i
  · have hmono : Finsupp.supported R R (F.block j) ≤
        ⨆ k, Finsupp.supported R R (⋃ (_ : F.r k i), F.block k) :=
      le_iSup_of_le j (by simp [hji])
    simpa [hji] using
      (F.block_invariant j).trans (Submodule.comap_mono hmono)
  · simp [hji]

/-- The submodule supported on the coordinates through a stage is preserved by
the endomorphism. -/
theorem through_invariant (F : CountableInvariantCoordinateFiltration p)
    (i : ι) :
    Finsupp.supported R R (F.through i) ≤
      (Finsupp.supported R R (F.through i)).comap p := by
  rw [through, Finsupp.supported_union]
  refine sup_le ?_ ?_
  · exact (F.before_invariant i).trans <| Submodule.comap_mono le_sup_left
  · exact (F.block_invariant i).trans <| Submodule.comap_mono le_sup_right

/-- Every stage contains its indexing coordinate. -/
theorem mem_through (F : CountableInvariantCoordinateFiltration p) (i : ι) :
    i ∈ F.through i :=
  Set.mem_union_right _ (F.mem_block i)

/-- The coordinates before a stage are contained in the coordinates through
that stage. -/
theorem before_subset_through
    (F : CountableInvariantCoordinateFiltration p) (i : ι) :
    F.before i ⊆ F.through i :=
  Set.subset_union_left

/-- The new coordinates at each stage form a countable set. -/
theorem increment_countable (F : CountableInvariantCoordinateFiltration p)
    (i : ι) : (F.through i \ F.before i).Countable :=
  (F.block_countable i).mono fun x hx ↦ by
    rcases hx with ⟨hxthrough, hxnot⟩
    rcases hxthrough with hxbefore | hxblock
    · exact (hxnot hxbefore).elim
    · exact hxblock

/-- A completed stage lies in the coordinates before every later stage. -/
theorem through_subset_before_of_rel
    (F : CountableInvariantCoordinateFiltration p) {i j : ι}
    (hij : F.r i j) : F.through i ⊆ F.before j := by
  let _ := F.isWellOrder
  intro x hx
  rcases hx with hx | hx
  · rw [before] at hx ⊢
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hki, hx⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨k,
      Set.mem_iUnion.mpr ⟨Trans.trans hki hij, hx⟩⟩
  · rw [before]
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hij, hx⟩⟩

/-- Earlier open stages are contained in later open stages. -/
theorem before_subset_before_of_rel
    (F : CountableInvariantCoordinateFiltration p) {i j : ι}
    (hij : F.r i j) : F.before i ⊆ F.before j :=
  (F.before_subset_through i).trans (F.through_subset_before_of_rel hij)

/-- Earlier completed stages are contained in later completed stages. -/
theorem through_subset_through_of_rel
    (F : CountableInvariantCoordinateFiltration p) {i j : ι}
    (hij : F.r i j) : F.through i ⊆ F.through j :=
  (F.through_subset_before_of_rel hij).trans (F.before_subset_through j)

/-- The coordinates before a stage are exactly the union of all completed
earlier stages. -/
theorem before_eq_iUnion_through
    (F : CountableInvariantCoordinateFiltration p) (i : ι) :
    F.before i = ⋃ j, ⋃ (_ : F.r j i), F.through j := by
  let _ := F.isWellOrder
  ext x
  constructor
  · intro hx
    rw [before] at hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hji, hx⟩ := Set.mem_iUnion.mp hj
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hji,
      Set.mem_union_right _ hx⟩⟩
  · intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hji, hx⟩ := Set.mem_iUnion.mp hj
    exact F.through_subset_before_of_rel hji hx

/-- The completed stages cover all coordinates. -/
theorem iUnion_through (F : CountableInvariantCoordinateFiltration p) :
    ⋃ i, F.through i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro i
  exact Set.mem_iUnion.mpr ⟨i, F.mem_through i⟩

end CountableInvariantCoordinateFiltration

/-- Every endomorphism of an arbitrary standard free module admits a
well-ordered invariant coordinate filtration with countable increments. -/
theorem exists_countable_invariant_coordinate_filtration
    (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) :
    Nonempty (CountableInvariantCoordinateFiltration p) := by
  classical
  obtain ⟨r, hr, _⟩ := Cardinal.exists_ord_eq ι
  let _ := hr
  have hblock : ∀ i : ι, ∃ t : Set ι, {i} ⊆ t ∧ t.Countable ∧
      Finsupp.supported R R t ≤ (Finsupp.supported R R t).comap p :=
    fun i ↦ p.exists_countable_invariant_supported (Set.countable_singleton i)
  choose block hmem hcount hinvariant using hblock
  exact ⟨{
    r := r
    isWellOrder := hr
    block := block
    mem_block := fun i ↦ hmem i (Set.mem_singleton i)
    block_countable := hcount
    block_invariant := hinvariant
  }⟩

namespace CountableInvariantCoordinateFiltration

universe uS uJ

variable {S : Type uS} [Ring S] {κ : Type uJ}
variable {q : (κ →₀ S) →ₗ[S] (κ →₀ S)}

/-- For an idempotent endomorphism, a completed filtration stage is the
product of its open stage and the kernel of the canonical retraction. -/
noncomputable def beforeProdIncrementEquiv
    (F : CountableInvariantCoordinateFiltration q)
    (hq : IsIdempotentElem q) (i : κ) :
    (LinearMap.ker (q.supportedRangeRetraction
        (F.before i) (F.through i) (F.before_invariant i)) ×
      q.supportedRange (F.before i)) ≃ₗ[S]
        q.supportedRange (F.through i) :=
  q.supportedRangeProdComplementEquiv hq
    (F.before_subset_through i) (F.before_invariant i)

/-- The split increment between the open and completed parts of every
filtration stage is projective. -/
theorem increment_projective
    (F : CountableInvariantCoordinateFiltration q)
    (hq : IsIdempotentElem q) (i : κ) :
    Module.Projective S (LinearMap.ker (q.supportedRangeRetraction
      (F.before i) (F.through i) (F.before_invariant i))) :=
  q.supportedRangeComplement_projective hq
    (F.before_subset_through i) (F.before_invariant i)
    (F.through_invariant i)

/-- Every split increment in the filtration of an idempotent endomorphism is
countably generated. -/
theorem increment_countablyGenerated
    (F : CountableInvariantCoordinateFiltration q)
    (hq : IsIdempotentElem q) (i : κ) :
    Module.CountablyGenerated S (LinearMap.ker (q.supportedRangeRetraction
      (F.before i) (F.through i) (F.before_invariant i))) :=
  q.supportedRangeComplement_countablyGenerated hq
    (F.before_subset_through i) (F.before_invariant i)
    (F.through_invariant i) (F.increment_countable i)

end CountableInvariantCoordinateFiltration

end LinearMap
