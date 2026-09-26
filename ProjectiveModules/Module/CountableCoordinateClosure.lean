/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.Data.Set.Countable
public import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Countable invariant coordinate closures

This file constructs a countable coordinate summand of an arbitrary standard
free module that contains a prescribed countable set of coordinates and is
preserved by a chosen linear endomorphism.  No countability assumption is made
on the full basis index type.

The construction repeatedly adjoins the finite supports of the images of the
currently selected basis vectors, then takes the union over the natural
numbers.  It is a reusable set-theoretic ingredient in transfinite
decompositions of projective modules.
-/

@[expose] public section

noncomputable section

open Set Submodule

namespace LinearMap

universe uR uI

variable {R : Type uR} [Semiring R] {ι : Type uI}

/-- The coordinates obtained after `n` finite-support closure steps. -/
private def coordinateStage (p : (ι →₀ R) →ₗ[R] (ι →₀ R))
    (s : Set ι) : ℕ → Set ι :=
  Nat.rec s (fun _ t => t ∪ ⋃ i ∈ t, (p (Finsupp.single i 1)).support)

/-- The union of all finite-support closure steps. -/
private def coordinateClosure (p : (ι →₀ R) →ₗ[R] (ι →₀ R))
    (s : Set ι) : Set ι :=
  ⋃ n, coordinateStage p s n

private theorem coordinateStage_countable
    (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) {s : Set ι} (hs : s.Countable) :
    ∀ n, (coordinateStage p s n).Countable
  | 0 => hs
  | n + 1 =>
      (coordinateStage_countable p hs n).union <|
        (coordinateStage_countable p hs n).biUnion fun i _ =>
          (p (Finsupp.single i 1)).support.finite_toSet.countable

private theorem coordinateClosure_countable
    (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) {s : Set ι} (hs : s.Countable) :
    (coordinateClosure p s).Countable :=
  Set.countable_iUnion (coordinateStage_countable p hs)

private theorem subset_coordinateClosure
    (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) (s : Set ι) :
    s ⊆ coordinateClosure p s := by
  intro i hi
  exact Set.mem_iUnion.mpr ⟨0, hi⟩

private theorem support_image_single_subset_coordinateClosure
    (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) (s : Set ι)
    {i : ι} (hi : i ∈ coordinateClosure p s) :
    ((p (Finsupp.single i 1)).support : Set ι) ⊆ coordinateClosure p s := by
  intro j hj
  obtain ⟨n, hin⟩ := Set.mem_iUnion.mp hi
  apply Set.mem_iUnion.mpr
  refine ⟨n + 1, Set.mem_union_right _ ?_⟩
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hin, hj⟩⟩

/-- A countable set of coordinates in a standard free module is contained in
a countable coordinate set whose supported submodule is preserved by a chosen
linear endomorphism. -/
theorem exists_countable_invariant_supported
    (p : (ι →₀ R) →ₗ[R] (ι →₀ R)) {s : Set ι} (hs : s.Countable) :
    ∃ t : Set ι, s ⊆ t ∧ t.Countable ∧
      Finsupp.supported R R t ≤ (Finsupp.supported R R t).comap p := by
  let t := coordinateClosure p s
  refine ⟨t, subset_coordinateClosure p s, coordinateClosure_countable p hs, ?_⟩
  intro x hx
  change p x ∈ Finsupp.supported R R t
  rw [Finsupp.supported_eq_span_single] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact support_image_single_subset_coordinateClosure p s hi
  | zero => simp
  | add x y _ _ hx hy =>
      simpa only [map_add] using (Finsupp.supported R R t).add_mem hx hy
  | smul r x _ hx =>
      simpa only [map_smul] using (Finsupp.supported R R t).smul_mem r hx

end LinearMap
