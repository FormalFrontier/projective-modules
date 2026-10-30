/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Data.Finset.NoncommProd

/-!
# Finite products of commuting idempotents

A finite product of pairwise commuting idempotent elements of a monoid is idempotent.
Left multiplication by an idempotent factor fixes the product of a finite pairwise commuting family.
-/

@[expose] public section

universe uα uβ

namespace IsIdempotentElem

/-- A finite product of pairwise commuting idempotent elements in a monoid is idempotent. -/
lemma noncommProd {α : Type uα} {β : Type uβ} [Monoid β] (s : Finset α) (f : α → β)
    (comm : (s : Set α).Pairwise (fun i j => Commute (f i) (f j)))
    (hf : ∀ i ∈ s, IsIdempotentElem (f i)) : IsIdempotentElem (s.noncommProd f comm) := by
  change s.noncommProd f comm * s.noncommProd f comm = s.noncommProd f comm
  rw [← Finset.noncommProd_mul_distrib f f comm comm comm]
  exact (Finset.noncommProd_congr (f := f) (g := f * f) rfl
    (fun i hi => Eq.symm (hf i hi)) comm).symm

/-- Left multiplication by an idempotent factor fixes a finite product of pairwise commuting
elements. The other factors need not be idempotent. -/
lemma mul_noncommProd {α : Type uα} {β : Type uβ} [Monoid β] (s : Finset α) (f : α → β)
    (comm : (s : Set α).Pairwise (fun i j => Commute (f i) (f j)))
    {i : α} (hi : i ∈ s) (hf : IsIdempotentElem (f i)) :
    f i * s.noncommProd f comm = s.noncommProd f comm := by
  classical
  revert comm i
  refine Finset.induction_on s ?_ ?_
  · intro _ i hi _
    exact (Finset.notMem_empty i hi).elim
  · intro a t ha ih comm i hi hf
    have tailComm : (t : Set α).Pairwise (fun j k => Commute (f j) (f k)) := by
      intro j hj k hk hjk
      exact comm (Finset.mem_insert.mpr (Or.inr hj))
        (Finset.mem_insert.mpr (Or.inr hk)) hjk
    rw [Finset.noncommProd_insert_of_notMem t a f comm ha]
    rcases Finset.mem_insert.mp hi with hia | hit
    · subst i
      exact hf.mul_self_mul _
    · have hia : i ≠ a := by
        intro hia
        subst i
        exact ha hit
      have hcomm : Commute (f i) (f a) :=
        comm (Finset.mem_insert.mpr (Or.inr hit))
          (Finset.mem_insert.mpr (Or.inl rfl)) hia
      exact (hcomm.left_comm _).trans
        (congrArg (fun x : β => f a * x) (ih tailComm (i := i) hit hf))

end IsIdempotentElem
