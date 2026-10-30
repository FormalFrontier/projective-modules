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

end IsIdempotentElem
