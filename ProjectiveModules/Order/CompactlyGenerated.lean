/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.Directed

/-!
# Compact elements and order isomorphisms

Order isomorphisms preserve compactness of elements of partial orders. Compactness is
Mathlib's `IsCompactElement`, expressed using nonempty directed sets with least upper
bounds. Neither completeness nor a distinguished top element is needed.

## Main results

* `OrderIso.isCompactElement`: the image of a compact element is compact.
* `OrderIso.isCompactElement_iff`: an element is compact exactly when its image is compact.

## References

* Mathlib's `Mathlib.Order.CompactlyGenerated.Basic`, by Oliver Nash, for the definition
  of a compact element.
* Mathlib's `Mathlib.Order.Bounds.OrderIso`, by Johannes Hölzl and Yury Kudryashov,
  for transport of least upper bounds.
* Mathlib's `Mathlib.Order.Directed`, by Johannes Hölzl and Yaël Dillies,
  for transport of directed sets.

The proofs below use these existing definitions and transport lemmas.

## Implementation notes

The proof pulls a nonempty directed set and its least upper bound back along the inverse
order isomorphism, applies compactness there, and maps the resulting witness forward.
The inverse direction then follows by applying the same argument to the inverse
isomorphism. No complete lattice structure or greatest element is required.
-/

@[expose] public section

universe u v

namespace OrderIso

variable {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β]

/-- An order isomorphism maps compact elements to compact elements. -/
theorem isCompactElement (e : α ≃o β) {k : α} (hk : IsCompactElement k) :
    IsCompactElement (e k) := by
  intro s z hs hd hz hkz
  have hs' : (e.symm '' s).Nonempty := by
    obtain ⟨y, hy⟩ := hs
    exact ⟨e.symm y, y, hy, rfl⟩
  have hd' : DirectedOn (· ≤ ·) (e.symm '' s) := by
    exact DirectedOn.mono_comp e.symm.monotone hd
  have hz' : IsLUB (e.symm '' s) (e.symm z) := e.symm.isLUB_image'.mpr hz
  have hkz' : k ≤ e.symm z := e.le_symm_apply.mpr hkz
  obtain ⟨x, ⟨y, hy, rfl⟩, hky⟩ := hk (e.symm '' s) (e.symm z) hs' hd' hz' hkz'
  exact ⟨y, hy, e.le_symm_apply.mp hky⟩

/-- An element of a partial order is compact if and only if its image under an order
isomorphism is compact. -/
theorem isCompactElement_iff (e : α ≃o β) (k : α) :
    IsCompactElement (e k) ↔ IsCompactElement k := by
  constructor
  · intro hk
    simpa only [e.symm_apply_apply] using e.symm.isCompactElement hk
  · exact e.isCompactElement

end OrderIso
