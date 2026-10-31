/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite support in exterior powers

A finite set of elements of an exterior power comes from the exterior power of the span of
finitely many vectors. Consequently, if an exterior power is finitely generated, some finite
span in the original module maps onto it. No finite generation of the original module is needed.

The proofs use Mathlib's generation by pure wedges (`exteriorPower.ιMulti_span`) and finite-span
extraction (`Submodule.subset_span_finite_of_subset_span`). All degrees, including zero, are
allowed.
-/

@[expose] public section

universe uR uM uI

namespace exteriorPower

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- A finite set in an exterior power lifts to the exterior power of a finite span in the
original module. -/
theorem exists_finset_mem_range (n : ℕ) (t : Finset (⋀[R]^n M)) :
    ∃ s : Finset M, ∀ x ∈ t,
      x ∈ LinearMap.range (map n (Submodule.span R (s : Set M)).subtype) := by
  classical
  have ht : (t : Set (⋀[R]^n M)) ⊆
      (Submodule.span R (Set.range (ιMulti R n : (Fin n → M) → ⋀[R]^n M)) :
        Set (⋀[R]^n M)) := by
    rw [ιMulti_span R n M]
    intro _ _
    trivial
  obtain ⟨q, hq, htq⟩ := Submodule.subset_span_finite_of_subset_span ht
  have hq' : ∀ w : q, ∃ v : Fin n → M, ιMulti R n v = (w : ⋀[R]^n M) := by
    intro w
    exact hq w.property
  let v : q → Fin n → M := fun w => Classical.choose (hq' w)
  have hv (w : q) : ιMulti R n (v w) = (w : ⋀[R]^n M) :=
    Classical.choose_spec (hq' w)
  -- Collect every vector occurring in the finitely many chosen pure wedges.
  let s : Finset M := Finset.univ.image (fun p : q × Fin n => v p.1 p.2)
  have hvs (w : q) (i : Fin n) : v w i ∈ Submodule.span R (s : Set M) := by
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨(w, i), Finset.mem_univ _, rfl⟩
  have hqrange (w : q) :
      (w : ⋀[R]^n M) ∈
        LinearMap.range (map n (Submodule.span R (s : Set M)).subtype) := by
    apply LinearMap.mem_range.mpr
    refine ⟨ιMulti R n (fun i => ⟨v w i, hvs w i⟩), ?_⟩
    rw [map_apply_ιMulti]
    exact hv w
  have hspan : Submodule.span R (q : Set (⋀[R]^n M)) ≤
      LinearMap.range (map n (Submodule.span R (s : Set M)).subtype) := by
    apply Submodule.span_le.mpr
    intro w hw
    exact hqrange ⟨w, hw⟩
  exact ⟨s, fun x hx => hspan (htq hx)⟩

/-- A family indexed by a finite type in an exterior power lifts to the exterior power of a
single finite span. No choice of a finite enumeration is required in the statement. -/
theorem exists_finset_forall_mem_range (n : ℕ) {ι : Type uI} [Finite ι]
    (x : ι → ⋀[R]^n M) :
    ∃ s : Finset M, ∀ i,
      x i ∈ LinearMap.range (map n (Submodule.span R (s : Set M)).subtype) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨s, hs⟩ := exists_finset_mem_range n (Finset.univ.image x)
  exact ⟨s, fun i => hs (x i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩

/-- If an exterior power is finitely generated, the inclusion of some finite span in the
original module induces a surjection on that exterior power. The span itself is a finite module
by `Module.Finite.span_finset`. -/
theorem exists_finset_surjective (n : ℕ) [Module.Finite R (⋀[R]^n M)] :
    ∃ s : Finset M,
      Function.Surjective (map n (Submodule.span R (s : Set M)).subtype) := by
  obtain ⟨_, x, hx⟩ := Module.Finite.exists_fin (R := R) (M := ⋀[R]^n M)
  obtain ⟨s, hs⟩ := exists_finset_forall_mem_range n x
  have hspan : Submodule.span R (Set.range x) ≤
      LinearMap.range (map n (Submodule.span R (s : Set M)).subtype) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hs i
  refine ⟨s, fun y => LinearMap.mem_range.mp (hspan ?_)⟩
  rw [hx]
  trivial

end exteriorPower
