/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.Data.Set.Countable
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Countably generated modules

This file defines countable generation by a sequence and supplies its basic
transport API.  Using a sequence rather than an arbitrary countable set makes
the witness directly usable in recursive module constructions; finite
generating families are padded by zero.
-/

@[expose] public section

universe uR uM uN

namespace Module

variable (R : Type uR) (M : Type uM)
variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- A module is countably generated if the range of some sequence spans it. -/
def CountablyGenerated : Prop :=
  ∃ x : ℕ → M, Submodule.span R (Set.range x) = ⊤

namespace CountablyGenerated

variable {R M}

/-- A finite module is countably generated. -/
theorem of_finite [Module.Finite R M] : Module.CountablyGenerated R M := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  refine ⟨fun i ↦ if hi : i < n then s ⟨i, hi⟩ else 0, ?_⟩
  apply top_unique
  rw [← hs]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨i, by simp [i.isLt]⟩

variable {N : Type uN} [AddCommMonoid N] [Module R N]

/-- A surjective linear image of a countably generated module is countably
generated. -/
theorem of_surjective (hM : Module.CountablyGenerated R M)
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.CountablyGenerated R N := by
  obtain ⟨x, hx⟩ := hM
  refine ⟨fun n ↦ f (x n), top_unique fun y _ ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hf y
  have hz : z ∈ Submodule.span R (Set.range x) := by rw [hx]; trivial
  have hrange : f '' Set.range x = Set.range (fun n ↦ f (x n)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨x n, ⟨n, rfl⟩, rfl⟩
  rw [← hrange]
  exact Submodule.apply_mem_span_image_of_mem_span f hz

/-- A module linearly equivalent to a countably generated module is countably
generated. -/
theorem equiv (hM : Module.CountablyGenerated R M) (e : M ≃ₗ[R] N) :
    Module.CountablyGenerated R N :=
  hM.of_surjective e.toLinearMap e.surjective

/-- Linearly equivalent modules are countably generated simultaneously. -/
theorem equiv_iff (e : M ≃ₗ[R] N) :
    Module.CountablyGenerated R M ↔ Module.CountablyGenerated R N := by
  constructor
  · intro h
    exact h.equiv e
  · intro h
    exact h.equiv e.symm

/-- A standard free module on a countable index type is countably generated. -/
theorem finsupp (ι : Type*) [Countable ι] :
    Module.CountablyGenerated R (ι →₀ R) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      refine ⟨fun _ ↦ 0, top_unique fun x _ ↦ ?_⟩
      rw [Subsingleton.elim x 0]
      exact Submodule.zero_mem _
  | inr hι =>
      let _ := hι
      obtain ⟨f, hf⟩ := countable_iff_exists_surjective.mp
        (inferInstance : Countable ι)
      refine ⟨fun n ↦ Finsupp.single (f n) 1, ?_⟩
      have hrange : Set.range (fun n ↦ Finsupp.single (f n) (1 : R)) =
          (fun i ↦ Finsupp.single i 1) '' Set.univ := by
        ext x
        constructor
        · rintro ⟨n, rfl⟩
          exact ⟨f n, Set.mem_univ _, rfl⟩
        · rintro ⟨i, _, rfl⟩
          obtain ⟨n, rfl⟩ := hf i
          exact ⟨n, rfl⟩
      rw [hrange, ← Finsupp.supported_eq_span_single,
        Finsupp.supported_univ]

/-- The submodule of finitely supported functions on a countable coordinate
set is countably generated. -/
theorem supported {ι : Type*} (s : Set ι) (hs : Set.Countable s) :
    Module.CountablyGenerated R (Finsupp.supported R R s) := by
  let _ : Countable s := hs.to_subtype
  exact (finsupp (R := R) s).equiv
    (Finsupp.supportedEquivFinsupp (R := R) s).symm

end CountablyGenerated

end Module
