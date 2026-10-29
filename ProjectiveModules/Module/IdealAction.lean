/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Span

/-!
# Finite ideal supports for submodule actions

A finitely generated submodule contained in `I • N` is already contained in `J • N`
for some finitely generated subideal `J` of `I`. Membership induction first finds
such an ideal for each element; finite-generation induction combines the ideals
needed for generators.

## References

The proof uses the Mathlib contributors' finite-generation induction from
`Mathlib.RingTheory.Finiteness.Basic`, scalar-action induction and monotonicity from
`Mathlib.Algebra.Algebra.Operations`, and span characteristics from
`Mathlib.RingTheory.Ideal.Span` and `Mathlib.LinearAlgebra.Span.Basic`.
-/

@[expose] public section

universe u v

namespace Submodule

variable {A : Type u} {M : Type v}
  [Semiring A] [AddCommMonoid M] [Module A M]

/-- A finitely generated submodule contained in `I • N` is contained in `J • N`
for some finitely generated subideal `J` of `I`. -/
theorem FG.exists_fg_ideal_le_smul
    {U : Submodule A M} (hfg : U.FG) (I : Ideal A) (N : Submodule A M)
    (hU : U ≤ I • N) :
    ∃ J : Ideal A, J.FG ∧ J ≤ I ∧ U ≤ J • N := by
  suffices h : ∃ J : Ideal A, Submodule.FG J ∧ J ≤ I ∧ U ≤ J • N by
    obtain ⟨J, ⟨s, hs⟩, hJI, hUJ⟩ := h
    refine ⟨J, ⟨s, ?_⟩, hJI, hUJ⟩
    simpa only [Ideal.submodule_span_eq] using hs
  have hmem : ∀ x ∈ I • N,
      ∃ J : Ideal A, Submodule.FG J ∧ J ≤ I ∧ x ∈ J • N := by
    intro x hx
    refine smul_induction_on
      (p := fun x => ∃ J : Ideal A, Submodule.FG J ∧ J ≤ I ∧ x ∈ J • N) hx ?_ ?_
    · intro r hr n hn
      refine ⟨Ideal.span {r}, ?_, (Ideal.span_singleton_le_iff_mem I).mpr hr, ?_⟩
      · simpa only [Ideal.submodule_span_eq] using (fg_span_singleton (R := A) r)
      · exact smul_mem_smul
          ((Ideal.span_singleton_le_iff_mem (Ideal.span {r})).mp le_rfl) hn
    · intro x y hx hy
      obtain ⟨J, hJfg, hJI, hxJ⟩ := hx
      obtain ⟨K, hKfg, hKI, hyK⟩ := hy
      refine ⟨J ⊔ K, hJfg.sup hKfg, sup_le hJI hKI, ?_⟩
      exact ((J ⊔ K) • N).add_mem
        (smul_mono_left (le_sup_left : J ≤ J ⊔ K) hxJ)
        (smul_mono_left (le_sup_right : K ≤ J ⊔ K) hyK)
  refine fg_induction (R := A) (M := M)
    (motive := fun V _ => V ≤ I • N →
      ∃ J : Ideal A, Submodule.FG J ∧ J ≤ I ∧ V ≤ J • N) ?_ ?_ U hfg hU
  · intro x hx
    obtain ⟨J, hJfg, hJI, hxJ⟩ :=
      hmem x ((span_singleton_le_iff_mem (R := A) x (I • N)).mp hx)
    exact ⟨J, hJfg, hJI, (span_singleton_le_iff_mem (R := A) x (J • N)).mpr hxJ⟩
  · intro V W _ _ ihV ihW hVW
    obtain ⟨J, hJfg, hJI, hVJ⟩ := ihV (le_trans le_sup_left hVW)
    obtain ⟨K, hKfg, hKI, hWK⟩ := ihW (le_trans le_sup_right hVW)
    refine ⟨J ⊔ K, hJfg.sup hKfg, sup_le hJI hKI, ?_⟩
    exact sup_le
      (le_trans hVJ (smul_mono_left (le_sup_left : J ≤ J ⊔ K)))
      (le_trans hWK (smul_mono_left (le_sup_right : K ≤ J ⊔ K)))

end Submodule
