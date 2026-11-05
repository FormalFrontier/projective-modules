/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.EndomorphismIdeals.DirectSum

/-!
# Evaluation of endomorphism ideals

The principal-ideal identity and monotonicity from the Galois connection show
that the whole endomorphism ideal evaluates to the whole module, using only
the public API. The coordinate axes in `ℤ × ℤ`, regarded as an `ℕ`-module, are
recognized as the evaluations of a unique ordered pair of complementary ideals.
-/

universe u v

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

example : Module.End.idealRange (⊤ : Ideal (Module.End R M)ᵐᵒᵖ) = ⊤ := by
  apply top_unique
  calc
    (⊤ : Submodule R M) =
        Module.End.idealRange (Ideal.span {MulOpposite.op (1 : Module.End R M)}) := by
      rw [Module.End.idealRange_span_singleton, Module.End.one_eq_id, LinearMap.range_id]
    _ ≤ Module.End.idealRange ⊤ :=
      (Module.End.gc_idealRange_rangeIdeal (R := R) (M := M)).monotone_l le_top

-- The coordinate axes over ℕ give an ordered recognition example without Ring ℕ.
example :
    ∃! IJ : Ideal (Module.End ℕ (ℤ × ℤ))ᵐᵒᵖ × Ideal (Module.End ℕ (ℤ × ℤ))ᵐᵒᵖ,
      IsCompl IJ.1 IJ.2 ∧
        Module.End.idealRange IJ.1 = LinearMap.ker (LinearMap.snd ℕ ℤ ℤ) ∧
        Module.End.idealRange IJ.2 = LinearMap.ker (LinearMap.fst ℕ ℤ ℤ) := by
  let P := LinearMap.ker (LinearMap.snd ℕ ℤ ℤ)
  let Q := LinearMap.ker (LinearMap.fst ℕ ℤ ℤ)
  apply (DirectSum.isInternal_bool_iff_existsUnique_isCompl P Q).mp
  apply (DirectSum.isInternal_bool_iff_bijective_coprod P Q).mpr
  have hp (p : P) : (p : ℤ × ℤ).2 = 0 := p.property
  have hq (q : Q) : (q : ℤ × ℤ).1 = 0 := q.property
  constructor
  · rintro ⟨p, q⟩ ⟨p', q'⟩ h
    change (p : ℤ × ℤ) + (q : ℤ × ℤ) = (p' : ℤ × ℤ) + (q' : ℤ × ℤ) at h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    simp only [Prod.fst_add, hq, add_zero] at h₁
    simp only [Prod.snd_add, hp, zero_add] at h₂
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext h₁ ((hp p).trans (hp p').symm)
    · apply Subtype.ext
      exact Prod.ext ((hq q).trans (hq q').symm) h₂
  · intro x
    refine ⟨(⟨(x.1, 0), rfl⟩, ⟨(0, x.2), rfl⟩), ?_⟩
    change (x.1, 0) + (0, x.2) = x
    ext <;> simp
