/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.EndomorphismIdeals

/-!
# Evaluation of the unit endomorphism ideal

The principal-ideal identity and monotonicity from the Galois connection show
that the whole endomorphism ideal evaluates to the whole module, using only
the public API.
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
