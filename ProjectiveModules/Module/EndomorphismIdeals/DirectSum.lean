/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.EndomorphismIdeals
public import ProjectiveModules.Module.DirectSum

/-!
# Endomorphism ideals of internal sums

Evaluating the range ideal of a summand of an internal direct sum recovers that summand.
-/

@[expose] public section

universe u v w

namespace DirectSum

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {I : Type w} {A : I → Submodule R M}

open Classical in
/-- Evaluating the range ideal of any summand of an internal direct sum recovers
that summand, with no finiteness assumption on the index type. -/
theorem IsInternal.idealRange_rangeIdeal (hA : IsInternal A) (i : I) :
    Module.End.idealRange (Module.End.rangeIdeal (A i)) = A i := by
  classical
  apply le_antisymm
  · exact Module.End.idealRange_le_iff.mpr le_rfl
  · let e := LinearEquiv.ofBijective (coeLinearMap A) hA
    let r := (component R I (fun j => A j) i).comp e.symm.toLinearMap
    let f : Module.End R M := (A i).subtype.comp r
    have hf : MulOpposite.op f ∈ Module.End.rangeIdeal (A i) :=
      Module.End.mem_rangeIdeal_iff.mpr fun x => (r x).property
    intro x hx
    have hr : r x = (⟨x, hx⟩ : A i) :=
      hA.ofBijective_coeLinearMap_same (⟨x, hx⟩ : A i)
    have hfix : f x = x := congrArg Subtype.val hr
    simpa only [hfix] using Module.End.apply_mem_idealRange hf x

end DirectSum
