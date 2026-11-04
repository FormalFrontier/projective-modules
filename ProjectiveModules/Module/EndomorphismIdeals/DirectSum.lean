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
An internal binary sum gives complementary range ideals in the opposite endomorphism semiring.
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

/-- The range ideals of the two summands of an internal binary sum are complementary. -/
theorem IsInternal.isCompl_rangeIdeal {P Q : Submodule R M}
    (h : IsInternal (fun b : Bool => cond b P Q)) :
    IsCompl (Module.End.rangeIdeal P) (Module.End.rangeIdeal Q) := by
  classical
  let c := LinearMap.coprod P.subtype Q.subtype
  have hc : Function.Bijective c :=
    (isInternal_bool_iff_bijective_coprod P Q).mp h
  have hzero (x : M) (hxP : x ∈ P) (hxQ : x ∈ Q) : x = 0 := by
    have hxy : c ((⟨x, hxP⟩ : P), 0) = c (0, (⟨x, hxQ⟩ : Q)) := by
      change x + 0 = 0 + x
      simp only [add_zero, zero_add]
    exact congrArg (fun z : P × Q => (z.1 : M)) (hc.1 hxy)
  refine ⟨?_, ?_⟩
  · apply Submodule.disjoint_def.mpr
    intro f hf hg
    apply MulOpposite.unop_injective
    ext x
    apply hzero
    · exact (Module.End.mem_rangeIdeal_iff (f := MulOpposite.unop f)).mp
        (by simpa only [MulOpposite.op_unop] using hf) x
    · exact (Module.End.mem_rangeIdeal_iff (f := MulOpposite.unop f)).mp
        (by simpa only [MulOpposite.op_unop] using hg) x
  · apply codisjoint_iff.mpr
    apply (Ideal.eq_top_iff_one _).mpr
    let e := LinearEquiv.ofBijective c hc
    let p : Module.End R M :=
      P.subtype.comp ((LinearMap.fst R P Q).comp e.symm.toLinearMap)
    let q : Module.End R M :=
      Q.subtype.comp ((LinearMap.snd R P Q).comp e.symm.toLinearMap)
    have hp : MulOpposite.op p ∈ Module.End.rangeIdeal P :=
      Module.End.mem_rangeIdeal_iff.mpr fun x => (e.symm x).1.property
    have hq : MulOpposite.op q ∈ Module.End.rangeIdeal Q :=
      Module.End.mem_rangeIdeal_iff.mpr fun x => (e.symm x).2.property
    have hsum : p + q = 1 := by
      ext x
      exact e.apply_symm_apply x
    have hop : MulOpposite.op p + MulOpposite.op q =
        (1 : (Module.End R M)ᵐᵒᵖ) := congrArg MulOpposite.op hsum
    rw [← hop]
    exact Submodule.add_mem_sup hp hq

end DirectSum
