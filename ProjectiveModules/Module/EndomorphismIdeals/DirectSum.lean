/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.Idempotents
public import ProjectiveModules.Module.EndomorphismIdeals
public import ProjectiveModules.Module.DirectSum
public import ProjectiveModules.Module.CommutingProjections
public import ProjectiveModules.RingTheory.Ideal.Complemented

/-!
# Endomorphism ideals of internal sums

Evaluating the range ideal of a summand of an internal direct sum recovers that summand.
An internal binary sum gives complementary range ideals in the opposite endomorphism semiring.
For an additive group, complementary ideals evaluate to an internal binary sum.
The two constructions recognize ordered pairs uniquely on these restricted loci;
they do not give inverse maps on the full submodule and ideal lattices.

## Implementation notes

The reverse direction uses `Ideal.exists_idempotent_eq_span_of_isCompl` and
`CompleteOrthogonalIdempotents.isInternal_ranges` with a Boolean family.
Its completeness and orthogonality use Andrew Yang's
`CompleteOrthogonalIdempotents.iff_ortho_complete` in Mathlib.
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

namespace Module.End

variable {R : Type u} {M : Type v} [Semiring R] [AddCommGroup M] [Module R M]

/-- A complemented right ideal is recovered from its evaluation submodule. -/
theorem rangeIdeal_idealRange_of_isCompl
    {I J : Ideal (Module.End R M)ᵐᵒᵖ} (h : IsCompl I J) :
    rangeIdeal (idealRange I) = I := by
  obtain ⟨e, he, hI, _⟩ := Ideal.exists_idempotent_eq_span_of_isCompl h
  have he' : MulOpposite.unop e * MulOpposite.unop e = MulOpposite.unop e :=
    congrArg MulOpposite.unop he
  rw [hI, ← MulOpposite.op_unop e, idealRange_span_singleton]
  exact rangeIdeal_range_eq_span_of_idempotent _ he'

/-- Complementary right ideals evaluate to an internal binary sum, with the
first ideal indexed by `true`. -/
theorem isInternal_idealRange {I J : Ideal (Module.End R M)ᵐᵒᵖ}
    (h : IsCompl I J) :
    DirectSum.IsInternal (fun b : Bool => cond b (idealRange I) (idealRange J)) := by
  obtain ⟨e, he, hI, hJ⟩ := Ideal.exists_idempotent_eq_span_of_isCompl h
  let f : Module.End R M := MulOpposite.unop e
  let g : Module.End R M := MulOpposite.unop (1 - e)
  have hfg : f * g = 0 := by
    change MulOpposite.unop ((1 - e) * e) = 0
    rw [sub_mul, one_mul, he, sub_self, MulOpposite.unop_zero]
  have hgf : g * f = 0 := by
    change MulOpposite.unop (e * (1 - e)) = 0
    rw [mul_sub, mul_one, he, sub_self, MulOpposite.unop_zero]
  have hs : f + g = 1 := by
    change MulOpposite.unop e + MulOpposite.unop (1 - e) = 1
    rw [add_comm, ← MulOpposite.unop_add, sub_add_cancel, MulOpposite.unop_one]
  have hc : CompleteOrthogonalIdempotents (fun b : Bool => cond b f g) := by
    apply CompleteOrthogonalIdempotents.iff_ortho_complete.mpr
    constructor
    · intro a b hab
      cases a <;> cases b <;> simp_all
    · simpa only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false] using hs
  have hI' : idealRange I = LinearMap.range f := by
    rw [hI]
    simpa only [f, MulOpposite.op_unop] using idealRange_span_singleton (MulOpposite.unop e)
  have hJ' : idealRange J = LinearMap.range g := by
    rw [hJ]
    simpa only [g, MulOpposite.op_unop] using
      idealRange_span_singleton (MulOpposite.unop (1 - e))
  have hfamily : (fun b : Bool => (cond b f g).range) =
      (fun b : Bool => cond b (idealRange I) (idealRange J)) := by
    funext b
    cases b <;> simp only [Bool.cond_false, Bool.cond_true, hI', hJ']
  rw [← hfamily]
  have hdec : (fun a b : Bool => Classical.propDecidable (a = b)) =
      instDecidableEqBool := Subsingleton.elim _ _
  rw [← hdec]
  exact hc.isInternal_ranges

end Module.End

namespace DirectSum

variable {R : Type u} {M : Type v} [Semiring R] [AddCommGroup M] [Module R M]

/-- An internal ordered pair is the evaluation of a unique ordered pair of
complementary right ideals. The first coordinate is indexed by `true`. -/
theorem isInternal_bool_iff_existsUnique_isCompl (P Q : Submodule R M) :
    IsInternal (fun b : Bool => cond b P Q) ↔
      ∃! IJ : Ideal (Module.End R M)ᵐᵒᵖ × Ideal (Module.End R M)ᵐᵒᵖ,
        IsCompl IJ.1 IJ.2 ∧ Module.End.idealRange IJ.1 = P ∧
          Module.End.idealRange IJ.2 = Q := by
  constructor
  · intro h
    have hVJ := IsInternal.idealRange_rangeIdeal (R := R) (M := M) (I := Bool)
      (A := fun b : Bool => cond b P Q)
    have hdec : (fun a b : Bool => Classical.propDecidable (a = b)) =
        instDecidableEqBool := Subsingleton.elim _ _
    rw [hdec] at hVJ
    refine ⟨(Module.End.rangeIdeal P, Module.End.rangeIdeal Q),
      ⟨h.isCompl_rangeIdeal, ?_, ?_⟩, ?_⟩
    · simpa only [Bool.cond_true] using hVJ h true
    · simpa only [Bool.cond_false] using hVJ h false
    · rintro ⟨I, J⟩ ⟨hIJ, hI, hJ⟩
      apply Prod.ext
      · change I = Module.End.rangeIdeal P
        rw [← hI]
        exact (Module.End.rangeIdeal_idealRange_of_isCompl hIJ).symm
      · change J = Module.End.rangeIdeal Q
        rw [← hJ]
        exact (Module.End.rangeIdeal_idealRange_of_isCompl hIJ.symm).symm
  · rintro ⟨⟨I, J⟩, ⟨hIJ, hI, hJ⟩, _⟩
    simpa only [hI, hJ] using Module.End.isInternal_idealRange hIJ

end DirectSum

namespace Module.End

variable {R : Type u} {M : Type v} [Semiring R] [AddCommGroup M] [Module R M]

/-- Complementary right ideals arise as the range ideals of a unique internal
ordered pair. The first submodule is indexed by `true`. -/
theorem isCompl_iff_existsUnique_isInternal (I J : Ideal (Module.End R M)ᵐᵒᵖ) :
    IsCompl I J ↔ ∃! PQ : Submodule R M × Submodule R M,
      DirectSum.IsInternal (fun b : Bool => cond b PQ.1 PQ.2) ∧
        rangeIdeal PQ.1 = I ∧ rangeIdeal PQ.2 = J := by
  constructor
  · intro h
    refine ⟨(idealRange I, idealRange J),
      ⟨isInternal_idealRange h, rangeIdeal_idealRange_of_isCompl h,
        rangeIdeal_idealRange_of_isCompl h.symm⟩, ?_⟩
    rintro ⟨P, Q⟩ ⟨hPQ, hP, hQ⟩
    have hVJ := DirectSum.IsInternal.idealRange_rangeIdeal
      (R := R) (M := M) (I := Bool) (A := fun b : Bool => cond b P Q)
    have hdec : (fun a b : Bool => Classical.propDecidable (a = b)) =
        instDecidableEqBool := Subsingleton.elim _ _
    rw [hdec] at hVJ
    apply Prod.ext
    · change P = idealRange I
      rw [← hP]
      simpa only [Bool.cond_true] using (hVJ hPQ true).symm
    · change Q = idealRange J
      rw [← hQ]
      simpa only [Bool.cond_false] using (hVJ hPQ false).symm
  · rintro ⟨⟨P, Q⟩, ⟨hPQ, hP, hQ⟩, _⟩
    rw [← hP, ← hQ]
    exact hPQ.isCompl_rangeIdeal

end Module.End
