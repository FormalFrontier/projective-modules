/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.FiniteIndex
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import ProjectiveModules.Free.BilinearIndex

/-!
# The regulator of an integer pairing

For finitely generated abelian groups of equal integer-module rank, the regulator of a
real-valued integer-bilinear pairing is its absolute determinant on independent full frames,
divided by the product of the frame spans' indices in the original groups. These indices
include the torsion in the groups. The groups have only their canonical integer actions;
no real-module structures or freeness assumptions on the original groups are required.

## Main results

* `LinearMap.pairingRegulator_frame_invariant` proves invariance of the normalized formula
  under arbitrary independent full frames.
* `LinearMap.pairingRegulator_eq` evaluates the choice-based definition on any such frames.
* `LinearMap.pairingRegulator_nonneg` and
  `LinearMap.pairingRegulator_eq_of_finrank_eq_zero` give nonnegativity and the rank-zero
  formula. The empty determinant is `1`.

The proof compares frame spans through their intersections. The full-rank criterion makes
these intersections finite-index, and the principal ideal domain basis theorem supplies
bases for them. Restricting the pairing scales the determinant by relative indices;
whole-group index multiplication then gives the normalized equality. The pairing
determinant is never cancelled and may vanish.

## References

This generalizes the normalized determinant identity in J. S. Milne, *Abelian Varieties*,
Version 2.0, Introduction, Exercise 0.2. Nondegeneracy, assumed there, is not needed for
this identity. The original finitely generated groups and their pairing are input data;
no point groups or height pairing are constructed here.

The proof uses Mathlib's `Module.Basis.span`, `Submodule.basisOfPidOfLESpan`,
`AddSubgroup.relIndex_eq_natAbs_det`, and `AddSubgroup.relIndex_mul_index`, together with
`LinearMap.abs_det_toMatrix₂Aux_eq_relIndex_mul`.
-/

@[expose] public section

universe u v w

open Module

namespace LinearMap

/-- The absolute determinant on chosen independent integer families of the common finrank,
normalized by the indices of their spans in the whole original abelian groups.

The expression is defined without finite generation; an infinite subgroup index is
represented by zero. For finitely generated groups the index factors are positive and
include torsion, and `LinearMap.pairingRegulator_eq` evaluates the expression on any
independent full frames. The families are chosen independently using the finrank equality
for the right family. No nondegeneracy assumption is needed, and the value can be zero. -/
noncomputable def pairingRegulator
    {M : Type u} {N : Type v} [AddCommGroup M] [AddCommGroup N]
    (B : M →ₗ[ℤ] N →ₗ[ℤ] ℝ)
    (h : Module.finrank ℤ M = Module.finrank ℤ N) : ℝ :=
  let e : Fin (Module.finrank ℤ M) → M :=
    Classical.choose (exists_linearIndependent_of_le_finrank (R := ℤ) (M := M) le_rfl)
  let f : Fin (Module.finrank ℤ M) → N :=
    Classical.choose (exists_linearIndependent_of_le_finrank (R := ℤ) (M := N) (le_of_eq h))
  |(toMatrix₂Aux ℤ e f B).det| /
    (((Submodule.span ℤ (Set.range e)).toAddSubgroup.index : ℝ) *
      ((Submodule.span ℤ (Set.range f)).toAddSubgroup.index : ℝ))

private theorem pairingRegulator_index_span_pos
    {M : Type u} [AddCommGroup M] [Module.Finite ℤ M] {r : ℕ}
    (hr : r = Module.finrank ℤ M) (e : Fin r → M) (he : LinearIndependent ℤ e) :
    0 < (Submodule.span ℤ (Set.range e)).toAddSubgroup.index := by
  subst r
  exact AddSubgroup.index_span_range_pos_of_linearIndependent e he

private noncomputable def pairingRegulator_submoduleBasis
    {M : Type u} [AddCommGroup M] [Module.Finite ℤ M]
    {r : ℕ} (e : Fin r → M) (he : LinearIndependent ℤ e)
    (I : Submodule ℤ M) (hI : I ≤ Submodule.span ℤ (Set.range e))
    (hfin : I.toAddSubgroup.FiniteIndex) (hr : Module.finrank ℤ M = r) :
    Basis (Fin r) ℤ I := by
  classical
  obtain ⟨n, b⟩ := Submodule.basisOfPidOfLESpan he hI
  have hn : n = r := by
    calc
      n = Module.finrank ℤ I := by
        simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis b).symm
      _ = Module.finrank ℤ M :=
        (AddSubgroup.finiteIndex_iff_finrank_eq I.toAddSubgroup).mp hfin
      _ = r := hr
  exact b.reindex (finCongr hn)

private theorem pairingRegulator_normalized_eq_of_le
    {M : Type u} {N : Type v} [AddCommGroup M] [AddCommGroup N]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (B : M →ₗ[ℤ] N →ₗ[ℤ] ℝ)
    {E' E : AddSubgroup M} {F' F : AddSubgroup N}
    [E'.FiniteIndex] [E.FiniteIndex] [F'.FiniteIndex] [F.FiniteIndex]
    (hE : E' ≤ E) (hF : F' ≤ F)
    (bE' : Basis ι ℤ E') (bE : Basis ι ℤ E)
    (bF' : Basis ι ℤ F') (bF : Basis ι ℤ F) :
    |(toMatrix₂Aux ℤ (fun i => (bE' i : M)) (fun i => (bF' i : N)) B).det| /
        ((E'.index : ℝ) * (F'.index : ℝ)) =
      |(toMatrix₂Aux ℤ (fun i => (bE i : M)) (fun i => (bF i : N)) B).det| /
        ((E.index : ℝ) * (F.index : ℝ)) := by
  have hE'0 : (E'.index : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (AddSubgroup.FiniteIndex.index_ne_zero (H := E'))
  have hE0 : (E.index : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (AddSubgroup.FiniteIndex.index_ne_zero (H := E))
  have hF'0 : (F'.index : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (AddSubgroup.FiniteIndex.index_ne_zero (H := F'))
  have hF0 : (F.index : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (AddSubgroup.FiniteIndex.index_ne_zero (H := F))
  have hindexE : (E'.relIndex E : ℝ) * (E.index : ℝ) = (E'.index : ℝ) := by
    rw [← Nat.cast_mul, AddSubgroup.relIndex_mul_index hE]
  have hindexF : (F'.relIndex F : ℝ) * (F.index : ℝ) = (F'.index : ℝ) := by
    rw [← Nat.cast_mul, AddSubgroup.relIndex_mul_index hF]
  apply (div_eq_div_iff (mul_ne_zero hE'0 hF'0) (mul_ne_zero hE0 hF0)).2
  rw [abs_det_toMatrix₂Aux_eq_relIndex_mul B hE hF bE' bE bF' bF]
  calc
    (E'.relIndex E : ℝ) * (F'.relIndex F : ℝ) *
          |(toMatrix₂Aux ℤ (fun i => (bE i : M)) (fun i => (bF i : N)) B).det| *
          ((E.index : ℝ) * (F.index : ℝ)) =
        |(toMatrix₂Aux ℤ (fun i => (bE i : M)) (fun i => (bF i : N)) B).det| *
          (((E'.relIndex E : ℝ) * (E.index : ℝ)) *
            ((F'.relIndex F : ℝ) * (F.index : ℝ))) := by ac_rfl
    _ = _ := by rw [hindexE, hindexF]

/-- The raw normalized pairing determinant is independent of the full independent integer
frames. The indices are taken in the original groups, not in their torsion quotients.
Arbitrary frames need not be unimodularly related. This generalizes the normalized
identity of Milne, *Abelian Varieties*, Introduction, Exercise 0.2: nondegeneracy is not
needed, and neither the pairing nor its determinant is assumed nonzero. -/
theorem pairingRegulator_frame_invariant
    {M : Type u} {N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module.Finite ℤ M] [Module.Finite ℤ N]
    (B : M →ₗ[ℤ] N →ₗ[ℤ] ℝ)
    (h : Module.finrank ℤ M = Module.finrank ℤ N)
    (e e' : Fin (Module.finrank ℤ M) → M)
    (f f' : Fin (Module.finrank ℤ M) → N)
    (he : LinearIndependent ℤ e) (he' : LinearIndependent ℤ e')
    (hf : LinearIndependent ℤ f) (hf' : LinearIndependent ℤ f') :
    |(toMatrix₂Aux ℤ e f B).det| /
        (((Submodule.span ℤ (Set.range e)).toAddSubgroup.index : ℝ) *
          ((Submodule.span ℤ (Set.range f)).toAddSubgroup.index : ℝ)) =
      |(toMatrix₂Aux ℤ e' f' B).det| /
        (((Submodule.span ℤ (Set.range e')).toAddSubgroup.index : ℝ) *
          ((Submodule.span ℤ (Set.range f')).toAddSubgroup.index : ℝ)) := by
  classical
  let E : Submodule ℤ M := Submodule.span ℤ (Set.range e)
  let E' : Submodule ℤ M := Submodule.span ℤ (Set.range e')
  let F : Submodule ℤ N := Submodule.span ℤ (Set.range f)
  let F' : Submodule ℤ N := Submodule.span ℤ (Set.range f')
  let : E.toAddSubgroup.FiniteIndex :=
    ⟨(AddSubgroup.index_span_range_pos_of_linearIndependent e he).ne'⟩
  let : E'.toAddSubgroup.FiniteIndex :=
    ⟨(AddSubgroup.index_span_range_pos_of_linearIndependent e' he').ne'⟩
  let : F.toAddSubgroup.FiniteIndex :=
    ⟨(pairingRegulator_index_span_pos h f hf).ne'⟩
  let : F'.toAddSubgroup.FiniteIndex :=
    ⟨(pairingRegulator_index_span_pos h f' hf').ne'⟩
  let I : Submodule ℤ M := E ⊓ E'
  let J : Submodule ℤ N := F ⊓ F'
  let : I.toAddSubgroup.FiniteIndex :=
    (inferInstance : (E.toAddSubgroup ⊓ E'.toAddSubgroup).FiniteIndex)
  let : J.toAddSubgroup.FiniteIndex :=
    (inferInstance : (F.toAddSubgroup ⊓ F'.toAddSubgroup).FiniteIndex)
  let bE : Basis (Fin (Module.finrank ℤ M)) ℤ E := Basis.span he
  let bE' : Basis (Fin (Module.finrank ℤ M)) ℤ E' := Basis.span he'
  let bF : Basis (Fin (Module.finrank ℤ M)) ℤ F := Basis.span hf
  let bF' : Basis (Fin (Module.finrank ℤ M)) ℤ F' := Basis.span hf'
  let bI : Basis (Fin (Module.finrank ℤ M)) ℤ I :=
    pairingRegulator_submoduleBasis e he I inf_le_left inferInstance rfl
  let bJ : Basis (Fin (Module.finrank ℤ M)) ℤ J :=
    pairingRegulator_submoduleBasis f hf J inf_le_left inferInstance h.symm
  have hleft := pairingRegulator_normalized_eq_of_le B
    (E' := I.toAddSubgroup) (E := E.toAddSubgroup)
    (F' := J.toAddSubgroup) (F := F.toAddSubgroup)
    (show I ≤ E from inf_le_left)
    (show J ≤ F from inf_le_left) bI bE bJ bF
  have hright := pairingRegulator_normalized_eq_of_le B
    (E' := I.toAddSubgroup) (E := E'.toAddSubgroup)
    (F' := J.toAddSubgroup) (F := F'.toAddSubgroup)
    (show I ≤ E' from inf_le_right)
    (show J ≤ F' from inf_le_right) bI bE' bJ bF'
  have hbe : (fun i => (bE i : M)) = e :=
    funext fun i => Basis.coe_span_apply he i
  have hbe' : (fun i => (bE' i : M)) = e' :=
    funext fun i => Basis.coe_span_apply he' i
  have hbf : (fun i => (bF i : N)) = f :=
    funext fun i => Basis.coe_span_apply hf i
  have hbf' : (fun i => (bF' i : N)) = f' :=
    funext fun i => Basis.coe_span_apply hf' i
  simpa only [hbe, hbe', hbf, hbf'] using hleft.symm.trans hright

/-- Evaluate the regulator on any full independent integer frames in the original groups.
The denominators are full-group indices, including torsion. No nondegeneracy or nonzero
pairing determinant is required. -/
theorem pairingRegulator_eq
    {M : Type u} {N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module.Finite ℤ M] [Module.Finite ℤ N]
    (B : M →ₗ[ℤ] N →ₗ[ℤ] ℝ)
    (h : Module.finrank ℤ M = Module.finrank ℤ N)
    (e : Fin (Module.finrank ℤ M) → M) (f : Fin (Module.finrank ℤ M) → N)
    (he : LinearIndependent ℤ e) (hf : LinearIndependent ℤ f) :
    B.pairingRegulator h =
      |(toMatrix₂Aux ℤ e f B).det| /
        (((Submodule.span ℤ (Set.range e)).toAddSubgroup.index : ℝ) *
          ((Submodule.span ℤ (Set.range f)).toAddSubgroup.index : ℝ)) := by
  exact pairingRegulator_frame_invariant B h
    (Classical.choose (exists_linearIndependent_of_le_finrank (R := ℤ) (M := M) le_rfl)) e
    (Classical.choose
      (exists_linearIndependent_of_le_finrank (R := ℤ) (M := N) (le_of_eq h))) f
    (Classical.choose_spec
      (exists_linearIndependent_of_le_finrank (R := ℤ) (M := M) le_rfl)) he
    (Classical.choose_spec
      (exists_linearIndependent_of_le_finrank (R := ℤ) (M := N) (le_of_eq h))) hf

/-- The regulator is nonnegative without finite generation, including when the pairing
determinant vanishes or a span has infinite index. -/
theorem pairingRegulator_nonneg
    {M : Type u} {N : Type v} [AddCommGroup M] [AddCommGroup N]
    (B : M →ₗ[ℤ] N →ₗ[ℤ] ℝ)
    (h : Module.finrank ℤ M = Module.finrank ℤ N) :
    0 ≤ B.pairingRegulator h := by
  unfold pairingRegulator
  exact div_nonneg (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- At rank zero the regulator is the reciprocal of the product of the original groups'
cardinalities. The empty determinant is `1`, and the frame spans are zero. -/
theorem pairingRegulator_eq_of_finrank_eq_zero
    {M : Type u} {N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module.Finite ℤ M] [Module.Finite ℤ N]
    (B : M →ₗ[ℤ] N →ₗ[ℤ] ℝ)
    (h : Module.finrank ℤ M = Module.finrank ℤ N)
    (hM : Module.finrank ℤ M = 0) :
    B.pairingRegulator h = 1 / ((Nat.card M : ℝ) * (Nat.card N : ℝ)) := by
  classical
  let : IsEmpty (Fin (Module.finrank ℤ M)) := by
    rw [hM]
    infer_instance
  let e : Fin (Module.finrank ℤ M) → M := isEmptyElim
  let f : Fin (Module.finrank ℤ M) → N := isEmptyElim
  rw [pairingRegulator_eq B h e f linearIndependent_empty_type linearIndependent_empty_type]
  simp only [Matrix.det_isEmpty, abs_one, Set.range_eq_empty, Submodule.span_empty,
    Submodule.bot_toAddSubgroup, AddSubgroup.index_bot]

end LinearMap
