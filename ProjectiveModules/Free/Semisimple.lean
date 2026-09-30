/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md
module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import StableRange.Cancellation
public import StableRange.DivisionRing

/-!
# Finite stably free modules over semisimple rings

This file proves that every finite stably free module over a semisimple ring is
free. The ring may be noncommutative or trivial.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u v w

namespace Module

private theorem stableRangeCondition_pi
    {ι : Type v} {S : ι → Type w} [(i : ι) → Ring (S i)] {n : ℕ}
    (h : ∀ i, Bass.StableRangeCondition (S i) n) :
    Bass.StableRangeCondition ((i : ι) → S i) n := by
  classical
  intro r₀ r hr
  have hrComponent (i : ι) :
      Bass.IsRightUnimodularCons (r₀ i) (fun j ↦ r j i) :=
    hr.map (Pi.evalRingHom S i)
  choose t ht using fun i ↦ h i (r₀ i) (fun j ↦ r j i) (hrComponent i)
  let s (i : ι) := (ht i).choose
  have hs (i : ι) := (ht i).choose_spec
  refine ⟨fun j i ↦ t i j, fun j i ↦ s i j, ?_⟩
  ext i
  simpa using hs i

private theorem stableRangeCondition_one_of_isSemisimpleRing
    (R : Type u) [Ring R] [IsSemisimpleRing R] :
    Bass.StableRangeCondition R 1 := by
  classical
  obtain ⟨n, D, d, _, _, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
  have hProduct : Bass.StableRangeCondition
      ((i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) (D i)) 1 :=
    stableRangeCondition_pi fun _ ↦
      Bass.isUnitRegular_matrix.stableRangeCondition_one
  exact hProduct.map_equiv e.symm

private def splitFiniteCoordinates
    (R : Type u) [Ring R] (m n : ℕ) (h : m ≤ n) :
    (Fin n → R) ≃ₗ[R] (Fin m → R) × (Fin (n - m) → R) :=
  (LinearEquiv.piCongrLeft R (fun _ : Fin n ↦ R)
    (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h)))).symm.trans
      (LinearEquiv.sumPiEquivProdPi R (Fin m) (Fin (n - m)) (fun _ ↦ R))

/-- A finite stably free module over a semisimple ring is free.

This applies to arbitrary left modules over possibly noncommutative rings and
also covers the zero ring and zero module. -/
theorem free_of_finite_isStablyFree_of_isSemisimpleRing
    (R : Type u) [Ring R] [IsSemisimpleRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    [Module.IsStablyFree R P] [Module.Finite R P] :
    Module.Free R P := by
  classical
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Module.Free.of_subsingleton' R P
  obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod R P
  let m := Fintype.card (Module.Free.ChooseBasisIndex R N)
  let n := Fintype.card (Module.Free.ChooseBasisIndex R (P × N))
  let bN := (Module.Free.chooseBasis R N).reindex
    (Fintype.equivFin (Module.Free.ChooseBasisIndex R N))
  let bPN := (Module.Free.chooseBasis R (P × N)).reindex
    (Fintype.equivFin (Module.Free.ChooseBasisIndex R (P × N)))
  let e : (P × (Fin m → R)) ≃ₗ[R] (Fin n → R) :=
    ((LinearEquiv.refl R P).prodCongr bN.equivFun).symm.trans bPN.equivFun
  let inclusion : (Fin m → R) →ₗ[R] (Fin n → R) :=
    e.toLinearMap.comp (LinearMap.inr R P (Fin m → R))
  have hmn : m ≤ n :=
    StrongRankCondition.le_of_fin_injective inclusion
      (e.injective.comp LinearMap.inr_injective)
  let aligned : ((Fin m → R) × P) ≃ₗ[R]
      ((Fin m → R) × (Fin (n - m) → R)) :=
    (LinearEquiv.prodComm R (Fin m → R) P).trans <|
      e.trans (splitFiniteCoordinates R m n hmn)
  let _ : IsSemisimpleRing (Module.End R (Fin m → R)) :=
    IsSemisimpleRing.moduleEnd R (Fin m → R)
  have hEnd : Bass.StableRangeCondition (Module.End R (Fin m → R)) 1 :=
    stableRangeCondition_one_of_isSemisimpleRing (Module.End R (Fin m → R))
  exact Module.Free.of_equiv
    (Bass.exists_linearEquiv_of_prod_of_end_stableRangeCondition_one
      hEnd aligned).some.symm

end Module
