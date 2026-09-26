/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism and the worker contributors identified in README.md and Git history
module

public import ProjectiveModules.Module.ComponentwiseFree

/-!
# Direct clients for componentwise-free modules

These compile-time clients exercise the edge cases of the componentwise-free
API: an empty decomposition over the zero ring, a connected nontrivial ring,
unequal and zero ranks on `Int × Int`, a nontrivial refinement, and a module
carrier lifted to an independent universe.
-/

section

open Function Set

noncomputable section

private def intOneIdempotent : Fin 1 → ℤ := fun _ ↦ 1

private def constantRank (n : ℕ) : Fin 1 → ℕ := fun _ ↦ n

private theorem intOneIdempotent_complete :
    CompleteOrthogonalIdempotents intOneIdempotent := by
  constructor
  · constructor
    · intro i
      exact IsIdempotentElem.one
    · intro i j hij
      exact (hij (Subsingleton.elim _ _)).elim
  · simp [intOneIdempotent]

-- Empty orthogonal family and empty spectrum over the zero ring.
private theorem emptyZeroRing : Module.ComponentwiseFree (ZMod 1)
    (Module.ComponentwiseFreeModel (fun i : Fin 0 ↦ (i.elim0 : ZMod 1))
      (fun i : Fin 0 ↦ i.elim0)) := by
  exact Module.componentwiseFree_of_model
    (fun i : Fin 0 ↦ (i.elim0 : ZMod 1)) (fun i : Fin 0 ↦ i.elim0)
    CompleteOrthogonalIdempotents.of_subsingleton ⟨LinearEquiv.refl _ _⟩

-- A connected, nontrivial ring client retains the explicit component model.
private theorem connectedIntegerModel : Module.ComponentwiseFree ℤ
    (Module.ComponentwiseFreeModel intOneIdempotent (constantRank 3)) :=
  Module.componentwiseFree_of_model intOneIdempotent (constantRank 3)
    intOneIdempotent_complete ⟨LinearEquiv.refl _ _⟩

-- Its rank is constant because the sole component idempotent is one.
private theorem integerModelRank (p : PrimeSpectrum ℤ) :
    Module.rankAtStalk (R := ℤ)
      (Module.ComponentwiseFreeModel intOneIdempotent (constantRank 3)) p = 3 :=
  Module.rankAtStalk_componentwiseFreeModel_of_notMem
    intOneIdempotent (constantRank 3) intOneIdempotent_complete 0 p
    p.asIdeal.one_notMem

-- On the connected nontrivial ring `Int`, componentwise freeness is an
-- additional equivalence-to-the-explicit-realization condition on a finite
-- projective, rather than merely the assertion that its rank is constant.
private theorem connectedClassification {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Finite ℤ M] [Module.Projective ℤ M] :
    Module.ComponentwiseFree ℤ M ↔ Nonempty
      (M ≃ₗ[ℤ] ModuleCat.FiniteProjective.ofLocallyConstantRank ℤ
        (Module.rankLocallyConstant ℤ M)) :=
  Module.ComponentwiseFree.iff_nonempty_linearEquiv_ofLocallyConstantRank

private def intRedundantIdempotent : Fin 2 → ℤ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0

private theorem intRedundantIdempotent_complete :
    CompleteOrthogonalIdempotents intRedundantIdempotent := by
  constructor
  · constructor
    · intro i
      fin_cases i <;> simp [intRedundantIdempotent, IsIdempotentElem]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [intRedundantIdempotent]
  · rw [Fin.sum_univ_two]
    simp [intRedundantIdempotent]

private def intRedundantRanks : Fin 2 → ℕ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 37

-- A zero idempotent component is harmless even when assigned a redundant
-- positive displayed rank.
private theorem redundantZeroComponent : Module.ComponentwiseFree ℤ
    (Module.ComponentwiseFreeModel intRedundantIdempotent intRedundantRanks) :=
  Module.componentwiseFree_of_model intRedundantIdempotent intRedundantRanks
    intRedundantIdempotent_complete ⟨LinearEquiv.refl _ _⟩

private def prodIdempotent : Fin 2 → ℤ × ℤ
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (0, 1)

private theorem prodIdempotent_complete :
    CompleteOrthogonalIdempotents prodIdempotent := by
  constructor
  · constructor
    · intro i
      fin_cases i <;> simp [prodIdempotent, IsIdempotentElem]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [prodIdempotent]
  · rw [Fin.sum_univ_two]
    simp [prodIdempotent]

private def unequalRanks : Fin 2 → ℕ
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 0

-- Unequal component ranks, including a zero-rank component, over `Int × Int`.
private theorem unequalProductRanks : Module.ComponentwiseFree (ℤ × ℤ)
    (Module.ComponentwiseFreeModel prodIdempotent unequalRanks) :=
  Module.componentwiseFree_of_model prodIdempotent unequalRanks
    prodIdempotent_complete ⟨LinearEquiv.refl _ _⟩

private def prodOneIdempotent : Fin 1 → ℤ × ℤ := fun _ ↦ 1

private theorem prodOneIdempotent_complete :
    CompleteOrthogonalIdempotents prodOneIdempotent := by
  constructor
  · constructor
    · intro i
      exact IsIdempotentElem.one
    · intro i j hij
      exact (hij (Subsingleton.elim _ _)).elim
  · simp [prodOneIdempotent]

private def rankTwo {I : Type*} (_ : I) : ℕ := 2

-- The one-piece decomposition and its two-piece product-ring refinement give
-- linearly equivalent models.
private theorem refinementEquivalence : Nonempty
    (Module.ComponentwiseFreeModel prodOneIdempotent rankTwo ≃ₗ[ℤ × ℤ]
      Module.ComponentwiseFreeModel prodIdempotent rankTwo) := by
  apply Nonempty.intro
  apply Module.componentwiseFreeModelEquivOfRankAtStalkEq
    prodOneIdempotent rankTwo prodOneIdempotent_complete
    prodIdempotent rankTwo prodIdempotent_complete
  funext p
  obtain ⟨i, hi⟩ : ∃ i, prodIdempotent i ∉ p.asIdeal := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hsum : ∑ i, prodIdempotent i ∈ p.asIdeal :=
      p.asIdeal.sum_mem fun i _ ↦ h i
    rw [prodIdempotent_complete.complete] at hsum
    exact p.asIdeal.one_notMem hsum
  rw [Module.rankAtStalk_componentwiseFreeModel_of_notMem
      prodOneIdempotent rankTwo prodOneIdempotent_complete 0 p p.asIdeal.one_notMem,
    Module.rankAtStalk_componentwiseFreeModel_of_notMem
      prodIdempotent rankTwo prodIdempotent_complete i p hi]
  rfl

-- The carrier may live in an independent `ULift` universe.
private theorem liftedCarrier : Module.ComponentwiseFree ℤ
    (ULift.{1} (Module.ComponentwiseFreeModel intOneIdempotent (constantRank 3))) :=
  (Module.componentwiseFree_of_model intOneIdempotent (constantRank 3)
    intOneIdempotent_complete ⟨LinearEquiv.refl _ _⟩).equiv ULift.moduleEquiv

end
