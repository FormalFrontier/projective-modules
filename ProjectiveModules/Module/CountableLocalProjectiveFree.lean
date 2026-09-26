/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import ProjectiveModules.Module.CountableLocalProjective
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Countably generated projective right modules over local rings

This file assembles a coherent finite-free biorthogonal exhaustion into a
basis.  Consequently, a countably generated projective right module over a
possibly noncommutative local ring is free.
-/

@[expose] public section

universe uR uP

open Finsupp Set

namespace Module.Projective

variable {R : Type uR} [Ring R]
variable {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P]

private def countableRightBasisVector {k : ℕ → ℕ}
    (f : (n : ℕ) → (Fin (k n) → R) →ₗ[Rᵐᵒᵖ] P)
    (a : Σ n, Fin (k n)) : P :=
  f a.1 (Pi.single a.2 1)

private def countableRightBasisCoord {k : ℕ → ℕ}
    (g : (n : ℕ) → P →ₗ[Rᵐᵒᵖ] (Fin (k n) → R))
    (a : Σ n, Fin (k n)) : P →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ :=
  (MulOpposite.opLinearEquiv Rᵐᵒᵖ).toLinearMap.comp
    ((LinearMap.proj a.2).comp (g a.1))

private theorem countableRightBasisCoord_apply {k : ℕ → ℕ}
    (f : (n : ℕ) → (Fin (k n) → R) →ₗ[Rᵐᵒᵖ] P)
    (g : (n : ℕ) → P →ₗ[Rᵐᵒᵖ] (Fin (k n) → R))
    (hsplit : ∀ n, (g n).comp (f n) = LinearMap.id)
    (horth : ∀ m n, m ≠ n → (g m).comp (f n) = 0)
    (a b : Σ n, Fin (k n)) :
    countableRightBasisCoord g a (countableRightBasisVector f b) =
      if b = a then 1 else 0 := by
  classical
  rcases a with ⟨m, i⟩
  rcases b with ⟨n, j⟩
  by_cases hmn : m = n
  · subst m
    have hdiag := LinearMap.congr_fun (hsplit n) (Pi.single j 1)
    change g n (f n (Pi.single j 1)) = Pi.single j 1 at hdiag
    by_cases hij : j = i
    · subst j
      simp [countableRightBasisCoord, countableRightBasisVector, hdiag]
    · have hsigma : (Sigma.mk n j : Σ n, Fin (k n)) ≠ Sigma.mk n i := by
        intro h
        exact hij (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
      simp [countableRightBasisCoord, countableRightBasisVector, hdiag,
        hsigma, hij]
  · have hoff := LinearMap.congr_fun (horth m n hmn) (Pi.single j 1)
    change g m (f n (Pi.single j 1)) = 0 at hoff
    have hsigma : (Sigma.mk n j : Σ n, Fin (k n)) ≠ Sigma.mk m i := by
      intro h
      exact hmn (Sigma.mk.inj_iff.mp h).1.symm
    simp [countableRightBasisCoord, countableRightBasisVector, hoff, hsigma]

private theorem countableRightBasisVector_linearIndependent {k : ℕ → ℕ}
    (f : (n : ℕ) → (Fin (k n) → R) →ₗ[Rᵐᵒᵖ] P)
    (g : (n : ℕ) → P →ₗ[Rᵐᵒᵖ] (Fin (k n) → R))
    (hsplit : ∀ n, (g n).comp (f n) = LinearMap.id)
    (horth : ∀ m n, m ≠ n → (g m).comp (f n) = 0) :
    LinearIndependent Rᵐᵒᵖ (countableRightBasisVector f) := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  apply Finsupp.ext
  intro a
  have ha := congrArg (fun p ↦ countableRightBasisCoord g a p) hl
  simpa [Finsupp.linearCombination_apply,
    map_finsuppSum, map_smul,
    countableRightBasisCoord_apply f g hsplit horth] using ha

private theorem countableRightBasisVector_block_mem_span {k : ℕ → ℕ}
    (f : (n : ℕ) → (Fin (k n) → R) →ₗ[Rᵐᵒᵖ] P)
    (n : ℕ) (y : Fin (k n) → R) :
    f n y ∈ Submodule.span Rᵐᵒᵖ (Set.range (countableRightBasisVector f)) := by
  classical
  have hy : y = ∑ i : Fin (k n), MulOpposite.op (y i) • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  rw [hy, map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_smul]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨Sigma.mk n i, rfl⟩)

private theorem countableRightBasisVector_spans {k : ℕ → ℕ}
    (x : ℕ → P)
    (f : (n : ℕ) → (Fin (k n) → R) →ₗ[Rᵐᵒᵖ] P)
    (g : (n : ℕ) → P →ₗ[Rᵐᵒᵖ] (Fin (k n) → R))
    (hspan : Submodule.span Rᵐᵒᵖ (Set.range x) = ⊤)
    (hreconstruct : ∀ n, x n = ∑ i : Fin (n + 1), f i (g i (x n))) :
    ⊤ ≤ Submodule.span Rᵐᵒᵖ (Set.range (countableRightBasisVector f)) := by
  rw [← hspan]
  apply Submodule.span_le.2
  intro p hp
  rcases hp with ⟨n, rfl⟩
  rw [hreconstruct n]
  apply Submodule.sum_mem
  intro i hi
  exact countableRightBasisVector_block_mem_span f i (g i (x n))

/-- A countably generated projective right module over a possibly
noncommutative ring with a proper two-sided ideal whose complement consists of
units has a basis indexed by a countable disjoint union of finite types. -/
theorem exists_sigma_fin_rightBasis_of_countablyGenerated
    [Module.Projective Rᵐᵒᵖ P]
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r)
    (hP : Module.CountablyGenerated Rᵐᵒᵖ P) :
    ∃ k : ℕ → ℕ, Nonempty (Basis (Σ n, Fin (k n)) Rᵐᵒᵖ P) := by
  classical
  obtain ⟨x, k, f, g, hspan, hsplit, horth, hreconstruct⟩ :=
    exists_fin_rightFree_biorthogonal_exhaustion_of_countablyGenerated
      I hI hunit hP
  have hli : LinearIndependent Rᵐᵒᵖ (countableRightBasisVector f) :=
    countableRightBasisVector_linearIndependent f g hsplit horth
  have hsp : ⊤ ≤ Submodule.span Rᵐᵒᵖ (Set.range (countableRightBasisVector f)) :=
    countableRightBasisVector_spans x f g hspan hreconstruct
  exact ⟨k, ⟨Basis.mk hli hsp⟩⟩

/-- Every countably generated projective right module over a possibly
noncommutative ring with a proper two-sided ideal whose complement consists of
units is free. -/
theorem free_of_countablyGenerated
    [Module.Projective Rᵐᵒᵖ P]
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r)
    (hP : Module.CountablyGenerated Rᵐᵒᵖ P) :
    Module.Free Rᵐᵒᵖ P := by
  obtain ⟨k, ⟨b⟩⟩ :=
    exists_sigma_fin_rightBasis_of_countablyGenerated I hI hunit hP
  exact Module.Free.of_basis b

end Module.Projective
