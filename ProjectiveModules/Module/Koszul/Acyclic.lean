/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Koszul.HomogeneousContraction
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Positive-degree acyclicity of homogeneous Koszul complexes

The contraction identities in degree zero and in each successor degree express
every cycle as a boundary, without division by the total degree.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, 2013.
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators
universe u v

namespace Module.Koszul

variable (R : Type u) [CommRing R]
variable (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
variable [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]

/-- Positive-total-degree acyclicity in the ambient module category, as in the
homogeneous Koszul exactness argument of Weibel's *The K-book*. -/
theorem homogeneousComplex_acyclic (n : ℕ) (hn : 0 < n) :
    (homogeneousComplex (Rᵐᵒᵖ) P n).Acyclic := by
  apply (HomologicalComplex.acyclic_iff
    (K := homogeneousComplex (Rᵐᵒᵖ) P n)).2
  intro j
  cases j with
  | zero =>
      apply (HomologicalComplex.exactAt_iff'
        (K := homogeneousComplex (Rᵐᵒᵖ) P n) (i := 1) (j := 0) (k := 0)
        (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero).2
      apply (CategoryTheory.ShortComplex.moduleCat_exact_iff _).2
      change ∀ (x : (homogeneousComplex (Rᵐᵒᵖ) P n).X 0),
        (homogeneousComplex (Rᵐᵒᵖ) P n).d 0 0 x = 0 →
        ∃ (y : (homogeneousComplex (Rᵐᵒᵖ) P n).X 1),
          (homogeneousComplex (Rᵐᵒᵖ) P n).d 1 0 y = x
      intro x _
      refine ⟨homogeneousContraction (Rᵐᵒᵖ) P n 0 x, ?_⟩
      have h := congrArg
        (fun f : (homogeneousComplex (Rᵐᵒᵖ) P n).X 0 ⟶
            (homogeneousComplex (Rᵐᵒᵖ) P n).X 0 => f x)
        (homogeneousContraction_homotopy_zero (Rᵐᵒᵖ) P n hn)
      change (homogeneousComplex (Rᵐᵒᵖ) P n).d 1 0
        (homogeneousContraction (Rᵐᵒᵖ) P n 0 x) = x at h
      exact h
  | succ i =>
      apply (HomologicalComplex.exactAt_iff'
        (K := homogeneousComplex (Rᵐᵒᵖ) P n)
        (i := i + 2) (j := i + 1) (k := i)
        (ChainComplex.prev ℕ (i + 1)) (ChainComplex.next_nat_succ i)).2
      apply (CategoryTheory.ShortComplex.moduleCat_exact_iff _).2
      change ∀ (x : (homogeneousComplex (Rᵐᵒᵖ) P n).X (i + 1)),
        (homogeneousComplex (Rᵐᵒᵖ) P n).d (i + 1) i x = 0 →
        ∃ (y : (homogeneousComplex (Rᵐᵒᵖ) P n).X (i + 2)),
          (homogeneousComplex (Rᵐᵒᵖ) P n).d (i + 2) (i + 1) y = x
      intro x hx
      refine ⟨homogeneousContraction (Rᵐᵒᵖ) P n (i + 1) x, ?_⟩
      have h := congrArg
        (fun f : (homogeneousComplex (Rᵐᵒᵖ) P n).X (i + 1) ⟶
            (homogeneousComplex (Rᵐᵒᵖ) P n).X (i + 1) => f x)
        (homogeneousContraction_homotopy_succ (Rᵐᵒᵖ) P n i)
      change (homogeneousComplex (Rᵐᵒᵖ) P n).d (i + 2) (i + 1)
          (homogeneousContraction (Rᵐᵒᵖ) P n (i + 1) x) +
        homogeneousContraction (Rᵐᵒᵖ) P n i
          ((homogeneousComplex (Rᵐᵒᵖ) P n).d (i + 1) i x) = x at h
      simpa [hx] using h

end Module.Koszul
