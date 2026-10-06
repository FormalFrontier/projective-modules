/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Free.InvariantBasisNumber
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Rank-condition pullback clients

Polynomial evaluation has a nonzero kernel, while monoid-algebra augmentation
and arbitrary maps to division rings give further applications. The opposite
homomorphism translates invariant basis number to right modules.
-/

open scoped MonoidAlgebra Polynomial

universe u v

private theorem evaluation_at_zero_not_injective :
    ¬ Function.Injective (Polynomial.evalRingHom (0 : ℚ)) := by
  intro hinj
  have h : (Polynomial.X : ℚ[X]) = 0 := hinj (by simp)
  exact Polynomial.X_ne_zero h

private theorem polynomial_evaluation_rankCondition : RankCondition ℚ[X] :=
  (Polynomial.evalRingHom (0 : ℚ)).rankCondition

private theorem polynomial_evaluation_invariantBasisNumber : InvariantBasisNumber ℚ[X] :=
  (Polynomial.evalRingHom (0 : ℚ)).invariantBasisNumber

private theorem division_ring_rankCondition {R : Type u} {D : Type v}
    [Semiring R] [DivisionRing D] (f : R →+* D) : RankCondition R :=
  f.rankCondition

private theorem division_ring_right_invariantBasisNumber {R : Type u} {D : Type v}
    [Semiring R] [DivisionRing D] (f : R →+* D) :
    InvariantBasisNumber Rᵐᵒᵖ := by
  have htarget : InvariantBasisNumber Dᵐᵒᵖ :=
    (MulOpposite.invariantBasisNumber_iff (R := D)).mpr inferInstance
  exact @RingHom.invariantBasisNumber _ _ _ _ (RingHom.op f) htarget

private theorem integer_monoid_algebra_invariantBasisNumber {M : Type u} [Monoid M] :
    InvariantBasisNumber ℤ[M] :=
  ((MonoidAlgebra.lift ℤ ℤ M (1 : M →* ℤ)).toRingHom).invariantBasisNumber

private theorem integer_group_algebra_right_invariantBasisNumber {G : Type u} [Group G] :
    InvariantBasisNumber ℤ[G]ᵐᵒᵖ := by
  let augmentation : ℤ[G] →+* ℤ :=
    (MonoidAlgebra.lift ℤ ℤ G (1 : G →* ℤ)).toRingHom
  have htarget : InvariantBasisNumber ℤᵐᵒᵖ :=
    (MulOpposite.invariantBasisNumber_iff (R := ℤ)).mpr inferInstance
  exact @RingHom.invariantBasisNumber _ _ _ _ (RingHom.op augmentation) htarget
