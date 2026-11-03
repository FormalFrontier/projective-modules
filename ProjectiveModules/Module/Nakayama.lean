/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.RingTheory.Nakayama
public import ProjectiveModules.LinearMap.Units
import Mathlib.Algebra.Polynomial.Div

/-!
# Nakayama's lemma and finite-range Jacobson perturbations

Nakayama's lemma applies to the inherited quotient by a submodule. Consequently,
a submodule is the whole module if that quotient is finitely generated and the
submodule, together with the action of an ideal in the Jacobson radical, generates
the module. The ideal need only be a left ideal; the module need not be finite.

Over a commutative ring, an endomorphism with finitely generated image in the
Jacobson-radical action has unit difference from the identity. Only the image is
assumed finite: the ambient module need not be finite, free, or projective, and the
endomorphism need not be nilpotent. The proof applies the finite-module
Cayley–Hamilton theorem to the image, evaluates its annihilating polynomial at one,
and transports a two-sided inverse back to the ambient module.

## References

The finite-module Cayley–Hamilton, Jacobson-radical unit criterion, and polynomial
factorization and evaluation interfaces used here are from Mathlib.
-/

@[expose] public section

universe uA uN
open scoped Pointwise

/-- A submodule with finitely generated quotient is the whole module if it and the
action of a left ideal contained in the Jacobson radical generate the module. -/
theorem Submodule.eq_top_of_finite_quotient_of_sup_smul_eq_top
    {A : Type uA} [Ring A]
    {N : Type uN} [AddCommGroup N] [Module A N]
    (P : Submodule A N) [Module.Finite A (N ⧸ P)]
    (J : Ideal A) (hJ : J ≤ Ideal.jacobson (⊥ : Ideal A))
    (hgen : P ⊔ J • (⊤ : Submodule A N) = ⊤) :
    P = ⊤ := by
  let π : N →ₗ[A] N ⧸ P := P.mkQ
  let T : Submodule A (N ⧸ P) := ⊤
  have hT : T.FG := Module.Finite.fg_top
  have hsup : P ⊔ J • (⊤ : Submodule A N) ≤
      ((Ideal.jacobson (⊥ : Ideal A)) • T).comap π := by
    refine sup_le ?_ ?_
    · intro x hx
      change π x ∈ (Ideal.jacobson (⊥ : Ideal A)) • T
      have hxzero : π x = 0 := by
        change (Submodule.Quotient.mk x : N ⧸ P) = 0
        simpa only [Submodule.Quotient.mk_eq_zero] using hx
      rw [hxzero]
      exact ((Ideal.jacobson (⊥ : Ideal A)) • T).zero_mem
    · apply Submodule.smul_le.mpr
      intro r hr x hx
      change π (r • x) ∈ (Ideal.jacobson (⊥ : Ideal A)) • T
      rw [π.map_smul]
      exact Submodule.smul_mem_smul (hJ hr) (show π x ∈ T from trivial)
  have hTgen : T ≤ (Ideal.jacobson (⊥ : Ideal A)) • T := by
    intro y _
    induction y using Submodule.Quotient.induction_on with
    | _ x =>
        have hx : x ∈ P ⊔ J • (⊤ : Submodule A N) := by
          rw [hgen]
          trivial
        exact hsup hx
  have hTzero : T = ⊥ := by
    apply hT.eq_bot_of_le_jacobson_smul
    simpa only [Ideal.jacobson_bot] using hTgen
  apply top_unique
  intro x _
  have hxT : π x ∈ T := by trivial
  have hxzero : π x = 0 := by
    simpa only [hTzero, Submodule.mem_bot] using hxT
  change (Submodule.Quotient.mk x : N ⧸ P) = 0 at hxzero
  simpa only [Submodule.Quotient.mk_eq_zero] using hxzero

universe u v

namespace Polynomial

private theorem eval_one_sub_one_mem_of_coeff_mem_pow
    {R : Type u} [CommRing R] (p : R[X]) (I : Ideal R) (hp : p.Monic)
    (hcoeff : ∀ k, p.coeff k ∈ I ^ (p.natDegree - k)) :
    p.eval 1 - 1 ∈ I := by
  have heval : p.eval 1 = 1 + ∑ k ∈ Finset.range p.natDegree, p.coeff k := by
    simpa only [eval_add, eval_X_pow, eval_finsetSum, eval_C_mul, one_pow, mul_one]
      using congrArg (Polynomial.eval (1 : R)) hp.as_sum
  rw [heval, add_sub_cancel_left]
  exact Submodule.sum_mem I fun k hk =>
    (Ideal.pow_le_self (ne_of_gt (Nat.sub_pos_of_lt (Finset.mem_range.mp hk)))) (hcoeff k)

private theorem isUnit_one_sub_of_aeval_eq_zero
    {R : Type u} [CommRing R] {A : Type v} [Ring A] [Algebra R A]
    (x : A) (p : R[X]) (hp : aeval x p = 0) (hc : IsUnit (p.eval 1)) :
    IsUnit (1 - x) := by
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := (1 : R)) (p := p)
  -- Reverse the factors in the commutative polynomial ring, before evaluation.
  have hq' : p - C (p.eval 1) = q * (X - C 1) := hq.trans (mul_comm _ _)
  have he : -algebraMap R A (p.eval 1) = (x - 1) * aeval x q := by
    simpa only [aeval_sub, hp, aeval_C, aeval_mul, aeval_X, map_one, zero_sub]
      using congrArg (aeval x) hq
  have he' : -algebraMap R A (p.eval 1) = aeval x q * (x - 1) := by
    simpa only [aeval_sub, hp, aeval_C, aeval_mul, aeval_X, map_one, zero_sub]
      using congrArg (aeval x) hq'
  have hleft : (1 - x) * aeval x q = algebraMap R A (p.eval 1) := by
    rw [← neg_sub x 1, neg_mul, ← he, neg_neg]
  have hright : aeval x q * (1 - x) = algebraMap R A (p.eval 1) := by
    rw [← neg_sub x 1, mul_neg, ← he', neg_neg]
  have hcomm : Commute (1 - x) (aeval x q) :=
    (commute_iff_eq _ _).mpr (hleft.trans hright.symm)
  have hprod : IsUnit ((1 - x) * aeval x q) :=
    hleft.symm ▸ hc.map (algebraMap R A)
  exact (hcomm.isUnit_mul_iff.mp hprod).1

end Polynomial

namespace Module.End

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]

private theorem isUnit_one_sub_of_range_le_jacobson [Module.Finite R M]
    (S : Module.End R M)
    (hS : LinearMap.range S ≤ (⊥ : Ideal R).jacobson • (⊤ : Submodule R M)) :
    IsUnit (1 - S) := by
  obtain ⟨p, hp, _, hcoeff, hzero⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      R S (⊥ : Ideal R).jacobson hS
  exact Polynomial.isUnit_one_sub_of_aeval_eq_zero S p hzero
    (Ideal.isUnit_of_sub_one_mem_jacobson_bot _
      (Polynomial.eval_one_sub_one_mem_of_coeff_mem_pow p _ hp hcoeff))

/-- The identity minus an endomorphism with finitely generated image contained in
the Jacobson-radical action is a unit. No finiteness of the ambient module or
nilpotence of the endomorphism is required. -/
theorem isUnit_one_sub_of_fg_range_le_jacobson
    (T : Module.End R M) (hfg : (LinearMap.range T).FG)
    (hJ : LinearMap.range T ≤ (⊥ : Ideal R).jacobson • (⊤ : Submodule R M)) :
    IsUnit ((1 : Module.End R M) - T) := by
  let U := LinearMap.range T
  let i : U →ₗ[R] M := U.subtype
  let r : M →ₗ[R] U := T.rangeRestrict
  let : Module.Finite R U := Module.Finite.of_fg hfg
  -- Apply the corestriction to the ambient ideal-action bound. The needed bound
  -- is on the range of r ∘ i, not on all of U.
  have hS : LinearMap.range (r.comp i) ≤
      (⊥ : Ideal R).jacobson • (⊤ : Submodule R U) := by
    rintro _ ⟨x, rfl⟩
    exact (Submodule.smul_top_le_comap_smul_top (⊥ : Ideal R).jacobson r)
      (hJ x.property)
  have hunit := (LinearMap.isUnit_one_sub_comp_iff i r).mpr
    (isUnit_one_sub_of_range_le_jacobson (r.comp i) hS)
  simpa only [i, r, U, LinearMap.subtype_comp_rangeRestrict] using hunit

/-- The identity minus an endomorphism with finitely generated image is a unit
when its image is controlled by an ideal contained in the Jacobson radical. -/
theorem isUnit_one_sub_of_fg_range_le_ideal_smul_of_le_jacobson
    (T : Module.End R M) (I : Ideal R) (hfg : (LinearMap.range T).FG)
    (hT : LinearMap.range T ≤ I • (⊤ : Submodule R M))
    (hI : I ≤ (⊥ : Ideal R).jacobson) : IsUnit (1 - T) := by
  exact isUnit_one_sub_of_fg_range_le_jacobson T hfg
    (hT.trans (Submodule.smul_mono_left hI))

end Module.End
