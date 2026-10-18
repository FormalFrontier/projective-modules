/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Topology.LocallyConstant.Algebra
public import ProjectiveModules.Module.ProjectivePi
public import ProjectiveModules.Module.RankFiberDecomposition

/-!
# Locally constant rank of finite projective modules

For a finite projective left module over a commutative ring,
`Module.rankLocallyConstant R M` is a bundled Nat-valued locally constant
function on the prime spectrum. Its definition and application theorem are in
`ProjectiveModules.Module.RankFiberDecomposition`.

This file proves isomorphism invariance, the zero and regular-module
normalizations, addition under finite dependent products and binary products,
and multiplication under tensor products. Scalar extension is pullback by
`LocallyConstant.comapRingHom` along the continuous prime-spectrum comap.
All equalities use the pointwise semiring structure on locally constant
functions. The zero ring has empty prime spectrum, and finite dependent
products include an empty index.

## References

The proofs use the stalk-rank laws from Andrew Yang's Mathlib free-locus
formalization. The locally constant function and finite-projective closure
interfaces are the existing Mathlib and ProjectiveModules interfaces.
-/

@[expose] public section

universe uR uS uM uN uι

open scoped BigOperators TensorProduct

namespace Module

variable (R : Type uR) [CommRing R]

/-- Linearly isomorphic finite projective modules have the same locally constant rank. -/
theorem rankLocallyConstant_eq_of_equiv
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (N : Type uN) [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (e : M ≃ₗ[R] N) :
    rankLocallyConstant R M = rankLocallyConstant R N := by
  ext p
  exact congrFun (rankAtStalk_eq_of_equiv e) p

/-- A subsingleton finite projective module has locally constant rank zero. -/
@[simp]
theorem rankLocallyConstant_eq_zero_of_subsingleton
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] [Subsingleton M] :
    rankLocallyConstant R M = 0 := by
  ext p
  exact congrFun (rankAtStalk_eq_zero_of_subsingleton (R := R) (M := M)) p

/-- The regular module has locally constant rank one, including over the zero ring,
whose prime spectrum is empty. -/
@[simp]
theorem rankLocallyConstant_self : rankLocallyConstant R R = 1 := by
  ext p
  let := PrimeSpectrum.nontrivial p
  exact congrFun (rankAtStalk_self (R := R)) p

/-- The locally constant rank of a finite dependent product is the sum of the
locally constant ranks of its factors. The index may be empty. -/
@[simp]
theorem rankLocallyConstant_pi (ι : Type uι) [_root_.Finite ι]
    (M : ι → Type uM) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Finite R (M i)] [∀ i, Module.Projective R (M i)] :
    rankLocallyConstant R (∀ i, M i) = ∑ᶠ i, rankLocallyConstant R (M i) := by
  classical
  let := Fintype.ofFinite ι
  ext p
  have hsum :
      (∑ i, rankLocallyConstant R (M i)) p =
        ∑ i, rankLocallyConstant R (M i) p :=
    map_sum (LocallyConstant.evalAddMonoidHom p) _ _
  simpa only [finsum_eq_sum_of_fintype, hsum, rankLocallyConstant_apply] using
    (rankAtStalk_pi (R := R) M p)

/-- Binary products add the locally constant ranks of finite projective modules. -/
@[simp]
theorem rankLocallyConstant_prod
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (N : Type uN) [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] :
    rankLocallyConstant R (M × N) = rankLocallyConstant R M + rankLocallyConstant R N := by
  ext p
  exact congrFun (rankAtStalk_prod (R := R) M N) p

/-- Tensor products multiply the locally constant ranks of finite projective modules. -/
@[simp]
theorem rankLocallyConstant_tensorProduct
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (N : Type uN) [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] :
    rankLocallyConstant R (M ⊗[R] N) = rankLocallyConstant R M * rankLocallyConstant R N := by
  ext p
  exact congrFun (rankAtStalk_tensorProduct (R := R) (M := M) N) p

/-- Scalar extension to any commutative algebra pulls the locally constant rank
back along the induced continuous map on prime spectra. -/
@[simp]
theorem rankLocallyConstant_baseChange
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (S : Type uS) [CommRing S] [Algebra R S] :
    rankLocallyConstant S (S ⊗[R] M) =
      LocallyConstant.comapRingHom
        ⟨PrimeSpectrum.comap (algebraMap R S),
          PrimeSpectrum.continuous_comap (algebraMap R S)⟩
        (rankLocallyConstant R M) := by
  ext p
  exact rankAtStalk_baseChange (R := R) (M := M) (S := S) p

end Module
