/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine.Scalar
public import ProjectiveModules.LinearAlgebra.TensorProduct.Determinant
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.LocalRing.Module

/-!
# Determinants of tensor-product endomorphisms

The determinant of the tensor product of two endomorphisms of finite projective
modules is the product of the rank-dependent powers of their determinants.
Consequently, tensor products correspond to composition of the multiplicative
scalar powers `Module.rankPower`.

The determinant identity is checked in the full localizations at maximal ideals.
There the two scalar-extended factors are finite free, and the calculation is the
Kronecker determinant formula. In particular, neither constant rank nor
invertibility of the endomorphisms is required.

## References

* C. Weibel, *The K-book: An introduction to algebraic K-theory*, I.3.4.
* The Stacks Project, Tag 00NZ: finite flat modules over local rings are free.
* Mathlib's tensor-product base-change comparison and Kronecker determinant formula.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Module

/-- The determinant of a tensor product of arbitrary endomorphisms of finite
projective modules is the product of their determinants raised to the
rank-dependent powers of the other factors, as in Weibel, *The K-book*, I.3.4.
Rank-dependent powers allow the ranks of the factors to vary. -/
theorem determinant_tensorProduct_map
    (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q]
    (f : Module.End R P) (g : Module.End R Q) :
    determinant R (P ⊗[R] Q) (TensorProduct.map f g) =
      rankPower R Q (determinant R P f) * rankPower R P (determinant R Q g) := by
  classical
  apply Module.eq_of_localization_maximal
    (fun (m : Ideal R) (_ : m.IsMaximal) => Localization.AtPrime m)
    (fun m _ => Algebra.linearMap R (Localization.AtPrime m))
  intro m hm
  let S := Localization.AtPrime m
  let : Module.Free S (S ⊗[R] P) := Module.free_of_flat_of_isLocalRing
  let : Module.Free S (S ⊗[R] Q) := Module.free_of_flat_of_isLocalRing
  change algebraMap R S (determinant R (P ⊗[R] Q) (TensorProduct.map f g)) =
    algebraMap R S
      (rankPower R Q (determinant R P f) * rankPower R P (determinant R Q g))
  have hdet :
      determinant S (S ⊗[R] (P ⊗[R] Q)) ((TensorProduct.map f g).baseChange S) =
        determinant S ((S ⊗[R] P) ⊗[S] (S ⊗[R] Q))
          (TensorProduct.map (f.baseChange S) (g.baseChange S)) := by
    apply determinant_eq_of_intertwining
      (e := TensorProduct.AlgebraTensorModule.distribBaseChange R S P Q)
    ext p q
    simp
  calc
    algebraMap R S (determinant R (P ⊗[R] Q) (TensorProduct.map f g)) =
        determinant S (S ⊗[R] (P ⊗[R] Q))
          ((TensorProduct.map f g).baseChange S) := by
      rw [determinant_baseChange]
    _ = determinant S ((S ⊗[R] P) ⊗[S] (S ⊗[R] Q))
        (TensorProduct.map (f.baseChange S) (g.baseChange S)) := hdet
    _ = (determinant S (S ⊗[R] P) (f.baseChange S)) ^ Module.finrank S (S ⊗[R] Q) *
        (determinant S (S ⊗[R] Q) (g.baseChange S)) ^ Module.finrank S (S ⊗[R] P) := by
      simpa only [determinant_eq_det] using
        (LinearMap.det_tensorProduct_map (R := S) (P := S ⊗[R] P) (Q := S ⊗[R] Q)
          (f.baseChange S) (g.baseChange S))
    _ = rankPower S (S ⊗[R] Q) (determinant S (S ⊗[R] P) (f.baseChange S)) *
        rankPower S (S ⊗[R] P) (determinant S (S ⊗[R] Q) (g.baseChange S)) := by
      simp only [← determinant_smul_id, determinant_eq_det, LinearMap.det_smul,
        LinearMap.det_id, mul_one]
    _ = algebraMap R S
        (rankPower R Q (determinant R P f) * rankPower R P (determinant R Q g)) := by
      rw [determinant_baseChange, determinant_baseChange,
        rankPower_baseChange, rankPower_baseChange, map_mul]

/-- The multiplicative scalar power of a tensor product of finite projective
modules is the composition of the scalar powers of its two factors. -/
theorem rankPower_tensorProduct
    (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q] :
    rankPower R (P ⊗[R] Q) = (rankPower R P).comp (rankPower R Q) := by
  ext r
  have hmap :
      TensorProduct.map (1 : Module.End R P) (r • (LinearMap.id : Module.End R Q)) =
        r • (LinearMap.id : Module.End R (P ⊗[R] Q)) := by
    ext p q
    simp [TensorProduct.tmul_smul]
  simpa only [MonoidHom.comp_apply, hmap, determinant_smul_id, map_one, one_mul] using
    (determinant_tensorProduct_map R P Q (1 : Module.End R P)
      (r • (LinearMap.id : Module.End R Q)))

end Module
