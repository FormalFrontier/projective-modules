/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

The proof of `LinearMap.toMatrix₂_compl₁₂_algebra` adapts the scalar-valued
`LinearMap.toMatrix₂_compl₁₂` proof in Mathlib's
`Mathlib/LinearAlgebra/Matrix/SesquilinearForm.lean`. Original notice:

Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Moritz Doll

The algebra-valued extension and coefficient-centrality changes are by
Formal Frontier Agents.
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Matrices of algebra-valued bilinear maps

For an `R`-bilinear map valued in an `R`-algebra `S`, composition with linear maps
changes the pairing matrix by multiplication with their coefficient matrices mapped
through `algebraMap R S`. The algebra `S` need not be commutative: the images of the
coefficients from `R` commute with every entry of the pairing matrix.

## References

This extends Mathlib's scalar-valued `LinearMap.toMatrix₂_compl₁₂`, using
`LinearMap.sum_repr_mul_repr_mul` for the basis-coefficient expansion.
-/

@[expose] public section

open Finset Module
open scoped Matrix

universe uR uS uM₁ uM₂ uM₁' uM₂' un um un' um'

namespace LinearMap

variable {R : Type uR} {S : Type uS}
variable {M₁ : Type uM₁} {M₂ : Type uM₂} {M₁' : Type uM₁'} {M₂' : Type uM₂'}
variable {n : Type un} {m : Type um} {n' : Type un'} {m' : Type um'}
variable [CommSemiring R]
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
variable [AddCommMonoid M₁'] [Module R M₁'] [AddCommMonoid M₂'] [Module R M₂']
variable [Fintype n] [Fintype m] [Fintype n'] [Fintype m']
variable [DecidableEq n] [DecidableEq m] [DecidableEq n'] [DecidableEq m']
variable (b₁ : Basis n R M₁) (b₂ : Basis m R M₂)
variable (b₁' : Basis n' R M₁') (b₂' : Basis m' R M₂')

/-- Composition of an algebra-valued bilinear map with two linear maps transforms
its matrix by their coefficient matrices, mapped into the target algebra. -/
theorem toMatrix₂_compl₁₂_algebra [Semiring S] [Algebra R S]
    (B : M₁ →ₗ[R] M₂ →ₗ[R] S) (l : M₁' →ₗ[R] M₁) (r : M₂' →ₗ[R] M₂) :
    toMatrix₂ b₁' b₂' (B.compl₁₂ l r) =
      ((toMatrix b₁' b₁ l).map (algebraMap R S))ᵀ * toMatrix₂ b₁ b₂ B *
        (toMatrix b₂' b₂ r).map (algebraMap R S) := by
  ext i j
  simp only [toMatrix₂_apply, compl₁₂_apply, Matrix.transpose_apply, Matrix.mul_apply,
    Matrix.map_apply, toMatrix_apply, sum_mul]
  rw [sum_comm]
  conv_lhs => rw [← sum_repr_mul_repr_mul b₁ b₂]
  rw [Finsupp.sum_fintype]
  · apply sum_congr rfl
    rintro i' -
    rw [Finsupp.sum_fintype]
    · apply sum_congr rfl
      rintro j' -
      simp only [Algebra.smul_def, ← mul_assoc]
      exact Algebra.right_comm _ _ _
    · intros
      simp only [zero_smul, smul_zero]
  · intros
    simp

/-- For the identity algebra, the algebra-valued composition formula gives the
scalar-valued matrix composition formula. -/
private theorem toMatrix₂_compl₁₂_algebra_self (B : M₁ →ₗ[R] M₂ →ₗ[R] R)
    (l : M₁' →ₗ[R] M₁) (r : M₂' →ₗ[R] M₂) :
    toMatrix₂ b₁' b₂' (B.compl₁₂ l r) =
      (toMatrix b₁' b₁ l)ᵀ * toMatrix₂ b₁ b₂ B * toMatrix b₂' b₂ r := by
  simpa only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] using
    (toMatrix₂_compl₁₂_algebra (S := R) b₁ b₂ b₁' b₂' B l r)

end LinearMap
