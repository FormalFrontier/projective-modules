/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine.Stabilization
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Finiteness.Projective

/-!
# Determinants of product and block triangular endomorphisms

The scalar determinant of a product endomorphism is the product of the scalar
determinants, even when the finite projective factors have varying stalk ranks.
The same formula holds for upper and lower triangular endomorphisms with arbitrary
off-diagonal maps. The coefficient ring may be trivial, and the diagonal
endomorphisms may be noninvertible.

The proofs use Mathlib's finite-free split presentations and the scalar comparison
with their stabilizations, which act by the identity on the complementary summands.
The free ambient calculations use `LinearMap.det_prodMap` in the diagonal case
and `Matrix.det_fromBlocks_zero₂₁` in the upper triangular case. The lower
triangular formula follows by interchanging the factors.

`LinearMap.toMatrix_prod_coprod` describes a four-block map in independently chosen
source and target product bases over a commutative semiring. With the same product
basis on both sides, `Module.determinant_prod_coprod_eq_det_fromBlocks` identifies
the scalar determinant with the block matrix determinant. In particular, Mathlib's
`Matrix.det_fromBlocks₁₁` applies to this matrix when its upper-left block is invertible.

## References

For determinants of finite projective modules, see C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*.
-/

@[expose] public section

noncomputable section

universe u v w x y

/-- The matrix of a four-block linear map in product bases is the matrix formed
from the four component matrices. The source and target bases are independent. -/
theorem LinearMap.toMatrix_prod_coprod
    {R : Type u} [CommSemiring R]
    {M₁ : Type v} [AddCommMonoid M₁] [Module R M₁]
    {M₂ : Type w} [AddCommMonoid M₂] [Module R M₂]
    {N₁ : Type x} [AddCommMonoid N₁] [Module R N₁]
    {N₂ : Type y} [AddCommMonoid N₂] [Module R N₂]
    {ι₁ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    {ι₂ : Type*} [Fintype ι₂] [DecidableEq ι₂]
    {κ₁ : Type*} [Finite κ₁] {κ₂ : Type*} [Finite κ₂]
    (e₁ : Module.Basis ι₁ R M₁) (e₂ : Module.Basis ι₂ R M₂)
    (f₁ : Module.Basis κ₁ R N₁) (f₂ : Module.Basis κ₂ R N₂)
    (a : M₁ →ₗ[R] N₁) (b : M₂ →ₗ[R] N₁)
    (c : M₁ →ₗ[R] N₂) (d : M₂ →ₗ[R] N₂) :
    LinearMap.toMatrix (e₁.prod e₂) (f₁.prod f₂) ((a.coprod b).prod (c.coprod d)) =
      Matrix.fromBlocks (LinearMap.toMatrix e₁ f₁ a) (LinearMap.toMatrix e₂ f₁ b)
        (LinearMap.toMatrix e₁ f₂ c) (LinearMap.toMatrix e₂ f₂ d) := by
  ext (i | i) (j | j) <;>
    simp [LinearMap.toMatrix_apply, LinearMap.prod_apply, LinearMap.coprod_apply,
      Module.Basis.prod_apply]

namespace Module

variable (R : Type u) [CommRing R]
variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
variable (Q : Type w) [AddCommGroup Q] [Module R Q]
  [Module.Finite R Q] [Module.Projective R Q]

/-- Scalar determinants of arbitrary finite projective endomorphisms multiply
under direct products, with no constant-rank or freeness hypothesis on the factors. -/
theorem determinant_prodMap
    (f : Module.End R P) (g : Module.End R Q) :
    Module.determinant R (P × Q) (f.prodMap g) =
      Module.determinant R P f * Module.determinant R Q g := by
  obtain ⟨n, pP, jP, _, _, hpP⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R P
  obtain ⟨m, pQ, jQ, _, _, hpQ⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R Q
  have hpjProd : (pP.prodMap pQ).comp (jP.prodMap jQ) =
      (LinearMap.id : Module.End R (P × Q)) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · simpa only [LinearMap.comp_apply, LinearMap.prodMap_apply,
        LinearMap.id_apply] using DFunLike.congr_fun hpP x.1
    · simpa only [LinearMap.comp_apply, LinearMap.prodMap_apply,
        LinearMap.id_apply] using DFunLike.congr_fun hpQ x.2
  have hblock :
      (jP.prodMap jQ).comp ((f.prodMap g).comp (pP.prodMap pQ)) +
        (LinearMap.id - (jP.prodMap jQ).comp (pP.prodMap pQ)) =
      (jP.comp (f.comp pP) + (LinearMap.id - jP.comp pP)).prodMap
        (jQ.comp (g.comp pQ) + (LinearMap.id - jQ.comp pQ)) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;>
      simp [LinearMap.prodMap_apply, LinearMap.comp_apply,
        LinearMap.id_apply, LinearMap.add_apply, LinearMap.sub_apply]
  have hPQ := Module.determinant_eq_det_stabilization R (P × Q)
    ((Fin n → R) × (Fin m → R)) (f.prodMap g)
    (pP.prodMap pQ) (jP.prodMap jQ) hpjProd
  have hP := Module.determinant_eq_det_stabilization R P (Fin n → R)
    f pP jP hpP
  have hQ := Module.determinant_eq_det_stabilization R Q (Fin m → R)
    g pQ jQ hpQ
  rw [hPQ, hblock, LinearMap.det_prodMap, ← hP, ← hQ]

/-- In finite bases, the scalar determinant of a four-block endomorphism is the
determinant of its block matrix. The same product basis is used for source and target. -/
theorem determinant_prod_coprod_eq_det_fromBlocks
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : Basis ι R P) (q : Basis κ R Q)
    (a : Module.End R P) (b : Q →ₗ[R] P)
    (c : P →ₗ[R] Q) (d : Module.End R Q) :
    Module.determinant R (P × Q) ((a.coprod b).prod (c.coprod d)) =
      Matrix.det (Matrix.fromBlocks (LinearMap.toMatrix p p a) (LinearMap.toMatrix q p b)
        (LinearMap.toMatrix p q c) (LinearMap.toMatrix q q d)) := by
  let : Module.Free R P := Module.Free.of_basis p
  let : Module.Free R Q := Module.Free.of_basis q
  rw [Module.determinant_eq_det, ← LinearMap.det_toMatrix (p.prod q),
    LinearMap.toMatrix_prod_coprod]

/-- The determinant of an upper triangular product endomorphism is the product
of the determinants of its diagonal endomorphisms. -/
theorem determinant_prod_coprod_zero₂₁
    (a : Module.End R P) (b : Q →ₗ[R] P) (d : Module.End R Q) :
    Module.determinant R (P × Q)
        ((LinearMap.coprod a b).prod
          (LinearMap.coprod (0 : P →ₗ[R] Q) d)) =
      Module.determinant R P a * Module.determinant R Q d := by
  classical
  obtain ⟨n, pP, jP, _, _, hpP⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R P
  obtain ⟨m, pQ, jQ, _, _, hpQ⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R Q
  have hpjProd : (pP.prodMap pQ).comp (jP.prodMap jQ) =
      (LinearMap.id : Module.End R (P × Q)) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · simpa only [LinearMap.comp_apply, LinearMap.prodMap_apply,
        LinearMap.id_apply] using DFunLike.congr_fun hpP x.1
    · simpa only [LinearMap.comp_apply, LinearMap.prodMap_apply,
        LinearMap.id_apply] using DFunLike.congr_fun hpQ x.2
  let A : Module.End R (Fin n → R) :=
    jP.comp (a.comp pP) + (LinearMap.id - jP.comp pP)
  let B : (Fin m → R) →ₗ[R] (Fin n → R) := jP.comp (b.comp pQ)
  let D : Module.End R (Fin m → R) :=
    jQ.comp (d.comp pQ) + (LinearMap.id - jQ.comp pQ)
  have hblock :
      (jP.prodMap jQ).comp
          (((a.coprod b).prod ((0 : P →ₗ[R] Q).coprod d)).comp
            (pP.prodMap pQ)) +
        (LinearMap.id - (jP.prodMap jQ).comp (pP.prodMap pQ)) =
      (A.coprod B).prod
        ((0 : (Fin n → R) →ₗ[R] (Fin m → R)).coprod D) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;>
      simp [A, B, D, LinearMap.prodMap_apply, LinearMap.comp_apply,
        LinearMap.prod_apply, LinearMap.coprod_apply, LinearMap.id_apply,
        LinearMap.add_apply, LinearMap.sub_apply, add_assoc, add_left_comm, add_comm]
  have hPQ := Module.determinant_eq_det_stabilization R (P × Q)
    ((Fin n → R) × (Fin m → R))
    ((a.coprod b).prod ((0 : P →ₗ[R] Q).coprod d))
    (pP.prodMap pQ) (jP.prodMap jQ) hpjProd
  have hP : Module.determinant R P a = LinearMap.det A :=
    Module.determinant_eq_det_stabilization R P (Fin n → R) a pP jP hpP
  have hQ : Module.determinant R Q d = LinearMap.det D :=
    Module.determinant_eq_det_stabilization R Q (Fin m → R) d pQ jQ hpQ
  rw [hPQ, hblock,
    ← LinearMap.det_toMatrix ((Pi.basisFun R (Fin n)).prod (Pi.basisFun R (Fin m))),
    LinearMap.toMatrix_prod_coprod, map_zero, Matrix.det_fromBlocks_zero₂₁,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix, ← hP, ← hQ]

/-- The determinant of a lower triangular product endomorphism is the product
of the determinants of its diagonal endomorphisms. -/
theorem determinant_prod_coprod_zero₁₂
    (a : Module.End R P) (c : P →ₗ[R] Q) (d : Module.End R Q) :
    Module.determinant R (P × Q)
        ((LinearMap.coprod a (0 : Q →ₗ[R] P)).prod
          (LinearMap.coprod c d)) =
      Module.determinant R P a * Module.determinant R Q d := by
  have hswap :
      (LinearEquiv.prodComm R P Q).toLinearMap.comp
          ((a.coprod (0 : Q →ₗ[R] P)).prod (c.coprod d)) =
        ((d.coprod c).prod ((0 : Q →ₗ[R] P).coprod a)).comp
          (LinearEquiv.prodComm R P Q).toLinearMap := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;>
      simp [LinearMap.comp_apply, LinearMap.prod_apply, LinearMap.coprod_apply,
        LinearEquiv.prodComm_apply, add_comm]
  calc
    Module.determinant R (P × Q)
        ((a.coprod (0 : Q →ₗ[R] P)).prod (c.coprod d)) =
        Module.determinant R (Q × P)
          ((d.coprod c).prod ((0 : Q →ₗ[R] P).coprod a)) :=
      Module.determinant_eq_of_intertwining R (P × Q) (Q × P)
        (LinearEquiv.prodComm R P Q) _ _ hswap
    _ = Module.determinant R Q d * Module.determinant R P a :=
      determinant_prod_coprod_zero₂₁ R Q P d c a
    _ = Module.determinant R P a * Module.determinant R Q d := mul_comm _ _

end Module
