/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine.Endomorphism.Product

/-!
# Schur determinants on finite projective modules

For a block endomorphism of `P × Q` whose upper-left block is a linear equivalence
`e`, the scalar determinant is the determinant of `e` times the determinant of
`d - c.comp (e.symm.toLinearMap.comp b)`. The modules may have varying stalk ranks
and need not be faithful, and neither the Schur complement nor the full block map
needs to be invertible.

The proof factors the block map as the composite of a lower unitriangular map
with an upper triangular map, and uses multiplicativity and the two triangular
determinant laws.
For finite bases, `Module.determinant_prod_coprod_eq_det_fromBlocks` gives the
coordinate comparison with the block matrix determinant, to which Mathlib's
`Matrix.det_fromBlocks₁₁` applies.

## References

The block-factorization approach follows the formalization of Schur determinants
in Mathlib's `Mathlib.LinearAlgebra.Matrix.SchurComplement`, by Alexander Bentkamp,
Eric Wieser, Jeremy Avigad and Johan Commelin. The determinant of a finite projective
module is the scalar of its action on the determinant line; for background, see
C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*.
-/

@[expose] public section

universe u v w

namespace Module

variable (R : Type u) [CommRing R]
variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
variable (Q : Type w) [AddCommGroup Q] [Module R Q]
  [Module.Finite R Q] [Module.Projective R Q]

/-- The Schur determinant formula for finite projective modules with an invertible
upper-left block, supplied as a linear equivalence. Neither the Schur complement
nor the full block endomorphism is required to be invertible.

This is the intrinsic finite-projective counterpart of `Matrix.det_fromBlocks₁₁`
in Mathlib's Schur-complement formalization. -/
theorem determinant_prod_coprod_of_linearEquiv
    (e : P ≃ₗ[R] P) (b : Q →ₗ[R] P) (c : P →ₗ[R] Q) (d : Module.End R Q) :
    Module.determinant R (P × Q)
        ((LinearMap.coprod e.toLinearMap b).prod (LinearMap.coprod c d)) =
      Module.determinant R P e.toLinearMap *
        Module.determinant R Q (d - c.comp (e.symm.toLinearMap.comp b)) := by
  have hfactor :
      (e.toLinearMap.coprod b).prod (c.coprod d) =
        (((LinearMap.id : Module.End R P).coprod (0 : Q →ₗ[R] P)).prod
          ((c.comp e.symm.toLinearMap).coprod (LinearMap.id : Module.End R Q))).comp
            ((e.toLinearMap.coprod b).prod
              ((0 : P →ₗ[R] Q).coprod (d - c.comp (e.symm.toLinearMap.comp b)))) := by
    apply LinearMap.ext
    intro z
    apply Prod.ext <;>
      simp [LinearMap.comp_apply, LinearMap.prod_apply, LinearMap.coprod_apply,
        LinearMap.sub_apply, map_add, add_assoc, add_comm]
  rw [hfactor, Module.determinant_comp,
    Module.determinant_prod_coprod_zero₁₂, Module.determinant_prod_coprod_zero₂₁]
  simp only [Module.determinant_id, one_mul]

end Module
