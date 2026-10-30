/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Tactic.Abel

/-!
# Calculus of left contraction

Left contraction by a covector is the existing `CliffordAlgebra.contractLeft`. This file
characterizes it by its value on one and its recursion on left multiplication by a vector,
and proves its twisted product rule, compatibility with the grade involution, and naturality.
The product rule uses the grade involution `CliffordAlgebra.involute`, so it applies to
inhomogeneous elements as well as homogeneous ones.

The linear-endomorphism form of the contraction–creation identity is also provided. A vector
whose pairing with the covector is one gives an identity endomorphism as the sum of the two
composites; no hypothesis about such a vector is implicit.

## References

Mathlib's `CliffordAlgebra.Contraction`, `CliffordAlgebra.Fold`, and
`CliffordAlgebra.Conjugation` provide the underlying formalization of contraction, left
induction, and grade involution, respectively, by Eric Wieser. We use those constructions
without changing the algebra or its module structure. The exterior-algebra statements are
specializations to the zero quadratic form, using the defining abbreviation of
`ExteriorAlgebra`, not an equivalence requiring two to be invertible. In particular, exterior
naturality holds for every linear map.
-/

@[expose] public section

universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace CliffordAlgebra

variable {Q : QuadraticForm R M}

/-- Left contraction is the unique linear endomorphism that vanishes on one and satisfies
its recursion on left multiplication by a vector. This characterization holds for every
quadratic form. -/
theorem contractLeft_unique (d : Module.Dual R M)
    (D : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) (h_one : D 1 = 0)
    (h_ι_mul : ∀ (m : M) (x : CliffordAlgebra Q),
      D (ι Q m * x) = d m • x - ι Q m * D x) :
    D = contractLeft (Q := Q) d := by
  apply LinearMap.ext
  intro x
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [Algebra.algebraMap_eq_smul_one, map_smul, h_one,
        contractLeft_one, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | ι_mul x m hx => rw [h_ι_mul, contractLeft_ι_mul, hx]

/-- The twisted Leibniz rule for left contraction. The twist is the grade involution on the
whole left factor, so neither factor needs to be homogeneous. -/
theorem contractLeft_mul (d : Module.Dual R M) (x y : CliffordAlgebra Q) :
    contractLeft d (x * y) =
      contractLeft d x * y + involute x * contractLeft d y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      rw [contractLeft_algebraMap_mul, contractLeft_algebraMap, zero_mul, zero_add,
        AlgHom.commutes]
  | add x z hx hz =>
      rw [add_mul, map_add, map_add, map_add, add_mul, add_mul, hx, hz]
      abel
  | ι_mul x m hx =>
      rw [mul_assoc, contractLeft_ι_mul, hx, contractLeft_ι_mul, map_mul, involute_ι]
      simp only [mul_add, sub_mul, smul_mul_assoc, mul_assoc, neg_mul]
      abel

/-- Left contraction anticommutes with the grade involution. -/
@[simp]
theorem contractLeft_involute (d : Module.Dual R M) (x : CliffordAlgebra Q) :
    contractLeft d (involute x) = -involute (contractLeft d x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [AlgHom.commutes, contractLeft_algebraMap, map_zero, neg_zero]
  | add x y hx hy =>
      simp only [map_add, hx, hy, neg_add]
  | ι_mul x m hx =>
      simp only [map_mul, involute_ι, neg_mul, map_neg, contractLeft_ι_mul,
        map_sub, map_smul, hx, mul_neg]

variable {N : Type w} [AddCommGroup N] [Module R N]
variable {Q' : QuadraticForm R N}

/-- Contraction is natural under a linear map preserving the two quadratic forms, with the
covector pulled back along that map. No injectivity or surjectivity is required. -/
theorem map_contractLeft (f : Q →qᵢ Q') (d : Module.Dual R N) (x : CliffordAlgebra Q) :
    map f (contractLeft (d.comp f.toLinearMap) x) = contractLeft d (map f x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [contractLeft_algebraMap, map_zero, AlgHom.commutes]
  | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add, hx, hy]
  | ι_mul x m hx =>
      simp only [contractLeft_ι_mul, map_sub, map_smul, map_mul, map_apply_ι,
        LinearMap.comp_apply, QuadraticMap.Isometry.coe_toLinearMap, hx]

/-- The contraction–creation identity as an equation of linear endomorphisms. Creation is
ordinary left multiplication by the vector's image in the Clifford algebra. -/
theorem contractLeft_comp_mulLeft_add_mulLeft_comp (d : Module.Dual R M) (m : M) :
    (contractLeft (Q := Q) d).comp (LinearMap.mulLeft R (ι Q m)) +
        (LinearMap.mulLeft R (ι Q m)).comp (contractLeft (Q := Q) d) =
      d m • (LinearMap.id : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) := by
  apply LinearMap.ext
  intro x
  change contractLeft d (ι Q m * x) + ι Q m * contractLeft d x = d m • x
  rw [contractLeft_ι_mul, sub_add_cancel]

/-- If a covector and vector pair to one, contraction and creation have anticommutator equal
to the identity endomorphism. The unit-pairing hypothesis is essential. -/
theorem contractLeft_comp_mulLeft_add_mulLeft_comp_of_eq_one
    (d : Module.Dual R M) (m : M) (h : d m = 1) :
    (contractLeft (Q := Q) d).comp (LinearMap.mulLeft R (ι Q m)) +
        (LinearMap.mulLeft R (ι Q m)).comp (contractLeft (Q := Q) d) =
      (LinearMap.id : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) := by
  rw [contractLeft_comp_mulLeft_add_mulLeft_comp, h, one_smul]

end CliffordAlgebra

namespace ExteriorAlgebra

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Exterior contraction is natural for every ordinary linear map: pulling back the covector
and then contracting commutes with the induced exterior-algebra map. The zero quadratic forms
are automatically compatible, so no extra condition on the linear map is imposed. -/
theorem map_contractLeft (f : M →ₗ[R] N) (d : Module.Dual R N) (x : ExteriorAlgebra R M) :
    map f (CliffordAlgebra.contractLeft (d.comp f) x) =
      CliffordAlgebra.contractLeft d (map f x) :=
  CliffordAlgebra.map_contractLeft
    (Q := (0 : QuadraticForm R M)) (Q' := (0 : QuadraticForm R N))
    { f with map_app' := fun _ => rfl } d x

end ExteriorAlgebra
