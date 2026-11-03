/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Reduction

/-!
# Reduction of the regular module

The reduction of the left regular module of a ring is canonically linearly equivalent,
over the quotient ring, to that quotient ring. Under this equivalence, reduction of a
scalar-to-vector map is the quotient scalar action.

The construction uses the universal property `Module.reductionLift` and Mathlib's
noncommutative scalar-to-vector map `LinearMap.smulRight`.
-/

@[expose] public section

universe u v

namespace Module

variable {R : Type u} [Ring R] (I : Ideal R) [I.IsTwoSided]

/-- The quotient-ring-linear identification of the reduction of the left regular module
with the quotient ring. It sends the reduction class of `r` to its quotient-ring class;
its inverse sends `a` to `a • reductionMk I R 1`. -/
def reductionSelfEquiv : Reduction I R ≃ₗ[R ⧸ I] (R ⧸ I) :=
  let h : ∀ r s : R, Ideal.Quotient.mk I (r • s) =
      Ideal.Quotient.mk I r • Ideal.Quotient.mk I s := by
    intro r s
    change Ideal.Quotient.mk I (r * s) =
      Ideal.Quotient.mk I r * Ideal.Quotient.mk I s
    exact map_mul (Ideal.Quotient.mk I) r s
  let f : Reduction I R →ₗ[R ⧸ I] (R ⧸ I) :=
    reductionLift I (Ideal.Quotient.mk I).toAddMonoidHom h
  let g : (R ⧸ I) →ₗ[R ⧸ I] Reduction I R :=
    (LinearMap.id : (R ⧸ I) →ₗ[R ⧸ I] (R ⧸ I)).smulRight (reductionMk I R 1)
  LinearEquiv.ofLinearMap f g
    (by
      apply LinearMap.ext
      intro a
      change f (a • reductionMk I R 1) = a
      rw [map_smul]
      have hf : f (reductionMk I R 1) = Ideal.Quotient.mk I 1 :=
        reductionLift_mk I (Ideal.Quotient.mk I).toAddMonoidHom h 1
      rw [hf, map_one, smul_eq_mul, mul_one])
    (by
      apply reduction_hom_ext I
      intro r
      change g (f (reductionMk I R r)) = reductionMk I R r
      have hf : f (reductionMk I R r) = Ideal.Quotient.mk I r :=
        reductionLift_mk I (Ideal.Quotient.mk I).toAddMonoidHom h r
      rw [hf]
      change Ideal.Quotient.mk I r • reductionMk I R 1 = reductionMk I R r
      simpa only [smul_eq_mul, mul_one] using (reductionMk_smul I r (1 : R)).symm)

/-- The regular reduction equivalence sends a representative to its quotient-ring class. -/
@[simp] theorem reductionSelfEquiv_mk (r : R) :
    reductionSelfEquiv I (reductionMk I R r) = Ideal.Quotient.mk I r := by
  rfl

/-- The inverse regular reduction equivalence is scalar multiplication on the class of `1`. -/
@[simp] theorem reductionSelfEquiv_symm_apply (a : R ⧸ I) :
    (reductionSelfEquiv I).symm a = a • reductionMk I R 1 := by
  rfl

/-- The inverse regular reduction equivalence sends a quotient-ring representative
back to its reduction class. -/
theorem reductionSelfEquiv_symm_mk (r : R) :
    (reductionSelfEquiv I).symm (Ideal.Quotient.mk I r) = reductionMk I R r := by
  rw [reductionSelfEquiv_symm_apply, ← reductionMk_smul]
  simp only [smul_eq_mul, mul_one]

/-- Reduction of the original scalar-to-vector map, transported along the regular
reduction equivalence, is the quotient scalar action on the reduced vector. -/
theorem reductionMap_smulRight_reductionSelfEquiv_symm {M : Type v}
    [AddCommGroup M] [Module R M] (m : M) (a : R ⧸ I) :
    reductionMap I ((LinearMap.id : R →ₗ[R] R).smulRight m)
      ((reductionSelfEquiv I).symm a) = a • reductionMk I M m := by
  rw [reductionSelfEquiv_symm_apply, map_smul, reductionMap_mk,
    LinearMap.smulRight_apply, LinearMap.id_apply, one_smul]

end Module
