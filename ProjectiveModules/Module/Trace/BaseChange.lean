/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Trace.Comparison

import Mathlib.LinearAlgebra.Dual.BaseChange

/-!
# Finite-projective trace and scalar extension

The contraction trace of an endomorphism of a finite projective module commutes
with arbitrary scalar extension between commutative semirings. The scalar
semirings and the module carrier may inhabit independent universes. No freeness
of the module or flatness or finiteness of the scalar extension is required.

On finite free modules over commutative rings, comparison with the finite-basis
trace identifies this formula with `LinearMap.trace_baseChange`.

## References

The finite-free scalar-extension trace formula is from the Mathlib trace
formalization by Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen and
Antoine Labelle. The contraction trace and its comparison with the finite-basis
trace are from `ProjectiveModules.Module.Trace.Basic` and
`ProjectiveModules.Module.Trace.Comparison`. The dual tensor–Hom and contraction
interfaces are from Oliver Nash and Antoine Labelle's Mathlib formalization; the
dual scalar-extension interface is from Antoine Chambert-Loir's formalization in
`Mathlib.LinearAlgebra.Dual.BaseChange`.
-/

@[expose] public section

universe uR uA uM

open scoped TensorProduct

namespace LinearMap

/-- The finite-projective trace commutes with arbitrary scalar extension between
commutative semirings. This generalizes `LinearMap.trace_baseChange`, which
assumes finite freeness over commutative rings. -/
@[simp] theorem traceOfFiniteProjective_baseChange
    (R : Type uR) [CommSemiring R]
    (A : Type uA) [CommSemiring A] [Algebra R A]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (f : M →ₗ[R] M) :
    traceOfFiniteProjective A (A ⊗[R] M) (f.baseChange A) =
      algebraMap R A (traceOfFiniteProjective R M f) := by
  obtain ⟨t, rfl⟩ := (dualTensorHom_bijective (R := R) (M := M) (N := M)).2 f
  induction t using TensorProduct.inductionOn with
  | tmul φ x =>
      have h : (dualTensorHom R M M (φ ⊗ₜ[R] x)).baseChange A =
          (Module.Dual.baseChange A φ).smulRight (1 ⊗ₜ[R] x) := by
        apply TensorProduct.AlgebraTensorModule.ext
        intro a m
        simp only [baseChange_tmul, dualTensorHom_apply, smulRight_apply,
          Module.Dual.baseChange_apply_tmul, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h, traceOfFiniteProjective_smulRight,
        traceOfFiniteProjective_dualTensorHom, contractLeft_apply,
        Module.Dual.baseChange_apply_tmul, Algebra.algebraMap_eq_smul_one]
  | add t₁ t₂ h₁ h₂ =>
      simp only [map_add, baseChange_add, h₁, h₂]

/-- On finite free modules over commutative rings, the finite-projective
scalar-extension trace identity agrees with `LinearMap.trace_baseChange` after
comparison with the finite-basis trace. -/
theorem traceOfFiniteProjective_baseChange_iff_trace
    (R : Type uR) [CommRing R]
    (A : Type uA) [CommRing A] [Algebra R A]
    (M : Type uM) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) :
    (traceOfFiniteProjective A (A ⊗[R] M) (f.baseChange A) =
        algebraMap R A (traceOfFiniteProjective R M f)) ↔
      (trace A (A ⊗[R] M) (f.baseChange A) =
        algebraMap R A (trace R M f)) := by
  rw [traceOfFiniteProjective_eq_trace A (A ⊗[R] M),
    traceOfFiniteProjective_eq_trace R M]

end LinearMap
