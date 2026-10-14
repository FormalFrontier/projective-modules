/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Trace.Basic

/-!
# Conjugation invariance of the finite-projective trace

The contraction trace is unchanged by transporting an endomorphism across a
linear equivalence of finite projective modules over a commutative semiring.
The proof reduces to rank-one endomorphisms through the canonical dual
tensor–Hom equivalence.

## References

The tensor description and evaluation formulas used here are from the
formalization by Oliver Nash and Antoine Labelle in
`Mathlib.LinearAlgebra.Contraction`.

-/

@[expose] public section

universe uR uM uN

open scoped TensorProduct

namespace LinearMap

/-- The trace of a finite-projective endomorphism is invariant under conjugation
by a linear equivalence. -/
theorem traceOfFiniteProjective_conj
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (N : Type uN) [AddCommMonoid N] [Module R N]
    [Module.Finite R N] [Module.Projective R N]
    (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) :
    traceOfFiniteProjective R N (e.conj f) = traceOfFiniteProjective R M f := by
  obtain ⟨t, rfl⟩ := (dualTensorHom_bijective (R := R) (M := M) (N := M)).2 f
  induction t using TensorProduct.inductionOn with
  | tmul φ x =>
      have h : e.conj (dualTensorHom R M M (φ ⊗ₜ[R] x)) =
          (φ.comp e.symm.toLinearMap).smulRight (e x) := by
        apply LinearMap.ext
        intro y
        change e (φ (e.symm y) • x) = φ (e.symm y) • e x
        exact e.map_smul _ _
      rw [h, traceOfFiniteProjective_smulRight,
        traceOfFiniteProjective_dualTensorHom, contractLeft_apply]
      change φ (e.symm (e x)) = φ x
      exact congrArg φ (e.symm_apply_apply x)
  | add t₁ t₂ h₁ h₂ =>
      simp only [map_add, h₁, h₂]

end LinearMap
