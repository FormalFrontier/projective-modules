/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Contraction

/-!
# Trace of a finite projective module endomorphism

The inverse of the canonical dual tensor–Hom equivalence, followed by contraction,
gives a linear trace on endomorphisms of finite projective modules over a
commutative semiring. The construction does not require a basis.

Unlike `LinearMap.trace`, the contraction trace need not be zero on a nonfree
projective module. Its agreement with the finite-basis trace is established only
in the finite free case.

## References

This construction and its characteristic formulas use the dual tensor–Hom and
contraction formalization by Oliver Nash and Antoine Labelle in
`Mathlib.LinearAlgebra.Contraction`.

-/

@[expose] public section

universe uR uM

open scoped TensorProduct

namespace LinearMap

variable (R : Type uR) [CommSemiring R]
variable (M : Type uM) [AddCommMonoid M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]

/-- The linear trace of a finite projective module endomorphism, obtained by
contracting its inverse image under the canonical dual tensor–Hom equivalence. -/
noncomputable def traceOfFiniteProjective : (M →ₗ[R] M) →ₗ[R] R :=
  (contractLeft R M).comp (dualTensorHomEquiv R M M).symm.toLinearMap

/-- The contraction formula for the finite-projective trace. -/
theorem traceOfFiniteProjective_apply (f : M →ₗ[R] M) :
    traceOfFiniteProjective R M f =
      contractLeft R M ((dualTensorHomEquiv R M M).symm f) :=
  rfl

/-- Applying the trace after the dual tensor–Hom map is contraction. -/
@[simp] theorem traceOfFiniteProjective_dualTensorHom
    (t : Module.Dual R M ⊗[R] M) :
    traceOfFiniteProjective R M (dualTensorHom R M M t) = contractLeft R M t := by
  rw [traceOfFiniteProjective_apply, dualTensorHomEquiv_symm_dualTensorHom]

/-- The trace of the rank-one endomorphism `m ↦ φ m • x` is `φ x`. -/
@[simp] theorem traceOfFiniteProjective_smulRight (φ : Module.Dual R M) (x : M) :
    traceOfFiniteProjective R M (φ.smulRight x) = φ x := by
  have h : dualTensorHom R M M (φ ⊗ₜ[R] x) = φ.smulRight x :=
    LinearMap.ext fun y => dualTensorHom_apply φ y x
  rw [← h, traceOfFiniteProjective_dualTensorHom, contractLeft_apply]

end LinearMap
