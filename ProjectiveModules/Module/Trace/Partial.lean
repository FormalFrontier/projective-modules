/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Trace.Basic

/-!
# Partial trace over a finite projective tensor factor

The partial trace contracts the first tensor factor of an arbitrary linear map
`M ⊗[R] N →ₗ[R] M ⊗[R] P`, producing a linear map `N →ₗ[R] P`. The scalar
semiring is commutative, only the traced factor `M` is finite projective, and the
untraced factors `N` and `P` are arbitrary semimodules at independent universes.
The construction is itself linear in the entire input map, not only in maps
of pure tensor form.

Currying and flipping the input gives `n ↦ (m ↦ f (m ⊗ₜ[R] n))`. The inverse
of the canonical right tensor–Hom equivalence then gives an element of
`(M →ₗ[R] M) ⊗[R] P`; tensoring the existing finite-projective trace with the
identity of `P` and applying the left unitor gives the output in `P`.
This is the ordinary, unnormalized partial trace: the pure-tensor formula is
`partialTrace (TensorProduct.map a b) = traceOfFiniteProjective R M a • b`,
without division by a dimension or rank.

The characteristic formulas below express the contraction on arbitrary maps
and identify its value on pure tensor maps.

## References

The construction reuses the finite-projective trace in
`ProjectiveModules.Module.Trace.Basic` and the tensor–Hom equivalence and
contraction formalization by Oliver Nash and Antoine Labelle in
`Mathlib.LinearAlgebra.Contraction`. The tensor-product currying, symmetry,
and linear-map interfaces are from the Mathlib formalization by Kenny Lau
and Mario Carneiro.
-/

@[expose] public section

universe uR uM uN uP

open scoped TensorProduct

namespace LinearMap

variable (R : Type uR) [CommSemiring R]
variable (M : Type uM) [AddCommMonoid M] [Module R M]
variable (N : Type uN) [AddCommMonoid N] [Module R N]
variable (P : Type uP) [AddCommMonoid P] [Module R P]
variable [Module.Finite R M] [Module.Projective R M]

/-- The partial trace over the first, finite-projective tensor factor, bundled
as a linear map on all linear maps `M ⊗[R] N →ₗ[R] M ⊗[R] P`. -/
noncomputable def partialTraceOfFiniteProjective :
    (M ⊗[R] N →ₗ[R] M ⊗[R] P) →ₗ[R] (N →ₗ[R] P) :=
  let K : (M →ₗ[R] M ⊗[R] P) →ₗ[R] P :=
    (TensorProduct.lid R P).toLinearMap.comp
      (((traceOfFiniteProjective R M).rTensor P).comp
        (rTensorHomEquivHomRTensor R M M P).symm.toLinearMap)
  (LinearMap.llcomp R N (M →ₗ[R] M ⊗[R] P) P K).comp
    ((LinearMap.lflip (R₀ := R)).toLinearMap.comp
      (TensorProduct.lcurry (.id R) M N (M ⊗[R] P)))

/-- The inverse tensor–Hom contraction formula for the partial trace of every
input map at every argument. -/
theorem partialTraceOfFiniteProjective_apply
    (f : M ⊗[R] N →ₗ[R] M ⊗[R] P) (n : N) :
    partialTraceOfFiniteProjective R M N P f n =
      TensorProduct.lid R P
        ((traceOfFiniteProjective R M).rTensor P
          ((rTensorHomEquivHomRTensor R M M P).symm
            ((TensorProduct.curry f).flip n))) := by
  rfl

/-- Partial trace of a pure tensor is scalar trace on the first factor times
the arbitrary second-factor map. -/
theorem partialTraceOfFiniteProjective_tensorProduct
    (a : M →ₗ[R] M) (b : N →ₗ[R] P) :
    partialTraceOfFiniteProjective R M N P (TensorProduct.map a b) =
      traceOfFiniteProjective R M a • b := by
  ext n
  rw [partialTraceOfFiniteProjective_apply]
  have h : (rTensorHomEquivHomRTensor R M M P).symm
      ((TensorProduct.curry (TensorProduct.map a b)).flip n) = a ⊗ₜ[R] b n := by
    apply (rTensorHomEquivHomRTensor R M M P).symm_apply_eq.mpr
    ext m
    simp only [flip_apply, TensorProduct.curry_apply, TensorProduct.map_tmul,
      rTensorHomEquivHomRTensor_apply, TensorProduct.rTensorHomToHomRTensor_apply]
  rw [h, rTensor_tmul, TensorProduct.lid_tmul, smul_apply]

end LinearMap
