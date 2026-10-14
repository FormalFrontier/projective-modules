/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Trace.Comparison
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Trace and tensor products

For finite projective modules over a commutative semiring, the trace of the tensor
product of two endomorphisms is the product of their traces. The bilinear form of
this identity uses `TensorProduct.mapBilinear`. The scalar and module carriers
may inhabit independent universes, and no chosen bases are required.

For finite free modules over a commutative ring, comparison with the finite-basis
trace identifies the pointwise identity with `LinearMap.trace_tensorProduct'`.

## References

The finite-free tensor-product trace identities are formalized by Johannes Hölzl,
Patrick Massot, Casper Putz, Anne Baanen and Antoine Labelle in
`Mathlib.LinearAlgebra.Trace`. The proof here follows the dual tensor–Hom
reduction in `LinearMap.trace_tensorProduct`, using the finite-projective
contraction trace. The dual tensor–Hom and contraction API are formalized by
Oliver Nash and Antoine Labelle in `Mathlib.LinearAlgebra.Contraction`.
-/

@[expose] public section

universe uR uM uN

open scoped TensorProduct

namespace LinearMap

/-- The finite-projective trace takes the tensor-product bilinear map on
endomorphisms to the product of the two traces. This generalizes
`LinearMap.trace_tensorProduct` from finite free modules over a commutative ring
to finite projective modules over a commutative semiring. -/
theorem traceOfFiniteProjective_tensorProduct
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    (N : Type uN) [AddCommMonoid N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] :
    compr₂ (TensorProduct.mapBilinear (.id R) M N M N)
        (traceOfFiniteProjective R (M ⊗[R] N)) =
      compl₁₂ (lsmul R R : R →ₗ[R] R →ₗ[R] R)
        (traceOfFiniteProjective R M) (traceOfFiniteProjective R N) := by
  apply
    (compl₁₂_inj
      (show Function.Surjective (dualTensorHom R M M) from
        (dualTensorHomEquiv R M M).surjective)
      (show Function.Surjective (dualTensorHom R N N) from
        (dualTensorHomEquiv R N N).surjective)).1
  apply TensorProduct.ext'
  intro φ x
  apply TensorProduct.ext'
  intro ψ y
  simp only [compl₁₂_apply, compr₂_apply, TensorProduct.mapBilinear_apply,
    map_dualTensorHom, traceOfFiniteProjective_dualTensorHom, contractLeft_apply,
    TensorProduct.dualDistrib_apply, lsmul_apply, smul_eq_mul]

/-- The trace of the tensor product of two finite-projective endomorphisms is the
product of their traces. This is the pointwise form of
`LinearMap.traceOfFiniteProjective_tensorProduct` and generalizes
`LinearMap.trace_tensorProduct'`. -/
theorem traceOfFiniteProjective_tensorProduct'
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    (N : Type uN) [AddCommMonoid N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    traceOfFiniteProjective R (M ⊗[R] N) (TensorProduct.map f g) =
      traceOfFiniteProjective R M f * traceOfFiniteProjective R N g := by
  have h := congr_fun₂ (traceOfFiniteProjective_tensorProduct R M N) f g
  simpa only [compr₂_apply, TensorProduct.mapBilinear_apply, compl₁₂_apply,
    lsmul_apply, smul_eq_mul] using h

/-- On finite free modules over a commutative ring, the finite-projective
pointwise tensor-product trace identity is equivalent to the finite-basis
identity `LinearMap.trace_tensorProduct'`. -/
theorem traceOfFiniteProjective_tensorProduct_iff_trace
    (R : Type uR) [CommRing R]
    (M : Type uM) [AddCommGroup M] [Module R M]
    (N : Type uN) [AddCommGroup N] [Module R N]
    [Module.Free R M] [Module.Finite R M]
    [Module.Free R N] [Module.Finite R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    (traceOfFiniteProjective R (M ⊗[R] N) (TensorProduct.map f g) =
        traceOfFiniteProjective R M f * traceOfFiniteProjective R N g) ↔
      (trace R (M ⊗[R] N) (TensorProduct.map f g) =
        trace R M f * trace R N g) := by
  rw [traceOfFiniteProjective_eq_trace R M, traceOfFiniteProjective_eq_trace R N,
    traceOfFiniteProjective_eq_trace R (M ⊗[R] N)]

end LinearMap
