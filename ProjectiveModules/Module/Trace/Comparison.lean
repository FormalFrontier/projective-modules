/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Trace.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# Comparison with the trace of a finite free module

For a finite free module over a commutative semiring, the finite-basis trace
agrees with contraction after the canonical dual tensor–Hom map. Consequently,
`LinearMap.traceOfFiniteProjective` agrees with `LinearMap.trace` on finite free
modules.

The comparison requires freeness: the finite-basis trace is defined to be zero
when no finite basis exists, whereas the finite-projective trace is defined by
contraction without requiring a basis.

## References

The finite-basis trace and matrix interface are from the formalization by
Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen and Antoine Labelle in
`Mathlib.LinearAlgebra.Trace`. The contraction and tensor–Hom API are from
Oliver Nash and Antoine Labelle in `Mathlib.LinearAlgebra.Contraction`.

-/

@[expose] public section

universe uR uM

open scoped TensorProduct

namespace LinearMap

variable (R : Type uR) [CommSemiring R]
variable (M : Type uM) [AddCommMonoid M] [Module R M]
variable [Module.Finite R M] [Module.Free R M]

/-- On a finite free module over a commutative semiring, applying the finite-basis
trace after the canonical dual tensor–Hom map is contraction. -/
@[simp] theorem trace_dualTensorHom (t : Module.Dual R M ⊗[R] M) :
    trace R M (dualTensorHom R M M t) = contractLeft R M t := by
  classical
  have h : (trace R M).comp (dualTensorHom R M M) = contractLeft R M := by
    apply TensorProduct.ext'
    intro φ x
    change trace R M (φ.smulRight x) = φ x
    let b := Module.Free.chooseBasis R M
    calc
      trace R M (φ.smulRight x) = ∑ i, b.repr x i * φ (b i) := by
        rw [trace_eq_matrix_trace R b, toMatrix_smulRight]
        rfl
      _ = φ (∑ i, b.repr x i • b i) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = φ x := by rw [b.sum_repr]
  exact congrArg (fun F : Module.Dual R M ⊗[R] M →ₗ[R] R => F t) h

/-- The finite-projective trace agrees with the finite-basis trace on finite free
modules over a commutative semiring. -/
theorem traceOfFiniteProjective_eq_trace :
    traceOfFiniteProjective R M = trace R M := by
  apply LinearMap.ext
  intro f
  rw [traceOfFiniteProjective_apply]
  calc
    contractLeft R M ((dualTensorHomEquiv R M M).symm f) =
        trace R M (dualTensorHom R M M ((dualTensorHomEquiv R M M).symm f)) :=
      (trace_dualTensorHom R M _).symm
    _ = trace R M f := by rw [dualTensorHom_dualTensorHomEquiv_symm]

end LinearMap
