/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis
public import ProjectiveModules.Module.Trace.Basic

/-!
# Trace on an empty product of regular modules

The canonical module `Fin 0 → R` over a commutative semiring has the empty
standard basis. Every endomorphism is zero, so its finite-projective trace is
zero, as is the finite sum of its diagonal-block traces. The identity trace is
also zero. These are empty-product boundary cases: the module is subsingleton,
even when the scalar semiring is `ℕ`.

The class evidence uses Mathlib's standard basis and free-module API. The trace
calculation uses only linearity of the contraction trace; it does not use a
trace formula for products of modules.

## References

The standard basis and finite-sum API are from Mathlib. The trace is the
contraction of the inverse canonical dual tensor–Hom equivalence from
`ProjectiveModules.Module.Trace.Basic`.
-/

@[expose] public section

universe uR

namespace LinearMap

-- These instances supply only proof-class evidence for the existing Pi module.
private instance finZeroArrowFree (R : Type uR) [CommSemiring R] :
    Module.Free R (Fin 0 → R) :=
  Module.Free.of_basis (Pi.basisFun R (Fin 0))

private instance finZeroArrowFinite (R : Type uR) [CommSemiring R] :
    Module.Finite R (Fin 0 → R) :=
  Module.Finite.of_basis (Pi.basisFun R (Fin 0))

private instance finZeroArrowProjective (R : Type uR) [CommSemiring R] :
    Module.Projective R (Fin 0 → R) :=
  Module.Projective.of_free

private theorem finZeroEnd_eq_zero (R : Type uR) [CommSemiring R]
    (f : (Fin 0 → R) →ₗ[R] (Fin 0 → R)) : f = 0 :=
  LinearMap.ext fun _ => Subsingleton.elim _ _

private theorem trace_finZero_eq_zero (R : Type uR) [CommSemiring R]
    (f : (Fin 0 → R) →ₗ[R] (Fin 0 → R)) :
    traceOfFiniteProjective R (Fin 0 → R) f = 0 := by
  rw [finZeroEnd_eq_zero R f]
  exact map_zero (traceOfFiniteProjective R (Fin 0 → R))

private theorem finsum_finZero_diagonal_eq_zero (R : Type uR) [CommSemiring R]
    (f : (Fin 0 → R) →ₗ[R] (Fin 0 → R)) :
    (∑ᶠ i : Fin 0, traceOfFiniteProjective R R
      ((LinearMap.proj i).comp
        (f.comp (LinearMap.single R (fun _ : Fin 0 => R) i)))) = 0 :=
  finsum_of_isEmpty _

private theorem trace_finZero_eq_finsum (R : Type uR) [CommSemiring R]
    (f : (Fin 0 → R) →ₗ[R] (Fin 0 → R)) :
    traceOfFiniteProjective R (Fin 0 → R) f =
      ∑ᶠ i : Fin 0, traceOfFiniteProjective R R
        ((LinearMap.proj i).comp
          (f.comp (LinearMap.single R (fun _ : Fin 0 => R) i))) :=
  (trace_finZero_eq_zero R f).trans (finsum_finZero_diagonal_eq_zero R f).symm

private theorem trace_finZero_id_eq_zero (R : Type uR) [CommSemiring R] :
    traceOfFiniteProjective R (Fin 0 → R) (LinearMap.id : (Fin 0 → R) →ₗ[R] (Fin 0 → R)) = 0 :=
  trace_finZero_eq_zero R _

-- The scalar semiring need not be a ring; the empty Pi module is still zero.
example : Subsingleton (Fin 0 → ℕ) := inferInstance

example (f : (Fin 0 → ℕ) →ₗ[ℕ] (Fin 0 → ℕ)) : f = 0 :=
  finZeroEnd_eq_zero ℕ f

example (f : (Fin 0 → ℕ) →ₗ[ℕ] (Fin 0 → ℕ)) :
    traceOfFiniteProjective ℕ (Fin 0 → ℕ) f = 0 :=
  trace_finZero_eq_zero ℕ f

example (f : (Fin 0 → ℕ) →ₗ[ℕ] (Fin 0 → ℕ)) :
    traceOfFiniteProjective ℕ (Fin 0 → ℕ) f =
      ∑ᶠ i : Fin 0, traceOfFiniteProjective ℕ ℕ
        ((LinearMap.proj i).comp
          (f.comp (LinearMap.single ℕ (fun _ : Fin 0 => ℕ) i))) :=
  trace_finZero_eq_finsum ℕ f

example : traceOfFiniteProjective ℕ (Fin 0 → ℕ)
    (LinearMap.id : (Fin 0 → ℕ) →ₗ[ℕ] (Fin 0 → ℕ)) = 0 :=
  trace_finZero_id_eq_zero ℕ

end LinearMap
