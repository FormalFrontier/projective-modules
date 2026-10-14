/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Trace.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Map

import Mathlib.Tactic.NormNum

/-!
# Tensor traces of diagonal endomorphisms over the natural numbers

The standard modules `Fin 2 → ℕ` and `Fin 3 → ℕ` are finite, projective and
nonzero with their canonical operations. The diagonal endomorphisms with weights
`(2, 3)` and `(1, 4, 6)` have finite-projective traces `5` and `11`. In the tensor
product of the standard bases, their tensor map has diagonal weights
`(2, 8, 12, 3, 12, 18)`, and its trace is computed directly as `55`.

The direct calculation uses the comparison with the finite-basis trace and
matrix coordinates over a commutative semiring, independently of a tensor trace
formula. A separate application of the tensor trace formula recovers `55` from
the two factor traces.

## References

The matrix and finite-basis trace interfaces are from the Mathlib formalization
by Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen and Antoine Labelle.
The tensor-product basis interface is from Jakob von Raumer's Mathlib
formalization, and the tensor map interface is from Kenny Lau and Mario
Carneiro's Mathlib formalization.
-/

noncomputable section

open scoped TensorProduct

namespace ProjectiveModulesTests

private abbrev M := Fin 2 → ℕ
private abbrev N := Fin 3 → ℕ

private def weightsM : Fin 2 → ℕ := ![2, 3]
private def weightsN : Fin 3 → ℕ := ![1, 4, 6]

private def f : M →ₗ[ℕ] M :=
  Matrix.toLin' (Matrix.diagonal weightsM)

private def g : N →ₗ[ℕ] N :=
  Matrix.toLin' (Matrix.diagonal weightsN)

private theorem f_apply (x : M) (i : Fin 2) :
    f x i = weightsM i * x i := by
  exact Matrix.mulVec_diagonal weightsM x i

private theorem g_apply (y : N) (j : Fin 3) :
    g y j = weightsN j * y j := by
  exact Matrix.mulVec_diagonal weightsN y j

private def tensorMap : M ⊗[ℕ] N →ₗ[ℕ] M ⊗[ℕ] N :=
  TensorProduct.map f g

private theorem tensorMap_tmul (x : M) (y : N) :
    tensorMap (x ⊗ₜ[ℕ] y) = f x ⊗ₜ[ℕ] g y :=
  TensorProduct.map_tmul f g x y

private def tensorBasis : Module.Basis (Fin 2 × Fin 3) ℕ (M ⊗[ℕ] N) :=
  (Pi.basisFun ℕ (Fin 2)).tensorProduct (Pi.basisFun ℕ (Fin 3))

private instance : Module.Finite ℕ (M ⊗[ℕ] N) :=
  Module.Finite.of_basis tensorBasis

private instance : Module.Free ℕ (M ⊗[ℕ] N) :=
  Module.Free.of_basis tensorBasis

private theorem tensorBasis_apply (i : Fin 2) (j : Fin 3) :
    tensorBasis (i, j) =
      Pi.basisFun ℕ (Fin 2) i ⊗ₜ[ℕ] Pi.basisFun ℕ (Fin 3) j :=
  Module.Basis.tensorProduct_apply _ _ i j

private theorem tensorBasis_repr_tmul (x : M) (y : N) (i : Fin 2) (j : Fin 3) :
    tensorBasis.repr (x ⊗ₜ[ℕ] y) (i, j) = y j * x i := by
  calc
    tensorBasis.repr (x ⊗ₜ[ℕ] y) (i, j) =
        (Pi.basisFun ℕ (Fin 3)).repr y j • (Pi.basisFun ℕ (Fin 2)).repr x i :=
      Module.Basis.tensorProduct_repr_tmul_apply
        (Pi.basisFun ℕ (Fin 2)) (Pi.basisFun ℕ (Fin 3)) x y i j
    _ = y j • x i :=
      congrArg₂ (fun a b : ℕ => a • b)
        (Pi.basisFun_repr ℕ (Fin 3) y j) (Pi.basisFun_repr ℕ (Fin 2) x i)
    _ = y j * x i := smul_eq_mul _ _

private theorem tensorMatrix_diag (i : Fin 2) (j : Fin 3) :
    LinearMap.toMatrix tensorBasis tensorBasis tensorMap (i, j) (i, j) =
      weightsM i * weightsN j := by
  rw [LinearMap.toMatrix_apply, tensorBasis_apply, tensorMap_tmul,
    tensorBasis_repr_tmul]
  simp [f_apply, g_apply, mul_comm]

private theorem trace_f : LinearMap.traceOfFiniteProjective ℕ M f = 5 := by
  calc
    LinearMap.traceOfFiniteProjective ℕ M f =
        Matrix.trace (Matrix.diagonal weightsM) := by
      rw [LinearMap.traceOfFiniteProjective_eq_trace]
      exact Matrix.trace_toLin'_eq _
    _ = 5 := by
      rw [Matrix.trace_diagonal]
      norm_num [weightsM, Fin.sum_univ_succ]

private theorem trace_g : LinearMap.traceOfFiniteProjective ℕ N g = 11 := by
  calc
    LinearMap.traceOfFiniteProjective ℕ N g =
        Matrix.trace (Matrix.diagonal weightsN) := by
      rw [LinearMap.traceOfFiniteProjective_eq_trace]
      exact Matrix.trace_toLin'_eq _
    _ = 11 := by
      rw [Matrix.trace_diagonal]
      norm_num [weightsN, Fin.sum_univ_succ]

private theorem trace_tensorMap :
    LinearMap.traceOfFiniteProjective ℕ (M ⊗[ℕ] N) tensorMap = 55 := by
  calc
    LinearMap.traceOfFiniteProjective ℕ (M ⊗[ℕ] N) tensorMap =
        ∑ i : Fin 2, ∑ j : Fin 3, weightsM i * weightsN j := by
      rw [LinearMap.traceOfFiniteProjective_eq_trace,
        LinearMap.trace_eq_matrix_trace ℕ tensorBasis]
      simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type,
        tensorMatrix_diag]
    _ = 55 := by norm_num [weightsM, weightsN, Fin.sum_univ_succ]

private theorem f_ne_zero : f ≠ 0 := by
  intro h
  have h' : (0 : ℕ) = 5 := by simpa only [h, map_zero] using trace_f
  norm_num at h'

private theorem g_ne_zero : g ≠ 0 := by
  intro h
  have h' : (0 : ℕ) = 11 := by simpa only [h, map_zero] using trace_g
  norm_num at h'

private theorem tensorMap_ne_zero : tensorMap ≠ 0 := by
  intro h
  have h' : (0 : ℕ) = 55 := by simpa only [h, map_zero] using trace_tensorMap
  norm_num at h'

private theorem pureBasis_ne_zero :
    Pi.basisFun ℕ (Fin 2) 0 ⊗ₜ[ℕ] Pi.basisFun ℕ (Fin 3) 0 ≠
      (0 : M ⊗[ℕ] N) := by
  intro h
  have h' := congrArg (fun z : M ⊗[ℕ] N => tensorBasis.repr z (0, 0)) h
  simp [tensorBasis_repr_tmul] at h'

example : Module.Finite ℕ M := inferInstance
example : Module.Projective ℕ M := inferInstance
example : Nontrivial M := inferInstance

example : Module.Finite ℕ N := inferInstance
example : Module.Projective ℕ N := inferInstance
example : Nontrivial N := inferInstance

example : Module.Finite ℕ (M ⊗[ℕ] N) := inferInstance
example : Module.Projective ℕ (M ⊗[ℕ] N) := inferInstance
example : Nontrivial (M ⊗[ℕ] N) := ⟨⟨_, _, pureBasis_ne_zero⟩⟩

example : LinearMap.traceOfFiniteProjective ℕ M f = 5 := trace_f
example : LinearMap.traceOfFiniteProjective ℕ N g = 11 := trace_g
example : LinearMap.traceOfFiniteProjective ℕ (M ⊗[ℕ] N)
    (TensorProduct.map f g) = 55 := trace_tensorMap

example : f ≠ 0 := f_ne_zero
example : g ≠ 0 := g_ne_zero
example : TensorProduct.map f g ≠ 0 := tensorMap_ne_zero

private theorem trace_tensorMap_from_factor_traces :
    LinearMap.traceOfFiniteProjective ℕ (M ⊗[ℕ] N)
      (TensorProduct.map f g) = 55 := by
  have h := LinearMap.traceOfFiniteProjective_tensorProduct' ℕ M N f g
  norm_num only [trace_f, trace_g] at h
  exact h

end ProjectiveModulesTests
