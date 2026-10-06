/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Free.StableKernel
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Stably free kernel clients

Coordinate projections, a rectangular integer matrix, empty targets, and a
noncommutative matrix ring exercise the finite-kernel statements. Infinite free
coordinates distinguish the general surjection theorem from its finite-domain
specialization.
-/

namespace ProjectiveModulesTests

private theorem integer_coordinates_are_finite_kernel :
    ∃ m n : ℕ, ∃ f : (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ),
      Function.Surjective f ∧
        Nonempty ((Fin 1 → ℤ) ≃ₗ[ℤ] LinearMap.ker f) :=
  (Module.finite_isStablyFree_iff_exists_fin_surjective_ker_equiv
    ℤ (Fin 1 → ℤ)).mp ⟨inferInstance, inferInstance⟩

private def integerProjection : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 1 → ℤ) :=
  (LinearMap.fst ℤ (Fin 1 → ℤ) (Fin 1 → ℤ)).comp
    ((LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin 1) ℤ ℤ).symm.trans
      (LinearEquiv.funCongrLeft ℤ ℤ finSumFinEquiv).symm).symm.toLinearMap

private theorem integerProjection_surjective : Function.Surjective integerProjection := by
  intro y
  let e := (LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin 1) ℤ ℤ).symm.trans
    (LinearEquiv.funCongrLeft ℤ ℤ finSumFinEquiv).symm
  refine ⟨e (y, 0), ?_⟩
  change (e.symm (e (y, 0))).1 = y
  simp

private theorem integer_projection_kernel_finite_stably_free :
    Module.Finite ℤ (LinearMap.ker integerProjection) ∧
      Module.IsStablyFree ℤ (LinearMap.ker integerProjection) :=
  (Module.finite_isStablyFree_iff_exists_fin_surjective_ker_equiv
    ℤ (LinearMap.ker integerProjection)).mpr
    ⟨1, 2, integerProjection, integerProjection_surjective,
      ⟨LinearEquiv.refl ℤ (LinearMap.ker integerProjection)⟩⟩

private theorem empty_target_infinite_free_domain :
    Module.IsStablyFree ℤ
      (LinearMap.ker (0 : (ℕ →₀ ℤ) →ₗ[ℤ] (Fin 0 → ℤ))) ∧
      ¬ Module.Finite ℤ (ℕ →₀ ℤ) := by
  constructor
  · apply Module.IsStablyFree.ker_of_surjective
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  · exact Module.not_finite_of_infinite_basis (Finsupp.basisSingleOne (R := ℤ))

private theorem zero_ring_empty_kernel :
    Module.IsStablyFree (ZMod 1)
      (LinearMap.ker (0 : (Fin 0 → ZMod 1) →ₗ[ZMod 1] (Fin 0 → ZMod 1))) := by
  apply Module.IsStablyFree.ker_of_surjective
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩

private theorem separate_module_universes :
    Module.IsStablyFree ℤ (LinearMap.ker
      (0 : ULift.{1} (Fin 1 → ℤ) →ₗ[ℤ] ULift.{2} (Fin 0 → ℤ))) := by
  apply Module.IsStablyFree.ker_of_surjective
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩

private def integerRectangularMatrix : Matrix (Fin 2) (Fin 3) ℤ :=
  fun row col ↦ if row.val = col.val then 1 else 0

private theorem integerRectangularMatrix_surjective :
    Function.Surjective
      (Matrix.mulVecBilin ℤ ℤᵐᵒᵖ integerRectangularMatrix) := by
  intro y
  refine ⟨![y 0, y 1, 0], ?_⟩
  funext row
  fin_cases row <;>
    simp [integerRectangularMatrix, Matrix.mulVecBilin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem integer_rectangular_kernel_finite_stably_free :
    Module.Finite ℤᵐᵒᵖ
      (LinearMap.ker (Matrix.mulVecBilin ℤ ℤᵐᵒᵖ integerRectangularMatrix)) ∧
    Module.IsStablyFree ℤᵐᵒᵖ
      (LinearMap.ker (Matrix.mulVecBilin ℤ ℤᵐᵒᵖ integerRectangularMatrix)) :=
  Matrix.finite_isStablyFree_ker_mulVecBilin_of_surjective
    integerRectangularMatrix integerRectangularMatrix_surjective

private theorem integer_rectangular_kernel_nonzero :
    ∃ x : LinearMap.ker (Matrix.mulVecBilin ℤ ℤᵐᵒᵖ integerRectangularMatrix),
      (x : Fin 3 → ℤ) 2 = 1 := by
  refine ⟨⟨![0, 0, 1], ?_⟩, rfl⟩
  funext row
  fin_cases row <;>
    simp [integerRectangularMatrix, Matrix.mulVecBilin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem integer_product_splitter_kernel_axis :
    ∃ k : LinearMap.ker (LinearMap.fst ℤ ℤ ℤ),
      (k : ℤ × ℤ).2 = 1 ∧
        Module.Projective.prodKerEquivOfSurjective
          (LinearMap.fst ℤ ℤ ℤ) LinearMap.fst_surjective (0, k) =
          ((0, 1) : ℤ × ℤ) := by
  refine ⟨⟨(0, 1), rfl⟩, rfl, ?_⟩
  simp

private theorem integer_product_splitter_target_coordinate :
    (LinearMap.fst ℤ ℤ ℤ)
      (Module.Projective.prodKerEquivOfSurjective
        (LinearMap.fst ℤ ℤ ℤ) LinearMap.fst_surjective
        (7, (⟨(0, 1), rfl⟩ : LinearMap.ker (LinearMap.fst ℤ ℤ ℤ)))) = 7 := by
  simp

private theorem integer_product_splitter_inverse_target :
    ((Module.Projective.prodKerEquivOfSurjective
      (LinearMap.fst ℤ ℤ ℤ) LinearMap.fst_surjective).symm (7, 9)).1 = 7 := by
  simp

private abbrev MatrixRing := Matrix (Fin 2) (Fin 2) ℤ

private def leftCoefficient : MatrixRing := Matrix.single 0 1 1
private def rightInput : MatrixRing := Matrix.single 1 0 1

private def noncommutativeRectangularMatrix : Matrix (Fin 2) (Fin 3) MatrixRing :=
  fun row col ↦
    if row = 0 ∧ col = 2 then leftCoefficient
    else if row.val = col.val then 1 else 0

private def noncommutativeVector : Fin 3 → MatrixRing :=
  ![0, 0, rightInput]

private theorem noncommutativeRectangularMatrix_surjective :
    Function.Surjective
      (Matrix.mulVecBilin MatrixRing MatrixRingᵐᵒᵖ noncommutativeRectangularMatrix) := by
  intro y
  refine ⟨![y 0, y 1, 0], ?_⟩
  funext row
  fin_cases row <;>
    simp [noncommutativeRectangularMatrix, Matrix.mulVecBilin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem noncommutative_rectangular_kernel_finite_stably_free :
    Module.Finite MatrixRingᵐᵒᵖ
      (LinearMap.ker (Matrix.mulVecBilin MatrixRing MatrixRingᵐᵒᵖ
        noncommutativeRectangularMatrix)) ∧
    Module.IsStablyFree MatrixRingᵐᵒᵖ
      (LinearMap.ker (Matrix.mulVecBilin MatrixRing MatrixRingᵐᵒᵖ
        noncommutativeRectangularMatrix)) :=
  Matrix.finite_isStablyFree_ker_mulVecBilin_of_surjective
    noncommutativeRectangularMatrix noncommutativeRectangularMatrix_surjective

private theorem noncommutative_left_coefficient_evaluation :
    ((Matrix.mulVecBilin MatrixRing MatrixRingᵐᵒᵖ
      noncommutativeRectangularMatrix) noncommutativeVector) 0 ≠
      ∑ col : Fin 3,
        noncommutativeVector col * noncommutativeRectangularMatrix 0 col := by
  intro h
  have h00 := congrArg (fun matrix : MatrixRing ↦ matrix 0 0) h
  norm_num [noncommutativeRectangularMatrix, noncommutativeVector,
    leftCoefficient, rightInput, Matrix.mulVecBilin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.mul_apply, Matrix.single_apply] at h00

private theorem empty_index_matrix_kernel :
    Module.Finite ℤᵐᵒᵖ
      (LinearMap.ker (Matrix.mulVecBilin ℤ ℤᵐᵒᵖ (0 : Matrix (Fin 0) (Fin 1) ℤ))) ∧
    Module.IsStablyFree ℤᵐᵒᵖ
      (LinearMap.ker (Matrix.mulVecBilin ℤ ℤᵐᵒᵖ (0 : Matrix (Fin 0) (Fin 1) ℤ))) := by
  apply Matrix.finite_isStablyFree_ker_mulVecBilin_of_surjective
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩

private theorem separate_index_universes :
    Module.Finite ℤᵐᵒᵖ (LinearMap.ker
      (Matrix.mulVecBilin ℤ ℤᵐᵒᵖ
        (0 : Matrix (ULift.{2} (Fin 0)) (ULift.{3} (Fin 1)) ℤ))) ∧
    Module.IsStablyFree ℤᵐᵒᵖ (LinearMap.ker
      (Matrix.mulVecBilin ℤ ℤᵐᵒᵖ
        (0 : Matrix (ULift.{2} (Fin 0)) (ULift.{3} (Fin 1)) ℤ))) := by
  apply Matrix.finite_isStablyFree_ker_mulVecBilin_of_surjective
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩

end ProjectiveModulesTests
