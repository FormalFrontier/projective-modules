/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules
import ProjectiveModulesTests.ScalarRankClient
public import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Free right-matrix rank clients

For a free right module over a matrix ring on a finite nonempty index type,
restriction along the opposite scalar-matrix map multiplies its cardinal rank
by the square of the matrix size. Its multiplicity of the concrete simple row
is the matrix size times its free rank. Both equations include zero and
infinite free ranks, and do not require central scalar matrices.
The final rank formula in Weibel's example does not repeat the preceding
freeness qualification for basis rank; here freeness is explicit and the
ranks are compared as universe-lifted cardinals.

The single row over two-by-two quaternion matrices has scalar rank two and
row multiplicity one, but is not free over the matrix ring: a nonzero free
module has scalar rank at least four, and an infinite free rank gives an
infinite scalar rank. Thus the freeness assumption cannot be dropped from
the free-rank formulas, although Projective's scalar-multiplicity formula
continues to apply to this row.

## References

Charles A. Weibel, *The K-book*, Example I.1.1.1, motivates the free
matrix-module comparison. Mathlib's `lift_rank_mul_lift_rank` supplies the
free-module rank tower; Projective Modules' `Matrix.lift_rank_op_scalar_eq_card_mul_multiplicity`
and concrete-row multiplicity API supply the scalar action and row dimension.
-/

set_option warningAsError true

namespace ProjectiveModulesTests.FreeMatrixRankClient

noncomputable section

open scoped Quaternion
open Cardinal

universe u v w

private def matrixOpScalarLinearEquiv
    (i : Type v) [Fintype i] [DecidableEq i]
    (D : Type u) [DivisionRing D] :
    letI : Module Dᵐᵒᵖ (Matrix i i D)ᵐᵒᵖ :=
      Module.compHom _ (RingHom.op (Matrix.scalar i))
    Matrix i i Dᵐᵒᵖ ≃ₗ[Dᵐᵒᵖ] (Matrix i i D)ᵐᵒᵖ := by
  letI : Module Dᵐᵒᵖ (Matrix i i D)ᵐᵒᵖ :=
    Module.compHom _ (RingHom.op (Matrix.scalar i))
  refine { (RingEquiv.mopMatrix : Matrix i i Dᵐᵒᵖ ≃+* (Matrix i i D)ᵐᵒᵖ).toAddEquiv with
    map_smul' := ?_ }
  intro scalar matrix
  have hScalar :
      (RingEquiv.mopMatrix (Matrix.scalar i scalar) : (Matrix i i D)ᵐᵒᵖ) =
        (RingHom.op (Matrix.scalar i)) scalar := by
    apply MulOpposite.unop_injective
    change ((Matrix.scalar i scalar).transpose.map MulOpposite.unop) =
      Matrix.scalar i scalar.unop
    simp [Matrix.scalar_apply, Matrix.diagonal_transpose,
      Matrix.diagonal_map]
  change RingEquiv.mopMatrix (scalar • matrix) =
    (RingHom.op (Matrix.scalar i)) scalar * RingEquiv.mopMatrix matrix
  rw [← hScalar, ← map_mul, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

private theorem free_matrix_scalar_rank
    (i : Type v) [Fintype i] [Nonempty i] [DecidableEq i]
    (D : Type u) [DivisionRing D]
    {M : Type w} [AddCommGroup M] [Module (Matrix i i D)ᵐᵒᵖ M]
    [Module.Free (Matrix i i D)ᵐᵒᵖ M] :
    Cardinal.lift.{max u v}
        (@Module.rank Dᵐᵒᵖ M inferInstance inferInstance
          (Module.compHom M (RingHom.op (Matrix.scalar i)))) =
      ((Fintype.card i : Cardinal.{max u v w}) ^ 2) *
        Cardinal.lift.{max u v} (Module.rank (Matrix i i D)ᵐᵒᵖ M) := by
  exact
    letI : Module Dᵐᵒᵖ (Matrix i i D)ᵐᵒᵖ :=
      Module.compHom _ (RingHom.op (Matrix.scalar i))
    letI : Module Dᵐᵒᵖ M := Module.compHom M (RingHom.op (Matrix.scalar i))
    letI : SMul Dᵐᵒᵖ (Matrix i i D)ᵐᵒᵖ :=
      SMul.comp _ (RingHom.op (Matrix.scalar i))
    letI : SMul Dᵐᵒᵖ M := SMul.comp M (RingHom.op (Matrix.scalar i))
    letI : IsScalarTower Dᵐᵒᵖ (Matrix i i D)ᵐᵒᵖ M := SMul.comp.isScalarTower _
    letI : Module.Free Dᵐᵒᵖ (Matrix i i D)ᵐᵒᵖ :=
      Module.Free.of_equiv (matrixOpScalarLinearEquiv i D)
    by
      calc
        _ = Cardinal.lift.{w} (Module.rank Dᵐᵒᵖ (Matrix i i D)ᵐᵒᵖ) *
            Cardinal.lift.{max u v} (Module.rank (Matrix i i D)ᵐᵒᵖ M) :=
          (lift_rank_mul_lift_rank Dᵐᵒᵖ (Matrix i i D)ᵐᵒᵖ M).symm
        _ = _ := by
          rw [← (matrixOpScalarLinearEquiv i D).rank_eq, rank_matrix']
          simp only [Cardinal.lift_mul, Cardinal.mk_fintype,
            Cardinal.lift_natCast, pow_two]

private theorem free_matrix_row_multiplicity
    (i : Type v) [Fintype i] [Nonempty i] [DecidableEq i]
    (D : Type u) [DivisionRing D]
    {M : Type w} [AddCommGroup M] [Module (Matrix i i D)ᵐᵒᵖ M]
    [Module.Free (Matrix i i D)ᵐᵒᵖ M] :
    (IsSimpleRing.isIsotypicOfType (Matrix i i D)ᵐᵒᵖ M (i → D)).multiplicity =
      (Fintype.card i : Cardinal.{max u v w}) *
        Cardinal.lift.{max u v} (Module.rank (Matrix i i D)ᵐᵒᵖ M) := by
  have scalarRank := Matrix.lift_rank_op_scalar_eq_card_mul_multiplicity i D (M := M)
  rw [free_matrix_scalar_rank i D] at scalarRank
  apply (Cardinal.natCast_mul_inj (Fintype.card_ne_zero : Fintype.card i ≠ 0)).mp
  rw [← scalarRank, pow_two, mul_assoc]

private abbrev QuaternionMatrix := (Matrix (Fin 2) (Fin 2) (Quaternion ℚ))ᵐᵒᵖ

private theorem quaternion_regular_right_action
    (coefficient : Quaternion ℚ) (matrix : Matrix (Fin 2) (Fin 2) (Quaternion ℚ)) :
    (RingHom.op (Matrix.scalar (Fin 2))) (MulOpposite.op coefficient) •
        (MulOpposite.op matrix : QuaternionMatrix) =
      MulOpposite.op (matrix * Matrix.scalar (Fin 2) coefficient) := by
  rfl

private theorem quaternion_regular_scalar_rank :
    @Module.rank (Quaternion ℚ)ᵐᵒᵖ QuaternionMatrix inferInstance inferInstance
      (Module.compHom QuaternionMatrix (RingHom.op (Matrix.scalar (Fin 2)))) = 4 := by
  have formula := free_matrix_scalar_rank (Fin 2) (Quaternion ℚ) (M := QuaternionMatrix)
  norm_num [Module.rank_self] at formula
  exact formula

private theorem quaternion_regular_row_multiplicity :
    (IsSimpleRing.isIsotypicOfType QuaternionMatrix QuaternionMatrix
      (Fin 2 → Quaternion ℚ)).multiplicity = 2 := by
  have formula := free_matrix_row_multiplicity (Fin 2) (Quaternion ℚ)
    (M := QuaternionMatrix)
  simpa [Module.rank_self] using formula

private theorem quaternion_zero_scalar_rank :
    @Module.rank (Quaternion ℚ)ᵐᵒᵖ (Fin 0 →₀ QuaternionMatrix)
      inferInstance inferInstance
      (Module.compHom _ (RingHom.op (Matrix.scalar (Fin 2)))) = 0 := by
  have formula := free_matrix_scalar_rank (Fin 2) (Quaternion ℚ)
    (M := Fin 0 →₀ QuaternionMatrix)
  simpa only [Cardinal.lift_id, rank_finsupp_self, Cardinal.mk_fintype,
    Fintype.card_fin, Nat.cast_zero, mul_zero] using formula

private theorem quaternion_zero_row_multiplicity :
    (IsSimpleRing.isIsotypicOfType QuaternionMatrix (Fin 0 →₀ QuaternionMatrix)
      (Fin 2 → Quaternion ℚ)).multiplicity = 0 := by
  have formula := free_matrix_row_multiplicity (Fin 2) (Quaternion ℚ)
    (M := Fin 0 →₀ QuaternionMatrix)
  simpa only [Cardinal.lift_id, rank_finsupp_self, Cardinal.mk_fintype,
    Fintype.card_fin, Nat.cast_zero, mul_zero] using formula

private abbrev SingletonMatrix := (Matrix (Fin 1) (Fin 1) ℚ)ᵐᵒᵖ

private theorem singleton_three_coordinates :
    @Module.rank ℚᵐᵒᵖ (Fin 3 →₀ SingletonMatrix) inferInstance inferInstance
        (Module.compHom _ (RingHom.op (Matrix.scalar (Fin 1)))) = 3 ∧
      (IsSimpleRing.isIsotypicOfType SingletonMatrix (Fin 3 →₀ SingletonMatrix)
        (Fin 1 → ℚ)).multiplicity = 3 := by
  have scalar := free_matrix_scalar_rank (Fin 1) ℚ (M := Fin 3 →₀ SingletonMatrix)
  have rows := free_matrix_row_multiplicity (Fin 1) ℚ
    (M := Fin 3 →₀ SingletonMatrix)
  constructor
  · simpa [rank_finsupp_self] using scalar
  · simpa [rank_finsupp_self] using rows

private abbrev LiftedQuaternionMatrix :=
  (Matrix (ULift.{1} (Fin 2)) (ULift.{1} (Fin 2)) (Quaternion ℚ))ᵐᵒᵖ

private theorem infinite_quaternion_free_coordinates :
    ℵ₀ ≤ Module.rank LiftedQuaternionMatrix
        (ULift.{2} ℕ →₀ LiftedQuaternionMatrix) ∧
    Cardinal.lift.{1} (@Module.rank (Quaternion ℚ)ᵐᵒᵖ
        (ULift.{2} ℕ →₀ LiftedQuaternionMatrix) inferInstance inferInstance
        (Module.compHom _
          (RingHom.op (Matrix.scalar (ULift.{1} (Fin 2)))))) =
      (4 : Cardinal.{2}) * #(ULift.{2} ℕ) ∧
    (IsSimpleRing.isIsotypicOfType LiftedQuaternionMatrix
      (ULift.{2} ℕ →₀ LiftedQuaternionMatrix)
      (ULift.{1} (Fin 2) → Quaternion ℚ)).multiplicity =
      (2 : Cardinal.{2}) * #(ULift.{2} ℕ) := by
  have scalar := free_matrix_scalar_rank (ULift.{1} (Fin 2)) (Quaternion ℚ)
    (M := ULift.{2} ℕ →₀ LiftedQuaternionMatrix)
  have rows := free_matrix_row_multiplicity (ULift.{1} (Fin 2)) (Quaternion ℚ)
    (M := ULift.{2} ℕ →₀ LiftedQuaternionMatrix)
  have coordinateRank :
      Module.rank LiftedQuaternionMatrix (ULift.{2} ℕ →₀ LiftedQuaternionMatrix) =
        #(ULift.{2} ℕ) :=
    (rank_finsupp_self LiftedQuaternionMatrix (ULift.{2} ℕ)).trans
      (Cardinal.lift_id'.{1, 2} _)
  refine ⟨?_, ?_, ?_⟩
  · rw [coordinateRank]
    exact Cardinal.aleph0_le_mk (ULift.{2} ℕ)
  · rw [coordinateRank, Cardinal.lift_id'.{1, 2} (#(ULift.{2} ℕ))] at scalar
    simpa only [Fintype.card_ulift, Fintype.card_fin, Nat.cast_ofNat,
      show (2 : Cardinal.{2}) ^ 2 = 4 by norm_num] using scalar
  · rw [coordinateRank, Cardinal.lift_id'.{1, 2} (#(ULift.{2} ℕ))] at rows
    simpa only [Fintype.card_ulift, Fintype.card_fin, Nat.cast_ofNat] using rows

/-- The quaternion row has scalar rank two and multiplicity one over the opposite
two-by-two matrix ring. -/
public theorem quaternion_row_boundary :
    @Module.rank (Quaternion ℚ)ᵐᵒᵖ (Fin 2 → Quaternion ℚ)
      inferInstance inferInstance
      (Module.compHom _ (RingHom.op (Matrix.scalar (Fin 2)))) = 2 ∧
      (IsSimpleRing.isIsotypicOfType
        (Matrix (Fin 2) (Fin 2) (Quaternion ℚ))ᵐᵒᵖ (Fin 2 → Quaternion ℚ)
        (Fin 2 → Quaternion ℚ)).multiplicity = 1 := by
  constructor
  · rw [Matrix.op_scalar_module_row (Fin 2) (Quaternion ℚ)]
    exact ScalarRankClient.quaternion_row_scalar_rank
  · exact IsIsotypicOfType.multiplicity_self _ _

end

end ProjectiveModulesTests.FreeMatrixRankClient
