/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules
import ProjectiveModulesTests.ScalarRankClient
public import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Ring.ULift
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.SimpleRing.Congr

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

For a chosen equivalence between any ring and a finite matrix ring over a
division ring, the same comparison uses the scalar inclusion selected by
that equivalence and the specifically transported simple row. The arbitrary
module equation and the two free-module equations are stated separately.
Concrete raised-universe quaternion examples check the chosen right action,
finite and infinite free ranks, and a nonfree simple row independently of
those statements.

## References

Charles A. Weibel, *The K-book*, Example I.1.1.1, motivates the free
matrix-module comparison. Mathlib's `lift_rank_mul_lift_rank` supplies the
free-module rank tower, while `Basis.mapCoeffs` and
`lift_rank_eq_of_equiv_equiv` handle transport. Projective Modules'
`Matrix.lift_rank_op_scalar_eq_card_mul_multiplicity` and
`IsIsotypicOfType.lift_multiplicity_eq_of_semilinearEquiv` supply the
fixed-row comparisons.
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

section ChosenMatrixPresentation

universe uR uD uI uM

variable (R : Type uR) [Ring R]
    (i : Type uI) [Fintype i] [Nonempty i] [DecidableEq i]
    (D : Type uD) [DivisionRing D]

private def chosenOppEquiv (e : R ≃+* Matrix i i D) :
    Rᵐᵒᵖ ≃+* (Matrix i i D)ᵐᵒᵖ :=
  RingEquiv.op e

private def chosenScalar (e : R ≃+* Matrix i i D) : D →+* R :=
  e.symm.toRingHom.comp (Matrix.scalar i)

private abbrev chosenRowModule (e : R ≃+* Matrix i i D) : Module Rᵐᵒᵖ (i → D) :=
  Module.compHom (i → D) (chosenOppEquiv R i D e).toRingHom

omit [Nonempty i] in
private theorem chosen_scalar_compatibility (e : R ≃+* Matrix i i D)
    (scalar : Dᵐᵒᵖ) :
    chosenOppEquiv R i D e ((RingHom.op (chosenScalar R i D e)) scalar) =
      (RingHom.op (Matrix.scalar i)) scalar := by
  apply MulOpposite.unop_injective
  change e (e.symm (Matrix.scalar i scalar.unop)) = Matrix.scalar i scalar.unop
  exact e.apply_symm_apply _

omit [Nonempty i] in
private theorem chosen_row_scalar_action (e : R ≃+* Matrix i i D)
    (scalar : Dᵐᵒᵖ) (row : i → D) :
    letI : Module Rᵐᵒᵖ (i → D) := chosenRowModule R i D e
    (RingHom.op (chosenScalar R i D e)) scalar • row = scalar • row := by
  let : Module Rᵐᵒᵖ (i → D) := chosenRowModule R i D e
  change chosenOppEquiv R i D e ((RingHom.op (chosenScalar R i D e)) scalar) • row =
    scalar • row
  rw [chosen_scalar_compatibility R i D e]
  exact Matrix.op_scalar_smul_row i D scalar row

omit [Nonempty i] in
private theorem chosen_row_restriction (e : R ≃+* Matrix i i D) :
    letI : Module Rᵐᵒᵖ (i → D) := chosenRowModule R i D e
    (Module.compHom (i → D) (RingHom.op (chosenScalar R i D e)) :
      Module Dᵐᵒᵖ (i → D)) = (inferInstance : Module Dᵐᵒᵖ (i → D)) := by
  let : Module Rᵐᵒᵖ (i → D) := chosenRowModule R i D e
  apply Module.ext'
  intro scalar row
  exact chosen_row_scalar_action R i D e scalar row

attribute [local instance] RingHomInvPair.of_ringEquiv

private def chosenModuleEquiv (e : R ≃+* Matrix i i D)
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    letI : Module (Matrix i i D)ᵐᵒᵖ M :=
      Module.compHom M (chosenOppEquiv R i D e).symm.toRingHom
    M ≃ₛₗ[(chosenOppEquiv R i D e : Rᵐᵒᵖ →+* (Matrix i i D)ᵐᵒᵖ)] M := by
  letI : Module (Matrix i i D)ᵐᵒᵖ M :=
    Module.compHom M (chosenOppEquiv R i D e).symm.toRingHom
  refine { AddEquiv.refl M with map_smul' := ?_ }
  intro scalar value
  change scalar • value =
    (chosenOppEquiv R i D e).symm (chosenOppEquiv R i D e scalar) • value
  rw [RingEquiv.symm_apply_apply]

omit [Nonempty i] in
private theorem chosen_matrix_free (e : R ≃+* Matrix i i D)
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Free Rᵐᵒᵖ M] :
    letI : Module (Matrix i i D)ᵐᵒᵖ M :=
      Module.compHom M (chosenOppEquiv R i D e).symm.toRingHom
    Module.Free (Matrix i i D)ᵐᵒᵖ M := by
  let : Module (Matrix i i D)ᵐᵒᵖ M :=
    Module.compHom M (chosenOppEquiv R i D e).symm.toRingHom
  obtain ⟨⟨basisIndex, basis⟩⟩ := Module.Free.exists_basis (R := Rᵐᵒᵖ) (M := M)
  exact Module.Free.of_basis (basis.mapCoeffs (chosenOppEquiv R i D e)
    (fun scalar value => by
      change (chosenOppEquiv R i D e).symm (chosenOppEquiv R i D e scalar) • value =
        scalar • value
      rw [RingEquiv.symm_apply_apply]))

private def chosenRowEquiv (e : R ≃+* Matrix i i D) :
    letI : Module Rᵐᵒᵖ (i → D) := chosenRowModule R i D e
    (i → D) ≃ₛₗ[(chosenOppEquiv R i D e : Rᵐᵒᵖ →+* (Matrix i i D)ᵐᵒᵖ)]
      (i → D) := by
  letI : Module Rᵐᵒᵖ (i → D) := chosenRowModule R i D e
  refine { AddEquiv.refl (i → D) with map_smul' := ?_ }
  intro scalar row
  rfl

omit [DecidableEq i] in
private theorem chosenOppSimpleRing (e : R ≃+* Matrix i i D) : IsSimpleRing Rᵐᵒᵖ := by
  classical
  exact IsSimpleRing.of_ringEquiv (chosenOppEquiv R i D e).symm inferInstance

omit [Nonempty i] [DecidableEq i] in
private theorem chosenOppSemisimpleRing (e : R ≃+* Matrix i i D) :
    IsSemisimpleRing Rᵐᵒᵖ := by
  classical
  exact (chosenOppEquiv R i D e).symm.isSemisimpleRing

private theorem chosenRowSimple (e : R ≃+* Matrix i i D) :
    letI : Module Rᵐᵒᵖ (i → D) := chosenRowModule R i D e
    IsSimpleModule Rᵐᵒᵖ (i → D) := by
  let : Module Rᵐᵒᵖ (i → D) := chosenRowModule R i D e
  let equivalence := chosenRowEquiv R i D e
  exact (equivalence.toLinearMap.isSimpleModule_iff_of_bijective
    equivalence.bijective).mpr inferInstance

private theorem chosenIsotypic (e : R ≃+* Matrix i i D)
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    letI : Module Rᵐᵒᵖ (i → D) := chosenRowModule R i D e
    letI : IsSimpleModule Rᵐᵒᵖ (i → D) := chosenRowSimple R i D e
    letI : IsSemisimpleRing Rᵐᵒᵖ := chosenOppSemisimpleRing R i D e
    IsIsotypicOfType Rᵐᵒᵖ M (i → D) := by
  let : Module Rᵐᵒᵖ (i → D) := chosenRowModule R i D e
  let : IsSimpleModule Rᵐᵒᵖ (i → D) := chosenRowSimple R i D e
  let : IsSemisimpleRing Rᵐᵒᵖ := chosenOppSemisimpleRing R i D e
  let : IsSimpleRing Rᵐᵒᵖ := chosenOppSimpleRing R i D e
  exact IsSimpleRing.isIsotypicOfType Rᵐᵒᵖ M (i → D)

private theorem chosen_scalar_rank_eq_card_mul_multiplicity
    (e : R ≃+* Matrix i i D)
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    letI : Module Rᵐᵒᵖ (i → D) := chosenRowModule R i D e
    letI : IsSimpleModule Rᵐᵒᵖ (i → D) := chosenRowSimple R i D e
    letI : IsSemisimpleRing Rᵐᵒᵖ := chosenOppSemisimpleRing R i D e
    Cardinal.lift.{max uR uD uI}
        (@Module.rank Dᵐᵒᵖ M inferInstance inferInstance
          (Module.compHom M (RingHom.op (chosenScalar R i D e)))) =
      (Fintype.card i : Cardinal.{max uR uD uI uM}) *
        Cardinal.lift.{uR} (chosenIsotypic R i D e M).multiplicity := by
  let : Module Rᵐᵒᵖ (i → D) := chosenRowModule R i D e
  let : IsSimpleModule Rᵐᵒᵖ (i → D) := chosenRowSimple R i D e
  let : IsSemisimpleRing Rᵐᵒᵖ := chosenOppSemisimpleRing R i D e
  let : Module (Matrix i i D)ᵐᵒᵖ M :=
    Module.compHom M (chosenOppEquiv R i D e).symm.toRingHom
  have scalarModule :
      (Module.compHom M (RingHom.op (chosenScalar R i D e)) : Module Dᵐᵒᵖ M) =
        (Module.compHom M (RingHom.op (Matrix.scalar i)) : Module Dᵐᵒᵖ M) := by
    apply Module.ext'
    intro scalar value
    change (RingHom.op (chosenScalar R i D e)) scalar • value =
      (chosenOppEquiv R i D e).symm
        ((RingHom.op (Matrix.scalar i)) scalar) • value
    rw [← chosen_scalar_compatibility R i D e scalar,
      RingEquiv.symm_apply_apply]
  have multiplicityTransport :=
    (chosenIsotypic R i D e M).lift_multiplicity_eq_of_semilinearEquiv
      (IsSimpleRing.isIsotypicOfType (Matrix i i D)ᵐᵒᵖ M (i → D))
      (chosenOppEquiv R i D e) (chosenModuleEquiv R i D e M)
      (chosenRowEquiv R i D e)
  have multiplicityEq :
      Cardinal.lift.{uR} (chosenIsotypic R i D e M).multiplicity =
        Cardinal.lift.{uR}
          (IsSimpleRing.isIsotypicOfType (Matrix i i D)ᵐᵒᵖ M (i → D)).multiplicity := by
    have equality : (chosenIsotypic R i D e M).multiplicity =
        (IsSimpleRing.isIsotypicOfType (Matrix i i D)ᵐᵒᵖ M (i → D)).multiplicity := by
      simpa only [Cardinal.lift_id] using multiplicityTransport
    exact congrArg Cardinal.lift.{uR} equality
  have matrixFormula := congrArg Cardinal.lift.{uR}
    (Matrix.lift_rank_op_scalar_eq_card_mul_multiplicity i D (M := M))
  simp only [Cardinal.lift_lift, Cardinal.lift_mul, Cardinal.lift_natCast] at matrixFormula
  rw [scalarModule, multiplicityEq]
  exact matrixFormula

private theorem chosen_free_row_multiplicity
    (e : R ≃+* Matrix i i D)
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Free Rᵐᵒᵖ M] :
    letI : Module Rᵐᵒᵖ (i → D) := chosenRowModule R i D e
    letI : IsSimpleModule Rᵐᵒᵖ (i → D) := chosenRowSimple R i D e
    letI : IsSemisimpleRing Rᵐᵒᵖ := chosenOppSemisimpleRing R i D e
    Cardinal.lift.{uR} (chosenIsotypic R i D e M).multiplicity =
      (Fintype.card i : Cardinal.{max uR uD uI uM}) *
        Cardinal.lift.{max uR uD uI} (Module.rank Rᵐᵒᵖ M) := by
  let : Module Rᵐᵒᵖ (i → D) := chosenRowModule R i D e
  let : IsSimpleModule Rᵐᵒᵖ (i → D) := chosenRowSimple R i D e
  let : IsSemisimpleRing Rᵐᵒᵖ := chosenOppSemisimpleRing R i D e
  let : Module (Matrix i i D)ᵐᵒᵖ M :=
    Module.compHom M (chosenOppEquiv R i D e).symm.toRingHom
  let : Module.Free (Matrix i i D)ᵐᵒᵖ M := chosen_matrix_free R i D e M
  have multiplicityTransport :=
    (chosenIsotypic R i D e M).lift_multiplicity_eq_of_semilinearEquiv
      (IsSimpleRing.isIsotypicOfType (Matrix i i D)ᵐᵒᵖ M (i → D))
      (chosenOppEquiv R i D e) (chosenModuleEquiv R i D e M)
      (chosenRowEquiv R i D e)
  have multiplicityEq :
      Cardinal.lift.{uR} (chosenIsotypic R i D e M).multiplicity =
        Cardinal.lift.{uR}
          (IsSimpleRing.isIsotypicOfType (Matrix i i D)ᵐᵒᵖ M (i → D)).multiplicity := by
    have equality : (chosenIsotypic R i D e M).multiplicity =
        (IsSimpleRing.isIsotypicOfType (Matrix i i D)ᵐᵒᵖ M (i → D)).multiplicity := by
      simpa only [Cardinal.lift_id] using multiplicityTransport
    exact congrArg Cardinal.lift.{uR} equality
  have rankTransport :=
    lift_rank_eq_of_equiv_equiv (chosenOppEquiv R i D e)
      (AddEquiv.refl M) (chosenOppEquiv R i D e).bijective
      (by
        intro scalar value
        change scalar • value =
          (chosenOppEquiv R i D e).symm (chosenOppEquiv R i D e scalar) • value
        rw [RingEquiv.symm_apply_apply])
  have rankEq :
      Cardinal.lift.{max uR uD uI} (Module.rank Rᵐᵒᵖ M) =
        Cardinal.lift.{max uR uD uI}
          (Module.rank (Matrix i i D)ᵐᵒᵖ M) := by
    have equality : Module.rank Rᵐᵒᵖ M =
        Module.rank (Matrix i i D)ᵐᵒᵖ M := by
      simpa only [Cardinal.lift_id] using rankTransport
    exact congrArg Cardinal.lift.{max uR uD uI} equality
  have matrixFormula := congrArg Cardinal.lift.{uR}
    (free_matrix_row_multiplicity i D (M := M))
  simp only [Cardinal.lift_mul, Cardinal.lift_natCast,
    Cardinal.lift_lift] at matrixFormula
  rw [multiplicityEq, rankEq]
  exact matrixFormula

private theorem chosen_free_scalar_rank
    (e : R ≃+* Matrix i i D)
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Free Rᵐᵒᵖ M] :
    Cardinal.lift.{max uR uD uI}
        (@Module.rank Dᵐᵒᵖ M inferInstance inferInstance
          (Module.compHom M (RingHom.op (chosenScalar R i D e)))) =
      ((Fintype.card i : Cardinal.{max uR uD uI uM}) ^ 2) *
        Cardinal.lift.{max uR uD uI} (Module.rank Rᵐᵒᵖ M) := by
  let : Module Rᵐᵒᵖ (i → D) := chosenRowModule R i D e
  let : IsSimpleModule Rᵐᵒᵖ (i → D) := chosenRowSimple R i D e
  let : IsSemisimpleRing Rᵐᵒᵖ := chosenOppSemisimpleRing R i D e
  rw [chosen_scalar_rank_eq_card_mul_multiplicity R i D e M,
    chosen_free_row_multiplicity R i D e M, pow_two, mul_assoc]

end ChosenMatrixPresentation

section RaisedQuaternionPresentation

private abbrev RaisedQuaternionIndex := ULift.{1} (Fin 2)
private abbrev RaisedQuaternionRow := RaisedQuaternionIndex → Quaternion ℚ
private abbrev RaisedQuaternionMatrix :=
  Matrix RaisedQuaternionIndex RaisedQuaternionIndex (Quaternion ℚ)
private abbrev RaisedQuaternionRing := ULift.{2} RaisedQuaternionMatrix

private def raisedQuaternionPresentation :
    RaisedQuaternionRing ≃+* RaisedQuaternionMatrix :=
  ULift.ringEquiv

private instance : Module RaisedQuaternionRingᵐᵒᵖ RaisedQuaternionRow :=
  chosenRowModule RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
    raisedQuaternionPresentation

private instance : IsSimpleModule RaisedQuaternionRingᵐᵒᵖ RaisedQuaternionRow :=
  chosenRowSimple RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
    raisedQuaternionPresentation

private instance : IsSemisimpleRing RaisedQuaternionRingᵐᵒᵖ :=
  chosenOppSemisimpleRing RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
    raisedQuaternionPresentation

private instance : IsSimpleRing RaisedQuaternionRingᵐᵒᵖ :=
  chosenOppSimpleRing RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
    raisedQuaternionPresentation

private theorem raised_quaternion_regular_right_action
    (coefficient : Quaternion ℚ) (matrix : RaisedQuaternionMatrix) :
    (RingHom.op (chosenScalar RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
      raisedQuaternionPresentation)) (MulOpposite.op coefficient) •
        (MulOpposite.op (ULift.up matrix) : RaisedQuaternionRingᵐᵒᵖ) =
      MulOpposite.op (ULift.up (matrix * Matrix.scalar RaisedQuaternionIndex coefficient)) := by
  rfl

private def raisedQuaternionI : Quaternion ℚ := ⟨0, 1, 0, 0⟩
private def raisedQuaternionJ : Quaternion ℚ := ⟨0, 0, 1, 0⟩

private theorem raised_quaternion_row_noncentral :
    ((RingHom.op (chosenScalar RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
      raisedQuaternionPresentation)) (MulOpposite.op raisedQuaternionI) •
        (Pi.single (ULift.up (0 : Fin 2)) raisedQuaternionJ : RaisedQuaternionRow))
          (ULift.up (0 : Fin 2)) = raisedQuaternionJ * raisedQuaternionI ∧
    ((RingHom.op (chosenScalar RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
      raisedQuaternionPresentation)) (MulOpposite.op raisedQuaternionI) •
        (Pi.single (ULift.up (0 : Fin 2)) raisedQuaternionJ : RaisedQuaternionRow))
          (ULift.up (0 : Fin 2)) ≠ raisedQuaternionI * raisedQuaternionJ := by
  have action :
      ((RingHom.op (chosenScalar RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
        raisedQuaternionPresentation)) (MulOpposite.op raisedQuaternionI) •
          (Pi.single (ULift.up (0 : Fin 2)) raisedQuaternionJ : RaisedQuaternionRow))
            (ULift.up (0 : Fin 2)) = raisedQuaternionJ * raisedQuaternionI := by
    rw [chosen_row_scalar_action]
    simp [MulOpposite.smul_eq_mul_unop]
  have noncommutative : raisedQuaternionI * raisedQuaternionJ ≠
      raisedQuaternionJ * raisedQuaternionI := by
    intro equality
    have imaginaryPart := congrArg (fun value : Quaternion ℚ => value.imK) equality
    norm_num [Quaternion.imK_mul, raisedQuaternionI, raisedQuaternionJ] at imaginaryPart
  exact ⟨action, fun equality => noncommutative (action.symm.trans equality).symm⟩

private theorem raised_quaternion_row_values :
    @Module.rank (Quaternion ℚ)ᵐᵒᵖ RaisedQuaternionRow inferInstance inferInstance
      (Module.compHom RaisedQuaternionRow (RingHom.op (chosenScalar RaisedQuaternionRing
        RaisedQuaternionIndex (Quaternion ℚ) raisedQuaternionPresentation))) = 2 ∧
    (chosenIsotypic RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
      raisedQuaternionPresentation RaisedQuaternionRow).multiplicity = 1 := by
  constructor
  · rw [chosen_row_restriction RaisedQuaternionRing RaisedQuaternionIndex
      (Quaternion ℚ) raisedQuaternionPresentation]
    simpa only [Fintype.card_ulift, Fintype.card_fin, Nat.cast_ofNat] using
      Matrix.rank_row_op_scalar RaisedQuaternionIndex (Quaternion ℚ)
  · change (IsIsotypicOfType.of_isSimpleModule RaisedQuaternionRingᵐᵒᵖ
      RaisedQuaternionRow).multiplicity = 1
    exact IsIsotypicOfType.multiplicity_self _ _

private theorem raised_quaternion_row_not_free :
    ¬ Module.Free RaisedQuaternionRingᵐᵒᵖ RaisedQuaternionRow := by
  intro freeRow
  let : Module.Free RaisedQuaternionRingᵐᵒᵖ RaisedQuaternionRow := freeRow
  have matrixAction :
      (Module.compHom RaisedQuaternionRow
        (chosenOppEquiv RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
          raisedQuaternionPresentation).symm.toRingHom :
          Module RaisedQuaternionMatrixᵐᵒᵖ RaisedQuaternionRow) =
        (inferInstance : Module RaisedQuaternionMatrixᵐᵒᵖ RaisedQuaternionRow) := by
    apply Module.ext'
    intro scalar row
    change (chosenOppEquiv RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
      raisedQuaternionPresentation)
        ((chosenOppEquiv RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
          raisedQuaternionPresentation).symm scalar) • row = scalar • row
    rw [RingEquiv.apply_symm_apply]
  have matrixFree : Module.Free RaisedQuaternionMatrixᵐᵒᵖ RaisedQuaternionRow := by
    have transported : @Module.Free RaisedQuaternionMatrixᵐᵒᵖ RaisedQuaternionRow
        inferInstance inferInstance
        (Module.compHom RaisedQuaternionRow
          (chosenOppEquiv RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
            raisedQuaternionPresentation).symm.toRingHom) :=
      chosen_matrix_free RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
        raisedQuaternionPresentation RaisedQuaternionRow
    rw [matrixAction] at transported
    exact transported
  let : Module.Free RaisedQuaternionMatrixᵐᵒᵖ RaisedQuaternionRow := matrixFree
  have matrixMultiplicity := free_matrix_row_multiplicity RaisedQuaternionIndex
    (Quaternion ℚ) (M := RaisedQuaternionRow)
  have multiplicityOne :
      (IsSimpleRing.isIsotypicOfType RaisedQuaternionMatrixᵐᵒᵖ
        RaisedQuaternionRow RaisedQuaternionRow).multiplicity = 1 :=
    IsIsotypicOfType.multiplicity_self _ _
  have impossible : (1 : Cardinal.{1}) =
      2 * Cardinal.lift.{1}
        (Module.rank RaisedQuaternionMatrixᵐᵒᵖ RaisedQuaternionRow) := by
    simpa only [multiplicityOne, Fintype.card_ulift, Fintype.card_fin,
      Nat.cast_ofNat] using matrixMultiplicity
  have rankNonzero : Cardinal.lift.{1}
      (Module.rank RaisedQuaternionMatrixᵐᵒᵖ RaisedQuaternionRow) ≠ 0 := by
    intro zeroRank
    rw [zeroRank, mul_zero] at impossible
    norm_num at impossible
  have bound : (2 : Cardinal.{1}) ≤ 1 := by
    rw [impossible]
    exact Cardinal.le_mul_right rankNonzero
  norm_num at bound

private theorem raised_quaternion_regular_values :
    @Module.rank (Quaternion ℚ)ᵐᵒᵖ RaisedQuaternionRingᵐᵒᵖ inferInstance inferInstance
      (Module.compHom RaisedQuaternionRingᵐᵒᵖ (RingHom.op (chosenScalar
        RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
        raisedQuaternionPresentation))) = 4 ∧
    (chosenIsotypic RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
      raisedQuaternionPresentation RaisedQuaternionRingᵐᵒᵖ).multiplicity = 2 ∧
    Module.rank RaisedQuaternionRingᵐᵒᵖ RaisedQuaternionRingᵐᵒᵖ = 1 := by
  let : Module (Quaternion ℚ)ᵐᵒᵖ RaisedQuaternionRingᵐᵒᵖ :=
    Module.compHom RaisedQuaternionRingᵐᵒᵖ (RingHom.op (chosenScalar
      RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
      raisedQuaternionPresentation))
  let : Module (Quaternion ℚ)ᵐᵒᵖ RaisedQuaternionMatrixᵐᵒᵖ :=
    Module.compHom RaisedQuaternionMatrixᵐᵒᵖ
      (RingHom.op (Matrix.scalar RaisedQuaternionIndex))
  have matrixScalarRank : Module.rank (Quaternion ℚ)ᵐᵒᵖ
      RaisedQuaternionMatrixᵐᵒᵖ = 4 := by
    have formula := free_matrix_scalar_rank RaisedQuaternionIndex (Quaternion ℚ)
      (M := RaisedQuaternionMatrixᵐᵒᵖ)
    norm_num [Module.rank_self, Fintype.card_ulift, Fintype.card_fin] at formula ⊢
    exact formula
  have matrixMultiplicity : (IsSimpleRing.isIsotypicOfType
      RaisedQuaternionMatrixᵐᵒᵖ RaisedQuaternionMatrixᵐᵒᵖ
      RaisedQuaternionRow).multiplicity = 2 := by
    have formula := free_matrix_row_multiplicity RaisedQuaternionIndex (Quaternion ℚ)
      (M := RaisedQuaternionMatrixᵐᵒᵖ)
    simpa [Module.rank_self, Fintype.card_ulift, Fintype.card_fin] using formula
  have scalarTransport : Cardinal.lift.{1} (Module.rank (Quaternion ℚ)ᵐᵒᵖ
      RaisedQuaternionRingᵐᵒᵖ) = Cardinal.lift.{2} (Module.rank (Quaternion ℚ)ᵐᵒᵖ
      RaisedQuaternionMatrixᵐᵒᵖ) := by
    apply lift_rank_eq_of_equiv_equiv (Equiv.refl (Quaternion ℚ)ᵐᵒᵖ)
      (chosenOppEquiv RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
        raisedQuaternionPresentation).toAddEquiv
        (Equiv.refl (Quaternion ℚ)ᵐᵒᵖ).bijective
    intro scalar value
    change (chosenOppEquiv RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
      raisedQuaternionPresentation) (((RingHom.op (chosenScalar RaisedQuaternionRing
      RaisedQuaternionIndex (Quaternion ℚ) raisedQuaternionPresentation)) scalar) * value) =
      (RingHom.op (Matrix.scalar RaisedQuaternionIndex)) scalar *
        (chosenOppEquiv RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
          raisedQuaternionPresentation) value
    rw [map_mul, chosen_scalar_compatibility]
  have multiplicityTransport :=
    (chosenIsotypic RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
      raisedQuaternionPresentation RaisedQuaternionRingᵐᵒᵖ).lift_multiplicity_eq_of_semilinearEquiv
        (IsSimpleRing.isIsotypicOfType RaisedQuaternionMatrixᵐᵒᵖ
          RaisedQuaternionMatrixᵐᵒᵖ RaisedQuaternionRow)
        (chosenOppEquiv RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
          raisedQuaternionPresentation)
        (chosenOppEquiv RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
          raisedQuaternionPresentation).toSemilinearEquiv
        (chosenRowEquiv RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
          raisedQuaternionPresentation)
  refine ⟨?_, ?_, Module.rank_self _⟩
  · simpa [matrixScalarRank] using scalarTransport
  · rw [Cardinal.lift_id'.{1, 2}] at multiplicityTransport
    simpa only [matrixMultiplicity, Cardinal.lift_ofNat] using multiplicityTransport

private theorem raised_quaternion_zero_values :
    @Module.rank (Quaternion ℚ)ᵐᵒᵖ (Fin 0 →₀ RaisedQuaternionRingᵐᵒᵖ)
      inferInstance inferInstance
      (Module.compHom _ (RingHom.op (chosenScalar RaisedQuaternionRing
        RaisedQuaternionIndex (Quaternion ℚ) raisedQuaternionPresentation))) = 0 ∧
    (chosenIsotypic RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
      raisedQuaternionPresentation (Fin 0 →₀ RaisedQuaternionRingᵐᵒᵖ)).multiplicity = 0 ∧
    Module.rank RaisedQuaternionRingᵐᵒᵖ (Fin 0 →₀ RaisedQuaternionRingᵐᵒᵖ) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact @rank_subsingleton' (Quaternion ℚ)ᵐᵒᵖ
      (Fin 0 →₀ RaisedQuaternionRingᵐᵒᵖ) inferInstance inferInstance
      (Module.compHom _ (RingHom.op (chosenScalar RaisedQuaternionRing
        RaisedQuaternionIndex (Quaternion ℚ) raisedQuaternionPresentation)))
      inferInstance inferInstance
  · exact IsIsotypicOfType.multiplicity_eq_zero_of_subsingleton _
  · simp

private theorem raised_quaternion_three_free_rank :
    Module.rank RaisedQuaternionRingᵐᵒᵖ
      (Fin 3 →₀ RaisedQuaternionRingᵐᵒᵖ) = 3 := by
  rw [rank_finsupp_self, Cardinal.mk_fintype, Fintype.card_fin,
    Cardinal.lift_natCast]
  norm_num

private theorem raised_quaternion_infinite_free_rank :
    ℵ₀ ≤ Module.rank RaisedQuaternionRingᵐᵒᵖ
      (ULift.{3} ℕ →₀ RaisedQuaternionRingᵐᵒᵖ) := by
  rw [rank_finsupp_self, Cardinal.lift_id'.{2, 3} (#(ULift.{3} ℕ))]
  exact Cardinal.aleph0_le_mk (ULift.{3} ℕ)

/-- The chosen right-scalar rank of the quaternion row is twice its row multiplicity. -/
private theorem raised_quaternion_row_scalar_multiplicity_formula :
    Cardinal.lift.{2} (@Module.rank (Quaternion ℚ)ᵐᵒᵖ RaisedQuaternionRow
      inferInstance inferInstance (Module.compHom RaisedQuaternionRow
        (RingHom.op (chosenScalar RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
          raisedQuaternionPresentation)))) =
      (2 : Cardinal.{2}) * Cardinal.lift.{2}
        (chosenIsotypic RaisedQuaternionRing RaisedQuaternionIndex (Quaternion ℚ)
          raisedQuaternionPresentation RaisedQuaternionRow).multiplicity := by
  simpa only [Fintype.card_ulift, Fintype.card_fin, Nat.cast_ofNat] using
    chosen_scalar_rank_eq_card_mul_multiplicity RaisedQuaternionRing RaisedQuaternionIndex
      (Quaternion ℚ) raisedQuaternionPresentation RaisedQuaternionRow

/-- The row multiplicity and right-scalar rank of the infinite free quaternion module
are respectively two and four times its free rank. -/
private theorem raised_quaternion_infinite_rank_formulas :
    let M := ULift.{3} ℕ →₀ RaisedQuaternionRingᵐᵒᵖ
    let isotypic := chosenIsotypic RaisedQuaternionRing RaisedQuaternionIndex
      (Quaternion ℚ) raisedQuaternionPresentation M
    Cardinal.lift.{2} (@Module.rank (Quaternion ℚ)ᵐᵒᵖ M inferInstance inferInstance
      (Module.compHom M (RingHom.op (chosenScalar RaisedQuaternionRing
        RaisedQuaternionIndex (Quaternion ℚ) raisedQuaternionPresentation)))) =
        (2 : Cardinal.{3}) * Cardinal.lift.{2} isotypic.multiplicity ∧
    Cardinal.lift.{2} isotypic.multiplicity =
        (2 : Cardinal.{3}) * Cardinal.lift.{2}
          (Module.rank RaisedQuaternionRingᵐᵒᵖ M) ∧
    Cardinal.lift.{2} (@Module.rank (Quaternion ℚ)ᵐᵒᵖ M inferInstance inferInstance
      (Module.compHom M (RingHom.op (chosenScalar RaisedQuaternionRing
        RaisedQuaternionIndex (Quaternion ℚ) raisedQuaternionPresentation)))) =
        (4 : Cardinal.{3}) * Cardinal.lift.{2}
          (Module.rank RaisedQuaternionRingᵐᵒᵖ M) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_ulift, Fintype.card_fin, Nat.cast_ofNat] using
      chosen_scalar_rank_eq_card_mul_multiplicity RaisedQuaternionRing
        RaisedQuaternionIndex (Quaternion ℚ) raisedQuaternionPresentation
        (ULift.{3} ℕ →₀ RaisedQuaternionRingᵐᵒᵖ)
  · simpa only [Fintype.card_ulift, Fintype.card_fin, Nat.cast_ofNat] using
      chosen_free_row_multiplicity RaisedQuaternionRing RaisedQuaternionIndex
        (Quaternion ℚ) raisedQuaternionPresentation
        (ULift.{3} ℕ →₀ RaisedQuaternionRingᵐᵒᵖ)
  · simpa only [Fintype.card_ulift, Fintype.card_fin, Nat.cast_ofNat,
      show (2 : Cardinal.{3}) ^ 2 = 4 by norm_num] using
      chosen_free_scalar_rank RaisedQuaternionRing RaisedQuaternionIndex
        (Quaternion ℚ) raisedQuaternionPresentation
        (ULift.{3} ℕ →₀ RaisedQuaternionRingᵐᵒᵖ)

end RaisedQuaternionPresentation

end

end ProjectiveModulesTests.FreeMatrixRankClient
