/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.MatrixRow
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Scalar rank and fixed-simple multiplicity

For a semisimple module consisting of copies of a fixed simple module, compatible
scalar actions relate its scalar rank to the rank of one copy and its cardinal
multiplicity. The matrix-row specialization restricts the opposite matrix action
along the opposite of `Matrix.scalar`; it works over noncommutative division rings
and does not assume that the matrix module is free.

## References

Charles A. Weibel, *The K-book*, Example I.1.1.1, motivates the matrix-row
dimension identity. The generic scalar-rank statement applies to arbitrary
simple types, beyond the simple Artinian matrix example. Mathlib's
`rank_finsupp` and `LinearEquiv.restrictScalars` supply the scalar and
direct-sum interfaces.
-/

@[expose] public section

noncomputable section

universe u v w x

namespace IsIsotypicOfType

variable {A : Type u} {F : Type v} {S : Type w} {M : Type x}
  [Ring A] [Semiring F]
  [AddCommGroup S] [Module A S] [Module F S] [Module.Free F S]
  [AddCommGroup M] [Module A M] [IsSemisimpleModule A M] [Module F M]
  [LinearMap.CompatibleSMul S M F A]

/-- An isotypic semisimple module is free over compatible scalars whenever
its fixed simple type is free over those scalars. No freeness over `A` is needed. -/
theorem free_restrictScalars (h : IsIsotypicOfType A M S) : Module.Free F M := by
  obtain ⟨ι, ⟨e⟩⟩ := h.linearEquiv_finsupp
  exact Module.Free.of_equiv (e.symm.restrictScalars F)

variable [IsSimpleModule A S] [StrongRankCondition F]

/-- Over a scalar semiring satisfying the strong rank condition, the scalar
rank of an isotypic semisimple module is the scalar rank of its fixed simple
type times its cardinal multiplicity when that simple type is free over the
scalars. All ranks are lifted to a common universe; the ambient module need
not be free over `A`. -/
theorem lift_rank_eq_mul_multiplicity (h : IsIsotypicOfType A M S) :
    Cardinal.lift.{w} (Module.rank F M) =
      Cardinal.lift.{x} (Module.rank F S) * h.multiplicity := by
  classical
  have : Module.Free F M := h.free_restrictScalars
  obtain ⟨ι, ⟨e⟩⟩ := h.linearEquiv_finsupp
  have rankEquality := (e.symm.restrictScalars F).lift_rank_eq
  have multiplicityEquality := h.lift_multiplicity_eq_of_linearEquiv_finsupp e
  calc
    Cardinal.lift.{w} (Module.rank F M) =
        Cardinal.lift.{x} (Module.rank F S) *
          Cardinal.lift.{max x w} (Cardinal.mk ι) := by
      have rankEquality' :
          Cardinal.lift.{w} (Module.rank F M) =
            Cardinal.lift.{x} (Module.rank F (ι →₀ S)) := by
        exact (congrFun (Cardinal.lift_umax.{x, w}) (Module.rank F M)).symm.trans
          rankEquality.symm
      rw [rankEquality', rank_finsupp, Cardinal.lift_mul]
      simp only [Cardinal.lift_lift]
      rw [mul_comm]
    _ = Cardinal.lift.{x} (Module.rank F S) * h.multiplicity := by
      rw [← multiplicityEquality, Cardinal.lift_id'.{x, w} h.multiplicity]

end IsIsotypicOfType

namespace Matrix

section Auxiliary

variable (ι : Type v) [Fintype ι] (D : Type u) [Semiring D]

section ScalarRow

variable [DecidableEq ι]

/-- Restriction of the canonical row action along the opposite of
`Matrix.scalar` is componentwise right multiplication, not left multiplication. -/
theorem op_scalar_smul_row (a : Dᵐᵒᵖ) (row : ι → D) :
    (RingHom.op (Matrix.scalar ι)) a • row = a • row := by
  classical
  funext index
  simp [Matrix.op_smul_eq_vecMul, Matrix.scalar_apply, Matrix.vecMul_diagonal,
    MulOpposite.smul_eq_mul_unop]

/-- Restriction along the opposite of `Matrix.scalar` gives precisely the
canonical pointwise right-scalar module structure on the row. -/
theorem op_scalar_module_row :
    (Module.compHom (ι → D) (RingHom.op (Matrix.scalar ι)) : Module Dᵐᵒᵖ (ι → D)) =
      (inferInstance : Module Dᵐᵒᵖ (ι → D)) := by
  apply Module.ext'
  intro a row
  exact op_scalar_smul_row ι D a row

end ScalarRow

section RowRank

variable [StrongRankCondition Dᵐᵒᵖ]

/-- The right-scalar rank of the canonical row is the number of columns. -/
theorem rank_row_op_scalar : Module.rank Dᵐᵒᵖ (ι → D) = Fintype.card ι := by
  calc
    Module.rank Dᵐᵒᵖ (ι → D) = Module.rank Dᵐᵒᵖ (ι → Dᵐᵒᵖ) :=
      ((LinearEquiv.piCongrRight fun _ : ι =>
        (MulOpposite.opLinearEquiv Dᵐᵒᵖ).symm).symm).rank_eq
    _ = Fintype.card ι := rank_fun' (R := Dᵐᵒᵖ)

end RowRank

end Auxiliary

variable (ι : Type v) [Fintype ι] (D : Type u) [DivisionRing D]
variable [DecidableEq ι] [Nonempty ι]
variable {M : Type w} [AddCommGroup M] [Module (Matrix ι ι D)ᵐᵒᵖ M]

/-- Every right module over a square matrix ring over `D` has right-scalar
rank equal to the row size times its fixed-row cardinal multiplicity.
The scalar action on `M` is restriction along the opposite of
`Matrix.scalar`; there is no matrix-ring freeness assumption.
This cardinal-multiplicity dimension identity for arbitrary right modules is
motivated by Charles A. Weibel, *The K-book*, Example I.1.1.1; that example's
separate free matrix-ring rank formulas are not asserted here. -/
theorem lift_rank_op_scalar_eq_card_mul_multiplicity :
    Cardinal.lift.{max u v}
        (@Module.rank Dᵐᵒᵖ M inferInstance inferInstance
          (Module.compHom M (RingHom.op (Matrix.scalar ι)))) =
      (Fintype.card ι : Cardinal.{max u v w}) *
        (IsSimpleRing.isIsotypicOfType (Matrix ι ι D)ᵐᵒᵖ M (ι → D)).multiplicity := by
  let _ : Module Dᵐᵒᵖ M := Module.compHom M (RingHom.op (Matrix.scalar ι))
  have : Module.Free Dᵐᵒᵖ (ι → D) :=
    Module.Free.of_equiv (LinearEquiv.piCongrRight fun _ : ι =>
      (MulOpposite.opLinearEquiv Dᵐᵒᵖ).symm)
  have : LinearMap.CompatibleSMul (ι → D) M Dᵐᵒᵖ (Matrix ι ι D)ᵐᵒᵖ := by
    constructor
    intro f a row
    calc
      f (a • row) = f ((RingHom.op (Matrix.scalar ι)) a • row) :=
        congrArg f (op_scalar_smul_row ι D a row).symm
      _ = (RingHom.op (Matrix.scalar ι)) a • f row := f.map_smul _ _
      _ = a • f row := rfl
  have : IsSemisimpleRing (Matrix ι ι D)ᵐᵒᵖ := inferInstance
  let h := IsSimpleRing.isIsotypicOfType (Matrix ι ι D)ᵐᵒᵖ M (ι → D)
  have scalarRank := h.lift_rank_eq_mul_multiplicity (F := Dᵐᵒᵖ)
  simpa only [rank_row_op_scalar, Cardinal.lift_natCast] using scalarRank

end Matrix
