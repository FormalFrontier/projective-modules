/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.IsotypicMultiplicity
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Simple right matrix rows

The canonical action of the opposite square matrix ring on a row is
`A • v = v ᵥ* A.unop`. Over a division ring and a finite nonempty index type,
this row is simple. Every module over that opposite matrix ring is isotypic
of this fixed type, hence is a direct sum of copies of the row; the sum may
be infinite or empty. Multiplicities and comparisons of different sums use
`IsIsotypicOfType.multiplicity` and its existing cardinality API.

## References

Charles A. Weibel, *The K-book*, Example I.1.1.1, motivates the
matrix-ring example. Mathlib's `Matrix` action and semisimple/isotypic
module interfaces provide the canonical representations and decomposition.
-/

@[expose] public section

universe u v w x

namespace IsSimpleRing

/-- Every module over a semisimple simple ring is isotypic of any fixed
simple-module type, including the zero module. This refines Mathlib's
`IsSimpleRing.isIsotypic` by specifying the simple type. -/
theorem isIsotypicOfType (R : Type u) [Ring R] [IsSimpleRing R]
    [IsSemisimpleRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (S : Type w) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    IsIsotypicOfType R M S := by
  classical
  have : IsArtinianRing R := inferInstance
  intro N _
  obtain ⟨I, ⟨eI⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R N
  obtain ⟨J, ⟨eJ⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R S
  have : IsSimpleModule R I := IsSimpleModule.congr eI.symm
  have : IsSimpleModule R J := IsSimpleModule.congr eJ.symm
  exact ⟨eI.trans (((isIsotypic R R) J I).some) |>.trans eJ.symm⟩

end IsSimpleRing

namespace Matrix

variable (ι : Type v) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (D : Type u) [DivisionRing D]

/-- The canonical right row of a matrix ring over a division ring is simple;
the opposite-ring action is given by `Matrix.op_smul_eq_vecMul`.
The row is the simple type in Weibel, *The K-book*, Example I.1.1.1. -/
instance (priority := low) instIsSimpleModuleVecMul :
    IsSimpleModule (Matrix ι ι D)ᵐᵒᵖ (ι → D) := by
  classical
  refine isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨inferInstance, ?_⟩
  intro row hrow target
  obtain ⟨index, hindex⟩ : ∃ index, row index ≠ 0 := by
    by_contra h
    push Not at h
    exact hrow (funext h)
  let transform : Matrix ι ι D := Matrix.of fun source column =>
    if source = index then (row index)⁻¹ * target column else 0
  refine ⟨MulOpposite.op transform, ?_⟩
  change row ᵥ* transform = target
  funext column
  simp [transform, Matrix.vecMul_apply_eq_sum, hindex]

/-- Every right module over a matrix ring over a division ring is a direct
sum of copies of its canonical row, with no bound on the number of copies. -/
theorem exists_linearEquiv_finsupp_vecMul
    (M : Type w) [AddCommGroup M] [Module (Matrix ι ι D)ᵐᵒᵖ M] :
    ∃ κ : Type w, Nonempty (M ≃ₗ[(Matrix ι ι D)ᵐᵒᵖ] (κ →₀ ι → D)) := by
  have : IsSemisimpleRing D := inferInstance
  have : IsSemisimpleRing (Matrix ι ι D)ᵐᵒᵖ := inferInstance
  exact (IsSimpleRing.isIsotypicOfType (Matrix ι ι D)ᵐᵒᵖ M (ι → D)).linearEquiv_finsupp

end Matrix
