/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Dual.ModuleCat
public import Mathlib.Data.Matrix.Basis

/-!
# The right-module dual on noncommuting integer matrices

The ordinary carrier of `M₂(ℤ)` has its canonical right regular action by the
opposite ring. Mathlib's `LinearMap.mulLeft` supplies both the right-linear
functions and the source morphisms used here. The public object, map and scalar
interfaces of `ModuleCat.rightDual` compute precomposition and the left
coefficient action without unfolding the functor.

The matrix units `p = e₁₁` and `q = e₁₂` distinguish multiplication order:
`p * q = q ≠ 0`, whereas `q * p = 0`. Changing the source morphism or the left
scalar gives distinct nonzero values. Contravariant composition has the nonzero
value `q`, and the reversed order has value zero. The raw function `x ↦ x * p`
fails right linearity and is not packaged as a linear map or a scalar action.

## References

* Mathlib's matrix-unit multiplication, opposite-module action, `LinearMap.mulLeft`
  and categorical functor interfaces.
* `ProjectiveModules.Module.RightRegular`, for the ordinary right regular module.
* `ProjectiveModules.Dual.ModuleCat`, for right-module dual precomposition.
-/

@[expose] public section

namespace ProjectiveModulesTests.RightDualFunctorClient

open CategoryTheory

/-- The canonical two-by-two matrix ring over the integers. -/
abbrev MatrixRing := Matrix (Fin 2) (Fin 2) ℤ

/-- The first diagonal matrix unit. -/
def p : MatrixRing := Matrix.single 0 0 1

/-- The upper-right matrix unit. -/
def q : MatrixRing := Matrix.single 0 1 1

/-- The ordinary matrix carrier with its canonical right regular action. -/
abbrev matrixModule := ModuleCat.of MatrixRingᵐᵒᵖ MatrixRing

/-- An existing right-linear left-multiplication map, bundled as a source arrow. -/
def leftMul (a : MatrixRing) : matrixModule ⟶ matrixModule :=
  ModuleCat.ofHom (LinearMap.mulLeft MatrixRingᵐᵒᵖ a)

/-- The same existing right-linear map, viewed as an element of the dual object. -/
def dualMap (a : MatrixRing) :
    (ModuleCat.rightDual MatrixRing).obj (Opposite.op matrixModule) :=
  LinearMap.mulLeft MatrixRingᵐᵒᵖ a

/-- The matrix-unit multiplication API gives the nonzero ordered product. -/
theorem p_mul_q : p * q = q := by
  simp [p, q]

/-- The reversed matrix-unit product vanishes. -/
theorem q_mul_p : q * p = 0 := by
  simp [q, p]

/-- The diagonal matrix unit is nonzero, witnessed by its first diagonal entry. -/
theorem p_ne_zero : p ≠ 0 := by
  intro h
  have hentry : (1 : ℤ) = 0 := by
    simpa [p] using congrArg (fun a : MatrixRing ↦ a 0 0) h
  exact one_ne_zero hentry

/-- The upper-right matrix unit is nonzero, witnessed by its upper-right entry. -/
theorem q_ne_zero : q ≠ 0 := by
  intro h
  have hentry : (1 : ℤ) = 0 := by
    simpa [q] using congrArg (fun a : MatrixRing ↦ a 0 1) h
  exact one_ne_zero hentry

/-- The two nonzero matrix units are distinct. -/
theorem p_ne_q : p ≠ q := by
  intro h
  have hentry : (1 : ℤ) = 0 := by
    simpa [p, q] using congrArg (fun a : MatrixRing ↦ a 0 0) h
  exact one_ne_zero hentry

/-- The coefficient ring is genuinely noncommutative on the selected units. -/
theorem p_not_commute_q : ¬ Commute p q := by
  intro h
  have hmul := h.eq
  rw [p_mul_q, q_mul_p] at hmul
  exact q_ne_zero hmul

/-- Source left multiplication is the provider, not a replacement action. -/
theorem leftMul_apply (a x : MatrixRing) : leftMul a x = a * x :=
  LinearMap.mulLeft_apply MatrixRingᵐᵒᵖ a x

/-- The dual element evaluates by left multiplication. -/
theorem dualMap_apply (a x : MatrixRing) : dualMap a x = a * x :=
  LinearMap.mulLeft_apply MatrixRingᵐᵒᵖ a x

/-- The public object interface retains ordinary right-linear matrix functions. -/
theorem dual_object :
    (ModuleCat.rightDual MatrixRing).obj (Opposite.op matrixModule) =
      ModuleCat.of MatrixRing (MatrixRing →ₗ[MatrixRingᵐᵒᵖ] MatrixRing) :=
  ModuleCat.rightDual_obj MatrixRing (Opposite.op matrixModule)

/-- The canonical opposite scalar multiplies on the right of the source carrier. -/
theorem source_right_action (b x : MatrixRing) : MulOpposite.op b • x = x * b :=
  op_smul_eq_mul b x

/-- The selected dual elements satisfy the inherited right-linearity law. -/
theorem dualMap_right_action (a b x : MatrixRing) :
    dualMap a (MulOpposite.op b • x) = dualMap a x * b := by
  simpa only [op_smul_eq_mul] using
    (dualMap a).map_smul (MulOpposite.op b) x

/-- The public morphism interface is the left-linear precomposition provider. -/
theorem precomposition_hom (b : MatrixRing) :
    ((ModuleCat.rightDual MatrixRing).map (leftMul b).op).hom =
      LinearMap.lcomp MatrixRing MatrixRing (LinearMap.mulLeft MatrixRingᵐᵒᵖ b) :=
  ModuleCat.rightDual_map_hom MatrixRing (leftMul b).op

/-- Applied precomposition keeps the order of the two left coefficients. -/
theorem precomposition_apply (a b x : MatrixRing) :
    (ModuleCat.rightDual MatrixRing).map (leftMul b).op (dualMap a) x =
      a * (b * x) := by
  rw [ModuleCat.rightDual_map_apply, Quiver.Hom.unop_op, leftMul_apply, dualMap_apply]

/-- Precomposition gives equality of right-linear maps, not only one evaluation. -/
theorem precomposition_dualMap (a b : MatrixRing) :
    (ModuleCat.rightDual MatrixRing).map (leftMul b).op (dualMap a) =
      dualMap (a * b) := by
  apply LinearMap.ext
  intro x
  rw [precomposition_apply, dualMap_apply, mul_assoc]

/-- At the unit, the applied map exposes the ordered coefficient product. -/
theorem precomposition_at_one (a b : MatrixRing) :
    (ModuleCat.rightDual MatrixRing).map (leftMul b).op (dualMap a) (1 : MatrixRing) =
      a * b := by
  rw [precomposition_apply, mul_one]

/-- A nonzero coefficient gives a nonzero dual element. -/
theorem dualMap_ne_zero {a : MatrixRing} (ha : a ≠ 0) : dualMap a ≠ 0 := by
  intro h
  apply ha
  have hvalue :=
    congrArg (fun f : (ModuleCat.rightDual MatrixRing).obj (Opposite.op matrixModule) ↦
      f (1 : MatrixRing)) h
  rw [dualMap_apply, mul_one, LinearMap.zero_apply] at hvalue
  exact hvalue

/-- The distinct nonzero coefficients give distinct nonzero dual elements. -/
theorem dualMap_p_q_ne_zero_and_ne :
    dualMap p ≠ 0 ∧ dualMap q ≠ 0 ∧ dualMap p ≠ dualMap q := by
  refine ⟨dualMap_ne_zero p_ne_zero, dualMap_ne_zero q_ne_zero, ?_⟩
  intro h
  apply p_ne_q
  have hvalue :=
    congrArg (fun f : (ModuleCat.rightDual MatrixRing).obj (Opposite.op matrixModule) ↦
      f (1 : MatrixRing)) h
  rw [dualMap_apply p 1, dualMap_apply q 1, mul_one, mul_one] at hvalue
  exact hvalue

/-- Identity precomposition fixes the specified nonzero dual element. -/
theorem identity_on_q_ne_zero :
    (ModuleCat.rightDual MatrixRing).map (𝟙 (Opposite.op matrixModule)) (dualMap q) =
        dualMap q ∧
      dualMap q (1 : MatrixRing) = q ∧ q ≠ 0 := by
  refine ⟨?_, ?_, q_ne_zero⟩
  · rw [CategoryTheory.Functor.map_id]
    exact ModuleCat.id_apply _ _
  · rw [dualMap_apply, mul_one]

/-- Changing the source morphism gives two distinct nonzero evaluated values. -/
theorem moving_morphism_values :
    (ModuleCat.rightDual MatrixRing).map (leftMul p).op (dualMap 1) (1 : MatrixRing) = p ∧
      (ModuleCat.rightDual MatrixRing).map (leftMul q).op (dualMap 1) (1 : MatrixRing) = q ∧
      p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q := by
  refine ⟨?_, ?_, p_ne_zero, q_ne_zero, p_ne_q⟩
  · rw [precomposition_at_one, one_mul]
  · rw [precomposition_at_one, one_mul]

/-- Changing the morphism also gives distinct nonzero elements of the dual object. -/
theorem precomposition_p_q_ne_zero_and_ne :
    (ModuleCat.rightDual MatrixRing).map (leftMul p).op (dualMap 1) ≠ 0 ∧
      (ModuleCat.rightDual MatrixRing).map (leftMul q).op (dualMap 1) ≠ 0 ∧
      (ModuleCat.rightDual MatrixRing).map (leftMul p).op (dualMap 1) ≠
        (ModuleCat.rightDual MatrixRing).map (leftMul q).op (dualMap 1) := by
  rw [precomposition_dualMap 1 p, precomposition_dualMap 1 q, one_mul, one_mul]
  exact dualMap_p_q_ne_zero_and_ne

/-- The two moving dual morphisms differ, as witnessed on the same input at the unit. -/
theorem moving_morphisms_distinct :
    (ModuleCat.rightDual MatrixRing).map (leftMul p).op ≠
      (ModuleCat.rightDual MatrixRing).map (leftMul q).op := by
  intro h
  apply p_ne_q
  have hvalue :=
    congrArg (fun k :
      (ModuleCat.rightDual MatrixRing).obj (Opposite.op matrixModule) ⟶
        (ModuleCat.rightDual MatrixRing).obj (Opposite.op matrixModule) ↦
      k (dualMap 1) (1 : MatrixRing)) h
  rw [precomposition_at_one 1 p, precomposition_at_one 1 q, one_mul, one_mul] at hvalue
  exact hvalue

/-- The scalar interface acts on the left by associativity, not by centrality. -/
theorem scalar_apply (r a x : MatrixRing) :
    (r • dualMap a) x = r * (a * x) := by
  rw [ModuleCat.rightDual_smul_apply MatrixRing (X := Opposite.op matrixModule),
    dualMap_apply]

/-- At the unit, the left coefficient action changes the dual element nontrivially. -/
theorem scalar_at_one (r a : MatrixRing) :
    (r • dualMap a) (1 : MatrixRing) = r * a := by
  rw [scalar_apply, mul_one]

/-- Changing the scalar gives two distinct nonzero evaluated values. -/
theorem moving_scalar_values :
    (p • dualMap 1) (1 : MatrixRing) = p ∧
      (q • dualMap 1) (1 : MatrixRing) = q ∧
      p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q := by
  refine ⟨?_, ?_, p_ne_zero, q_ne_zero, p_ne_q⟩
  · rw [scalar_at_one, mul_one]
  · rw [scalar_at_one, mul_one]

/-- The changed left scalars produce distinct dual elements. -/
theorem moving_scalars_distinct : p • dualMap 1 ≠ q • dualMap 1 := by
  intro h
  apply p_ne_q
  have hvalue :=
    congrArg (fun f : (ModuleCat.rightDual MatrixRing).obj (Opposite.op matrixModule) ↦
      f (1 : MatrixRing)) h
  rw [scalar_at_one p 1, scalar_at_one q 1, mul_one, mul_one] at hvalue
  exact hvalue

/-- Precomposition commutes with the noncentral left scalar on a nonzero output. -/
theorem noncentral_scalar_precomposition :
    (ModuleCat.rightDual MatrixRing).map (leftMul q).op (p • dualMap 1)
        (1 : MatrixRing) = q ∧
      (p • (ModuleCat.rightDual MatrixRing).map (leftMul q).op (dualMap 1))
        (1 : MatrixRing) = q ∧ q ≠ 0 := by
  refine ⟨?_, ?_, q_ne_zero⟩
  · rw [ModuleCat.rightDual_map_apply, Quiver.Hom.unop_op, leftMul_apply,
      scalar_apply, mul_one, one_mul, p_mul_q]
  · rw [ModuleCat.rightDual_smul_apply MatrixRing (X := Opposite.op matrixModule),
      precomposition_at_one, one_mul, p_mul_q]

/-- The input coefficient and source morphism expose both ordered products. -/
theorem ordered_precomposition_values :
    (ModuleCat.rightDual MatrixRing).map (leftMul q).op (dualMap p) (1 : MatrixRing) = q ∧
      (ModuleCat.rightDual MatrixRing).map (leftMul p).op (dualMap q) (1 : MatrixRing) = 0 ∧
      q ≠ 0 := by
  refine ⟨?_, ?_, q_ne_zero⟩
  · rw [precomposition_at_one, p_mul_q]
  · rw [precomposition_at_one, q_mul_p]

/-- Source composition puts the later left coefficient first. -/
theorem leftMul_comp (b c : MatrixRing) :
    leftMul b ≫ leftMul c = leftMul (c * b) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [leftMul, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_assoc]

/-- The selected source composite is the nonzero upper-right multiplication map. -/
theorem source_composite : leftMul q ≫ leftMul p = leftMul q := by
  rw [leftMul_comp, p_mul_q]

/-- Opposite-category composition reverses the two selected source morphisms. -/
theorem opposite_composite : (leftMul p).op ≫ (leftMul q).op = (leftMul q).op := by
  rw [← CategoryTheory.op_comp, source_composite]

/-- The public functor law preserves composition in the opposite category. -/
theorem dual_functor_composition :
    (ModuleCat.rightDual MatrixRing).map ((leftMul p).op ≫ (leftMul q).op) =
      (ModuleCat.rightDual MatrixRing).map (leftMul p).op ≫
        (ModuleCat.rightDual MatrixRing).map (leftMul q).op :=
  CategoryTheory.Functor.map_comp (ModuleCat.rightDual MatrixRing)
    (leftMul p).op (leftMul q).op

/-- The mapped opposite composite has the required nonzero value. -/
theorem mapped_composite_at_one :
    (ModuleCat.rightDual MatrixRing).map ((leftMul p).op ≫ (leftMul q).op)
      (dualMap 1) (1 : MatrixRing) = q := by
  rw [opposite_composite, precomposition_at_one, one_mul]

/-- Correct contravariant order gives `q`, whereas the false covariant order gives zero. -/
theorem composition_order_values :
    (ModuleCat.rightDual MatrixRing).map (leftMul q).op
        ((ModuleCat.rightDual MatrixRing).map (leftMul p).op (dualMap 1))
        (1 : MatrixRing) = q ∧
      (ModuleCat.rightDual MatrixRing).map (leftMul p).op
        ((ModuleCat.rightDual MatrixRing).map (leftMul q).op (dualMap 1))
        (1 : MatrixRing) = 0 ∧ q ≠ 0 := by
  refine ⟨?_, ?_, q_ne_zero⟩
  · rw [ModuleCat.rightDual_map_apply, Quiver.Hom.unop_op, leftMul_apply,
      mul_one, precomposition_apply, one_mul, p_mul_q]
  · rw [ModuleCat.rightDual_map_apply, Quiver.Hom.unop_op, leftMul_apply,
      mul_one, precomposition_apply, one_mul, q_mul_p]

/-- The raw right-coefficient function fails the scalar law at `1` and `op q`. -/
theorem raw_right_coefficient_values :
    (MulOpposite.op q • (1 : MatrixRing)) * p = 0 ∧
      MulOpposite.op q • ((1 : MatrixRing) * p) = q ∧ q ≠ 0 := by
  refine ⟨?_, ?_, q_ne_zero⟩
  · rw [op_smul_eq_mul, one_mul, q_mul_p]
  · rw [op_smul_eq_mul, one_mul, p_mul_q]

/-- The function `x ↦ x * p` is not right-linear; no linear-map package is asserted. -/
theorem raw_right_coefficient_not_right_linear :
    ¬ ∀ (c : MatrixRingᵐᵒᵖ) (x : MatrixRing), (c • x) * p = c • (x * p) := by
  intro h
  have hwrong : (0 : MatrixRing) = q := by
    simpa only [op_smul_eq_mul, mul_one, one_mul, q_mul_p, p_mul_q] using
      h (MulOpposite.op q) (1 : MatrixRing)
  exact q_ne_zero hwrong.symm

end ProjectiveModulesTests.RightDualFunctorClient
