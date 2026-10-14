/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.RightExtensionTensorProduct
public import Mathlib.Data.ZMod.Defs
import ProjectiveModulesTests.RightFreeScalarExtensionClient
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.PUnit
import Mathlib.Algebra.Module.ULift
import Mathlib.Tactic.NormNum

/-!
# Tensor-agreement clients

Integer reduction modulo five is noninjective, but its rank-one extended unit
is nonzero. Finite-free coordinates detect this before applying the tensor
comparison. Integer matrix coefficients distinguish right multiplication from
its reversed order, and instantiate the comparison without a commutative
coefficient ring. A diagonal homomorphism from a function ring into the
matrices has noncentral image and exercises the same comparison. A swapped endomorphism
on a product ring distinguishes the specified coefficient action from the
regular self-action, including when the module and both rings have the same
underlying carrier.

Zero modules, zero coefficients and an all-zero example use unital ring
homomorphisms. Source scalars, coefficient scalars and module carriers are lifted
independently. The categorical examples use the module-first tensor functor,
including its identity and composition laws, and the specified Mathlib object
and maps.
The direct tensor morphism moves the modulo-five unit from coefficient one
to coefficient two. The existing pointwise comparison independently identifies
it with right extension of the doubling morphism.

The integer matrix type is the public provider in
`RightFreeScalarExtensionClient`. Nonzero extended coordinates use this
library's right-free extension API.
Mathlib's balanced tensor evaluation detects nonzero tensor coefficients
independently of the comparison maps; matrix units, scalar views and lifts
use Mathlib.
The nonzero rank-one tensor modulo five is a public example; the other
declarations are private importing examples.
-/

noncomputable section

universe uR uS uM

namespace ProjectiveModulesTests.RightExtensionTensorProduct

open CategoryTheory ModuleCat.RightExtension
open scoped TensorProduct

private theorem tensorFunctor_map_right_action
    {R : Type uR} {S : Type uS} [CommRing R] [Ring S]
    (φ : R →+* S) {M N : ModuleCat.{uM} Rᵐᵒᵖ}
    (g : M ⟶ N) (m : M) (s t : S) :
    (tensorFunctor φ).map g
        (@SMul.smul Sᵐᵒᵖ (tensorProductObj φ M)
          (tensorProductObj φ M).isModule.toSMul
          (MulOpposite.op t) (tensorProductTmul φ M m s)) =
      tensorProductTmul φ N (g m) (s * t) := by
  calc
    _ = @SMul.smul Sᵐᵒᵖ (tensorProductObj φ N)
        (tensorProductObj φ N).isModule.toSMul (MulOpposite.op t)
        ((tensorFunctor φ).map g (tensorProductTmul φ M m s)) :=
      ((tensorFunctor φ).map g).hom.map_smul _ _
    _ = tensorProductTmul φ N (g m) (s * t) := by
      rw [tensorFunctor_map_tmul, tensorProductObj_smul_tmul]

private theorem tensorFunctor_composition_right_action
    {R : Type uR} {S : Type uS} [CommRing R] [Ring S]
    (φ : R →+* S) {M N P : ModuleCat.{uM} Rᵐᵒᵖ}
    (g : M ⟶ N) (h : N ⟶ P) (m : M) (s t : S) :
    (tensorFunctor φ).map (g ≫ h)
        (@SMul.smul Sᵐᵒᵖ (tensorProductObj φ M)
          (tensorProductObj φ M).isModule.toSMul
          (MulOpposite.op t) (tensorProductTmul φ M m s)) =
      tensorProductTmul φ P (h (g m)) (s * t) := by
  exact (tensorFunctor_map_comp_apply φ g h _).trans
    ((congrArg (fun x : tensorProductObj φ N ↦ (tensorFunctor φ).map h x)
      (tensorFunctor_map_right_action φ g m s t)).trans
        (tensorFunctor_map_tmul φ h (g m) (s * t)))

private theorem tensorProductMap_composition_right_action
    {R : Type uR} {S : Type uS} [CommRing R] [Ring S]
    (φ : R →+* S) {M N P : ModuleCat.{uM} Rᵐᵒᵖ}
    (g : M ⟶ N) (h : N ⟶ P) (m : M) (s t : S) :
    tensorProductMap φ (g ≫ h)
        (@SMul.smul Sᵐᵒᵖ (tensorProductObj φ M)
          (tensorProductObj φ M).isModule.toSMul
          (MulOpposite.op t) (tensorProductTmul φ M m s)) =
      tensorProductTmul φ P (h (g m)) (s * t) := by
  exact (DFunLike.congr_fun (tensorProductMap_comp φ g h) _).trans
    ((congrArg (tensorProductMap φ h)
      ((congrArg (tensorProductMap φ g) (tensorProductObj_smul_tmul φ M m s t)).trans
        (tensorProductMap_tmul φ g m (s * t)))).trans
          (tensorProductMap_tmul φ h (g m) (s * t)))

private abbrev Z := ModuleCat.of ℤᵐᵒᵖ (Fin 1 → ℤ)
private abbrev leftZ :=
  (ModuleCat.restrictScalars (RingEquiv.toOpposite ℤ).toRingHom).obj Z
private abbrev coefficientFive :=
  (ModuleCat.restrictScalars (algebraMap ℤ (ZMod 5))).obj (ModuleCat.of (ZMod 5) (ZMod 5))

private def sourceUnit : Z := fun _ ↦ 1
private def extendedUnit : Obj (algebraMap ℤ (ZMod 5)) Z :=
  tmul (algebraMap ℤ (ZMod 5)) sourceUnit 1
private def reducedTensor : tensorProductObj (algebraMap ℤ (ZMod 5)) Z :=
  tensorProductTmul (algebraMap ℤ (ZMod 5)) Z sourceUnit 1

private theorem reduction_not_injective : ¬ Function.Injective (algebraMap ℤ (ZMod 5)) := by
  intro h
  have hcast : algebraMap ℤ (ZMod 5) (5 : ℤ) = algebraMap ℤ (ZMod 5) 0 := by
    rw [algebraMap_int_eq, _root_.map_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (5 : ℤ) 5).mpr (dvd_refl _)
  have hfive : (5 : ℤ) = 0 := h hcast
  norm_num at hfive

private theorem modFive_one_ne_zero : (1 : ZMod 5) ≠ 0 := by
  intro h
  have h51 : (5 : ℕ) = 1 := ZMod.one_eq_zero_iff.mp h
  norm_num at h51

-- This nonzero statement uses only the existing finite-free extension API.
private theorem extendedUnit_ne_zero : extendedUnit ≠ 0 := by
  intro h
  have hc := congrArg
    (fun x : Obj (algebraMap ℤ (ZMod 5)) Z ↦
      rightFreeLinearEquiv (algebraMap ℤ (ZMod 5)) (Fin 1) x 0) h
  apply modFive_one_ne_zero
  simpa [extendedUnit, sourceUnit] using hc

private theorem comparison_at_unit :
    tensorProductLinearEquiv (algebraMap ℤ (ZMod 5)) Z extendedUnit = reducedTensor := by
  exact tensorProductLinearEquiv_tmul (algebraMap ℤ (ZMod 5)) Z sourceUnit 1

private theorem comparison_inverse_at_unit :
    (tensorProductLinearEquiv (algebraMap ℤ (ZMod 5)) Z).symm reducedTensor = extendedUnit := by
  exact tensorProductLinearEquiv_symm_tmul (algebraMap ℤ (ZMod 5)) Z sourceUnit 1

/-- The rank-one pure tensor remains nonzero under the noninjective integer
reduction modulo five. Balanced evaluation detects its coefficient independently
of the scalar-extension comparison equivalences. -/
public theorem modFive_tensor_unit_ne_zero :
    tensorProductTmul (algebraMap ℤ (ZMod 5)) (ModuleCat.of ℤᵐᵒᵖ (Fin 1 → ℤ))
      (fun _ ↦ (1 : ℤ)) (1 : ZMod 5) ≠ 0 := by
  let φ := algebraMap ℤ (ZMod 5)
  let sourceAdd : AddCommMonoid (Fin 1 → ℤ) := Z.isAddCommGroup.toAddCommMonoid
  let coefficientAdd : AddCommMonoid (ZMod 5) :=
    (ModuleCat.of (ZMod 5) (ZMod 5)).isAddCommGroup.toAddCommMonoid
  let sourceModule : Module ℤ (Fin 1 → ℤ) := leftZ.isModule
  let coefficientModule : Module ℤ (ZMod 5) := coefficientFive.isModule
  let evaluation : (Fin 1 → ℤ) →+ ZMod 5 →+ ZMod 5 :=
    { toFun := fun m ↦
        { toFun := fun s ↦ φ (m 0) * s
          map_zero' := mul_zero _
          map_add' := fun s t ↦ mul_add _ s t }
      map_zero' := by
        apply AddMonoidHom.ext
        intro s
        change φ 0 * s = 0
        rw [φ.map_zero, zero_mul]
      map_add' := by
        intro m n
        apply AddMonoidHom.ext
        intro s
        change φ (m 0 + n 0) * s = φ (m 0) * s + φ (n 0) * s
        rw [φ.map_add, add_mul] }
  have balanced : ∀ (r : ℤ) (m : Fin 1 → ℤ) (s : ZMod 5),
      evaluation (@SMul.smul ℤ (Fin 1 → ℤ) sourceModule.toSMul r m) s =
        evaluation m (@SMul.smul ℤ (ZMod 5) coefficientModule.toSMul r s) := by
    intro r m s
    -- Read both actions from their bundled restriction, not from a bare ℤ-instance.
    have sourceAction :
        (@SMul.smul ℤ (Fin 1 → ℤ) sourceModule.toSMul r m) 0 = m 0 * r := by
      have h :
          @SMul.smul ℤ (Fin 1 → ℤ) sourceModule.toSMul r m =
            @SMul.smul ℤᵐᵒᵖ Z Z.isModule.toSMul
              ((RingEquiv.toOpposite ℤ).toRingHom r) m :=
        ModuleCat.restrictScalars.smul_def'
          (RingEquiv.toOpposite ℤ).toRingHom (M := Z) r m
      have hcoordinate := congrArg (fun x : Fin 1 → ℤ ↦ x 0) h
      have hregular :
          (@SMul.smul ℤᵐᵒᵖ Z Z.isModule.toSMul
            ((RingEquiv.toOpposite ℤ).toRingHom r) m) 0 = m 0 * r := rfl
      exact hcoordinate.trans hregular
    have coefficientAction :
        @SMul.smul ℤ (ZMod 5) coefficientModule.toSMul r s = φ r * s := by
      have h :
          @SMul.smul ℤ (ZMod 5) coefficientModule.toSMul r s =
            @SMul.smul (ZMod 5) (ZMod 5) (ModuleCat.of (ZMod 5) (ZMod 5)).isModule.toSMul (φ r) s :=
        ModuleCat.restrictScalars.smul_def' φ (M := ModuleCat.of (ZMod 5) (ZMod 5)) r s
      have hregular :
          @SMul.smul (ZMod 5) (ZMod 5)
            (ModuleCat.of (ZMod 5) (ZMod 5)).isModule.toSMul (φ r) s = φ r * s := rfl
      exact h.trans hregular
    change φ ((@SMul.smul ℤ (Fin 1 → ℤ) sourceModule.toSMul r m) 0) * s =
      φ (m 0) * (@SMul.smul ℤ (ZMod 5) coefficientModule.toSMul r s)
    rw [sourceAction, coefficientAction, φ.map_mul, mul_assoc]
  let evaluateTensor :
      @TensorProduct ℤ _ (Fin 1 → ℤ) (ZMod 5) sourceAdd coefficientAdd
        sourceModule coefficientModule →+ ZMod 5 :=
    @TensorProduct.liftAddHom ℤ _ (Fin 1 → ℤ) (ZMod 5) (ZMod 5)
      sourceAdd coefficientAdd _ sourceModule coefficientModule evaluation balanced
  have pure : evaluateTensor reducedTensor = (1 : ZMod 5) := by
    calc
      _ = φ (sourceUnit 0) * 1 := by
        rw [reducedTensor, tensorProductTmul_eq_tmul]
        exact @TensorProduct.liftAddHom_tmul ℤ _ (Fin 1 → ℤ) (ZMod 5) (ZMod 5)
          sourceAdd coefficientAdd _ sourceModule coefficientModule evaluation balanced sourceUnit 1
      _ = 1 := by rw [show sourceUnit 0 = 1 from rfl, φ.map_one, one_mul]
  intro h
  exact modFive_one_ne_zero
    (pure.symm.trans ((congrArg evaluateTensor h).trans evaluateTensor.map_zero))

-- Doubling is a specified nonidentity module morphism.
private def doubling : Z ⟶ Z := ModuleCat.ofHom
  ((LinearMap.id (R := ℤᵐᵒᵖ) (M := Z)) + LinearMap.id)

private theorem doubling_moves_extendedUnit :
    map (algebraMap ℤ (ZMod 5)) doubling.hom extendedUnit ≠ extendedUnit := by
  let φ := algebraMap ℤ (ZMod 5)
  let coordinate (x : Obj φ Z) := rightFreeLinearEquiv φ (Fin 1) x 0
  have moved : coordinate (map φ doubling.hom extendedUnit) = (2 : ZMod 5) := by
    calc
      _ = coordinate (tmul φ (doubling.hom sourceUnit) 1) :=
        congrArg coordinate (map_tmul φ doubling.hom sourceUnit 1)
      _ = φ (doubling.hom sourceUnit 0) * 1 :=
        congrFun (rightFreeLinearEquiv_tmul φ (Fin 1) (doubling.hom sourceUnit) 1) 0
      _ = 2 := by
        rw [show doubling.hom sourceUnit 0 = (1 + 1 : ℤ) from rfl,
          φ.map_add, φ.map_one, mul_one, one_add_one_eq_two]
  have original : coordinate extendedUnit = (1 : ZMod 5) := by
    calc
      _ = φ (sourceUnit 0) * 1 :=
        congrFun (rightFreeLinearEquiv_tmul φ (Fin 1) sourceUnit 1) 0
      _ = 1 := by rw [show sourceUnit 0 = 1 from rfl, φ.map_one, one_mul]
  intro h
  have hc : (2 : ZMod 5) = 1 := moved.symm.trans ((congrArg coordinate h).trans original)
  have hv := congrArg ZMod.val hc
  rw [ZMod.val_two_eq_two_mod, ZMod.val_one_eq_one_mod] at hv
  norm_num at hv

private theorem doubling_tensor_agreement :
    tensorProductLinearEquiv (algebraMap ℤ (ZMod 5)) Z
        (map (algebraMap ℤ (ZMod 5)) doubling.hom extendedUnit) =
      TensorProduct.map (M := leftZ) (N := coefficientFive) (M₂ := leftZ) (N₂ := coefficientFive)
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite ℤ).toRingHom).map doubling).hom
        (@LinearMap.id ℤ coefficientFive _ _ coefficientFive.isModule) reducedTensor := by
  exact (tensorProductLinearEquiv_naturality (algebraMap ℤ (ZMod 5)) doubling
    extendedUnit).trans (congrArg
      (TensorProduct.map (M := leftZ) (N := coefficientFive) (M₂ := leftZ) (N₂ := coefficientFive)
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite ℤ).toRingHom).map doubling).hom
        (@LinearMap.id ℤ coefficientFive _ _ coefficientFive.isModule)) comparison_at_unit)

private theorem doubling_functor_agreement :
    tensorProductLinearEquiv (algebraMap ℤ (ZMod 5)) Z
        ((functor' (algebraMap ℤ (ZMod 5))).map doubling extendedUnit) =
      TensorProduct.map (M := leftZ) (N := coefficientFive) (M₂ := leftZ) (N₂ := coefficientFive)
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite ℤ).toRingHom).map doubling).hom
        (@LinearMap.id ℤ coefficientFive _ _ coefficientFive.isModule) reducedTensor := by
  exact (tensorProductLinearEquiv_functor'_map (algebraMap ℤ (ZMod 5)) doubling
    extendedUnit).trans (congrArg
      (TensorProduct.map (M := leftZ) (N := coefficientFive) (M₂ := leftZ) (N₂ := coefficientFive)
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite ℤ).toRingHom).map doubling).hom
        (@LinearMap.id ℤ coefficientFive _ _ coefficientFive.isModule)) comparison_at_unit)

private theorem tensorFunctor_at_Z :
    (tensorFunctor (algebraMap ℤ (ZMod 5))).obj Z =
      tensorProductObj (algebraMap ℤ (ZMod 5)) Z :=
  tensorFunctor_obj (algebraMap ℤ (ZMod 5)) Z

example : reducedTensor ≠ 0 := modFive_tensor_unit_ne_zero

private theorem doubling_tensorFunctor_at_unit :
    (tensorFunctor (algebraMap ℤ (ZMod 5))).map doubling reducedTensor =
      tensorProductTmul (algebraMap ℤ (ZMod 5)) Z sourceUnit (2 : ZMod 5) := by
  let φ := algebraMap ℤ (ZMod 5)
  have pure : tensorProductTmul φ Z (doubling sourceUnit) 1 =
      tensorProductTmul φ Z sourceUnit (2 : ZMod 5) :=
    (tensorProductTmul_add_left φ Z sourceUnit sourceUnit 1).trans
      ((tensorProductTmul_add_right φ Z sourceUnit 1 1).symm.trans
        (congrArg (tensorProductTmul φ Z sourceUnit) one_add_one_eq_two))
  exact (tensorFunctor_map_tmul φ doubling sourceUnit 1).trans pure

private theorem doubling_tensorFunctor_linearMap :
    ((tensorFunctor (algebraMap ℤ (ZMod 5))).map doubling).hom =
      LinearMap.id + LinearMap.id := by
  rw [tensorFunctor_map_hom]
  apply tensorProduct_hom_ext (algebraMap ℤ (ZMod 5)) Z
  intro m s
  calc
    _ = tensorProductTmul (algebraMap ℤ (ZMod 5)) Z (doubling m) s :=
      tensorProductMap_tmul (algebraMap ℤ (ZMod 5)) doubling m s
    _ = tensorProductTmul (algebraMap ℤ (ZMod 5)) Z (m + m) s := rfl
    _ = _ := tensorProductTmul_add_left (algebraMap ℤ (ZMod 5)) Z m m s

private theorem doubling_tensorFunctor_comp_linearMap :
    ((tensorFunctor (algebraMap ℤ (ZMod 5))).map (doubling ≫ doubling)).hom =
      (LinearMap.id + LinearMap.id).comp (LinearMap.id + LinearMap.id) := by
  simp only [Functor.map_comp, ModuleCat.hom_comp, doubling_tensorFunctor_linearMap]

private theorem doubling_tensorFunctor_map_agreement :
    tensorProductLinearEquiv (algebraMap ℤ (ZMod 5)) Z
        (map (algebraMap ℤ (ZMod 5)) doubling.hom extendedUnit) =
      (tensorFunctor (algebraMap ℤ (ZMod 5))).map doubling reducedTensor := by
  exact doubling_tensor_agreement.trans
    (tensorFunctor_map_apply (algebraMap ℤ (ZMod 5)) doubling reducedTensor).symm

private theorem doubling_tensorFunctor_functor_agreement :
    tensorProductLinearEquiv (algebraMap ℤ (ZMod 5)) Z
        ((functor' (algebraMap ℤ (ZMod 5))).map doubling extendedUnit) =
      (tensorFunctor (algebraMap ℤ (ZMod 5))).map doubling reducedTensor := by
  exact doubling_functor_agreement.trans
    (tensorFunctor_map_apply (algebraMap ℤ (ZMod 5)) doubling reducedTensor).symm

private theorem doubling_tensorFunctor_moves_unit :
    (tensorFunctor (algebraMap ℤ (ZMod 5))).map doubling reducedTensor ≠ reducedTensor := by
  intro h
  apply doubling_moves_extendedUnit
  apply (tensorProductLinearEquiv (algebraMap ℤ (ZMod 5)) Z).injective
  exact doubling_tensorFunctor_map_agreement.trans (h.trans comparison_at_unit.symm)

private theorem tensorFunctor_identity_at_unit :
    (tensorFunctor (algebraMap ℤ (ZMod 5))).map (𝟙 Z) reducedTensor = reducedTensor := by
  exact tensorFunctor_map_id_apply (algebraMap ℤ (ZMod 5)) Z reducedTensor

private theorem tensorFunctor_composition_at_unit :
    (tensorFunctor (algebraMap ℤ (ZMod 5))).map (doubling ≫ doubling) reducedTensor =
      (tensorFunctor (algebraMap ℤ (ZMod 5))).map doubling
        ((tensorFunctor (algebraMap ℤ (ZMod 5))).map doubling reducedTensor) := by
  exact tensorFunctor_map_comp_apply (algebraMap ℤ (ZMod 5)) doubling doubling reducedTensor

example : (functor' (algebraMap ℤ (ZMod 5))).obj Z ≅
    (tensorFunctor (algebraMap ℤ (ZMod 5))).obj Z :=
  (tensorProductLinearEquiv (algebraMap ℤ (ZMod 5)) Z).toModuleIso

/-! The arbitrary ring target is the integer matrix algebra, not a field. -/

private abbrev A := RightFreeScalarExtension.IntMatrices
private def e12 : A := Matrix.single (0 : Fin 2) 1 1
private def e21 : A := Matrix.single (1 : Fin 2) 0 1
private def e11 : A := Matrix.single (0 : Fin 2) 0 1
private def e22 : A := Matrix.single (1 : Fin 2) 1 1

private theorem matrix_product : e12 * e21 = e11 := by simp [e12, e21, e11]
private theorem matrix_product_reversed : e21 * e12 = e22 := by simp [e12, e21, e22]
private theorem matrix_diagonals_distinct : e11 ≠ e22 := by
  intro h
  have hc := congrArg (fun x : A ↦ x 0 0) h
  norm_num [e11, e22] at hc

private theorem target_noncommutative : e12 * e21 ≠ e21 * e12 := by
  rw [matrix_product, matrix_product_reversed]
  exact matrix_diagonals_distinct

private def matrixTensor (a : A) : tensorProductObj (algebraMap ℤ A) Z :=
  tensorProductTmul (algebraMap ℤ A) Z sourceUnit a

private theorem matrixTensor_injective : Function.Injective matrixTensor := by
  let φ := algebraMap ℤ A
  let sourceAdd : AddCommMonoid (Fin 1 → ℤ) := Z.isAddCommGroup.toAddCommMonoid
  let coefficientAdd : AddCommMonoid A :=
    (ModuleCat.of A A).isAddCommGroup.toAddCommMonoid
  let sourceModule : Module ℤ (Fin 1 → ℤ) := leftZ.isModule
  let coefficientModule : Module ℤ A :=
    ((ModuleCat.restrictScalars (algebraMap ℤ A)).obj (ModuleCat.of A A)).isModule
  let evaluation : (Fin 1 → ℤ) →+ A →+ A :=
    { toFun := fun m ↦
        { toFun := fun s ↦ φ (m 0) * s
          map_zero' := mul_zero _
          map_add' := fun s t ↦ mul_add _ s t }
      map_zero' := by
        apply AddMonoidHom.ext
        intro s
        change φ 0 * s = 0
        rw [φ.map_zero, zero_mul]
      map_add' := by
        intro m n
        apply AddMonoidHom.ext
        intro s
        change φ (m 0 + n 0) * s = φ (m 0) * s + φ (n 0) * s
        rw [φ.map_add, add_mul] }
  have balanced : ∀ (r : ℤ) (m : Fin 1 → ℤ) (s : A),
      evaluation (@SMul.smul ℤ (Fin 1 → ℤ) sourceModule.toSMul r m) s =
        evaluation m (@SMul.smul ℤ A coefficientModule.toSMul r s) := by
    intro r m s
    -- Read both actions from their bundled restriction, not from a bare ℤ-instance.
    have sourceAction :
        (@SMul.smul ℤ (Fin 1 → ℤ) sourceModule.toSMul r m) 0 = m 0 * r := by
      have h :
          @SMul.smul ℤ (Fin 1 → ℤ) sourceModule.toSMul r m =
            @SMul.smul ℤᵐᵒᵖ Z Z.isModule.toSMul
              ((RingEquiv.toOpposite ℤ).toRingHom r) m :=
        ModuleCat.restrictScalars.smul_def'
          (RingEquiv.toOpposite ℤ).toRingHom (M := Z) r m
      have hcoordinate := congrArg (fun x : Fin 1 → ℤ ↦ x 0) h
      have hregular :
          (@SMul.smul ℤᵐᵒᵖ Z Z.isModule.toSMul
            ((RingEquiv.toOpposite ℤ).toRingHom r) m) 0 = m 0 * r := rfl
      exact hcoordinate.trans hregular
    have coefficientAction :
        @SMul.smul ℤ A coefficientModule.toSMul r s = φ r * s := by
      have h :
          @SMul.smul ℤ A coefficientModule.toSMul r s =
            @SMul.smul A A (ModuleCat.of A A).isModule.toSMul (φ r) s :=
        ModuleCat.restrictScalars.smul_def' φ (M := ModuleCat.of A A) r s
      have hregular :
          @SMul.smul A A (ModuleCat.of A A).isModule.toSMul (φ r) s = φ r * s := rfl
      exact h.trans hregular
    change φ ((@SMul.smul ℤ (Fin 1 → ℤ) sourceModule.toSMul r m) 0) * s =
      φ (m 0) * (@SMul.smul ℤ A coefficientModule.toSMul r s)
    rw [sourceAction, coefficientAction, φ.map_mul, mul_assoc]
  let evaluateTensor :
      @TensorProduct ℤ _ (Fin 1 → ℤ) A sourceAdd coefficientAdd
        sourceModule coefficientModule →+ A :=
    @TensorProduct.liftAddHom ℤ _ (Fin 1 → ℤ) A A
      sourceAdd coefficientAdd _ sourceModule coefficientModule evaluation balanced
  have pure (a : A) : evaluateTensor (matrixTensor a) = a := by
    calc
      _ = φ (sourceUnit 0) * a := by
        rw [matrixTensor, tensorProductTmul_eq_tmul]
        exact @TensorProduct.liftAddHom_tmul ℤ _ (Fin 1 → ℤ) A A
          sourceAdd coefficientAdd _ sourceModule coefficientModule evaluation balanced sourceUnit a
      _ = a := by rw [show sourceUnit 0 = 1 from rfl, φ.map_one, one_mul]
  intro a b h
  exact (pure a).symm.trans ((congrArg evaluateTensor h).trans (pure b))

private theorem matrixTensor_e11_ne_zero : matrixTensor e11 ≠ 0 := by
  intro h
  have hz : matrixTensor (0 : A) = 0 := by
    simp only [matrixTensor, tensorProductTmul_zero_right]
  have he : e11 = 0 := matrixTensor_injective (h.trans hz.symm)
  have hc := congrArg (fun x : A ↦ x 0 0) he
  norm_num [e11] at hc

private theorem matrix_right_action :
    @SMul.smul Aᵐᵒᵖ (tensorProductObj (algebraMap ℤ A) Z)
      (tensorProductObj (algebraMap ℤ A) Z).isModule.toSMul
      (MulOpposite.op e21) (matrixTensor e12) = matrixTensor e11 := by
  simpa only [matrixTensor, matrix_product] using
    tensorProductObj_smul_tmul (algebraMap ℤ A) Z sourceUnit e12 e21

-- The negative control uses the transferred Mathlib action, not its comparison formula.
private theorem matrix_wrong_order_control :
    @SMul.smul Aᵐᵒᵖ (tensorProductObj (algebraMap ℤ A) Z)
      (tensorProductObj (algebraMap ℤ A) Z).isModule.toSMul
      (MulOpposite.op e21) (matrixTensor e12) ≠ matrixTensor e22 := by
  let sourceModule : Module ℤ (Fin 1 → ℤ) := leftZ.isModule
  let coefficientModule : Module ℤ A :=
    ((ModuleCat.restrictScalars (algebraMap ℤ A)).obj (ModuleCat.of A A)).isModule
  let : Module ℤ (Fin 1 → ℤ) := sourceModule
  let : Module ℤ A := coefficientModule
  let : SMul ℤ (Fin 1 → ℤ) := sourceModule.toSMul
  let : SMul ℤ A := coefficientModule.toSMul
  let : SMulCommClass ℤ Aᵐᵒᵖ A := by
    have module_eq : coefficientModule = (algebraMap ℤ A).toModule := Subsingleton.elim _ _
    change @SMulCommClass ℤ Aᵐᵒᵖ A coefficientModule.toSMul _
    rw [module_eq]
    exact smulCommClass (algebraMap ℤ A)
  -- Keep the tensor's own integer modules when projecting the commutation equivalence.
  let : Module ℤ (TensorProduct ℤ (Fin 1 → ℤ) A) := TensorProduct.instModule
  let : Module ℤ (TensorProduct ℤ A (Fin 1 → ℤ)) := TensorProduct.instModule
  let commute := @TensorProduct.comm ℤ _ (Fin 1 → ℤ) A _ _ sourceModule coefficientModule
  have physical :
      @SMul.smul Aᵐᵒᵖ (tensorProductObj (algebraMap ℤ A) Z)
        (tensorProductObj (algebraMap ℤ A) Z).isModule.toSMul
        (MulOpposite.op e21) (matrixTensor e12) = matrixTensor (e12 * e21) := by
    change commute.symm (MulOpposite.op e21 • commute
      (@TensorProduct.tmul ℤ _ (Fin 1 → ℤ) A _ _ sourceModule coefficientModule sourceUnit e12)) =
        @TensorProduct.tmul ℤ _ (Fin 1 → ℤ) A _ _ sourceModule coefficientModule
          sourceUnit (e12 * e21)
    rw [TensorProduct.comm_tmul, TensorProduct.smul_tmul', TensorProduct.comm_symm_tmul]
    rfl
  rw [physical, matrix_product]
  exact fun h ↦ matrix_diagonals_distinct (matrixTensor_injective h)

private theorem matrix_comparison_inverse :
    (tensorProductLinearEquiv (algebraMap ℤ A) Z).symm (matrixTensor e12) =
      tmul (algebraMap ℤ A) sourceUnit e12 :=
  tensorProductLinearEquiv_symm_tmul (algebraMap ℤ A) Z sourceUnit e12

/-! The diagonal coefficient homomorphism has noncentral image. -/

private abbrev D := Fin 2 → ℤ
private def diagonalHom : D →+* A := Matrix.diagonalRingHom (Fin 2) ℤ
private def diagonalIdempotent : D := Pi.single (0 : Fin 2) 1

private theorem diagonalIdempotent_image : diagonalHom diagonalIdempotent = e11 := by
  ext i j
  change Matrix.diagonal diagonalIdempotent i j = Matrix.single (0 : Fin 2) 0 1 i j
  by_cases hi : (0 : Fin 2) = i
  · subst i
    simp [diagonalIdempotent, Matrix.diagonal_apply, Matrix.single_apply]
  · simp [diagonalIdempotent, Matrix.diagonal_apply, hi, Ne.symm hi]

private theorem e12_ne_zero : e12 ≠ 0 := by
  intro h
  have hc := congrArg (fun x : A ↦ x 0 1) h
  norm_num [e12] at hc

private theorem diagonal_left_product : diagonalHom diagonalIdempotent * e12 = e12 := by
  rw [diagonalIdempotent_image]
  simp [e11, e12]

private theorem diagonal_right_product : e12 * diagonalHom diagonalIdempotent = 0 := by
  rw [diagonalIdempotent_image]
  simp [e11, e12]

-- An algebra map would commute with every coefficient; this one does not.
private theorem diagonal_image_noncentral :
    diagonalHom diagonalIdempotent * e12 ≠ e12 * diagonalHom diagonalIdempotent := by
  rw [diagonal_left_product, diagonal_right_product]
  exact e12_ne_zero

private abbrev diagonalModule := ModuleCat.of Dᵐᵒᵖ (Fin 1 → D)
private def diagonalUnit : diagonalModule := fun _ ↦ 1
private def diagonalExtended (a : A) : Obj diagonalHom diagonalModule :=
  tmul diagonalHom diagonalUnit a
private def diagonalTensor (a : A) : tensorProductObj diagonalHom diagonalModule :=
  tensorProductTmul diagonalHom diagonalModule diagonalUnit a

-- Coordinate detection precedes and does not depend on the tensor comparison.
private theorem diagonalExtended_e12_ne_zero : diagonalExtended e12 ≠ 0 := by
  intro h
  have hc := congrArg
    (fun x : Obj diagonalHom diagonalModule ↦
      rightFreeLinearEquiv diagonalHom (Fin 1) x 0) h
  apply e12_ne_zero
  simpa [diagonalExtended, diagonalUnit] using hc

private theorem diagonal_comparison (a : A) :
    tensorProductLinearEquiv diagonalHom diagonalModule (diagonalExtended a) =
      diagonalTensor a :=
  tensorProductLinearEquiv_tmul diagonalHom diagonalModule diagonalUnit a

private theorem diagonal_comparison_inverse (a : A) :
    (tensorProductLinearEquiv diagonalHom diagonalModule).symm (diagonalTensor a) =
      diagonalExtended a :=
  tensorProductLinearEquiv_symm_tmul diagonalHom diagonalModule diagonalUnit a

private theorem diagonalTensor_e12_ne_zero : diagonalTensor e12 ≠ 0 := by
  let φ := diagonalHom
  let sourceAdd : AddCommMonoid (Fin 1 → D) := diagonalModule.isAddCommGroup.toAddCommMonoid
  let coefficientAdd : AddCommMonoid A :=
    (ModuleCat.of A A).isAddCommGroup.toAddCommMonoid
  let sourceModule : Module D (Fin 1 → D) :=
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite D).toRingHom).obj diagonalModule).isModule
  let coefficientModule : Module D A :=
    ((ModuleCat.restrictScalars diagonalHom).obj (ModuleCat.of A A)).isModule
  let evaluation : (Fin 1 → D) →+ A →+ A :=
    { toFun := fun m ↦
        { toFun := fun s ↦ φ (m 0) * s
          map_zero' := mul_zero _
          map_add' := fun s t ↦ mul_add _ s t }
      map_zero' := by
        apply AddMonoidHom.ext
        intro s
        change φ 0 * s = 0
        rw [φ.map_zero, zero_mul]
      map_add' := by
        intro m n
        apply AddMonoidHom.ext
        intro s
        change φ (m 0 + n 0) * s = φ (m 0) * s + φ (n 0) * s
        rw [φ.map_add, add_mul] }
  have balanced : ∀ (r : D) (m : Fin 1 → D) (s : A),
      evaluation (@SMul.smul D (Fin 1 → D) sourceModule.toSMul r m) s =
        evaluation m (@SMul.smul D A coefficientModule.toSMul r s) := by
    intro r m s
    -- Read both actions from their bundled restriction, not from a bare D-instance.
    have sourceAction :
        (@SMul.smul D (Fin 1 → D) sourceModule.toSMul r m) 0 = m 0 * r := by
      have h :
          @SMul.smul D (Fin 1 → D) sourceModule.toSMul r m =
            @SMul.smul Dᵐᵒᵖ diagonalModule diagonalModule.isModule.toSMul
              ((RingEquiv.toOpposite D).toRingHom r) m :=
        ModuleCat.restrictScalars.smul_def'
          (RingEquiv.toOpposite D).toRingHom (M := diagonalModule) r m
      have hcoordinate := congrArg (fun x : Fin 1 → D ↦ x 0) h
      have hregular :
          (@SMul.smul Dᵐᵒᵖ diagonalModule diagonalModule.isModule.toSMul
            ((RingEquiv.toOpposite D).toRingHom r) m) 0 = m 0 * r := rfl
      exact hcoordinate.trans hregular
    have coefficientAction :
        @SMul.smul D A coefficientModule.toSMul r s = φ r * s := by
      have h :
          @SMul.smul D A coefficientModule.toSMul r s =
            @SMul.smul A A (ModuleCat.of A A).isModule.toSMul (φ r) s :=
        ModuleCat.restrictScalars.smul_def' φ (M := ModuleCat.of A A) r s
      have hregular :
          @SMul.smul A A (ModuleCat.of A A).isModule.toSMul (φ r) s = φ r * s := rfl
      exact h.trans hregular
    change φ ((@SMul.smul D (Fin 1 → D) sourceModule.toSMul r m) 0) * s =
      φ (m 0) * (@SMul.smul D A coefficientModule.toSMul r s)
    rw [sourceAction, coefficientAction, φ.map_mul, mul_assoc]
  let evaluateTensor :
      @TensorProduct D _ (Fin 1 → D) A sourceAdd coefficientAdd
        sourceModule coefficientModule →+ A :=
    @TensorProduct.liftAddHom D _ (Fin 1 → D) A A
      sourceAdd coefficientAdd _ sourceModule coefficientModule evaluation balanced
  have pure : evaluateTensor (diagonalTensor e12) = e12 := by
    calc
      _ = φ (diagonalUnit 0) * e12 := by
        rw [diagonalTensor, tensorProductTmul_eq_tmul]
        exact @TensorProduct.liftAddHom_tmul D _ (Fin 1 → D) A A
          sourceAdd coefficientAdd _ sourceModule coefficientModule evaluation balanced
          diagonalUnit e12
      _ = e12 := by rw [show diagonalUnit 0 = 1 from rfl, φ.map_one, one_mul]
  intro h
  exact e12_ne_zero
    (pure.symm.trans ((congrArg evaluateTensor h).trans evaluateTensor.map_zero))

private theorem diagonal_balance :
    tensorProductLinearEquiv diagonalHom diagonalModule
        (tmul diagonalHom (MulOpposite.op diagonalIdempotent • diagonalUnit) e12) =
      diagonalTensor e12 := by
  exact (tensorProductLinearEquiv_tmul diagonalHom diagonalModule
    (MulOpposite.op diagonalIdempotent • diagonalUnit) e12).trans
      ((tensorProductTmul_balance diagonalHom diagonalModule diagonalIdempotent
        diagonalUnit e12).trans
          (congrArg (tensorProductTmul diagonalHom diagonalModule diagonalUnit)
            diagonal_left_product))

private theorem diagonal_right_action :
    @SMul.smul Aᵐᵒᵖ (tensorProductObj diagonalHom diagonalModule)
      (tensorProductObj diagonalHom diagonalModule).isModule.toSMul
      (MulOpposite.op (diagonalHom diagonalIdempotent)) (diagonalTensor e12) =
      diagonalTensor (e12 * diagonalHom diagonalIdempotent) := by
  simpa only [diagonalTensor] using
    tensorProductObj_smul_tmul diagonalHom diagonalModule diagonalUnit e12
      (diagonalHom diagonalIdempotent)

private theorem diagonal_comparison_right_action :
    tensorProductLinearEquiv diagonalHom diagonalModule
        (MulOpposite.op (diagonalHom diagonalIdempotent) • diagonalExtended e12) =
      diagonalTensor (e12 * diagonalHom diagonalIdempotent) := by
  calc
    _ = @SMul.smul Aᵐᵒᵖ (tensorProductObj diagonalHom diagonalModule)
        (tensorProductObj diagonalHom diagonalModule).isModule.toSMul
        (MulOpposite.op (diagonalHom diagonalIdempotent))
        (tensorProductLinearEquiv diagonalHom diagonalModule (diagonalExtended e12)) :=
      (tensorProductLinearEquiv diagonalHom diagonalModule).map_smul _ _
    _ = @SMul.smul Aᵐᵒᵖ (tensorProductObj diagonalHom diagonalModule)
        (tensorProductObj diagonalHom diagonalModule).isModule.toSMul
        (MulOpposite.op (diagonalHom diagonalIdempotent)) (diagonalTensor e12) :=
      congrArg (fun x : tensorProductObj diagonalHom diagonalModule ↦
        @SMul.smul Aᵐᵒᵖ (tensorProductObj diagonalHom diagonalModule)
          (tensorProductObj diagonalHom diagonalModule).isModule.toSMul
          (MulOpposite.op (diagonalHom diagonalIdempotent)) x) (diagonal_comparison e12)
    _ = _ := diagonal_right_action

private theorem diagonal_right_action_eq_zero :
    @SMul.smul Aᵐᵒᵖ (tensorProductObj diagonalHom diagonalModule)
      (tensorProductObj diagonalHom diagonalModule).isModule.toSMul
      (MulOpposite.op (diagonalHom diagonalIdempotent)) (diagonalTensor e12) = 0 := by
  let sourceModule : Module D (Fin 1 → D) :=
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite D).toRingHom).obj diagonalModule).isModule
  let coefficientModule : Module D A :=
    ((ModuleCat.restrictScalars diagonalHom).obj (ModuleCat.of A A)).isModule
  let : Module D (Fin 1 → D) := sourceModule
  let : Module D A := coefficientModule
  let : SMul D (Fin 1 → D) := sourceModule.toSMul
  let : SMul D A := coefficientModule.toSMul
  let : SMulCommClass D Aᵐᵒᵖ A := smulCommClass diagonalHom
  let commute := @TensorProduct.comm D _ (Fin 1 → D) A _ _ sourceModule coefficientModule
  have physical :
      @SMul.smul Aᵐᵒᵖ (tensorProductObj diagonalHom diagonalModule)
        (tensorProductObj diagonalHom diagonalModule).isModule.toSMul
        (MulOpposite.op (diagonalHom diagonalIdempotent)) (diagonalTensor e12) =
          diagonalTensor (e12 * diagonalHom diagonalIdempotent) := by
    change commute.symm (MulOpposite.op (diagonalHom diagonalIdempotent) • commute
      (@TensorProduct.tmul D _ (Fin 1 → D) A _ _ sourceModule coefficientModule diagonalUnit e12)) =
        @TensorProduct.tmul D _ (Fin 1 → D) A _ _ sourceModule coefficientModule
          diagonalUnit (e12 * diagonalHom diagonalIdempotent)
    rw [TensorProduct.comm_tmul, TensorProduct.smul_tmul', TensorProduct.comm_symm_tmul]
    rfl
  exact physical.trans ((congrArg diagonalTensor diagonal_right_product).trans
    (tensorProductTmul_zero_right diagonalHom diagonalModule diagonalUnit))

private theorem diagonal_wrong_order_control :
    @SMul.smul Aᵐᵒᵖ (tensorProductObj diagonalHom diagonalModule)
      (tensorProductObj diagonalHom diagonalModule).isModule.toSMul
      (MulOpposite.op (diagonalHom diagonalIdempotent)) (diagonalTensor e12) ≠
      diagonalTensor (diagonalHom diagonalIdempotent * e12) := by
  rw [diagonal_right_action_eq_zero, diagonal_left_product]
  exact Ne.symm diagonalTensor_e12_ne_zero

private theorem diagonal_tensorFunctor_balance :
    (tensorFunctor diagonalHom).map (𝟙 diagonalModule)
        (tensorProductTmul diagonalHom diagonalModule
          (MulOpposite.op diagonalIdempotent • diagonalUnit) e12) =
      diagonalTensor e12 := by
  rw [tensorFunctor_map_tmul, ModuleCat.id_apply]
  exact (tensorProductTmul_balance diagonalHom diagonalModule diagonalIdempotent
    diagonalUnit e12).trans
      (congrArg (tensorProductTmul diagonalHom diagonalModule diagonalUnit)
        diagonal_left_product)

private theorem diagonal_tensorFunctor_wrong_order :
    (tensorFunctor diagonalHom).map (𝟙 diagonalModule)
        (@SMul.smul Aᵐᵒᵖ (tensorProductObj diagonalHom diagonalModule)
          (tensorProductObj diagonalHom diagonalModule).isModule.toSMul
          (MulOpposite.op (diagonalHom diagonalIdempotent)) (diagonalTensor e12)) ≠
      (tensorFunctor diagonalHom).map (𝟙 diagonalModule)
        (diagonalTensor (diagonalHom diagonalIdempotent * e12)) := by
  intro h
  apply diagonal_wrong_order_control
  exact (tensorFunctor_map_id_apply diagonalHom diagonalModule _).symm.trans
    (h.trans (tensorFunctor_map_id_apply diagonalHom diagonalModule _))

example : (functor' diagonalHom).obj diagonalModule ≅
    (tensorFunctor diagonalHom).obj diagonalModule :=
  (tensorProductLinearEquiv diagonalHom diagonalModule).toModuleIso

/-! Mathlib's categorical comparison is confined to commutative coefficients. -/

private def categoricalTensor :
    (ModuleCat.restrictScalars (RingEquiv.toOpposite (ZMod 5)).symm.toRingHom).obj
      ((ModuleCat.extendScalars (algebraMap ℤ (ZMod 5))).obj leftZ) :=
  @TensorProduct.tmul ℤ _ coefficientFive leftZ _ _
    coefficientFive.isModule leftZ.isModule (1 : ZMod 5) sourceUnit

private theorem categorical_at_unit :
    extendScalarsLinearEquiv (algebraMap ℤ (ZMod 5)) Z extendedUnit = categoricalTensor :=
  extendScalarsLinearEquiv_tmul (algebraMap ℤ (ZMod 5)) Z sourceUnit 1

private theorem categorical_inverse_at_unit :
    (extendScalarsLinearEquiv (algebraMap ℤ (ZMod 5)) Z).symm categoricalTensor = extendedUnit :=
  extendScalarsLinearEquiv_symm_tmul (algebraMap ℤ (ZMod 5)) Z sourceUnit 1

-- Commutation reduces scalar-first evaluation to the same independent balanced map.
private theorem categoricalTensor_ne_zero : categoricalTensor ≠ 0 := by
  let φ := algebraMap ℤ (ZMod 5)
  let sourceAdd : AddCommMonoid (Fin 1 → ℤ) := Z.isAddCommGroup.toAddCommMonoid
  let coefficientAdd : AddCommMonoid (ZMod 5) :=
    (ModuleCat.of (ZMod 5) (ZMod 5)).isAddCommGroup.toAddCommMonoid
  let sourceModule : Module ℤ (Fin 1 → ℤ) := leftZ.isModule
  let coefficientModule : Module ℤ (ZMod 5) := coefficientFive.isModule
  let evaluation : (Fin 1 → ℤ) →+ ZMod 5 →+ ZMod 5 :=
    { toFun := fun m ↦
        { toFun := fun s ↦ φ (m 0) * s
          map_zero' := mul_zero _
          map_add' := fun s t ↦ mul_add _ s t }
      map_zero' := by
        apply AddMonoidHom.ext
        intro s
        change φ 0 * s = 0
        rw [φ.map_zero, zero_mul]
      map_add' := by
        intro m n
        apply AddMonoidHom.ext
        intro s
        change φ (m 0 + n 0) * s = φ (m 0) * s + φ (n 0) * s
        rw [φ.map_add, add_mul] }
  have balanced : ∀ (r : ℤ) (m : Fin 1 → ℤ) (s : ZMod 5),
      evaluation (@SMul.smul ℤ (Fin 1 → ℤ) sourceModule.toSMul r m) s =
        evaluation m (@SMul.smul ℤ (ZMod 5) coefficientModule.toSMul r s) := by
    intro r m s
    -- Read both actions from their bundled restriction, not from a bare ℤ-instance.
    have sourceAction :
        (@SMul.smul ℤ (Fin 1 → ℤ) sourceModule.toSMul r m) 0 = m 0 * r := by
      have h :
          @SMul.smul ℤ (Fin 1 → ℤ) sourceModule.toSMul r m =
            @SMul.smul ℤᵐᵒᵖ Z Z.isModule.toSMul
              ((RingEquiv.toOpposite ℤ).toRingHom r) m :=
        ModuleCat.restrictScalars.smul_def'
          (RingEquiv.toOpposite ℤ).toRingHom (M := Z) r m
      have hcoordinate := congrArg (fun x : Fin 1 → ℤ ↦ x 0) h
      have hregular :
          (@SMul.smul ℤᵐᵒᵖ Z Z.isModule.toSMul
            ((RingEquiv.toOpposite ℤ).toRingHom r) m) 0 = m 0 * r := rfl
      exact hcoordinate.trans hregular
    have coefficientAction :
        @SMul.smul ℤ (ZMod 5) coefficientModule.toSMul r s = φ r * s := by
      have h :
          @SMul.smul ℤ (ZMod 5) coefficientModule.toSMul r s =
            @SMul.smul (ZMod 5) (ZMod 5) (ModuleCat.of (ZMod 5) (ZMod 5)).isModule.toSMul (φ r) s :=
        ModuleCat.restrictScalars.smul_def' φ (M := ModuleCat.of (ZMod 5) (ZMod 5)) r s
      have hregular :
          @SMul.smul (ZMod 5) (ZMod 5)
            (ModuleCat.of (ZMod 5) (ZMod 5)).isModule.toSMul (φ r) s = φ r * s := rfl
      exact h.trans hregular
    change φ ((@SMul.smul ℤ (Fin 1 → ℤ) sourceModule.toSMul r m) 0) * s =
      φ (m 0) * (@SMul.smul ℤ (ZMod 5) coefficientModule.toSMul r s)
    rw [sourceAction, coefficientAction, φ.map_mul, mul_assoc]
  let evaluateTensor :
      @TensorProduct ℤ _ (Fin 1 → ℤ) (ZMod 5) sourceAdd coefficientAdd
        sourceModule coefficientModule →+ ZMod 5 :=
    @TensorProduct.liftAddHom ℤ _ (Fin 1 → ℤ) (ZMod 5) (ZMod 5)
      sourceAdd coefficientAdd _ sourceModule coefficientModule evaluation balanced
  let : Module ℤ (Fin 1 → ℤ) := sourceModule
  let : Module ℤ (ZMod 5) := coefficientModule
  let : SMul ℤ (Fin 1 → ℤ) := sourceModule.toSMul
  let : SMul ℤ (ZMod 5) := coefficientModule.toSMul
  -- These are the tensor modules inferred by comm, not the default integer modules.
  let : Module ℤ (TensorProduct ℤ (ZMod 5) (Fin 1 → ℤ)) := TensorProduct.instModule
  let : Module ℤ (TensorProduct ℤ (Fin 1 → ℤ) (ZMod 5)) := TensorProduct.instModule
  let commute := @TensorProduct.comm ℤ _ (ZMod 5) (Fin 1 → ℤ)
    coefficientAdd sourceAdd coefficientModule sourceModule
  let evaluateCategorical := evaluateTensor.comp commute.toAddEquiv.toAddMonoidHom
  have pure : evaluateCategorical categoricalTensor = (1 : ZMod 5) := by
    calc
      _ = evaluateTensor
          (@TensorProduct.tmul ℤ _ (Fin 1 → ℤ) (ZMod 5) sourceAdd coefficientAdd
            sourceModule coefficientModule sourceUnit 1) := by
        exact congrArg evaluateTensor
          (@TensorProduct.comm_tmul ℤ _ (ZMod 5) (Fin 1 → ℤ)
            coefficientAdd sourceAdd coefficientModule sourceModule 1 sourceUnit)
      _ = φ (sourceUnit 0) * 1 :=
        @TensorProduct.liftAddHom_tmul ℤ _ (Fin 1 → ℤ) (ZMod 5) (ZMod 5)
          sourceAdd coefficientAdd _ sourceModule coefficientModule evaluation balanced sourceUnit 1
      _ = 1 := by rw [show sourceUnit 0 = 1 from rfl, φ.map_one, one_mul]
  intro h
  exact modFive_one_ne_zero
    (pure.symm.trans ((congrArg evaluateCategorical h).trans evaluateCategorical.map_zero))

private theorem categorical_switch_of_factors :
    categoricalTensor =
      @TensorProduct.comm ℤ _ leftZ coefficientFive _ _
        leftZ.isModule coefficientFive.isModule reducedTensor := by
  exact categorical_at_unit.symm.trans
    ((extendScalarsLinearEquiv_eq_comm (algebraMap ℤ (ZMod 5)) Z extendedUnit).trans
      (congrArg (@TensorProduct.comm ℤ _ leftZ coefficientFive _ _
        leftZ.isModule coefficientFive.isModule) comparison_at_unit))

private theorem categorical_doubling_agreement :
    extendScalarsLinearEquiv (algebraMap ℤ (ZMod 5)) Z
        (map (algebraMap ℤ (ZMod 5)) doubling.hom extendedUnit) =
      (ModuleCat.restrictScalars (RingEquiv.toOpposite (ZMod 5)).symm.toRingHom).map
        ((ModuleCat.extendScalars (algebraMap ℤ (ZMod 5))).map
          ((ModuleCat.restrictScalars (RingEquiv.toOpposite ℤ).toRingHom).map doubling))
        categoricalTensor := by
  exact (extendScalarsLinearEquiv_naturality (algebraMap ℤ (ZMod 5)) doubling
    extendedUnit).trans (congrArg
      ((ModuleCat.restrictScalars (RingEquiv.toOpposite (ZMod 5)).symm.toRingHom).map
        ((ModuleCat.extendScalars (algebraMap ℤ (ZMod 5))).map
          ((ModuleCat.restrictScalars (RingEquiv.toOpposite ℤ).toRingHom).map doubling)))
      categorical_at_unit)

/-! A nonidentity endomorphism tests the specified coefficient scalar view. -/

section SelfMap

private abbrev B := ℤ × ℤ
private def swapHom : B →+* B := (RingHom.snd ℤ ℤ).prod (RingHom.fst ℤ ℤ)
private abbrev productModule := ModuleCat.of Bᵐᵒᵖ (Fin 1 → B)
private def productUnit : productModule := fun _ ↦ 1

private theorem swapped_categorical_at_unit :
    extendScalarsLinearEquiv swapHom productModule (tmul swapHom productUnit (1, 0)) =
      @TensorProduct.tmul B _
        ((ModuleCat.restrictScalars swapHom).obj (ModuleCat.of B B))
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite B).toRingHom).obj productModule)
        _ _
        ((ModuleCat.restrictScalars swapHom).obj (ModuleCat.of B B)).isModule
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite B).toRingHom).obj productModule).isModule
        (1, 0) productUnit :=
  extendScalarsLinearEquiv_tmul swapHom productModule productUnit (1, 0)

-- The two scalar views share the carrier B but not the left B-action.
private abbrev regularProductModule := ModuleCat.of Bᵐᵒᵖ B
private abbrev regularProductLeft :=
  (ModuleCat.restrictScalars (RingEquiv.toOpposite B).toRingHom).obj regularProductModule
private abbrev swappedCoefficient :=
  (ModuleCat.restrictScalars swapHom).obj (ModuleCat.of B B)

private theorem regularProduct_source_action :
    @SMul.smul B B regularProductLeft.isModule.toSMul
      ((1, 0) : B) (1 : B) = ((1, 0) : B) := rfl

private theorem regularProduct_coefficient_action :
    @SMul.smul B B swappedCoefficient.isModule.toSMul
      ((1, 0) : B) (1 : B) = ((0, 1) : B) := rfl

private def regularProductTensor (b : B) : tensorProductObj swapHom regularProductModule :=
  @TensorProduct.tmul B _ B B _ _
    regularProductLeft.isModule swappedCoefficient.isModule (1 : B) b

private theorem regularProduct_constructor (b : B) :
    tensorProductTmul swapHom regularProductModule 1 b = regularProductTensor b :=
  tensorProductTmul_eq_tmul swapHom regularProductModule 1 b

private theorem regularProduct_forward (b : B) :
    tensorProductLinearEquiv swapHom regularProductModule
        (tmul swapHom (1 : regularProductModule) b) = regularProductTensor b := by
  rw [tensorProductLinearEquiv_tmul, regularProduct_constructor]

private theorem regularProduct_inverse (b : B) :
    (tensorProductLinearEquiv swapHom regularProductModule).symm (regularProductTensor b) =
      tmul swapHom (1 : regularProductModule) b := by
  rw [← regularProduct_constructor, tensorProductLinearEquiv_symm_tmul]

private def regularSwapEvaluation : Obj swapHom regularProductModule →ₗ[Bᵐᵒᵖ] B :=
  fromSemilinear swapHom
    { toFun := swapHom
      map_add' := swapHom.map_add
      map_smul' := fun r m ↦ by
        change swapHom (m * MulOpposite.unop r) =
          swapHom m * swapHom (MulOpposite.unop r)
        exact swapHom.map_mul _ _ }

private theorem regularSwapEvaluation_tmul (m : regularProductModule) (b : B) :
    regularSwapEvaluation (tmul swapHom m b) = swapHom m * b := by
  rw [regularSwapEvaluation, fromSemilinear_tmul]
  rfl

-- Evaluation on Mathlib's tensor product detects coefficients without the comparison API.
private theorem regularProductTensor_injective : Function.Injective regularProductTensor := by
  let sourceModule : Module B B := regularProductLeft.isModule
  let coefficientModule : Module B B := swappedCoefficient.isModule
  let evaluation : B →+ B →+ B :=
    { toFun := fun m ↦
        { toFun := fun b ↦ swapHom m * b
          map_zero' := mul_zero _
          map_add' := fun a b ↦ mul_add _ a b }
      map_zero' := by
        apply AddMonoidHom.ext
        intro b
        change swapHom (0 : B) * b = 0
        rw [swapHom.map_zero, zero_mul]
      map_add' := by
        intro m n
        apply AddMonoidHom.ext
        intro b
        change swapHom (m + n) * b = swapHom m * b + swapHom n * b
        rw [swapHom.map_add, add_mul] }
  have balanced : ∀ (r m b : B),
      evaluation (@SMul.smul B B sourceModule.toSMul r m) b =
        evaluation m (@SMul.smul B B coefficientModule.toSMul r b) := by
    intro r m b
    change swapHom (m * r) * b = swapHom m * (swapHom r * b)
    rw [swapHom.map_mul, mul_assoc]
  let evaluateTensor :
      @TensorProduct B _ B B _ _ sourceModule coefficientModule →+ B :=
    @TensorProduct.liftAddHom B _ B B B _ _ _
      sourceModule coefficientModule evaluation balanced
  have pure (b : B) : evaluateTensor (regularProductTensor b) = b := by
    calc
      _ = swapHom (1 : B) * b := by
        exact @TensorProduct.liftAddHom_tmul B _ B B B _ _ _
          sourceModule coefficientModule evaluation balanced (1 : B) b
      _ = b := by rw [swapHom.map_one, one_mul]
  intro a b h
  exact (pure a).symm.trans ((congrArg evaluateTensor h).trans (pure b))

private theorem regularProductTensor_ne_zero : regularProductTensor (0, 1) ≠ 0 := by
  intro h
  have hz : regularProductTensor 0 = 0 :=
    @TensorProduct.tmul_zero B _ B B _ _
      regularProductLeft.isModule swappedCoefficient.isModule (1 : B)
  have he : ((0, 1) : B) = 0 := regularProductTensor_injective (h.trans hz.symm)
  have hc := congrArg Prod.snd he
  norm_num at hc

private theorem regularProduct_balance_not_regular :
    tmul swapHom
        (@SMul.smul Bᵐᵒᵖ B regularProductModule.isModule.toSMul
          (MulOpposite.op ((1, 0) : B)) (1 : B)) 1 ≠
      tmul swapHom (1 : regularProductModule) (1, 0) := by
  intro h
  have he := congrArg regularSwapEvaluation h
  rw [regularSwapEvaluation_tmul, regularSwapEvaluation_tmul] at he
  change ((0, 1) : B) = ((1, 0) : B) at he
  have hc := congrArg Prod.fst he
  norm_num at hc

private theorem regularProduct_categorical (b : B) :
    extendScalarsLinearEquiv swapHom regularProductModule
        (tmul swapHom (1 : regularProductModule) b) =
      @TensorProduct.tmul B _ swappedCoefficient regularProductLeft _ _
        swappedCoefficient.isModule regularProductLeft.isModule b (1 : B) :=
  extendScalarsLinearEquiv_tmul swapHom regularProductModule 1 b

private theorem swapped_balance_not_regular :
    tmul swapHom
        (@SMul.smul Bᵐᵒᵖ (Fin 1 → B) productModule.isModule.toSMul
          (MulOpposite.op ((1, 0) : B)) productUnit) 1 ≠
      tmul swapHom productUnit (1, 0) := by
  let productCoefficient :=
    (ModuleCat.restrictScalars swapHom).obj (ModuleCat.of B B)
  have haction :
      @SMul.smul B B productCoefficient.isModule.toSMul ((1, 0) : B) (1 : B) =
        ((0, 1) : B) := rfl
  have hmap : swapHom ((1, 0) : B) = ((0, 1) : B) := by
    change swapHom ((1, 0) : B) * (1 : B) = ((0, 1) : B) at haction
    simpa only [mul_one] using haction
  have hnonidentity : swapHom ((1, 0) : B) ≠ ((1, 0) : B) := by
    rw [hmap]
    intro h
    have hc := congrArg Prod.fst h
    norm_num at hc
  have hbalance :
      tmul swapHom
          (@SMul.smul Bᵐᵒᵖ (Fin 1 → B) productModule.isModule.toSMul
            (MulOpposite.op ((1, 0) : B)) productUnit) 1 =
        tmul swapHom productUnit ((0, 1) : B) := by
    -- Freeze the original source fields, independently of the swapped coefficient action.
    let sourceAdd : AddCommGroup productModule := productModule.isAddCommGroup
    let sourceModule : @Module Bᵐᵒᵖ productModule _ sourceAdd.toAddCommMonoid :=
      productModule.isModule
    have bundledAction :
        @SMul.smul Bᵐᵒᵖ (Fin 1 → B) productModule.isModule.toSMul
          (MulOpposite.op ((1, 0) : B)) productUnit =
            fun _ : Fin 1 ↦ ((1, 0) : B) := by
      -- Evaluate the original bundled scalar action before computing its coordinate.
      have scalarApply (r : Bᵐᵒᵖ) (m : productModule) :
          (productModule.smul r).hom m =
            @SMul.smul Bᵐᵒᵖ productModule productModule.isModule.toSMul r m := rfl
      calc
        _ = (productModule.smul (MulOpposite.op ((1, 0) : B))).hom productUnit :=
          (scalarApply _ _).symm
        _ = _ := by
          rw [scalarApply]
          rfl
    have canonicalAction :
        @SMul.smul Bᵐᵒᵖ productModule sourceModule.toSMul
          (MulOpposite.op ((1, 0) : B)) productUnit =
            fun _ : Fin 1 ↦ ((1, 0) : B) :=
      bundledAction
    calc
      _ = @tmul B B _ _ swapHom productModule sourceAdd sourceModule
          (@SMul.smul Bᵐᵒᵖ productModule sourceModule.toSMul
            (MulOpposite.op ((1, 0) : B)) productUnit) (1 : B) :=
        congrArg (fun m : productModule ↦
          @tmul B B _ _ swapHom productModule sourceAdd sourceModule m (1 : B))
          (bundledAction.trans canonicalAction.symm)
      _ = @tmul B B _ _ swapHom productModule sourceAdd sourceModule
          productUnit (swapHom ((1, 0) : B) * (1 : B)) :=
        @smul_tmul B B _ _ swapHom productModule
          sourceAdd sourceModule ((1, 0) : B) productUnit (1 : B)
      _ = _ :=
        congrArg (fun b : B ↦
          @tmul B B _ _ swapHom productModule sourceAdd sourceModule productUnit b)
          ((mul_one _).trans hmap)
  intro h
  have he := hbalance.symm.trans h
  have hc := congrArg
    (fun x : Obj swapHom productModule ↦
      rightFreeLinearEquiv swapHom (Fin 1) x 0) he
  apply hnonidentity
  rw [hmap]
  simpa only [rightFreeLinearEquiv_tmul, productUnit, swapHom.map_one, one_mul] using hc

private theorem regularProduct_tensorFunctor_balance :
    (tensorFunctor swapHom).map (𝟙 regularProductModule)
        (tensorProductTmul swapHom regularProductModule
          (@SMul.smul Bᵐᵒᵖ B regularProductModule.isModule.toSMul
            (MulOpposite.op ((1, 0) : B)) (1 : B)) 1) =
      regularProductTensor (0, 1) := by
  rw [tensorFunctor_map_tmul, ModuleCat.id_apply]
  exact (tensorProductTmul_balance swapHom regularProductModule ((1, 0) : B) 1 1).trans
    (regularProduct_constructor (0, 1))

private theorem regularProduct_tensorFunctor_balance_not_regular :
    (tensorFunctor swapHom).map (𝟙 regularProductModule)
        (tensorProductTmul swapHom regularProductModule
          (@SMul.smul Bᵐᵒᵖ B regularProductModule.isModule.toSMul
            (MulOpposite.op ((1, 0) : B)) (1 : B)) 1) ≠
      (tensorFunctor swapHom).map (𝟙 regularProductModule) (regularProductTensor (1, 0)) := by
  intro h
  have he : regularProductTensor (0, 1) = regularProductTensor (1, 0) :=
    regularProduct_tensorFunctor_balance.symm.trans
      (h.trans (tensorFunctor_map_id_apply swapHom regularProductModule _))
  have hc := congrArg Prod.fst (regularProductTensor_injective he)
  norm_num at hc

example : (functor' swapHom).obj regularProductModule ≅
    (tensorFunctor swapHom).obj regularProductModule :=
  (tensorProductLinearEquiv swapHom regularProductModule).toModuleIso

end SelfMap

/-! Zero boundaries use canonical unital maps. -/

private abbrev emptyModule := ModuleCat.of ℤᵐᵒᵖ (Fin 0 → ℤ)
private def emptyVector : emptyModule := fun i ↦ Fin.elim0 i

private theorem zeroModule_agreement :
    tensorProductLinearEquiv (algebraMap ℤ (ZMod 5)) emptyModule
        (tmul (algebraMap ℤ (ZMod 5)) emptyVector 1) = 0 := by
  rw [tensorProductLinearEquiv_tmul]
  have h : emptyVector = 0 := Subsingleton.elim _ _
  rw [h, tensorProductTmul_zero_left]

private theorem zeroTarget_agreement :
    tensorProductLinearEquiv (algebraMap ℤ PUnit) Z
        (tmul (algebraMap ℤ PUnit) sourceUnit 1) = 0 := by
  rw [tensorProductLinearEquiv_tmul]
  have h : (1 : PUnit) = 0 := Subsingleton.elim _ _
  rw [h, tensorProductTmul_zero_right]

private abbrev allZeroModule := ModuleCat.of PUnitᵐᵒᵖ PUnit

private theorem allZero_agreement :
    tensorProductLinearEquiv (algebraMap PUnit PUnit) allZeroModule
        (tmul (algebraMap PUnit PUnit) (0 : allZeroModule) 1) = 0 := by
  rw [tensorProductLinearEquiv_tmul]
  simp only [tensorProductTmul_zero_left]

private theorem tensorFunctor_zeroModule :
    (tensorFunctor (algebraMap ℤ (ZMod 5))).map (𝟙 emptyModule)
        (tensorProductTmul (algebraMap ℤ (ZMod 5)) emptyModule emptyVector 1) = 0 := by
  exact (tensorFunctor_map_tmul (algebraMap ℤ (ZMod 5)) (𝟙 emptyModule) emptyVector 1).trans
    ((congrArg (fun m : emptyModule ↦
      tensorProductTmul (algebraMap ℤ (ZMod 5)) emptyModule m 1)
      (Subsingleton.elim emptyVector 0)).trans
        (tensorProductTmul_zero_left (algebraMap ℤ (ZMod 5)) emptyModule 1))

private theorem tensorFunctor_zeroTarget :
    (tensorFunctor (algebraMap ℤ PUnit)).map (𝟙 Z)
        (tensorProductTmul (algebraMap ℤ PUnit) Z sourceUnit 1) = 0 := by
  exact (tensorFunctor_map_tmul (algebraMap ℤ PUnit) (𝟙 Z) sourceUnit 1).trans
    ((congrArg (tensorProductTmul (algebraMap ℤ PUnit) Z sourceUnit)
      (Subsingleton.elim (1 : PUnit) 0)).trans
        (tensorProductTmul_zero_right (algebraMap ℤ PUnit) Z sourceUnit))

private theorem tensorFunctor_allZero :
    (tensorFunctor (algebraMap PUnit PUnit)).map (𝟙 allZeroModule)
        (tensorProductTmul (algebraMap PUnit PUnit) allZeroModule 0 1) = 0 := by
  exact (tensorFunctor_map_tmul (algebraMap PUnit PUnit) (𝟙 allZeroModule) 0 1).trans
    (tensorProductTmul_zero_left (algebraMap PUnit PUnit) allZeroModule 1)

example : (functor' (algebraMap ℤ (ZMod 5))).obj emptyModule ≅
    (tensorFunctor (algebraMap ℤ (ZMod 5))).obj emptyModule :=
  (tensorProductLinearEquiv (algebraMap ℤ (ZMod 5)) emptyModule).toModuleIso

example : (functor' (algebraMap ℤ PUnit)).obj Z ≅
    (tensorFunctor (algebraMap ℤ PUnit)).obj Z :=
  (tensorProductLinearEquiv (algebraMap ℤ PUnit) Z).toModuleIso

example : (functor' (algebraMap PUnit PUnit)).obj allZeroModule ≅
    (tensorFunctor (algebraMap PUnit PUnit)).obj allZeroModule :=
  (tensorProductLinearEquiv (algebraMap PUnit PUnit) allZeroModule).toModuleIso

/-! Independent lifts do not require the carrier universe to dominate either ring. -/

section Lifts

attribute [local instance] ULift.algebra'

private abbrev LiftR := ULift.{uR} ℤ
private abbrev LiftS := ULift.{uS} (ZMod 5)
private abbrev LiftM := ULift.{uM} (Fin 1 → ℤ)

private instance liftedBaseModule : Module LiftR.{uR}ᵐᵒᵖ (Fin 1 → ℤ) :=
  Module.compHom _ (RingHom.op (ULift.ringEquiv : LiftR.{uR} ≃+* ℤ).toRingHom)
private instance liftedCarrierModule : Module LiftR.{uR}ᵐᵒᵖ LiftM.{uM} := ULift.module'

private abbrev liftedModule := ModuleCat.of LiftR.{uR}ᵐᵒᵖ LiftM.{uM}
private abbrev liftedLeft :=
  (ModuleCat.restrictScalars (RingEquiv.toOpposite LiftR.{uR}).toRingHom).obj
    liftedModule.{uR, uM}
private abbrev liftedCoefficient :=
  (ModuleCat.restrictScalars (algebraMap LiftR.{uR} LiftS.{uS})).obj
    (ModuleCat.of LiftS.{uS} LiftS.{uS})

private def liftedTensor :
    tensorProductObj (algebraMap LiftR.{uR} LiftS.{uS}) liftedModule.{uR, uM} :=
  tensorProductTmul (algebraMap LiftR.{uR} LiftS.{uS}) liftedModule.{uR, uM}
    (ULift.up sourceUnit) (ULift.up (1 : ZMod 5))

private theorem lifted_forward :
    tensorProductLinearEquiv (algebraMap LiftR.{uR} LiftS.{uS}) liftedModule.{uR, uM}
        (tmul (algebraMap LiftR.{uR} LiftS.{uS})
          (ULift.up sourceUnit : LiftM.{uM}) (ULift.up 1)) = liftedTensor.{uR, uS, uM} :=
  tensorProductLinearEquiv_tmul (algebraMap LiftR.{uR} LiftS.{uS})
    liftedModule.{uR, uM} (ULift.up sourceUnit) (ULift.up 1)

private theorem lifted_inverse :
    (tensorProductLinearEquiv (algebraMap LiftR.{uR} LiftS.{uS}) liftedModule.{uR, uM}).symm
        liftedTensor.{uR, uS, uM} =
      tmul (algebraMap LiftR.{uR} LiftS.{uS}) (ULift.up sourceUnit : LiftM.{uM}) (ULift.up 1) :=
  tensorProductLinearEquiv_symm_tmul (algebraMap LiftR.{uR} LiftS.{uS})
    liftedModule.{uR, uM} (ULift.up sourceUnit) (ULift.up 1)

private def raisedSource : tensorProductObj (algebraMap LiftR.{1} LiftS.{0}) liftedModule.{1, 0} :=
  liftedTensor.{1, 0, 0}
private def raisedOutput : tensorProductObj (algebraMap LiftR.{0} LiftS.{1}) liftedModule.{0, 0} :=
  liftedTensor.{0, 1, 0}
private def raisedCarrier : tensorProductObj (algebraMap LiftR.{0} LiftS.{0}) liftedModule.{0, 1} :=
  liftedTensor.{0, 0, 1}

private theorem raisedSource_inverse :
    (tensorProductLinearEquiv (algebraMap LiftR.{1} LiftS.{0}) liftedModule.{1, 0}).symm
        raisedSource =
      tmul (algebraMap LiftR.{1} LiftS.{0}) (ULift.up sourceUnit : LiftM.{0}) (ULift.up 1) :=
  lifted_inverse.{1, 0, 0}

private theorem raisedOutput_inverse :
    (tensorProductLinearEquiv (algebraMap LiftR.{0} LiftS.{1}) liftedModule.{0, 0}).symm
        raisedOutput =
      tmul (algebraMap LiftR.{0} LiftS.{1}) (ULift.up sourceUnit : LiftM.{0}) (ULift.up 1) :=
  lifted_inverse.{0, 1, 0}

private theorem raisedCarrier_inverse :
    (tensorProductLinearEquiv (algebraMap LiftR.{0} LiftS.{0}) liftedModule.{0, 1}).symm
        raisedCarrier =
      tmul (algebraMap LiftR.{0} LiftS.{0}) (ULift.up sourceUnit : LiftM.{1}) (ULift.up 1) :=
  lifted_inverse.{0, 0, 1}

private def liftedCategoricalTensor :
    (ModuleCat.restrictScalars (RingEquiv.toOpposite LiftS.{uS}).symm.toRingHom).obj
      ((ModuleCat.extendScalars (algebraMap LiftR.{uR} LiftS.{uS})).obj
        liftedLeft.{uR, uM}) :=
  @TensorProduct.tmul LiftR.{uR} _ liftedCoefficient.{uR, uS} liftedLeft.{uR, uM} _ _
    liftedCoefficient.isModule liftedLeft.isModule (ULift.up (1 : ZMod 5))
    (ULift.up sourceUnit)

private theorem lifted_categorical_inverse :
    (extendScalarsLinearEquiv (algebraMap LiftR.{uR} LiftS.{uS}) liftedModule.{uR, uM}).symm
        liftedCategoricalTensor.{uR, uS, uM} =
      tmul (algebraMap LiftR.{uR} LiftS.{uS})
        (ULift.up sourceUnit : LiftM.{uM}) (ULift.up 1) :=
  extendScalarsLinearEquiv_symm_tmul (algebraMap LiftR.{uR} LiftS.{uS})
    liftedModule.{uR, uM} (ULift.up sourceUnit) (ULift.up 1)

private def raisedCategoricalOutput :
    (ModuleCat.restrictScalars (RingEquiv.toOpposite LiftS.{1}).symm.toRingHom).obj
      ((ModuleCat.extendScalars (algebraMap LiftR.{0} LiftS.{1})).obj liftedLeft.{0, 0}) :=
  liftedCategoricalTensor.{0, 1, 0}

private theorem raisedCategoricalOutput_inverse :
    (extendScalarsLinearEquiv (algebraMap LiftR.{0} LiftS.{1}) liftedModule.{0, 0}).symm
        raisedCategoricalOutput =
      tmul (algebraMap LiftR.{0} LiftS.{1})
        (ULift.up sourceUnit : LiftM.{0}) (ULift.up 1) :=
  lifted_categorical_inverse.{0, 1, 0}

private theorem lifted_tensorFunctor_identity :
    (tensorFunctor (algebraMap LiftR.{uR} LiftS.{uS})).map
        (𝟙 liftedModule.{uR, uM}) liftedTensor.{uR, uS, uM} =
      liftedTensor.{uR, uS, uM} := by
  exact tensorFunctor_map_tmul (algebraMap LiftR.{uR} LiftS.{uS})
    (𝟙 liftedModule.{uR, uM}) (ULift.up sourceUnit) (ULift.up 1)

private theorem raisedSource_tensorFunctor_identity :
    (tensorFunctor (algebraMap LiftR.{1} LiftS.{0})).map
      (𝟙 liftedModule.{1, 0}) raisedSource = raisedSource :=
  lifted_tensorFunctor_identity.{1, 0, 0}

private theorem raisedOutput_tensorFunctor_identity :
    (tensorFunctor (algebraMap LiftR.{0} LiftS.{1})).map
      (𝟙 liftedModule.{0, 0}) raisedOutput = raisedOutput :=
  lifted_tensorFunctor_identity.{0, 1, 0}

private theorem raisedCarrier_tensorFunctor_identity :
    (tensorFunctor (algebraMap LiftR.{0} LiftS.{0})).map
      (𝟙 liftedModule.{0, 1}) raisedCarrier = raisedCarrier :=
  lifted_tensorFunctor_identity.{0, 0, 1}

example : (functor' (algebraMap LiftR.{1} LiftS.{0})).obj liftedModule.{1, 0} ≅
    (tensorFunctor (algebraMap LiftR.{1} LiftS.{0})).obj liftedModule.{1, 0} :=
  (tensorProductLinearEquiv (algebraMap LiftR.{1} LiftS.{0}) liftedModule.{1, 0}).toModuleIso

example : (functor' (algebraMap LiftR.{0} LiftS.{1})).obj liftedModule.{0, 0} ≅
    (tensorFunctor (algebraMap LiftR.{0} LiftS.{1})).obj liftedModule.{0, 0} :=
  (tensorProductLinearEquiv (algebraMap LiftR.{0} LiftS.{1}) liftedModule.{0, 0}).toModuleIso

example : (functor' (algebraMap LiftR.{0} LiftS.{0})).obj liftedModule.{0, 1} ≅
    (tensorFunctor (algebraMap LiftR.{0} LiftS.{0})).obj liftedModule.{0, 1} :=
  (tensorProductLinearEquiv (algebraMap LiftR.{0} LiftS.{0}) liftedModule.{0, 1}).toModuleIso

end Lifts

end ProjectiveModulesTests.RightExtensionTensorProduct
