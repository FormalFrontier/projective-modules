/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
-- Contributors: Lens
module

import ProjectiveModules.Module.RightExtensionComparison
import ProjectiveModules.Module.RightExtensionFiniteResidue
import ProjectiveModulesTests.RightFreeScalarExtensionClient
import Mathlib.Algebra.Module.PUnit
import Mathlib.Algebra.Module.ULift
import Mathlib.Tactic.NormNum

/-!
# Right-extension comparison clients

The coefficient chain is the first projection from a product of integral
matrix rings, followed by entrywise reduction modulo five. Both maps have
explicit nonzero kernel elements. Rank-one free coordinates distinguish the
products E12 E21 and E21 E12, and detect nonzero tensors without unfolding
the balanced tensor quotient.

Identity, composition, zero-module, zero-target and all-zero examples use the
comparison application API. Four independent carrier/scalar lifts use the
opposite of the down ring homomorphism to transport the right action.

The matrix rings and reduction map reuse the public providers in
`RightFreeScalarExtensionClient`. Free tensor coordinates and equivalence
transport reuse the existing right-extension formalization (Prism and Lens);
matrix units, ring and carrier lifts, and module transport reuse Mathlib.

All declarations in this module are private importing examples.
-/

noncomputable section

namespace ProjectiveModulesTests.RightExtensionComparison

open ModuleCat.RightExtension

private abbrev A := RightFreeScalarExtension.IntMatrices
private abbrev B := RightFreeScalarExtension.ModFiveMatrices
private abbrev R := A × A
private abbrev S := A
private abbrev T := B
private abbrev M := Fin 1 → R

private def φ : R →+* S := RingHom.fst A A
private def ψ : S →+* T := RightFreeScalarExtension.modFive
private def basisOne : M := fun _ ↦ 1
private def s : S := Matrix.single (0 : Fin 2) 1 1
private def t : T := Matrix.single (1 : Fin 2) 0 1
private def e11 : T := Matrix.single (0 : Fin 2) 0 1
private def e22 : T := Matrix.single (1 : Fin 2) 1 1

private theorem modFive_one_ne_zero : (1 : ZMod 5) ≠ 0 := by
  intro h
  have h51 : (5 : ℕ) = 1 := ZMod.one_eq_zero_iff.mp h
  norm_num at h51

private theorem projection_kernel_ne_zero : ((0 : S), (1 : S)) ≠ (0 : R) := by
  intro h
  have h00 := congrArg (fun x : R ↦ x.2 0 0) h
  norm_num at h00

private theorem projection_kernel_image : φ ((0 : S), (1 : S)) = 0 := rfl

private theorem projection_not_injective : ¬ Function.Injective φ := by
  intro h
  apply projection_kernel_ne_zero
  apply h
  simpa only [_root_.map_zero] using projection_kernel_image

-- The natural-number cast in the matrix ring is five times its identity.
private theorem fiveIdentity_ne_zero : (5 : S) ≠ 0 := by
  intro h
  have h00 := congrArg (fun x : S ↦ x 0 0) h
  norm_num [Matrix.ofNat_apply] at h00

private theorem fiveIdentity_image : ψ (5 : S) = 0 := by
  calc
    ψ (5 : S) = (5 : T) := _root_.map_ofNat ψ 5
    _ = 0 := by
      ext i j
      simp [Matrix.ofNat_apply, RightFreeScalarExtension.five_modFive]

private theorem reduction_not_injective : ¬ Function.Injective ψ := by
  intro h
  apply fiveIdentity_ne_zero
  apply h
  simpa only [_root_.map_zero] using fiveIdentity_image

private theorem reduction_s : ψ s = Matrix.single (0 : Fin 2) 1 1 := by
  simpa [ψ, s] using RightFreeScalarExtension.modFive_single 0 1 (1 : ℤ)

private theorem coefficient_order : ψ s * t = e11 := by
  rw [reduction_s]
  simp [t, e11]

private theorem coefficient_reversed : t * ψ s = e22 := by
  rw [reduction_s]
  simp [t, e22]

private theorem e11_ne_zero : e11 ≠ 0 := by
  intro h
  apply modFive_one_ne_zero
  simpa [e11] using congrArg (fun x : T ↦ x 0 0) h

private theorem e11_ne_e22 : e11 ≠ e22 := by
  intro h
  apply modFive_one_ne_zero
  simpa [e11, e22] using congrArg (fun x : T ↦ x 0 0) h

private theorem target_noncommutative : ψ s * t ≠ t * ψ s := by
  rw [coefficient_order, coefficient_reversed]
  exact e11_ne_e22

/-! The following tensor data and coordinate proofs use only existing APIs. -/

private def directCoordinates : Obj (ψ.comp φ) M ≃ₗ[Tᵐᵒᵖ] (Fin 1 → T) :=
  rightFreeLinearEquiv (ψ.comp φ) (Fin 1)

private def iteratedCoordinates : Obj ψ (Obj φ M) ≃ₗ[Tᵐᵒᵖ] (Fin 1 → T) :=
  (mapLinearEquiv ψ (rightFreeLinearEquiv φ (Fin 1))).trans
    (rightFreeLinearEquiv ψ (Fin 1))

private def extendedUnit : Obj (ψ.comp φ) M := tmul (ψ.comp φ) basisOne 1
private def rightTensor : Obj (ψ.comp φ) M := tmul (ψ.comp φ) basisOne e11
private def reversedTensor : Obj (ψ.comp φ) M := tmul (ψ.comp φ) basisOne e22
private def nestedTensor : Obj ψ (Obj φ M) := tmul ψ (tmul φ basisOne s) t

private theorem direct_coordinates_basis (b : T) :
    directCoordinates (tmul (ψ.comp φ) basisOne b) = fun _ ↦ b := by
  simp [directCoordinates, basisOne]

private theorem iterated_coordinates_tmul (x : M) (a : S) (b : T) :
    iteratedCoordinates (tmul ψ (tmul φ x a) b) =
      fun i ↦ (ψ.comp φ) (x i) * (ψ a * b) := by
  ext i
  simp [iteratedCoordinates, map_mul, mul_assoc]

private theorem extendedUnit_ne_zero : extendedUnit ≠ 0 := by
  intro h
  have hc := congrArg directCoordinates h
  have h00 := congrArg (fun x : Fin 1 → T ↦ x 0 0 0) hc
  apply modFive_one_ne_zero
  simpa [extendedUnit, direct_coordinates_basis] using h00

private theorem rightTensor_ne_zero : rightTensor ≠ 0 := by
  intro h
  have hc := congrArg directCoordinates h
  have h00 := congrArg (fun x : Fin 1 → T ↦ x 0 0 0) hc
  apply modFive_one_ne_zero
  simpa [rightTensor, direct_coordinates_basis, e11] using h00

private theorem rightTensor_ne_reversedTensor : rightTensor ≠ reversedTensor := by
  intro h
  have hc := congrArg directCoordinates h
  have he := congrArg (fun x : Fin 1 → T ↦ x 0) hc
  apply e11_ne_e22
  simpa [rightTensor, reversedTensor, direct_coordinates_basis] using he

private theorem nestedTensor_ne_zero : nestedTensor ≠ 0 := by
  intro h
  have hc := congrArg iteratedCoordinates h
  have h00 := congrArg (fun x : Fin 1 → T ↦ x 0 0 0) hc
  apply modFive_one_ne_zero
  simpa [nestedTensor, iterated_coordinates_tmul, basisOne, coefficient_order, e11]
    using h00

/-! Comparison applications and agreement with finite-free coordinates. -/

private theorem comparison_on_nestedTensor :
    compLinearEquiv φ ψ M nestedTensor = rightTensor := by
  simp only [nestedTensor, compLinearEquiv_tmul, coefficient_order, rightTensor]

private theorem comparison_image_ne_zero :
    compLinearEquiv φ ψ M nestedTensor ≠ 0 := by
  rw [comparison_on_nestedTensor]
  exact rightTensor_ne_zero

private theorem comparison_detects_order :
    compLinearEquiv φ ψ M nestedTensor ≠ reversedTensor := by
  rw [comparison_on_nestedTensor]
  exact rightTensor_ne_reversedTensor

private theorem comparison_inverse_on_rightTensor :
    (compLinearEquiv φ ψ M).symm rightTensor =
      tmul ψ (tmul φ basisOne 1) e11 := by
  simp only [rightTensor, compLinearEquiv_symm_tmul]

-- Compare the core followed by free coordinates with the independently
-- assembled coordinates; neither coordinate equivalence is reconstructed.
private theorem comparison_free_coordinates (x : M) (a : S) (b : T) :
    ((compLinearEquiv φ ψ M).trans directCoordinates)
        (tmul ψ (tmul φ x a) b) =
      iteratedCoordinates (tmul ψ (tmul φ x a) b) := by
  simp [directCoordinates, iteratedCoordinates, map_mul, mul_assoc]

private theorem comparison_inverse_free_coordinates (x : M) (b : T) :
    iteratedCoordinates ((compLinearEquiv φ ψ M).symm (tmul (ψ.comp φ) x b)) =
      directCoordinates (tmul (ψ.comp φ) x b) := by
  simp [directCoordinates, iteratedCoordinates]

private theorem noncommutative_identity (x : Fin 1 → S) (a : S) :
    idLinearEquiv S (Fin 1 → S) (tmul (RingHom.id S) x a) =
      fun i ↦ x i * a := by
  rw [idLinearEquiv_tmul]
  rfl

private theorem noncommutative_identity_inverse (x : Fin 1 → S) :
    (idLinearEquiv S (Fin 1 → S)).symm x = tmul (RingHom.id S) x 1 := by
  simp only [idLinearEquiv_symm_apply]

private theorem identity_at_matrix_unit :
    idLinearEquiv S (Fin 1 → S) (tmul (RingHom.id S) (fun _ ↦ 1) s) =
      fun _ ↦ s := by
  rw [noncommutative_identity]
  simp

/-! Zero boundaries retain unital maps; no map out of a zero ring is used
with a nontrivial target. The empty coordinate module is the zero module. -/

private abbrev ZeroM := Fin 0 → R

private theorem zeroModule_identity (x : ZeroM) (r : R) :
    idLinearEquiv R ZeroM (tmul (RingHom.id R) x r) = 0 := by
  rw [idLinearEquiv_tmul]
  exact Subsingleton.elim _ _

private theorem zeroModule_identity_inverse (x : ZeroM) :
    (idLinearEquiv R ZeroM).symm x = 0 := by
  apply (rightFreeLinearEquiv (RingHom.id R) (Fin 0)).injective
  rw [idLinearEquiv_symm_apply]
  exact Subsingleton.elim _ _

private theorem zeroModule_composition (x : ZeroM) (a : S) (b : T) :
    compLinearEquiv φ ψ ZeroM (tmul ψ (tmul φ x a) b) = 0 := by
  apply (rightFreeLinearEquiv (ψ.comp φ) (Fin 0)).injective
  rw [compLinearEquiv_tmul, rightFreeLinearEquiv_tmul]
  exact Subsingleton.elim _ _

private theorem zeroModule_composition_inverse (x : ZeroM) (b : T) :
    (compLinearEquiv φ ψ ZeroM).symm (tmul (ψ.comp φ) x b) = 0 := by
  apply ((mapLinearEquiv ψ (rightFreeLinearEquiv φ (Fin 0))).trans
    (rightFreeLinearEquiv ψ (Fin 0))).injective
  rw [compLinearEquiv_symm_tmul]
  exact Subsingleton.elim _ _

private def toZero : S →+* PUnit where
  toFun _ := PUnit.unit
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem zeroTarget_composition (x : M) (a : S) (z : PUnit) :
    compLinearEquiv φ toZero M (tmul toZero (tmul φ x a) z) = 0 := by
  rw [compLinearEquiv_tmul]
  exact Module.eq_zero_of_zero_eq_one (R := PUnitᵐᵒᵖ) (x := _)
    (Subsingleton.elim _ _)

private theorem zeroTarget_composition_inverse (x : M) (z : PUnit) :
    (compLinearEquiv φ toZero M).symm (tmul (toZero.comp φ) x z) = 0 := by
  rw [compLinearEquiv_symm_tmul]
  exact Module.eq_zero_of_zero_eq_one (R := PUnitᵐᵒᵖ) (x := _)
    (Subsingleton.elim _ _)

private theorem allZero_identity (x r : PUnit) :
    idLinearEquiv PUnit PUnit (tmul (RingHom.id PUnit) x r) = 0 := by
  rw [idLinearEquiv_tmul]

private theorem allZero_identity_inverse (x : PUnit) :
    (idLinearEquiv PUnit PUnit).symm x = tmul (RingHom.id PUnit) x 1 := by
  simp only [idLinearEquiv_symm_apply]

private theorem allZero_composition (x a b : PUnit) :
    compLinearEquiv (RingHom.id PUnit) (RingHom.id PUnit) PUnit
      (tmul (RingHom.id PUnit) (tmul (RingHom.id PUnit) x a) b) = 0 := by
  rw [compLinearEquiv_tmul]
  exact Module.eq_zero_of_zero_eq_one (R := PUnitᵐᵒᵖ) (x := _)
    (Subsingleton.elim _ _)

private theorem allZero_composition_inverse (x b : PUnit) :
    (compLinearEquiv (RingHom.id PUnit) (RingHom.id PUnit) PUnit).symm
      (tmul ((RingHom.id PUnit).comp (RingHom.id PUnit)) x b) = 0 := by
  rw [compLinearEquiv_symm_tmul]
  exact Module.eq_zero_of_zero_eq_one (R := PUnitᵐᵒᵖ) (x := _)
    (Subsingleton.elim _ _)

/-! Four independent universes, with explicit transported action. -/

universe uR uS uT uM

private abbrev LiftedR := ULift.{uR} R
private abbrev LiftedS := ULift.{uS} S
private abbrev LiftedT := ULift.{uT} T
private abbrev LiftedM := ULift.{uM} M

private def sourceDown : LiftedR.{uR} →+* R :=
  (ULift.ringEquiv : LiftedR.{uR} ≃+* R).toRingHom

-- First restrict the old module along the OPPOSITE down homomorphism.
private instance liftedBaseModule : Module LiftedR.{uR}ᵐᵒᵖ M :=
  Module.compHom M (RingHom.op sourceDown.{uR})

-- Then use Mathlib's module-carrier lift, independently of the scalar lift.
private instance liftedCarrierModule : Module LiftedR.{uR}ᵐᵒᵖ LiftedM.{uM} :=
  inferInstance

private theorem lifted_smul (r : R) (x : M) :
    MulOpposite.op (ULift.up r : LiftedR.{uR}) • (ULift.up x : LiftedM.{uM}) =
      ULift.up (MulOpposite.op r • x) := rfl

private def liftedφ : LiftedR.{uR} →+* LiftedS.{uS} :=
  (ULift.ringEquiv : LiftedS.{uS} ≃+* S).symm.toRingHom.comp
    (φ.comp sourceDown.{uR})

private def liftedψ : LiftedS.{uS} →+* LiftedT.{uT} :=
  (ULift.ringEquiv : LiftedT.{uT} ≃+* T).symm.toRingHom.comp
    (ψ.comp (ULift.ringEquiv : LiftedS.{uS} ≃+* S).toRingHom)

private theorem liftedφ_up (r : R) :
    liftedφ.{uR, uS} (ULift.up r) = ULift.up (φ r) := rfl

private theorem liftedψ_up (a : S) :
    liftedψ.{uS, uT} (ULift.up a) = ULift.up (ψ a) := rfl

-- This coordinate identification is specific to the separately lifted
-- rank-one fixture, not a second scalar-extension construction.
private def liftedFreeEquiv :
    LiftedM.{uM} ≃ₗ[LiftedR.{uR}ᵐᵒᵖ] (Fin 1 → LiftedR.{uR}) where
  toFun x i := ULift.up (x.down i)
  invFun y := ULift.up (fun i ↦ (y i).down)
  left_inv _ := rfl
  right_inv y := by
    funext i
    exact ULift.ext _ _ rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def liftedDirectCoordinates :
    Obj (liftedψ.{uS, uT}.comp liftedφ.{uR, uS}) LiftedM.{uM}
      ≃ₗ[LiftedT.{uT}ᵐᵒᵖ] (Fin 1 → LiftedT.{uT}) :=
  (mapLinearEquiv (liftedψ.{uS, uT}.comp liftedφ.{uR, uS})
    liftedFreeEquiv).trans
      (rightFreeLinearEquiv (liftedψ.{uS, uT}.comp liftedφ.{uR, uS}) (Fin 1))

private theorem lifted_direct_coordinates (x : M) (b : T) :
    liftedDirectCoordinates
        (tmul (liftedψ.{uS, uT}.comp liftedφ.{uR, uS})
          (ULift.up x : LiftedM.{uM}) (ULift.up b)) =
      fun i ↦ ULift.up ((ψ.comp φ) (x i) * b) := by
  simp only [liftedDirectCoordinates, LinearEquiv.trans_apply,
    mapLinearEquiv_tmul, rightFreeLinearEquiv_tmul]
  funext i
  change (liftedψ.{uS, uT}.comp liftedφ.{uR, uS}) (ULift.up (x i)) * ULift.up b = _
  rw [RingHom.comp_apply, liftedφ_up, liftedψ_up]
  rfl

private theorem lifted_direct_coordinates_basis (b : T) :
    liftedDirectCoordinates
        (tmul (liftedψ.{uS, uT}.comp liftedφ.{uR, uS})
          (ULift.up basisOne : LiftedM.{uM}) (ULift.up b)) =
      fun _ ↦ ULift.up b := by
  simpa [basisOne] using (lifted_direct_coordinates basisOne b)

private theorem lifted_rightTensor_ne_zero :
    tmul (liftedψ.{uS, uT}.comp liftedφ.{uR, uS})
      (ULift.up basisOne : LiftedM.{uM}) (ULift.up e11) ≠ 0 := by
  intro h
  have hc := congrArg liftedDirectCoordinates h
  rw [lifted_direct_coordinates_basis, _root_.map_zero] at hc
  have h00 := congrArg (fun x : Fin 1 → LiftedT.{uT} ↦ (x 0).down 0 0) hc
  apply modFive_one_ne_zero
  simpa [e11] using h00

private theorem lifted_identity (x : M) (r : R) :
    idLinearEquiv LiftedR.{uR} LiftedM.{uM}
      (tmul (RingHom.id LiftedR.{uR}) (ULift.up x) (ULift.up r)) =
      ULift.up (MulOpposite.op r • x) := by
  rw [idLinearEquiv_tmul]
  exact lifted_smul r x

private theorem lifted_identity_inverse (x : M) :
    (idLinearEquiv LiftedR.{uR} LiftedM.{uM}).symm (ULift.up x) =
      tmul (RingHom.id LiftedR.{uR}) (ULift.up x) 1 := by
  simp only [idLinearEquiv_symm_apply]

private theorem lifted_composition (x : M) (a : S) (b : T) :
    compLinearEquiv liftedφ.{uR, uS} liftedψ.{uS, uT} LiftedM.{uM}
      (tmul liftedψ.{uS, uT} (tmul liftedφ.{uR, uS} (ULift.up x) (ULift.up a))
        (ULift.up b)) =
      tmul (liftedψ.{uS, uT}.comp liftedφ.{uR, uS}) (ULift.up x)
        (ULift.up (ψ a * b)) := by
  rw [compLinearEquiv_tmul, liftedψ_up]
  rfl

private theorem lifted_composition_inverse (x : M) (b : T) :
    (compLinearEquiv liftedφ.{uR, uS} liftedψ.{uS, uT} LiftedM.{uM}).symm
      (tmul (liftedψ.{uS, uT}.comp liftedφ.{uR, uS}) (ULift.up x) (ULift.up b)) =
      tmul liftedψ.{uS, uT} (tmul liftedφ.{uR, uS} (ULift.up x) 1) (ULift.up b) := by
  simp only [compLinearEquiv_symm_tmul]

private theorem lifted_comparison_image_ne_zero :
    compLinearEquiv liftedφ.{uR, uS} liftedψ.{uS, uT} LiftedM.{uM}
      (tmul liftedψ.{uS, uT}
        (tmul liftedφ.{uR, uS} (ULift.up basisOne) (ULift.up s)) (ULift.up t)) ≠ 0 := by
  rw [lifted_composition, coefficient_order]
  exact lifted_rightTensor_ne_zero

-- Here iterated extension has carrier Type 1; direct extension has carrier Type 0.
private abbrev HigherIntermediateIterated : Type 1 :=
  Obj liftedψ.{1, 0} (Obj liftedφ.{0, 1} LiftedM.{0})

private abbrev HigherIntermediateDirect : Type 0 :=
  Obj (liftedψ.{1, 0}.comp liftedφ.{0, 1}) LiftedM.{0}

private theorem higherIntermediate_comparison :
    compLinearEquiv liftedφ.{0, 1} liftedψ.{1, 0} LiftedM.{0}
      (tmul liftedψ.{1, 0} (tmul liftedφ.{0, 1} (ULift.up basisOne) (ULift.up s))
        (ULift.up t) : HigherIntermediateIterated) =
      (tmul (liftedψ.{1, 0}.comp liftedφ.{0, 1}) (ULift.up basisOne) (ULift.up e11) :
        HigherIntermediateDirect) := by
  rw [lifted_composition, coefficient_order]

-- Source scalar Type 1, input carrier Type 0, identity tensor carrier Type 1.
private theorem higherSource_identity (x : M) (r : R) :
    idLinearEquiv LiftedR.{1} LiftedM.{0}
      (tmul (RingHom.id LiftedR.{1}) (ULift.up x) (ULift.up r)) =
      (ULift.up (MulOpposite.op r • x) : LiftedM.{0}) := by
  exact lifted_identity x r

end ProjectiveModulesTests.RightExtensionComparison
