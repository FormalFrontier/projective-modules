/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.RightExtensionComparisonCoherence
import ProjectiveModulesTests.RightFreeScalarExtensionClient
import Mathlib.Tactic.NormNum

/-!
# Matrix clients for right-extension unit and associativity laws

The scalar chain is a projection from a product of integral matrix rings,
entrywise reduction followed by a diagonal map into a product of matrix rings
modulo five, and another projection. A rank-one free module detects ordered
triple coefficients. With coefficients `E12`, `(E21, E11)` and `E12`, the
ordered product is `E12`, whereas reversing either of the two multiplications
in the final coefficient gives zero.

Matrix rings and entrywise reduction reuse the public providers in
`RightFreeScalarExtensionClient`. Tensor coordinates and comparison evaluation
reuse the balanced right-extension APIs of Prism and Lens. Matrix units and
ring and index lifts use Mathlib. Lifting the finite index raises the module
carrier without introducing a new scalar-extension construction.

All declarations in this module are private importing examples.
-/

noncomputable section

namespace ProjectiveModulesTests.RightExtensionComparisonCoherence

open ModuleCat.RightExtension

private abbrev A := RightFreeScalarExtension.IntMatrices
private abbrev B := RightFreeScalarExtension.ModFiveMatrices
private abbrev R := A × A
private abbrev S := A
private abbrev T := B × B
private abbrev U := B
private abbrev M := Fin 1 → R

private def φ : R →+* S := RingHom.fst A A
private def ψ : S →+* T :=
  RightFreeScalarExtension.modFive.prod RightFreeScalarExtension.modFive
private def θ : T →+* U := RingHom.fst B B

private def basisOne : M := fun _ ↦ 1
private def s : S := Matrix.single (0 : Fin 2) 1 1
private def t : T := (Matrix.single (1 : Fin 2) 0 1, Matrix.single 0 0 1)
private def u : U := Matrix.single (0 : Fin 2) 1 1
private def e12 : U := Matrix.single (0 : Fin 2) 1 1
private def r : R := (Matrix.single (1 : Fin 2) 0 1, 0)

private theorem coefficient_one_ne_zero : (1 : ZMod 5) ≠ 0 := by
  intro h
  have h51 : (5 : ℕ) = 1 := ZMod.one_eq_zero_iff.mp h
  norm_num at h51

private theorem projection_kernel_ne_zero : ((0 : A), (1 : A)) ≠ (0 : R) := by
  intro h
  have h00 := congrArg (fun x : R ↦ x.2 0 0) h
  norm_num at h00

private theorem φ_not_injective : ¬ Function.Injective φ := by
  intro h
  apply projection_kernel_ne_zero
  exact h (show φ ((0 : A), (1 : A)) = φ 0 from rfl)

private theorem ψ_not_injective : ¬ Function.Injective ψ := by
  intro h
  have hi : ψ (Matrix.single (0 : Fin 2) 1 (5 : ℤ)) = ψ 0 := by
    ext <;> simp [ψ, RightFreeScalarExtension.modFive_single,
      RightFreeScalarExtension.five_modFive]
  have h01 := congrArg (fun x : S ↦ x 0 1) (h hi)
  norm_num at h01

private theorem θ_not_injective : ¬ Function.Injective θ := by
  intro h
  have hk := h (show θ ((0 : B), (1 : B)) = θ 0 from rfl)
  apply coefficient_one_ne_zero
  simpa using congrArg (fun x : T ↦ x.2 0 0) hk

private theorem reduced_s : θ (ψ s) = Matrix.single (0 : Fin 2) 1 1 := by
  simpa [θ, ψ, s] using RightFreeScalarExtension.modFive_single 0 1 (1 : ℤ)

private theorem ordered_coefficient : θ (ψ s * t) * u = e12 := by
  rw [θ.map_mul, reduced_s]
  simp [θ, t, u, e12]

private theorem inner_reversed_coefficient : θ (t * ψ s) * u = 0 := by
  rw [θ.map_mul, reduced_s]
  simp [θ, t, u]

private theorem outer_reversed_coefficient : u * θ (ψ s * t) = 0 := by
  rw [θ.map_mul, reduced_s]
  simp [θ, t, u]

private theorem e12_ne_zero : e12 ≠ 0 := by
  intro h
  apply coefficient_one_ne_zero
  simpa [e12] using congrArg (fun x : U ↦ x 0 1) h

private theorem inner_order_matters : θ (ψ s * t) * u ≠ θ (t * ψ s) * u := by
  rw [ordered_coefficient, inner_reversed_coefficient]
  exact e12_ne_zero

private theorem outer_order_matters : θ (ψ s * t) * u ≠ u * θ (ψ s * t) := by
  rw [ordered_coefficient, outer_reversed_coefficient]
  exact e12_ne_zero

private def tripleTensor : Obj θ (Obj ψ (Obj φ M)) :=
  tmul θ (tmul ψ (tmul φ basisOne s) t) u

private def firstRoute :
    Obj θ (Obj ψ (Obj φ M)) →ₗ[Uᵐᵒᵖ] Obj (θ.comp (ψ.comp φ)) M :=
  (compLinearEquiv (ψ.comp φ) θ M).toLinearMap.comp
    (map θ (compLinearEquiv φ ψ M).toLinearMap)

private def secondRoute :
    Obj θ (Obj ψ (Obj φ M)) →ₗ[Uᵐᵒᵖ] Obj (θ.comp (ψ.comp φ)) M :=
  (compLinearEquiv φ (θ.comp ψ) M).toLinearMap.comp
    (compLinearEquiv ψ θ (Obj φ M)).toLinearMap

private def coordinates : Obj (θ.comp (ψ.comp φ)) M ≃ₗ[Uᵐᵒᵖ] (Fin 1 → U) :=
  rightFreeLinearEquiv (θ.comp (ψ.comp φ)) (Fin 1)

private theorem tensor_coefficient_injective (a b : U)
    (h : tmul (θ.comp (ψ.comp φ)) basisOne a =
      tmul (θ.comp (ψ.comp φ)) basisOne b) : a = b := by
  have hc := congrArg coordinates h
  simpa [coordinates, basisOne] using congrArg (fun x : Fin 1 → U ↦ x 0) hc

private theorem ordered_tensor_ne_zero :
    tmul (θ.comp (ψ.comp φ)) basisOne e12 ≠ 0 := by
  intro h
  have hc := congrArg coordinates h
  apply coefficient_one_ne_zero
  simpa [coordinates, basisOne, e12] using
    congrArg (fun x : Fin 1 → U ↦ x 0 0 1) hc

private theorem firstRoute_image :
    firstRoute tripleTensor = tmul (θ.comp (ψ.comp φ)) basisOne (θ (ψ s * t) * u) := by
  simp only [firstRoute, tripleTensor, LinearMap.comp_apply, map_tmul,
    LinearEquiv.coe_coe, compLinearEquiv_tmul]

private theorem firstRoute_image_ne_zero : firstRoute tripleTensor ≠ 0 := by
  rw [firstRoute_image, ordered_coefficient]
  exact ordered_tensor_ne_zero

private theorem tripleTensor_ne_zero : tripleTensor ≠ 0 := by
  intro h
  apply firstRoute_image_ne_zero
  rw [h, _root_.map_zero]

private theorem firstRoute_detects_inner_order :
    firstRoute tripleTensor ≠
      tmul (θ.comp (ψ.comp φ)) basisOne (θ (t * ψ s) * u) := by
  rw [firstRoute_image]
  intro h
  exact inner_order_matters (tensor_coefficient_injective _ _ h)

private theorem firstRoute_detects_outer_order :
    firstRoute tripleTensor ≠
      tmul (θ.comp (ψ.comp φ)) basisOne (u * θ (ψ s * t)) := by
  rw [firstRoute_image]
  intro h
  exact outer_order_matters (tensor_coefficient_injective _ _ h)

private theorem left_unit_at_matrix_tensor :
    compLinearEquiv (RingHom.id R) φ M
        (tmul φ (tmul (RingHom.id R) basisOne r) s) =
      map φ (idLinearEquiv R M).toLinearMap
        (tmul φ (tmul (RingHom.id R) basisOne r) s) := by
  exact LinearMap.congr_fun (compLinearEquiv_id_left φ M) _

private theorem right_unit_at_matrix_tensor :
    compLinearEquiv φ (RingHom.id S) M
        (tmul (RingHom.id S) (tmul φ basisOne s) (φ r)) =
      idLinearEquiv S (Obj φ M)
        (tmul (RingHom.id S) (tmul φ basisOne s) (φ r)) := by
  exact DFunLike.congr_fun (compLinearEquiv_id_right φ M) _

private theorem assoc_at_matrix_tensor : firstRoute tripleTensor = secondRoute tripleTensor := by
  exact LinearMap.congr_fun (compLinearEquiv_assoc φ ψ θ M) tripleTensor

/-! Independent ring lifts and a raised finite coordinate index. -/

universe vR vS vT vU vM

private abbrev LiftedR := ULift.{vR} R
private abbrev LiftedS := ULift.{vS} S
private abbrev LiftedT := ULift.{vT} T
private abbrev LiftedU := ULift.{vU} U

private def liftedφ : LiftedR.{vR} →+* LiftedS.{vS} :=
  (ULift.ringEquiv : LiftedS.{vS} ≃+* S).symm.toRingHom.comp
    (φ.comp (ULift.ringEquiv : LiftedR.{vR} ≃+* R).toRingHom)

private def liftedψ : LiftedS.{vS} →+* LiftedT.{vT} :=
  (ULift.ringEquiv : LiftedT.{vT} ≃+* T).symm.toRingHom.comp
    (ψ.comp (ULift.ringEquiv : LiftedS.{vS} ≃+* S).toRingHom)

private def liftedθ : LiftedT.{vT} →+* LiftedU.{vU} :=
  (ULift.ringEquiv : LiftedU.{vU} ≃+* U).symm.toRingHom.comp
    (θ.comp (ULift.ringEquiv : LiftedT.{vT} ≃+* T).toRingHom)

private theorem liftedφ_not_injective : ¬ Function.Injective liftedφ.{vR, vS} := by
  intro h
  apply projection_kernel_ne_zero
  exact congrArg ULift.down
    (h (show liftedφ.{vR, vS} (ULift.up ((0 : A), (1 : A))) =
      liftedφ.{vR, vS} (ULift.up (0 : R)) from rfl))

private theorem lifted_ordered_tensor_ne_zero :
    tmul (liftedθ.{vT, vU}.comp (liftedψ.{vS, vT}.comp liftedφ.{vR, vS}))
      (fun _ : ULift.{vM} (Fin 1) ↦ (1 : LiftedR.{vR})) (ULift.up e12) ≠ 0 := by
  intro h
  have hc := congrArg
    (rightFreeLinearEquiv
      (liftedθ.{vT, vU}.comp (liftedψ.{vS, vT}.comp liftedφ.{vR, vS}))
      (ULift.{vM} (Fin 1))) h
  apply coefficient_one_ne_zero
  simpa [e12] using
    congrArg (fun x : ULift.{vM} (Fin 1) → LiftedU.{vU} ↦
      (x (ULift.up 0)).down 0 1) hc

private abbrev HigherM : Type 1 := ULift.{1} (Fin 1) → LiftedR.{0}

-- Intermediate scalar Type 2, input module Type 1, target scalar Type 0.
private abbrev HigherIterated : Type 2 :=
  Obj liftedθ.{0, 0} (Obj liftedψ.{2, 0} (Obj liftedφ.{0, 2} HigherM))

private abbrev HigherDirect : Type 1 :=
  Obj (liftedθ.{0, 0}.comp (liftedψ.{2, 0}.comp liftedφ.{0, 2})) HigherM

private def higherTensor : HigherIterated :=
  tmul liftedθ.{0, 0}
    (tmul liftedψ.{2, 0}
      (tmul liftedφ.{0, 2} (fun _ ↦ (1 : LiftedR.{0})) (ULift.up s))
      (ULift.up t)) (ULift.up u)

private theorem higher_firstRoute_image :
    compLinearEquiv (liftedψ.{2, 0}.comp liftedφ.{0, 2}) liftedθ.{0, 0} HigherM
        (map liftedθ.{0, 0}
          (compLinearEquiv liftedφ.{0, 2} liftedψ.{2, 0} HigherM).toLinearMap
          higherTensor) =
      (tmul (liftedθ.{0, 0}.comp (liftedψ.{2, 0}.comp liftedφ.{0, 2}))
        (fun _ ↦ (1 : LiftedR.{0})) (ULift.up e12) : HigherDirect) := by
  simp only [higherTensor, map_tmul, LinearEquiv.coe_coe, compLinearEquiv_tmul]
  change tmul _ _ (ULift.up (θ (ψ s * t) * u)) = _
  rw [ordered_coefficient]

private theorem higher_firstRoute_image_ne_zero :
    compLinearEquiv (liftedψ.{2, 0}.comp liftedφ.{0, 2}) liftedθ.{0, 0} HigherM
        (map liftedθ.{0, 0}
          (compLinearEquiv liftedφ.{0, 2} liftedψ.{2, 0} HigherM).toLinearMap
          higherTensor) ≠ 0 := by
  rw [higher_firstRoute_image]
  exact lifted_ordered_tensor_ne_zero

private theorem higher_left_unit_at_tensor :
    compLinearEquiv (RingHom.id LiftedR.{0}) liftedφ.{0, 2} HigherM
        (tmul liftedφ.{0, 2}
          (tmul (RingHom.id LiftedR.{0}) (fun _ ↦ (1 : LiftedR.{0})) (ULift.up r))
          (ULift.up s)) =
      map liftedφ.{0, 2} (idLinearEquiv LiftedR.{0} HigherM).toLinearMap
        (tmul liftedφ.{0, 2}
          (tmul (RingHom.id LiftedR.{0}) (fun _ ↦ (1 : LiftedR.{0})) (ULift.up r))
          (ULift.up s)) := by
  exact LinearMap.congr_fun (compLinearEquiv_id_left liftedφ.{0, 2} HigherM) _

private theorem higher_right_unit_at_tensor :
    compLinearEquiv liftedφ.{0, 2} (RingHom.id LiftedS.{2}) HigherM
        (tmul (RingHom.id LiftedS.{2})
          (tmul liftedφ.{0, 2} (fun _ ↦ (1 : LiftedR.{0})) (ULift.up s))
          (ULift.up (φ r))) =
      idLinearEquiv LiftedS.{2} (Obj liftedφ.{0, 2} HigherM)
        (tmul (RingHom.id LiftedS.{2})
          (tmul liftedφ.{0, 2} (fun _ ↦ (1 : LiftedR.{0})) (ULift.up s))
          (ULift.up (φ r))) := by
  exact DFunLike.congr_fun (compLinearEquiv_id_right liftedφ.{0, 2} HigherM) _

private theorem higher_assoc_at_tensor :
    (compLinearEquiv (liftedψ.{2, 0}.comp liftedφ.{0, 2}) liftedθ.{0, 0}
        HigherM).toLinearMap.comp
        (map liftedθ.{0, 0}
          (compLinearEquiv liftedφ.{0, 2} liftedψ.{2, 0} HigherM).toLinearMap)
        higherTensor =
      (compLinearEquiv liftedφ.{0, 2} (liftedθ.{0, 0}.comp liftedψ.{2, 0})
        HigherM).toLinearMap.comp
        (compLinearEquiv liftedψ.{2, 0} liftedθ.{0, 0}
          (Obj liftedφ.{0, 2} HigherM)).toLinearMap higherTensor := by
  exact LinearMap.congr_fun
    (compLinearEquiv_assoc liftedφ.{0, 2} liftedψ.{2, 0} liftedθ.{0, 0} HigherM)
    higherTensor

end ProjectiveModulesTests.RightExtensionComparisonCoherence
