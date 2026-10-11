/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Lens
module

public import ProjectiveModules.Module.RightEndomorphismMatrix
import ProjectiveModules.Free.CountableAbsorption
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.Algebra.Ring.ULift
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.ZMod.Basic

/-!
# Specified-map scalar-extension clients

The inputs here are explicit constructions. Characteristic and functorial conclusions
use the library API rather than providing independent proofs of its laws.
The countable self-doubling construction reuses the existing CountableAbsorption
API (Prism), following the endomorphism-ring assembly motivated by Charles A.
Weibel, *The K-book*, Exercise I.1.7. Transvections, matrix units, swaps and lifts
reuse Mathlib; in particular no auxiliary category is introduced.
-/

public section

noncomputable section

namespace ProjectiveModulesTests.RightFreeScalarExtension

open scoped Matrix

abbrev IntMatrices := Matrix (Fin 2) (Fin 2) ℤ
abbrev ModFiveMatrices := Matrix (Fin 2) (Fin 2) (ZMod 5)
abbrev NatMatrices := Matrix (Fin 2) (Fin 2) ℕ

def modFive : IntMatrices →+* ModFiveMatrices :=
  (Int.castRingHom (ZMod 5)).mapMatrix

def natInt : NatMatrices →+* IntMatrices :=
  (Nat.castRingHom ℤ).mapMatrix

/-- Reuse the specified inverse supplied by Mathlib's module transvection. -/
def shear (R : Type*) [Ring R] (a : R) :
    (Fin 2 → R) ≃ₗ[Rᵐᵒᵖ] (Fin 2 → R) :=
  (Module.rightFreeCoordEquiv R (Fin 2)).symm.trans <|
    (LinearEquiv.transvection
      (f := LinearMap.proj (1 : Fin 2)) (v := Pi.single (0 : Fin 2) (MulOpposite.op a))
      (by simp)).trans (Module.rightFreeCoordEquiv R (Fin 2))

lemma shear_first (R : Type*) [Ring R] (a : R) (x : Fin 2 → R) :
    shear R a x 0 = x 0 + a * x 1 := by
  rfl

lemma shear_second (R : Type*) [Ring R] (a : R) (x : Fin 2 → R) :
    shear R a x 1 = x 1 := by
  simp [shear, LinearMap.transvection]

/-- Genuine noncommutativity, in the order needed by the apply formula. -/
private theorem intMatrix_unit_zero_one_mul_unit_one_zero :
    (Matrix.single (0 : Fin 2) 1 (1 : ℤ) : IntMatrices) * Matrix.single 1 0 1 =
      Matrix.single 0 0 1 := by
  simp

private theorem intMatrix_unit_one_zero_mul_unit_zero_one :
    (Matrix.single (1 : Fin 2) 0 (1 : ℤ) : IntMatrices) * Matrix.single 0 1 1 =
      Matrix.single 1 1 1 := by
  simp

lemma modFive_single (i j : Fin 2) (z : ℤ) :
    modFive (Matrix.single i j z) = Matrix.single i j (z : ZMod 5) := by
  ext a b
  by_cases ha : i = a <;> by_cases hb : j = b <;>
    simp [modFive, ha, hb]

lemma five_modFive : (5 : ZMod 5) = 0 :=
  ZMod.natCast_self 5

/-- The chosen coefficient homomorphism is not faithful. -/
private theorem modFive_not_injective : ¬ Function.Injective modFive := by
  have hz : modFive (Matrix.single (0 : Fin 2) 1 (5 : ℤ)) = modFive 0 := by
    simp [modFive_single, five_modFive]
  intro h
  have heq := h hz
  have := congrArg (fun A : IntMatrices ↦ A 0 1) heq
  norm_num at this

/-- This specified source shear is not the identity. -/
private theorem shear_five_matrix_ne_refl
    : shear IntMatrices (Matrix.single 0 1 (5 : ℤ)) ≠ LinearEquiv.refl _ _ := by
  intro h
  have hv := congrArg (fun e : (Fin 2 → IntMatrices) ≃ₗ[IntMatricesᵐᵒᵖ]
      (Fin 2 → IntMatrices) ↦ e (Pi.single 1 1) 0 0 1) h
  norm_num [shear_first] at hv

/-- A noncentral source coefficient acts on the LEFT after transport. -/
private theorem modFive_shear_noncentral_coefficient_apply :
    Module.rightFreeLinearMapScalarExtension IntMatrices (Fin 2) (Fin 2) modFive
      (shear IntMatrices (Matrix.single 0 1 1)).toLinearMap
      (Pi.single 1 (Matrix.single 1 0 1)) 0 = Matrix.single 0 0 1 := by
  rw [Module.rightFreeLinearMapScalarExtension_apply]
  simp [Fin.sum_univ_two, shear_first, modFive_single]

/-- A specified nonidentity source shear becomes the identity map modulo five. -/
private theorem modFive_shear_five_linearMap_eq_id :
    Module.rightFreeLinearMapScalarExtension IntMatrices (Fin 2) (Fin 2) modFive
      (shear IntMatrices (Matrix.single 0 1 (5 : ℤ))).toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext i
  rw [Module.rightFreeLinearMapScalarExtension_apply]
  fin_cases i <;>
    simp [Fin.sum_univ_two, shear_first, shear_second, modFive_single, five_modFive]

/-- The equivalence transport uses that same specified shear. -/
private theorem modFive_shear_five_equiv_toLinearMap_eq_id :
    (Module.rightFreeScalarExtensionEquiv IntMatrices (Fin 2) (Fin 2) modFive
      (shear IntMatrices (Matrix.single 0 1 (5 : ℤ)))).toLinearMap = LinearMap.id := by
  rw [Module.rightFreeScalarExtensionEquiv_toLinearMap]
  apply LinearMap.ext
  intro x
  funext i
  rw [Module.rightFreeLinearMapScalarExtension_apply]
  fin_cases i <;>
    simp [Fin.sum_univ_two, shear_first, shear_second, modFive_single, five_modFive]

/-- Coordinate swap exists already over a noncommutative semiring without negatives. -/
def swap (R : Type*) [Semiring R] : (Fin 2 → R) ≃ₗ[Rᵐᵒᵖ] (Fin 2 → R) :=
  LinearEquiv.piCongrLeft' Rᵐᵒᵖ (fun _ : Fin 2 ↦ R) (Equiv.swap 0 1)

lemma swap_first (R : Type*) [Semiring R] (x : Fin 2 → R) : swap R x 0 = x 1 := by
  simp [swap]

lemma swap_second (R : Type*) [Semiring R] (x : Fin 2 → R) : swap R x 1 = x 0 := by
  simp [swap]

private theorem natMatrix_unit_zero_one_mul_unit_one_zero :
    (Matrix.single (0 : Fin 2) 1 (1 : ℕ) : NatMatrices) * Matrix.single 1 0 1 =
      Matrix.single 0 0 1 := by
  simp

private theorem natMatrix_swap_ne_refl : swap NatMatrices ≠ LinearEquiv.refl _ _ := by
  intro h
  have hv := congrArg (fun e : (Fin 2 → NatMatrices) ≃ₗ[NatMatricesᵐᵒᵖ]
      (Fin 2 → NatMatrices) ↦ e (Pi.single 1 1) 0 0 0) h
  norm_num [swap_first] at hv

/-- Nonidentity coordinate swap transported from Matrix₂(ℕ) to Matrix₂(ℤ). -/
private theorem natInt_swap_scalarExtension_apply (x : Fin 2 → IntMatrices) :
    Module.rightFreeLinearMapScalarExtension NatMatrices (Fin 2) (Fin 2) natInt
      (swap NatMatrices).toLinearMap x = swap IntMatrices x := by
  ext i
  rw [Module.rightFreeLinearMapScalarExtension_apply]
  fin_cases i <;> simp [Fin.sum_univ_two, swap_first, swap_second]

private theorem natInt_swap_scalarExtension_symm_toLinearMap :
    (Module.rightFreeScalarExtensionEquiv NatMatrices (Fin 2) (Fin 2) natInt
      (swap NatMatrices)).symm.toLinearMap =
      Module.rightFreeLinearMapScalarExtension NatMatrices (Fin 2) (Fin 2) natInt
        (swap NatMatrices).symm.toLinearMap := by
  rw [Module.rightFreeScalarExtensionEquiv_symm,
    Module.rightFreeScalarExtensionEquiv_toLinearMap]

abbrev CountableFree := ℕ →₀ ℤᵐᵒᵖ
abbrev E := Module.End ℤᵐᵒᵖ CountableFree

/-- Two copies of the countable module are one, using the existing witness. -/
def countableDouble : (CountableFree × CountableFree) ≃ₗ[ℤᵐᵒᵖ] CountableFree :=
  ((LinearEquiv.refl ℤᵐᵒᵖ CountableFree).prodCongr
    (Module.Free.natFinsuppCountableSelfSum ℤᵐᵒᵖ)).trans <|
    (Module.Free.prodFinsuppNatEquiv ℤᵐᵒᵖ CountableFree).trans
      (Module.Free.natFinsuppCountableSelfSum ℤᵐᵒᵖ).symm

def endDouble : E ≃ₗ[Eᵐᵒᵖ] E × E :=
  (Module.Free.linearMapProdEndEquiv ℤᵐᵒᵖ CountableFree CountableFree countableDouble).symm

/-- The specified, satisfiable unequal-rank input; no equality of ranks is assumed. -/
def oneToTwo : (PUnit → E) ≃ₗ[Eᵐᵒᵖ] (Fin 2 → E) :=
  (LinearEquiv.funUnique PUnit Eᵐᵒᵖ E).trans <|
    endDouble.trans (LinearEquiv.finTwoArrow Eᵐᵒᵖ E).symm

def diagonal : E →+* E × E := (RingHom.id E).prod (RingHom.id E)

/-- E is not a zero ring: its identity acts nontrivially on a source basis vector. -/
private theorem countableEnd_one_ne_zero : (1 : E) ≠ 0 := by
  intro h
  have hx := LinearMap.congr_fun h (Finsupp.single 0 (1 : ℤᵐᵒᵖ))
  have hz := congrArg (fun x : CountableFree ↦ MulOpposite.unop (x 0)) hx
  norm_num at hz

/-- Transport of an actual one-to-two witness along the specified diagonal. -/
def diagonalOneToTwo : (PUnit → E × E) ≃ₗ[(E × E)ᵐᵒᵖ] (Fin 2 → E × E) :=
  Module.rightFreeScalarExtensionEquiv E PUnit (Fin 2) diagonal oneToTwo

private theorem countableOneToTwo_diagonal_apply_single (s : E × E) :
    diagonalOneToTwo (Pi.single PUnit.unit s) =
      fun i ↦ diagonal (oneToTwo (Pi.single PUnit.unit 1) i) * s := by
  funext i
  rw [diagonalOneToTwo, Module.rightFreeScalarExtensionEquiv_apply]
  simp [oneToTwo]

/-- Finite source, genuinely infinite target; only the source index is finite. -/
def constantCoordinates : (PUnit → ℤ) →ₗ[ℤᵐᵒᵖ] (ℕ → ℤ) :=
  LinearMap.pi fun _ ↦ LinearMap.proj PUnit.unit

private theorem constantCoordinates_modFive_apply (y : PUnit → ZMod 5) (n : ℕ) :
    Module.rightFreeLinearMapScalarExtension ℤ PUnit ℕ (Int.castRingHom (ZMod 5))
      constantCoordinates y n = y PUnit.unit := by
  rw [Module.rightFreeLinearMapScalarExtension_apply]
  simp [constantCoordinates]

/-- An empty source still admits chosen maps to an inhabited, infinite target. -/
private theorem emptySource_modFive_zero_apply (x : Fin 0 → ZMod 5) (n : ℕ) :
    Module.rightFreeLinearMapScalarExtension ℤ (Fin 0) ℕ (Int.castRingHom (ZMod 5))
      (0 : (Fin 0 → ℤ) →ₗ[ℤᵐᵒᵖ] (ℕ → ℤ)) x n = 0 := by
  rw [Module.rightFreeLinearMapScalarExtension_apply]
  simp

/-- Empty source and target coordinates give an actual unique equivalence. -/
def emptyEquiv : (Fin 0 → ℤ) ≃ₗ[ℤᵐᵒᵖ] (PEmpty → ℤ) :=
  LinearEquiv.ofSubsingleton _ _

private theorem emptyEquiv_modFive_scalarExtension_symm :
    (Module.rightFreeScalarExtensionEquiv ℤ (Fin 0) PEmpty
      (Int.castRingHom (ZMod 5)) emptyEquiv).symm =
      Module.rightFreeScalarExtensionEquiv ℤ PEmpty (Fin 0)
        (Int.castRingHom (ZMod 5)) emptyEquiv.symm := by
  exact Module.rightFreeScalarExtensionEquiv_symm _ _

/-- Exactly one empty side is satisfiable over the zero ring. -/
def zeroRingEquiv : (Fin 0 → ZMod 1) ≃ₗ[(ZMod 1)ᵐᵒᵖ] (Fin 3 → ZMod 1) :=
  LinearEquiv.ofSubsingleton _ _

private theorem zeroRingEquiv_scalarExtension_toLinearMap :
    (Module.rightFreeScalarExtensionEquiv (ZMod 1) (Fin 0) (Fin 3)
      (RingHom.id _) zeroRingEquiv).toLinearMap =
      Module.rightFreeLinearMapScalarExtension (ZMod 1) (Fin 0) (Fin 3)
        (RingHom.id _) zeroRingEquiv.toLinearMap := by
  exact Module.rightFreeScalarExtensionEquiv_toLinearMap _ _

/-- With exactly one empty side, the specified zero-ring equivalence transports
and its output is the zero vector, by the characteristic empty-sum formula. -/
private theorem zeroRingEquiv_scalarExtension_apply_eq_zero (x : Fin 0 → ZMod 1) :
    Module.rightFreeScalarExtensionEquiv (ZMod 1) (Fin 0) (Fin 3)
      (RingHom.id _) zeroRingEquiv x = 0 := by
  funext i
  rw [Module.rightFreeScalarExtensionEquiv_apply]
  simp

/-- A nonidentity integer shear may also be transported to the zero ring. -/
private theorem integerShear_zeroRing_scalarExtension_eq_id :
    Module.rightFreeLinearMapScalarExtension ℤ (Fin 2) (Fin 2)
      (Int.castRingHom (ZMod 1)) (shear ℤ 1).toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

universe u v w

-- Use the same classical index data as the decidability-free tensor bridge.
local instance : DecidableEq (ULift.{u} (Fin 2)) :=
  fun a b ↦ Classical.propDecidable (a = b)

/-- The two finite coordinate types and target coefficient ring have independent lifts. -/
def liftedSwap : (ULift.{u} (Fin 2) → ℤ) ≃ₗ[ℤᵐᵒᵖ] (ULift.{w} (Fin 2) → ℤ) :=
  (LinearEquiv.piCongrLeft' ℤᵐᵒᵖ (fun _ : ULift.{u} (Fin 2) ↦ ℤ)
    Equiv.ulift).trans <|
    (swap ℤ).trans (LinearEquiv.piCongrLeft' ℤᵐᵒᵖ
      (fun _ : ULift.{w} (Fin 2) ↦ ℤ) Equiv.ulift).symm

def liftedHom : ℤ →+* ULift.{v} ℤ := ULift.ringEquiv.symm.toRingHom

private theorem liftedSwap_scalarExtension_toLinearMap :
    (Module.rightFreeScalarExtensionEquiv ℤ (ULift.{u} (Fin 2))
      (ULift.{w} (Fin 2)) liftedHom.{v} liftedSwap.{u, w}).toLinearMap =
      Module.rightFreeLinearMapScalarExtension ℤ (ULift.{u} (Fin 2))
        (ULift.{w} (Fin 2)) liftedHom.{v} liftedSwap.{u, w}.toLinearMap := by
  exact Module.rightFreeScalarExtensionEquiv_toLinearMap _ _

/-- Applied transport across three independent lifts, at a nonfixed coordinate. -/
private theorem liftedSwap_scalarExtension_apply_zero :
    Module.rightFreeLinearMapScalarExtension ℤ (ULift.{u} (Fin 2))
      (ULift.{w} (Fin 2)) liftedHom.{v} liftedSwap.{u, w}.toLinearMap
      (fun j ↦ liftedHom.{v} (if j.down = 0 then 7 else 11)) ⟨0⟩ =
        (ULift.up 11 : ULift.{v} ℤ) := by
  have h := Module.rightFreeLinearMapScalarExtension_coefficients
    liftedHom.{v} liftedSwap.{u, w}.toLinearMap
    (fun j : ULift.{u} (Fin 2) ↦ (if j.down = 0 then 7 else 11 : ℤ))
  simpa [liftedSwap, swap, liftedHom] using
    congrArg (fun y : ULift.{w} (Fin 2) → ULift.{v} ℤ ↦ y ⟨0⟩) h

/-- The independent-universe Ring bridge is unbundled, not forced into ModuleCat. -/
private theorem liftedSwap_scalarExtension_eq_rightExtension :
    Module.rightFreeLinearMapScalarExtension ℤ (ULift.{u} (Fin 2))
      (ULift.{w} (Fin 2)) liftedHom.{v} liftedSwap.{u, w}.toLinearMap =
      LinearEquiv.arrowCongrAddEquiv
        (ModuleCat.RightExtension.rightFreeLinearEquiv liftedHom.{v} (ULift.{u} (Fin 2)))
        (ModuleCat.RightExtension.rightFreeLinearEquiv liftedHom.{v} (ULift.{w} (Fin 2)))
        (ModuleCat.RightExtension.map liftedHom.{v} liftedSwap.{u, w}.toLinearMap) := by
  exact Module.rightFreeLinearMapScalarExtension_eq_rightExtension
    (R := ℤ) (S := ULift.{v} ℤ) (ι := ULift.{u} (Fin 2)) (κ := ULift.{w} (Fin 2))
    liftedHom.{v} liftedSwap.{u, w}.toLinearMap

set_option pp.universes true in
#check Module.rightFreeLinearMapScalarExtension
set_option pp.universes true in
#check Module.rightFreeScalarExtensionEquiv
set_option pp.universes true in
#check Module.rightFreeLinearMapScalarExtension_eq_rightExtension

-- The constructors provide specified inputs; characteristic conclusions use the library API.
#print axioms shear
#print axioms swap
#print axioms countableDouble
#print axioms endDouble
#print axioms oneToTwo
#print axioms diagonalOneToTwo
#print axioms emptyEquiv
#print axioms zeroRingEquiv
#print axioms liftedSwap
#print axioms Module.rightFreeLinearMapScalarExtension
#print axioms Module.rightFreeScalarExtensionEquiv

end ProjectiveModulesTests.RightFreeScalarExtension
