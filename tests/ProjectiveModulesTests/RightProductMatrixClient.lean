/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.RightProduct
import ProjectiveModules.Module.RightRegular
import Mathlib.Algebra.Module.PUnit
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Tactic.NormNum

/-!
# Matrix coefficients and additive crossmaps in right product modules

The coefficient factors are the 2-by-2 and 3-by-3 integer matrix rings.
Their countably indexed Finsupp modules use the canonical right regular
coefficient actions. Coordinate support, scalar extension and reconstruction
use the existing right-product bundles. No finite-generation, projectivity or
presentation property is used.

An additive entry map from a first-factor-supported module to a
second-factor-supported module is nonzero, but cannot be linear over the
coefficient product: the idempotent (1,0) fixes the source and kills the target.

Empty-index and zero-ring factors are treated in separate right-product examples.
-/

noncomputable section

namespace ProjectiveModulesTests.RightProductMatrixClient

open ModuleCat

private abbrev matrixRing (i : Fin 2) :=
  Matrix (Fin (i.val + 2)) (Fin (i.val + 2)) ℤ

private abbrev matrixModule (i : Fin 2) :=
  ModuleCat.of (matrixRing i)ᵐᵒᵖ (ℕ →₀ matrixRing i)

private abbrev matrixFamily := ModuleCat.piRight matrixRing matrixModule

private theorem family_carrier :
    (matrixFamily : Type) = (∀ i : Fin 2, ℕ →₀ matrixRing i) := by
  rfl

private theorem family_action (a : ∀ i, matrixRing i) (x : matrixFamily)
    (i : Fin 2) (k : ℕ) :
    (MulOpposite.op a • x) i k = x i k * a i := by
  rw [ModuleCat.piRight_smul_apply, Finsupp.smul_apply, op_smul_eq_mul]

private theorem supported_coordinate (i : Fin 2) (k : ℕ) (m : matrixRing i) :
    ModuleCat.piRightSingle matrixRing matrixModule i (Finsupp.single k m) i k = m := by
  rw [ModuleCat.piRightSingle_apply_same, Finsupp.single_eq_same]

private theorem supported_other_coordinate (i j : Fin 2) (h : j ≠ i)
    (k : ℕ) (m : matrixRing i) :
    ModuleCat.piRightSingle matrixRing matrixModule i (Finsupp.single k m) j = 0 :=
  ModuleCat.piRightSingle_apply_ne matrixRing matrixModule i j h _

private theorem supported_nonzero (i : Fin 2) (k : ℕ) :
    ModuleCat.piRightSingle matrixRing matrixModule i
      (Finsupp.single k (1 : matrixRing i)) ≠ 0 := by
  intro h
  have hentry := congrArg (fun x : matrixFamily => x i k 0 0) h
  rw [supported_coordinate] at hentry
  change (1 : ℤ) = 0 at hentry
  norm_num at hentry

private theorem unit_support (i : Fin 2) (k : ℕ) :
    (Finsupp.single k (1 : matrixRing i)).support = {k} :=
  Finsupp.support_single k one_ne_zero

private theorem finite_reconstruction (x : matrixFamily) :
    x = ∑ᶠ i, ModuleCat.piRightSingle matrixRing matrixModule i (x i) :=
  ModuleCat.piRight_eq_finsum_single matrixRing matrixModule x

private theorem recover_tensor_coordinate (i : Fin 2) (x : matrixFamily)
    (r : matrixRing i) (k : ℕ) :
    RightExtension.piRecoverLinearEquiv matrixRing matrixModule i
        (RightExtension.tmul (Pi.evalRingHom matrixRing i) x r) k = x i k * r := by
  rw [RightExtension.piRecoverLinearEquiv_tmul, Finsupp.smul_apply, op_smul_eq_mul]

private theorem recover_inverse (i : Fin 2) (y : matrixModule i) :
    (RightExtension.piRecoverLinearEquiv matrixRing matrixModule i).symm y =
      RightExtension.tmul (Pi.evalRingHom matrixRing i)
        (ModuleCat.piRightSingle matrixRing matrixModule i y) 1 :=
  RightExtension.piRecoverLinearEquiv_symm_apply matrixRing matrixModule i y

private theorem reconstruction_forward (x : matrixFamily) (i : Fin 2) :
    RightExtension.piLinearEquiv matrixRing matrixFamily x i =
      RightExtension.tmul (Pi.evalRingHom matrixRing i) x 1 :=
  RightExtension.piLinearEquiv_apply matrixRing matrixFamily x i

private theorem reconstruction_inverse_supported (i : Fin 2) (x : matrixFamily)
    (r : matrixRing i) :
    (RightExtension.piLinearEquiv matrixRing matrixFamily).symm
        (ModuleCat.piRightSingle matrixRing
          (fun j => ModuleCat.of (matrixRing j)ᵐᵒᵖ
            (RightExtension.Obj (Pi.evalRingHom matrixRing j) matrixFamily))
          i (RightExtension.tmul (Pi.evalRingHom matrixRing i) x r)) =
      MulOpposite.op
        (@Pi.single (Fin 2) matrixRing (fun _ => inferInstance)
          (Classical.decEq (Fin 2)) i r) • x :=
  RightExtension.piLinearEquiv_symm_single_tmul matrixRing matrixFamily i x r

private abbrev twoMatrix := matrixRing 0
private abbrev threeMatrix := matrixRing 1
private abbrev twoModule := matrixModule 0
private abbrev threeModule := matrixModule 1
private abbrev binaryMatrix :=
  ModuleCat.prodRight twoMatrix threeMatrix twoModule threeModule

private theorem binary_carrier :
    (binaryMatrix : Type) = ((ℕ →₀ twoMatrix) × (ℕ →₀ threeMatrix)) := by
  rfl

private theorem both_factors_noncommutative :
    (Matrix.single 0 1 (1 : ℤ) * Matrix.single 1 0 1 : twoMatrix) 0 0 ≠
        (Matrix.single 1 0 (1 : ℤ) * Matrix.single 0 1 1 : twoMatrix) 0 0 ∧
      (Matrix.single 0 1 (1 : ℤ) * Matrix.single 1 0 1 : threeMatrix) 0 0 ≠
        (Matrix.single 1 0 (1 : ℤ) * Matrix.single 0 1 1 : threeMatrix) 0 0 := by
  constructor <;> norm_num [Matrix.single_mul_single_same, Matrix.single_apply]

private def upperUnits : binaryMatrix :=
  ModuleCat.prodRightMk twoMatrix threeMatrix twoModule threeModule
    (Finsupp.single 0 (Matrix.single 0 1 1))
    (Finsupp.single 0 (Matrix.single 0 1 1))

private theorem right_multiplication_order :
    ((MulOpposite.op
        ((Matrix.single 1 0 1 : twoMatrix), (Matrix.single 1 0 1 : threeMatrix)) •
        upperUnits).1 0) 0 0 = 1 ∧
      ((MulOpposite.op
        ((Matrix.single 1 0 1 : twoMatrix), (Matrix.single 1 0 1 : threeMatrix)) •
        upperUnits).2 0) 0 0 = 1 := by
  simp only [ModuleCat.prodRight_smul]
  constructor <;>
    norm_num [upperUnits, ModuleCat.prodRightMk_apply, Finsupp.smul_apply,
      op_smul_eq_mul, Matrix.single_mul_single_same]

private abbrev twoZero := ModuleCat.of twoMatrixᵐᵒᵖ PUnit.{1}
private abbrev threeZero := ModuleCat.of threeMatrixᵐᵒᵖ PUnit.{1}
private abbrev firstSupported :=
  ModuleCat.prodRight twoMatrix threeMatrix twoModule threeZero
private abbrev secondSupported :=
  ModuleCat.prodRight twoMatrix threeMatrix twoZero threeModule

private theorem first_supported_carrier :
    (firstSupported : Type) = ((ℕ →₀ twoMatrix) × PUnit) := by
  rfl

private theorem second_supported_carrier :
    (secondSupported : Type) = (PUnit × (ℕ →₀ threeMatrix)) := by
  rfl

private def entryCross : firstSupported →+ secondSupported :=
  (0 : firstSupported →+ PUnit).prod
    ((Finsupp.lsingle (R := threeMatrixᵐᵒᵖ) (M := threeMatrix) 0).toAddMonoidHom.comp
      ((Matrix.singleAddMonoidHom (0 : Fin 3) 0).comp
        ((Matrix.entryAddMonoidHom ℤ (0 : Fin 2) 0).comp
          ((Finsupp.lapply (R := twoMatrixᵐᵒᵖ) (M := twoMatrix) 0).toAddMonoidHom.comp
            (ModuleCat.prodRightFst twoMatrix threeMatrix twoModule threeZero).toAddMonoidHom))))

private theorem entryCross_apply (x : firstSupported) :
    entryCross x = (0, Finsupp.single 0 (Matrix.single 0 0 (x.1 0 0 0))) := by
  rfl

private def firstUnit : firstSupported :=
  ModuleCat.prodRightMk twoMatrix threeMatrix twoModule threeZero
    (Finsupp.single 0 (Matrix.single 0 0 1)) 0

private theorem entryCross_unit_entry : (entryCross firstUnit).2 0 0 0 = 1 := by
  rw [entryCross_apply]
  simp [firstUnit, ModuleCat.prodRightMk_apply]

private theorem entryCross_nonzero : entryCross ≠ 0 := by
  intro h
  have hentry := congrArg (fun y : secondSupported => y.2 0 0 0)
    (DFunLike.congr_fun h firstUnit)
  change (entryCross firstUnit).2 0 0 0 = 0 at hentry
  rw [entryCross_unit_entry] at hentry
  norm_num at hentry

private theorem first_idempotent_fixes (x : firstSupported) :
    MulOpposite.op ((1 : twoMatrix), (0 : threeMatrix)) • x = x := by
  rw [ModuleCat.prodRight_smul]
  apply Prod.ext
  · simp
  · exact Subsingleton.elim _ _

private theorem first_idempotent_kills (y : secondSupported) :
    MulOpposite.op ((1 : twoMatrix), (0 : threeMatrix)) • y = 0 := by
  rw [ModuleCat.prodRight_smul]
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · change (0 : threeMatrixᵐᵒᵖ) • y.2 = (0 : ℕ →₀ threeMatrix)
    exact zero_smul _ _

private theorem linear_cross_zero
    (f : firstSupported →ₗ[(twoMatrix × threeMatrix)ᵐᵒᵖ] secondSupported) : f = 0 := by
  apply LinearMap.ext
  intro x
  have h := f.map_smul (MulOpposite.op ((1 : twoMatrix), (0 : threeMatrix))) x
  rw [first_idempotent_fixes, first_idempotent_kills] at h
  exact h

private theorem entryCross_not_product_linear :
    ¬ ∀ (a : (twoMatrix × threeMatrix)ᵐᵒᵖ) (x : firstSupported),
      entryCross (a • x) = a • entryCross x := by
  intro h
  have hx := h (MulOpposite.op ((1 : twoMatrix), (0 : threeMatrix))) firstUnit
  rw [first_idempotent_fixes, first_idempotent_kills] at hx
  have hentry := congrArg (fun y : secondSupported => y.2 0 0 0) hx
  change (entryCross firstUnit).2 0 0 0 = 0 at hentry
  rw [entryCross_unit_entry] at hentry
  norm_num at hentry

end ProjectiveModulesTests.RightProductMatrixClient
