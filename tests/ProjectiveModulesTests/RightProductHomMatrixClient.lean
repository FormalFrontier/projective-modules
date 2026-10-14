/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.RightProduct.Hom
import ProjectiveModules.Module.RightRegular
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.NormNum

/-!
# Noncommutative endomorphisms of right coefficient products

The coefficient factors are the 2-by-2 and 3-by-3 integer matrix rings, with
their canonical right regular modules. Left multiplication by the upper and
lower matrix units gives factor-linear endomorphisms. The inverse of
`Module.piRightEndEquiv` assembles them into coefficient-product-linear maps.

The two products have different (0,0) entries on the family of identity
matrices: upper after lower gives 1, whereas lower after upper gives 0.
Thus the calculation distinguishes ordinary endomorphism composition from
its opposite. Supported-input recovery and an off-support zero use the
component API rather than an independently computed whole-product map.

## References

* Mathlib's `RingEquiv.moduleEndSelfOp` for left multiplication on the right
  regular module, and its matrix-unit multiplication formulas.
* Projective Modules' right coefficient-product Hom and endomorphism APIs.
-/

noncomputable section

namespace ProjectiveModulesTests.RightProductHomMatrixClient

private abbrev matrixRing (i : Fin 2) :=
  Matrix (Fin (i.val + 2)) (Fin (i.val + 2)) ℤ

private abbrev matrixModule (i : Fin 2) :=
  ModuleCat.of (matrixRing i)ᵐᵒᵖ (matrixRing i)

private abbrev matrixFamily := ModuleCat.piRight matrixRing matrixModule

private def upperUnit (i : Fin 2) : matrixRing i := Matrix.single 0 1 1

private def lowerUnit (i : Fin 2) : matrixRing i := Matrix.single 1 0 1

private def upperFactor (i : Fin 2) : Module.End (matrixRing i)ᵐᵒᵖ (matrixRing i) :=
  RingEquiv.moduleEndSelfOp (matrixRing i) (upperUnit i)

private def lowerFactor (i : Fin 2) : Module.End (matrixRing i)ᵐᵒᵖ (matrixRing i) :=
  RingEquiv.moduleEndSelfOp (matrixRing i) (lowerUnit i)

private theorem upperFactor_apply (i : Fin 2) (a : matrixRing i) :
    upperFactor i a = upperUnit i * a := rfl

private theorem lowerFactor_apply (i : Fin 2) (a : matrixRing i) :
    lowerFactor i a = lowerUnit i * a := rfl

private def upperMap : Module.End (∀ i, matrixRing i)ᵐᵒᵖ matrixFamily :=
  (Module.piRightEndEquiv matrixRing matrixRing).symm upperFactor

private def lowerMap : Module.End (∀ i, matrixRing i)ᵐᵒᵖ matrixFamily :=
  (Module.piRightEndEquiv matrixRing matrixRing).symm lowerFactor

private def identityFamily : matrixFamily := fun i => (1 : matrixRing i)

private theorem upper_component (i : Fin 2) (a : matrixRing i) :
    Module.piRightEndEquiv matrixRing matrixRing upperMap i a = upperUnit i * a := by
  simp only [upperMap, RingEquiv.apply_symm_apply, upperFactor_apply]

private theorem upper_supported_recovery (i : Fin 2) (a : matrixRing i) :
    upperMap (ModuleCat.piRightSingle matrixRing matrixModule i a) i = upperUnit i * a := by
  calc
    upperMap (ModuleCat.piRightSingle matrixRing matrixModule i a) i =
        Module.piRightEndEquiv matrixRing matrixRing upperMap i a :=
      (Module.piRightEndEquiv_apply matrixRing matrixRing upperMap i a).symm
    _ = upperUnit i * a := upper_component i a

private theorem upper_off_support (i j : Fin 2) (h : j ≠ i) (a : matrixRing i) :
    upperMap (ModuleCat.piRightSingle matrixRing matrixModule i a) j = 0 :=
  Module.piRightHomAddEquiv_single_apply_of_ne matrixRing matrixRing matrixRing
    upperMap i j h a

/-- Evaluate a product through the component and inverse-component APIs. -/
private theorem product_coordinate
    (f g : Module.End (∀ i, matrixRing i)ᵐᵒᵖ matrixFamily)
    (x : matrixFamily) (i : Fin 2) :
    (f * g) x i =
      (Module.piRightEndEquiv matrixRing matrixRing f i *
        Module.piRightEndEquiv matrixRing matrixRing g i) (x i) := by
  calc
    (f * g) x i =
        (Module.piRightEndEquiv matrixRing matrixRing).symm
          (Module.piRightEndEquiv matrixRing matrixRing (f * g)) x i :=
      congrArg
        (fun h : @Module.End (∀ i, matrixRing i)ᵐᵒᵖ (∀ i, matrixRing i) _ _
          (Module.piRightModule matrixRing matrixRing) => h x i)
        ((Module.piRightEndEquiv matrixRing matrixRing).symm_apply_apply (f * g)).symm
    _ = Module.piRightEndEquiv matrixRing matrixRing (f * g) i (x i) :=
      Module.piRightEndEquiv_symm_apply matrixRing matrixRing _ x i
    _ = _ :=
      congrArg (fun h : Module.End (matrixRing i)ᵐᵒᵖ (matrixRing i) => h (x i))
        (Module.piRightEndEquiv_mul matrixRing matrixRing f g i)

private theorem upper_lower_entry :
    (upperMap * lowerMap) identityFamily 0 0 0 = 1 := by
  rw [product_coordinate]
  simp only [upperMap, lowerMap, RingEquiv.apply_symm_apply, Module.End.mul_apply,
    upperFactor_apply, lowerFactor_apply, identityFamily, mul_one]
  norm_num [upperUnit, lowerUnit, Matrix.single_mul_single_same, Matrix.single_apply]

private theorem lower_upper_entry :
    (lowerMap * upperMap) identityFamily 0 0 0 = 0 := by
  rw [product_coordinate]
  simp only [upperMap, lowerMap, RingEquiv.apply_symm_apply, Module.End.mul_apply,
    upperFactor_apply, lowerFactor_apply, identityFamily, mul_one]
  norm_num [upperUnit, lowerUnit, Matrix.single_mul_single_same, Matrix.single_apply]

private theorem assembled_endomorphisms_do_not_commute :
    upperMap * lowerMap ≠ lowerMap * upperMap := by
  intro h
  have hentry := congrArg
    (fun f : Module.End (∀ i, matrixRing i)ᵐᵒᵖ matrixFamily => f identityFamily 0 0 0) h
  rw [upper_lower_entry, lower_upper_entry] at hentry
  norm_num at hentry

end ProjectiveModulesTests.RightProductHomMatrixClient
