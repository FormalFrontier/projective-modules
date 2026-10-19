/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.InvariantBasisNumber
import ProjectiveModules.KTheory.Rank
import ProjectiveModules.KTheory.ZeroRing
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.ZMod.Defs

/-!
# The regular K₀ class over the rationals and the zero ring

The dimension equivalence identifies the rational regular-class orbit
independently. Over `ZMod 1` the regular class is zero and both infinite-order
conditions fail.
-/

@[expose] public section

open KTheory KTheory.K0

example (z : ℤ) :
    (finrankEquiv ℚ).symm z = zmultiplesHom (K0 ℚ) (of ℚ ℚᵐᵒᵖ) z :=
  finrankEquiv_symm_apply ℚ z

example : Function.Injective (zmultiplesHom (K0 ℚ) (of ℚ ℚᵐᵒᵖ)) :=
  (invariantBasisNumber_iff_injective_zmultiplesHom ℚ).mp inferInstance

example : addOrderOf (of ℚ ℚᵐᵒᵖ) = 0 :=
  (invariantBasisNumber_iff_addOrderOf_eq_zero ℚ).mp inferInstance

example : of (ZMod 1) (ZMod 1)ᵐᵒᵖ = 0 :=
  of_eq_zero_of_subsingleton (ZMod 1) (ZMod 1)ᵐᵒᵖ

example : ¬ InvariantBasisNumber (ZMod 1) ∧
    ¬ Function.Injective (zmultiplesHom (K0 (ZMod 1)) (of (ZMod 1) (ZMod 1)ᵐᵒᵖ)) ∧
    addOrderOf (of (ZMod 1) (ZMod 1)ᵐᵒᵖ) ≠ 0 := by
  have h : ¬ InvariantBasisNumber (ZMod 1) := by
    intro h
    letI : InvariantBasisNumber (ZMod 1) := h
    letI : Nontrivial (ZMod 1) := nontrivial_of_invariantBasisNumber (ZMod 1)
    exact zero_ne_one (Subsingleton.elim (0 : ZMod 1) 1)
  exact ⟨h,
    fun h' => h ((invariantBasisNumber_iff_injective_zmultiplesHom (ZMod 1)).mpr h'),
    fun h' => h ((invariantBasisNumber_iff_addOrderOf_eq_zero (ZMod 1)).mpr h')⟩
