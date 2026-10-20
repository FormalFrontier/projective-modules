/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.Nilpotent
import ProjectiveModules.KTheory.ZeroRing
import ProjectiveModules.Module.RightExtensionFree
import ProjectiveModules.Module.RightRegular
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.Algebra.Ring.PUnit

/-!
# Nilpotent change of rings for dual numbers

The projection from the dual numbers over the integers to the integers is
surjective but not injective: the nonzero element `inr 1` maps to zero. Its
kernel has square zero by `TrivSqZeroExt.kerIdeal_sq`. The class and K₀
change-of-rings equivalences normalize the right regular module to the right
regular module over the integers. The projection over the zero ring gives a
boundary case.

The hypothesis terms below are Mathlib's `fst_surjective` and `IsNilpotent.mk`
applied to `kerIdeal_sq`, in the commutative context required by that theorem.
No commutativity hypothesis is imposed on the general change-of-rings results.
-/

@[expose] public section

open KTheory

namespace ProjectiveModulesTests

example (R : Type*) [Ring R] :
    Function.Surjective (ProjectiveClass.map (RingHom.id R)) := by
  apply ProjectiveClass.map_surjective_of_lift_idempotents (RingHom.id R)
  intro n E hE
  exact ⟨E, hE, rfl⟩

local notation "π" => AlgHom.toRingHom (TrivSqZeroExt.fstHom ℤ ℤ ℤ)
local notation "hπ" => (TrivSqZeroExt.fst_surjective : Function.Surjective π)
local notation "hkerπ" =>
  (IsNilpotent.mk (RingHom.ker π) 2 (TrivSqZeroExt.kerIdeal_sq ℤ ℤ))

-- A nonzero square-zero direction is killed by the projection.
private theorem dualNumber_int_projection_kills_nonzero_direction :
    π (TrivSqZeroExt.inr (1 : ℤ)) = 0 ∧
      (TrivSqZeroExt.inr (1 : ℤ) : DualNumber ℤ) ≠ 0 ∧
      ¬ Function.Injective π := by
  have hne : (TrivSqZeroExt.inr (1 : ℤ) : DualNumber ℤ) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg TrivSqZeroExt.snd h)
  refine ⟨rfl, hne, ?_⟩
  intro hinj
  apply hne
  apply hinj
  rfl

-- Both general bijectivity statements specialize to the same projection.
private theorem dualNumber_int_projectiveClass_map_bijective : Function.Bijective (ProjectiveClass.map π) := by
  exact ProjectiveClass.map_bijective_of_surjective_of_isNilpotent_ker π hπ hkerπ

private theorem dualNumber_int_K0_map_bijective : Function.Bijective (K0.map π) := by
  exact K0.map_bijective_of_surjective_of_isNilpotent_ker π hπ hkerπ

-- The equivalences use the stock surjectivity and uniform nilpotence witnesses.
private theorem dualNumber_int_projectiveClass_regular_generator :
    ProjectiveClass.equivOfSurjectiveOfIsNilpotentKer π hπ hkerπ
        (ProjectiveClass.of (DualNumber ℤ) (DualNumber ℤ)) =
      ProjectiveClass.of ℤ ℤ := by
  erw [ProjectiveClass.equivOfSurjectiveOfIsNilpotentKer_apply,
    ProjectiveClass.map_of]
  exact ProjectiveClass.of_eq_of_equiv ℤ _
    ((ModuleCat.RightExtension.mapLinearEquiv π
      (LinearEquiv.funUnique PUnit.{1} (DualNumber ℤ)ᵐᵒᵖ (DualNumber ℤ)).symm).trans
      ((ModuleCat.RightExtension.rightFreeLinearEquiv π PUnit.{1}).trans
        (LinearEquiv.funUnique PUnit.{1} ℤᵐᵒᵖ ℤ)))

private theorem dualNumber_int_K0_regular_generator :
    K0.equivOfSurjectiveOfIsNilpotentKer π hπ hkerπ
        (K0.of (DualNumber ℤ) (DualNumber ℤ)) =
      K0.of ℤ ℤ := by
  erw [K0.equivOfSurjectiveOfIsNilpotentKer_apply,
    K0.map_of]
  exact K0.of_eq_of_equiv ℤ _
    ((ModuleCat.RightExtension.mapLinearEquiv π
      (LinearEquiv.funUnique PUnit.{1} (DualNumber ℤ)ᵐᵒᵖ (DualNumber ℤ)).symm).trans
      ((ModuleCat.RightExtension.rightFreeLinearEquiv π PUnit.{1}).trans
        (LinearEquiv.funUnique PUnit.{1} ℤᵐᵒᵖ ℤ)))

-- The same construction also includes the zero-ring boundary.
private theorem dualNumber_punit_K0_zero :
    K0.equivOfSurjectiveOfIsNilpotentKer
        (TrivSqZeroExt.fstHom PUnit.{1} PUnit.{1} PUnit.{1}).toRingHom
        TrivSqZeroExt.fst_surjective
        (IsNilpotent.mk _ 2 (TrivSqZeroExt.kerIdeal_sq PUnit.{1} PUnit.{1}))
        (K0.of (DualNumber PUnit.{1}) ((DualNumber PUnit.{1})ᵐᵒᵖ)) = 0 := by
  exact Subsingleton.elim _ _

end ProjectiveModulesTests
