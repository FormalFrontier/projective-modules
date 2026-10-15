/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Rank
import ProjectiveModules.KTheory.Dual
import ProjectiveModules.KTheory.ScalarExtension
import ProjectiveModules.KTheory.ZeroRing
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Ring.ULift
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Basic.Real.Basic

/-!
# Clients of the dimension maps on right-module K₀

The scalar-self regular module over a division ring has dimension one, its
binary direct sum has dimension two, and the zero module has dimension zero.
Independent carrier lifts leave these computations unchanged. The integer
map also evaluates negative generators and differences, so it is not merely
a natural-valued invariant on positive generators.

The examples use only the public class, completion and dimension APIs. The
module formulas allow arbitrary carrier universes and obtain projectivity
from the division-ring instances.
-/

@[expose] public section

universe u v w

open KTheory

namespace ProjectiveModulesTests.K0RankClient

variable (K : Type u) [DivisionRing K]

-- The regular right module, zero space and plane have distinct dimensions.
example : ProjectiveClass.finrankHom K (ProjectiveClass.of K Kᵐᵒᵖ) = 1 := by
  simp

example : ProjectiveClass.finrankHom K (ProjectiveClass.of K PUnit.{v + 1}) = 0 := by
  simp

example :
    ProjectiveClass.finrankHom K (ProjectiveClass.of K (Kᵐᵒᵖ × Kᵐᵒᵖ)) = 2 := by
  simp

example :
    ProjectiveClass.finrankHom K (ProjectiveClass.of K (ULift.{v} Kᵐᵒᵖ)) = 1 := by
  simp

example :
    ProjectiveClass.finrankHom K
      (ProjectiveClass.of K (ULift.{v} Kᵐᵒᵖ × PUnit.{w + 1})) = 1 := by
  simp

example : K0.finrankHom K (K0.of K Kᵐᵒᵖ) = 1 := by
  simp

example : K0.finrankHom K (K0.of K PUnit.{v + 1}) = 0 := by
  simp

example : K0.finrankHom K (K0.of K (Kᵐᵒᵖ × Kᵐᵒᵖ)) = 2 := by
  simp

example : K0.finrankHom K (K0.of K (ULift.{v} Kᵐᵒᵖ)) = 1 := by
  simp

example : K0.finrankHom K (-(K0.of K Kᵐᵒᵖ)) = -1 := by
  simp

-- Subtraction is evaluated by the group homomorphism, not by a class quotient.
example :
    K0.finrankHom K
      (K0.of K (ULift.{v} Kᵐᵒᵖ × ULift.{w} Kᵐᵒᵖ) - K0.of K Kᵐᵒᵖ) = 1 := by
  rw [map_sub]
  simp

example (a : ProjectiveClass K) :
    K0.finrankHom K (K0.ofClass K a - K0.of K Kᵐᵒᵖ) =
      (ProjectiveClass.finrankHom K a : ℤ) - 1 := by
  rw [map_sub, K0.finrankHom_ofClass, K0.finrankHom_of_self]

-- The universal extension agrees with the dimension map on negative inputs.
example :
    K0.lift K ((Int.ofNatHom : ℕ →+ ℤ).comp (ProjectiveClass.finrankHom K))
      (-(K0.of K (ULift.{v} Kᵐᵒᵖ))) = -1 := by
  rw [← K0.finrankHom_eq_lift]
  simp

-- Reference objects retain module dimension as the simp normal form.
example (X : ModuleCat.FiniteProjective.{u, u} Kᵐᵒᵖ) :
    ProjectiveClass.finrankHom K (ProjectiveClass.of K (X × PUnit.{v + 1})) =
      Module.finrank Kᵐᵒᵖ X := by
  simp

example (X : ModuleCat.FiniteProjective.{u, u} Kᵐᵒᵖ) :
    K0.finrankHom K (K0.of K (X × PUnit.{v + 1})) =
      (Module.finrank Kᵐᵒᵖ X : ℤ) := by
  simp

section FiniteModules

variable (M : Type v) (N : Type w)
  [AddCommGroup M] [Module Kᵐᵒᵖ M] [Module.Finite Kᵐᵒᵖ M]
  [AddCommGroup N] [Module Kᵐᵒᵖ N] [Module.Finite Kᵐᵒᵖ N]

-- These modules need not be bundled reference objects or share a carrier universe.
example :
    ProjectiveClass.finrankHom K
      (ProjectiveClass.of K (ULift.{w} M × (N × PUnit.{u + 1}))) =
        Module.finrank Kᵐᵒᵖ M + Module.finrank Kᵐᵒᵖ N := by
  simp only [ProjectiveClass.of_prod, ProjectiveClass.of_ulift,
    ProjectiveClass.of_zero, map_add, add_zero,
    ProjectiveClass.finrankHom_of_module]

example :
    K0.finrankHom K (K0.of K (ULift.{w} M × (N × PUnit.{u + 1}))) =
      (Module.finrank Kᵐᵒᵖ M : ℤ) + (Module.finrank Kᵐᵒᵖ N : ℤ) := by
  simp only [K0.of_prod, K0.of_ulift, K0.of_zero, map_add, add_zero,
    K0.finrankHom_of_module]

-- Restriction of the integer map recovers class dimension on arbitrary modules.
example :
    ((K0.finrankHom K).comp (K0.ofClass K))
      (ProjectiveClass.of K (ULift.{w} M × PUnit.{u + 1})) =
        (Module.finrank Kᵐᵒᵖ M : ℤ) := by
  rw [AddMonoidHom.comp_apply, K0.finrankHom_ofClass]
  simp only [ProjectiveClass.of_prod, ProjectiveClass.of_ulift,
    ProjectiveClass.of_zero, add_zero,
    ProjectiveClass.finrankHom_of_module]

end FiniteModules

section

-- Inverse ring maps between scalar Type 0 and Type (u + 1) act inversely on classes.
example :
    (ProjectiveClass.map (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).toRingHom).comp
      (ProjectiveClass.map (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).symm.toRingHom) =
        AddMonoidHom.id (ProjectiveClass ℚ) := by
  rw [← ProjectiveClass.map_comp, RingEquiv.toRingHom_comp_symm_toRingHom,
    ProjectiveClass.map_id]

example (a : ProjectiveClass (ULift.{u + 1} ℚ)) :
    ProjectiveClass.map (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).symm.toRingHom
      (ProjectiveClass.map (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).toRingHom a) = a := by
  simpa only [RingEquiv.symm_toRingHom_comp_toRingHom, ProjectiveClass.map_id,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply] using
    (DFunLike.congr_fun
      (ProjectiveClass.map_comp
        (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).toRingHom
        (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).symm.toRingHom) a).symm

-- The same round trips hold on the whole K₀ group, not only its positive generators.
example :
    (K0.map (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).toRingHom).comp
      (K0.map (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).symm.toRingHom) =
        AddMonoidHom.id (K0 ℚ) := by
  rw [← K0.map_comp, RingEquiv.toRingHom_comp_symm_toRingHom, K0.map_id]

example (z : K0 (ULift.{u + 1} ℚ)) :
    K0.map (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).symm.toRingHom
      (K0.map (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).toRingHom z) = z := by
  simpa only [RingEquiv.symm_toRingHom_comp_toRingHom, K0.map_id,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply] using
    (DFunLike.congr_fun
      (K0.map_comp
        (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).toRingHom
        (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).symm.toRingHom) z).symm

end

end ProjectiveModulesTests.K0RankClient

namespace ProjectiveModulesTests.K0RankClient

section DimensionEquivalences

variable (D : Type u) [DivisionRing D]

-- The equivalences retain the whole canonical forward homomorphisms.
private theorem dimension_forward_homs :
    (ProjectiveClass.finrankEquiv D).toAddMonoidHom = ProjectiveClass.finrankHom D ∧
      (K0.finrankEquiv D).toAddMonoidHom = K0.finrankHom D := by
  exact ⟨ProjectiveClass.finrankEquiv_toAddMonoidHom D,
    K0.finrankEquiv_toAddMonoidHom D⟩

private theorem dimension_zero :
    ProjectiveClass.finrankEquiv D 0 = 0 ∧
      (ProjectiveClass.finrankEquiv D).symm 0 = 0 ∧
      K0.finrankEquiv D 0 = 0 ∧ (K0.finrankEquiv D).symm 0 = 0 := by
  exact ⟨map_zero _, map_zero _, map_zero _, map_zero _⟩

-- Every natural number has its coordinate module as the computed inverse.
private theorem coordinate_dimension_and_inverse (n : ℕ) :
    ProjectiveClass.finrankEquiv D (ProjectiveClass.of D (Fin n → Dᵐᵒᵖ)) = n ∧
      (ProjectiveClass.finrankEquiv D).symm n =
        ProjectiveClass.of D (Fin n → Dᵐᵒᵖ) ∧
      (ProjectiveClass.finrankEquiv D).symm n =
        n • ProjectiveClass.of D Dᵐᵒᵖ := by
  refine ⟨?_, ProjectiveClass.finrankEquiv_symm_apply D n, ?_⟩
  · rw [ProjectiveClass.finrankEquiv_of_module, Module.finrank_fin_fun]
  · rw [ProjectiveClass.finrankEquiv_symm_apply, ProjectiveClass.of_fin_fun_eq_nsmul]

private theorem coordinate_round_trips (n : ℕ) :
    (ProjectiveClass.finrankEquiv D).symm
        (ProjectiveClass.finrankEquiv D (ProjectiveClass.of D (Fin n → Dᵐᵒᵖ))) =
      ProjectiveClass.of D (Fin n → Dᵐᵒᵖ) ∧
      ProjectiveClass.finrankHom D ((ProjectiveClass.finrankEquiv D).symm n) = n := by
  constructor
  · rw [ProjectiveClass.finrankEquiv_apply]
    exact ProjectiveClass.finrankEquiv_symm_apply_finrank D _
  · exact ProjectiveClass.finrankHom_finrankEquiv_symm D n

private theorem completion_coordinate_inverse (n : ℕ) :
    (K0.finrankEquiv D).symm (n : ℤ) = K0.of D (Fin n → Dᵐᵒᵖ) ∧
      K0.finrankEquiv D (K0.of D (Fin n → Dᵐᵒᵖ)) = (n : ℤ) := by
  refine ⟨K0.finrankEquiv_symm_natCast D n, ?_⟩
  rw [K0.finrankEquiv_of_module, Module.finrank_fin_fun]

-- This inverse formula and its two forward evaluations range over all integers.
private theorem integer_inverse_and_dimension (z : ℤ) :
    (K0.finrankEquiv D).symm z = z • K0.of D Dᵐᵒᵖ ∧
      K0.finrankEquiv D ((K0.finrankEquiv D).symm z) = z ∧
      K0.finrankHom D ((K0.finrankEquiv D).symm z) = z := by
  exact ⟨K0.finrankEquiv_symm_apply D z,
    (K0.finrankEquiv D).apply_symm_apply z, K0.finrankHom_finrankEquiv_symm D z⟩

private theorem canonical_dimension_round_trips (a : ProjectiveClass D) (x : K0 D) :
    (ProjectiveClass.finrankEquiv D).symm (ProjectiveClass.finrankHom D a) = a ∧
      (K0.finrankEquiv D).symm (K0.finrankHom D x) = x := by
  exact ⟨ProjectiveClass.finrankEquiv_symm_apply_finrank D a,
    K0.finrankEquiv_symm_apply_finrank D x⟩

private theorem regular_dimension_and_inverse :
    ProjectiveClass.finrankEquiv D (ProjectiveClass.of D Dᵐᵒᵖ) = 1 ∧
      K0.finrankEquiv D (K0.of D Dᵐᵒᵖ) = 1 ∧
      (ProjectiveClass.finrankEquiv D).symm 1 = ProjectiveClass.of D Dᵐᵒᵖ ∧
      (K0.finrankEquiv D).symm 1 = K0.of D Dᵐᵒᵖ := by
  exact ⟨ProjectiveClass.finrankEquiv_of_self D, K0.finrankEquiv_of_self D,
    ProjectiveClass.finrankEquiv_symm_one D, K0.finrankEquiv_symm_one D⟩

-- Completion and natural dimension together recover any positive class generator.
private theorem completion_class_round_trip (a : ProjectiveClass D) :
    (K0.finrankEquiv D).symm (ProjectiveClass.finrankEquiv D a : ℤ) =
      K0.ofClass D a := by
  rw [← K0.finrankEquiv_ofClass]
  exact (K0.finrankEquiv D).symm_apply_apply _

private theorem coordinate_inverse_add (n m : ℕ) :
    (ProjectiveClass.finrankEquiv D).symm (n + m) =
      ProjectiveClass.of D (Fin n → Dᵐᵒᵖ) +
        ProjectiveClass.of D (Fin m → Dᵐᵒᵖ) := by
  rw [map_add, ProjectiveClass.finrankEquiv_symm_apply,
    ProjectiveClass.finrankEquiv_symm_apply]

private theorem integer_inverse_sub (z t : ℤ) :
    (K0.finrankEquiv D).symm (z - t) =
      z • K0.of D Dᵐᵒᵖ - t • K0.of D Dᵐᵒᵖ := by
  rw [map_sub, K0.finrankEquiv_symm_apply, K0.finrankEquiv_symm_apply]

-- PUnit is a zero module over D, not a division-ring scalar model.
private theorem zero_module_dimension :
    ProjectiveClass.finrankEquiv D (ProjectiveClass.of D PUnit.{v + 1}) = 0 ∧
      K0.finrankEquiv D (K0.of D PUnit.{v + 1}) = 0 := by
  constructor
  · rw [ProjectiveClass.finrankEquiv_of_module, Module.finrank_zero_of_subsingleton]
  · rw [K0.finrankEquiv_of_module, Module.finrank_zero_of_subsingleton, Nat.cast_zero]

private theorem coordinate_product_zero_dimension (n : ℕ) :
    ProjectiveClass.finrankEquiv D
        (ProjectiveClass.of D ((Fin n → Dᵐᵒᵖ) × PUnit.{v + 1})) = n ∧
      K0.finrankEquiv D (K0.of D ((Fin n → Dᵐᵒᵖ) × PUnit.{v + 1})) = (n : ℤ) := by
  constructor
  · simp only [ProjectiveClass.of_prod, ProjectiveClass.of_zero, add_zero,
      ProjectiveClass.finrankEquiv_of_module, Module.finrank_fin_fun]
  · simp only [K0.of_prod, K0.of_zero, add_zero,
      K0.finrankEquiv_of_module, Module.finrank_fin_fun]

private theorem carrier_lift_regular_dimension :
    ProjectiveClass.finrankEquiv D
        (ProjectiveClass.of D (ULift.{v + 1} Dᵐᵒᵖ)) = 1 ∧
      K0.finrankEquiv D (K0.of D (ULift.{v + 1} Dᵐᵒᵖ)) = 1 := by
  constructor
  · rw [ProjectiveClass.finrankEquiv_of_module, finrank_ulift, Module.finrank_self]
  · rw [K0.finrankEquiv_of_module, finrank_ulift, Module.finrank_self, Nat.cast_one]

section FiniteModules

variable (M : Type v) (N : Type w)
  [AddCommGroup M] [Module Dᵐᵒᵖ M] [Module.Finite Dᵐᵒᵖ M]
  [AddCommGroup N] [Module Dᵐᵒᵖ N] [Module.Finite Dᵐᵒᵖ N]

-- Evaluation works on composite modules with independently sized carriers.
private theorem finite_module_dimensions :
    ProjectiveClass.finrankEquiv D
        (ProjectiveClass.of D (ULift.{w} M × (N × PUnit.{u + 1}))) =
      Module.finrank Dᵐᵒᵖ M + Module.finrank Dᵐᵒᵖ N ∧
      K0.finrankEquiv D (K0.of D (ULift.{w} M × (N × PUnit.{u + 1}))) =
        (Module.finrank Dᵐᵒᵖ M : ℤ) + (Module.finrank Dᵐᵒᵖ N : ℤ) := by
  constructor
  · rw [ProjectiveClass.finrankEquiv_of_module]
    simp only [Module.finrank_prod, finrank_ulift,
      Module.finrank_zero_of_subsingleton, add_zero]
  · rw [K0.finrankEquiv_of_module]
    simp only [Module.finrank_prod, finrank_ulift,
      Module.finrank_zero_of_subsingleton, add_zero, Nat.cast_add]

private theorem finite_module_coordinate_recovery :
    ProjectiveClass.of D M =
        ProjectiveClass.of D (Fin (Module.finrank Dᵐᵒᵖ M) → Dᵐᵒᵖ) ∧
      K0.of D M = (Module.finrank Dᵐᵒᵖ M : ℤ) • K0.of D Dᵐᵒᵖ := by
  constructor
  · rw [ProjectiveClass.of_eq_finrankEquiv_symm,
      ProjectiveClass.finrankEquiv_symm_apply]
  · exact K0.of_eq_finrank_zsmul D M

private theorem finite_module_classification :
    K0.of D M = K0.of D N ↔ ProjectiveClass.of D M = ProjectiveClass.of D N := by
  rw [K0.of_eq_iff_linearEquiv D M N, ProjectiveClass.of_eq_iff D M N]

end FiniteModules

end DimensionEquivalences

section RationalModels

private theorem rational_regular_dimension :
    ProjectiveClass.finrankEquiv ℚ (ProjectiveClass.of ℚ ℚᵐᵒᵖ) = 1 ∧
      K0.finrankEquiv ℚ (K0.of ℚ ℚᵐᵒᵖ) = 1 := by
  exact ⟨ProjectiveClass.finrankEquiv_of_self ℚ, K0.finrankEquiv_of_self ℚ⟩

private theorem rational_plane_dimension :
    ProjectiveClass.finrankEquiv ℚ (ProjectiveClass.of ℚ (Fin 2 → ℚᵐᵒᵖ)) = 2 ∧
      K0.finrankEquiv ℚ (K0.of ℚ (Fin 2 → ℚᵐᵒᵖ)) = 2 := by
  constructor
  · rw [ProjectiveClass.finrankEquiv_of_module, Module.finrank_fin_fun]
  · simp only [K0.finrankEquiv_of_module, Module.finrank_fin_fun, Nat.cast_ofNat]

private theorem rational_distinct_classes :
    ProjectiveClass.of ℚ ℚᵐᵒᵖ ≠ ProjectiveClass.of ℚ (Fin 2 → ℚᵐᵒᵖ) ∧
      K0.of ℚ ℚᵐᵒᵖ ≠ K0.of ℚ (Fin 2 → ℚᵐᵒᵖ) := by
  constructor
  · intro equality
    have dimensions := congrArg (ProjectiveClass.finrankEquiv ℚ) equality
    rw [rational_regular_dimension.1, rational_plane_dimension.1] at dimensions
    exact (by decide : (1 : ℕ) ≠ 2) dimensions
  · intro equality
    have dimensions := congrArg (K0.finrankEquiv ℚ) equality
    rw [rational_regular_dimension.2, rational_plane_dimension.2] at dimensions
    exact (by decide : (1 : ℤ) ≠ 2) dimensions

private theorem rational_negative_three :
    (K0.finrankEquiv ℚ).symm (-3 : ℤ) = (-3 : ℤ) • K0.of ℚ ℚᵐᵒᵖ ∧
      K0.finrankEquiv ℚ ((-3 : ℤ) • K0.of ℚ ℚᵐᵒᵖ) = -3 := by
  refine ⟨K0.finrankEquiv_symm_apply ℚ (-3), ?_⟩
  rw [← K0.finrankEquiv_symm_apply]
  exact (K0.finrankEquiv ℚ).apply_symm_apply (-3)

-- The canonical scalar lift preserves both whole forward homomorphisms.
private theorem rational_lift_dimension_homs :
    ((ProjectiveClass.finrankEquiv (ULift.{u + 1} ℚ)).toAddMonoidHom).comp
        (ProjectiveClass.map
          (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).symm.toRingHom) =
      (ProjectiveClass.finrankEquiv ℚ).toAddMonoidHom ∧
      ((K0.finrankEquiv (ULift.{u + 1} ℚ)).toAddMonoidHom).comp
          (K0.map (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).symm.toRingHom) =
        (K0.finrankEquiv ℚ).toAddMonoidHom := by
  constructor
  · rw [ProjectiveClass.finrankEquiv_toAddMonoidHom,
      ProjectiveClass.finrankEquiv_toAddMonoidHom]
    exact ProjectiveClass.finrankHom_comp_map _
  · rw [K0.finrankEquiv_toAddMonoidHom, K0.finrankEquiv_toAddMonoidHom]
    exact K0.finrankHom_comp_map _

private theorem rational_lift_negative_three :
    K0.map (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).symm.toRingHom
        ((K0.finrankEquiv ℚ).symm (-3 : ℤ)) =
      (-3 : ℤ) • K0.of (ULift.{u + 1} ℚ) (ULift.{u + 1} ℚ)ᵐᵒᵖ ∧
      K0.finrankEquiv (ULift.{u + 1} ℚ)
          (K0.map (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).symm.toRingHom
            ((K0.finrankEquiv ℚ).symm (-3 : ℤ))) = -3 := by
  have value :
      K0.finrankEquiv (ULift.{u + 1} ℚ)
          (K0.map (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).symm.toRingHom
            ((K0.finrankEquiv ℚ).symm (-3 : ℤ))) = -3 := by
    rw [K0.finrankEquiv_apply]
    have naturality := DFunLike.congr_fun
      (K0.finrankHom_comp_map
        (ULift.ringEquiv : ULift.{u + 1} ℚ ≃+* ℚ).symm.toRingHom)
      ((K0.finrankEquiv ℚ).symm (-3 : ℤ))
    exact naturality.trans (K0.finrankHom_finrankEquiv_symm ℚ (-3))
  refine ⟨?_, value⟩
  rw [← K0.finrankEquiv_symm_apply]
  apply (K0.finrankEquiv (ULift.{u + 1} ℚ)).injective
  exact value.trans ((K0.finrankEquiv (ULift.{u + 1} ℚ)).apply_symm_apply (-3)).symm

end RationalModels

section QuaternionModels

-- These are real-coefficient constructors, not assumed noncommuting elements.
private def quaternionI : Quaternion ℝ := QuaternionAlgebra.mk 0 1 0 0
private def quaternionJ : Quaternion ℝ := QuaternionAlgebra.mk 0 0 1 0

private theorem quaternion_imaginary_products :
    (quaternionI * quaternionJ).imK = 1 ∧ (quaternionJ * quaternionI).imK = -1 := by
  constructor <;> simp [quaternionI, quaternionJ]

private theorem quaternion_noncommutative :
    quaternionI * quaternionJ ≠ quaternionJ * quaternionI := by
  intro equality
  have coordinate : (1 : ℝ) = -1 := by
    simpa only [quaternion_imaginary_products.1, quaternion_imaginary_products.2] using
      congrArg (fun q : Quaternion ℝ => q.imK) equality
  exact one_ne_zero (CharZero.eq_neg_self_iff.mp coordinate)

private theorem quaternion_regular_dimension :
    ProjectiveClass.finrankEquiv (Quaternion ℝ)
        (ProjectiveClass.of (Quaternion ℝ) (Quaternion ℝ)ᵐᵒᵖ) = 1 ∧
      K0.finrankEquiv (Quaternion ℝ) (K0.of (Quaternion ℝ) (Quaternion ℝ)ᵐᵒᵖ) = 1 := by
  exact ⟨ProjectiveClass.finrankEquiv_of_self (Quaternion ℝ),
    K0.finrankEquiv_of_self (Quaternion ℝ)⟩

private theorem quaternion_plane_dimension :
    ProjectiveClass.finrankEquiv (Quaternion ℝ)
        (ProjectiveClass.of (Quaternion ℝ) (Fin 2 → (Quaternion ℝ)ᵐᵒᵖ)) = 2 ∧
      K0.finrankEquiv (Quaternion ℝ)
        (K0.of (Quaternion ℝ) (Fin 2 → (Quaternion ℝ)ᵐᵒᵖ)) = 2 := by
  constructor
  · rw [ProjectiveClass.finrankEquiv_of_module, Module.finrank_fin_fun]
  · simp only [K0.finrankEquiv_of_module, Module.finrank_fin_fun, Nat.cast_ofNat]

private theorem quaternion_negative_three :
    (K0.finrankEquiv (Quaternion ℝ)).symm (-3 : ℤ) =
        (-3 : ℤ) • K0.of (Quaternion ℝ) (Quaternion ℝ)ᵐᵒᵖ ∧
      K0.finrankEquiv (Quaternion ℝ)
        ((-3 : ℤ) • K0.of (Quaternion ℝ) (Quaternion ℝ)ᵐᵒᵖ) = -3 := by
  refine ⟨K0.finrankEquiv_symm_apply (Quaternion ℝ) (-3), ?_⟩
  rw [← K0.finrankEquiv_symm_apply]
  exact (K0.finrankEquiv (Quaternion ℝ)).apply_symm_apply (-3)

-- Form the opposite after fixing the scalar lift; then lift only the carrier.
private abbrev LiftedQuaternion : Type 1 := ULift.{1} (Quaternion ℝ)
private abbrev LiftedQuaternionPlane : Type 2 := ULift.{2} (Fin 2 → LiftedQuaternionᵐᵒᵖ)

private theorem lifted_quaternion_plane_dimension :
    ProjectiveClass.finrankEquiv LiftedQuaternion
        (ProjectiveClass.of LiftedQuaternion LiftedQuaternionPlane) = 2 ∧
      K0.finrankEquiv LiftedQuaternion
        (K0.of LiftedQuaternion LiftedQuaternionPlane) = 2 := by
  constructor
  · rw [ProjectiveClass.finrankEquiv_of_module]
    simp only [LiftedQuaternionPlane, finrank_ulift, Module.finrank_fin_fun]
  · rw [K0.finrankEquiv_of_module]
    simp only [LiftedQuaternionPlane, finrank_ulift, Module.finrank_fin_fun, Nat.cast_ofNat]

private theorem lifted_quaternion_plane_inverse :
    (ProjectiveClass.finrankEquiv LiftedQuaternion).symm 2 =
        ProjectiveClass.of LiftedQuaternion LiftedQuaternionPlane ∧
      (K0.finrankEquiv LiftedQuaternion).symm (2 : ℤ) =
        K0.of LiftedQuaternion LiftedQuaternionPlane := by
  constructor
  · simpa only [LiftedQuaternionPlane, ProjectiveClass.of_ulift] using
      ProjectiveClass.finrankEquiv_symm_apply LiftedQuaternion 2
  · simpa only [LiftedQuaternionPlane, K0.of_ulift, Nat.cast_ofNat] using
      K0.finrankEquiv_symm_natCast LiftedQuaternion 2

end QuaternionModels

section ScalarMapCoordinates

variable {D : Type u} [DivisionRing D] {S : Type v} [DivisionRing S]

-- Standard equivalence data can be built locally from the scalar-extension map.
-- Its forward hom is that map, and both directions compute every coordinate.
private theorem scalar_map_class_coordinates (φ : D →+* S) (n : ℕ) :
    let e := AddEquiv.ofBijective (ProjectiveClass.map φ)
      (ProjectiveClass.map_bijective φ)
    e.toAddMonoidHom = ProjectiveClass.map φ ∧
      e (ProjectiveClass.of D (Fin n → Dᵐᵒᵖ)) =
        ProjectiveClass.of S (Fin n → Sᵐᵒᵖ) ∧
      e.symm (ProjectiveClass.of S (Fin n → Sᵐᵒᵖ)) =
        ProjectiveClass.of D (Fin n → Dᵐᵒᵖ) ∧
      ProjectiveClass.finrankEquiv S
        (e (ProjectiveClass.of D (Fin n → Dᵐᵒᵖ))) = n ∧
      ProjectiveClass.finrankEquiv D
        (e.symm (ProjectiveClass.of S (Fin n → Sᵐᵒᵖ))) = n := by
  let e := AddEquiv.ofBijective (ProjectiveClass.map φ)
    (ProjectiveClass.map_bijective φ)
  have forward (a : ProjectiveClass D) : e a = ProjectiveClass.map φ a :=
    AddEquiv.ofBijective_apply (ProjectiveClass.map φ)
      (ProjectiveClass.map_bijective φ) a
  have whole : e.toAddMonoidHom = ProjectiveClass.map φ := by
    apply AddMonoidHom.ext
    exact forward
  have dimension : ProjectiveClass.finrankEquiv S
      (e (ProjectiveClass.of D (Fin n → Dᵐᵒᵖ))) = n := by
    rw [forward, ProjectiveClass.finrankEquiv_apply]
    simpa only [AddMonoidHom.comp_apply, ProjectiveClass.finrankHom_of_module,
      Module.finrank_fin_fun] using
      DFunLike.congr_fun (ProjectiveClass.finrankHom_comp_map φ)
        (ProjectiveClass.of D (Fin n → Dᵐᵒᵖ))
  have image : e (ProjectiveClass.of D (Fin n → Dᵐᵒᵖ)) =
      ProjectiveClass.of S (Fin n → Sᵐᵒᵖ) := by
    apply (ProjectiveClass.finrankEquiv S).injective
    exact dimension.trans (coordinate_dimension_and_inverse S n).1.symm
  have preimage : e.symm (ProjectiveClass.of S (Fin n → Sᵐᵒᵖ)) =
      ProjectiveClass.of D (Fin n → Dᵐᵒᵖ) := by
    apply e.injective
    rw [e.apply_symm_apply, image]
  refine ⟨whole, image, preimage, dimension, ?_⟩
  rw [preimage]
  exact (coordinate_dimension_and_inverse D n).1

private theorem scalar_map_integer_coordinates (φ : D →+* S) (z : ℤ) :
    let e := AddEquiv.ofBijective (K0.map φ) (K0.map_bijective φ)
    e.toAddMonoidHom = K0.map φ ∧
      e (z • K0.of D Dᵐᵒᵖ) = z • K0.of S Sᵐᵒᵖ ∧
      e.symm (z • K0.of S Sᵐᵒᵖ) = z • K0.of D Dᵐᵒᵖ ∧
      K0.finrankEquiv S (e (z • K0.of D Dᵐᵒᵖ)) = z ∧
      K0.finrankEquiv D (e.symm (z • K0.of S Sᵐᵒᵖ)) = z := by
  let e := AddEquiv.ofBijective (K0.map φ) (K0.map_bijective φ)
  have forward (x : K0 D) : e x = K0.map φ x :=
    AddEquiv.ofBijective_apply (K0.map φ) (K0.map_bijective φ) x
  have whole : e.toAddMonoidHom = K0.map φ := by
    apply AddMonoidHom.ext
    exact forward
  have dimension : K0.finrankEquiv S (e (z • K0.of D Dᵐᵒᵖ)) = z := by
    rw [forward, K0.finrankEquiv_apply]
    have naturality := DFunLike.congr_fun (K0.finrankHom_comp_map φ)
      (z • K0.of D Dᵐᵒᵖ)
    exact naturality.trans (by
      simpa only [K0.finrankEquiv_symm_apply] using
        (integer_inverse_and_dimension D z).2.2)
  have image : e (z • K0.of D Dᵐᵒᵖ) = z • K0.of S Sᵐᵒᵖ := by
    apply (K0.finrankEquiv S).injective
    exact dimension.trans (by
      simpa only [K0.finrankEquiv_symm_apply] using
        (integer_inverse_and_dimension S z).2.1.symm)
  have preimage : e.symm (z • K0.of S Sᵐᵒᵖ) = z • K0.of D Dᵐᵒᵖ := by
    apply e.injective
    rw [e.apply_symm_apply, image]
  refine ⟨whole, image, preimage, dimension, ?_⟩
  rw [preimage]
  simpa only [K0.finrankEquiv_symm_apply] using
    (integer_inverse_and_dimension D z).2.1

end ScalarMapCoordinates

section ComplexScalarMaps

-- The two scalar maps differ on I, although their induced bundled maps agree.
private theorem complex_scalar_homs_distinct : RingHom.id ℂ ≠ starRingEnd ℂ := by
  intro equality
  have imaginary : Complex.I = -Complex.I := by
    simpa only [RingHom.id_apply, Complex.conj_I] using
      DFunLike.congr_fun equality Complex.I
  have coordinate : (1 : ℝ) = -1 := by
    simpa only [Complex.I_im, Complex.neg_im] using congrArg Complex.im imaginary
  exact one_ne_zero (CharZero.eq_neg_self_iff.mp coordinate)

private theorem complex_scalar_maps_eq_id :
    ProjectiveClass.map (RingHom.id ℂ) = AddMonoidHom.id (ProjectiveClass ℂ) ∧
      ProjectiveClass.map (starRingEnd ℂ) = AddMonoidHom.id (ProjectiveClass ℂ) ∧
      K0.map (RingHom.id ℂ) = AddMonoidHom.id (K0 ℂ) ∧
      K0.map (starRingEnd ℂ) = AddMonoidHom.id (K0 ℂ) := by
  exact ⟨ProjectiveClass.map_id ℂ,
    (ProjectiveClass.map_eq_map (starRingEnd ℂ) (RingHom.id ℂ)).trans
      (ProjectiveClass.map_id ℂ),
    K0.map_id ℂ,
    (K0.map_eq_map (starRingEnd ℂ) (RingHom.id ℂ)).trans (K0.map_id ℂ)⟩

private theorem complex_conjugate_plane :
    ProjectiveClass.map (starRingEnd ℂ) (ProjectiveClass.of ℂ (Fin 2 → ℂᵐᵒᵖ)) =
        ProjectiveClass.of ℂ (Fin 2 → ℂᵐᵒᵖ) ∧
      K0.map (starRingEnd ℂ) (K0.of ℂ (Fin 2 → ℂᵐᵒᵖ)) =
        K0.of ℂ (Fin 2 → ℂᵐᵒᵖ) ∧
      ProjectiveClass.finrankEquiv ℂ
        (ProjectiveClass.map (starRingEnd ℂ)
          (ProjectiveClass.of ℂ (Fin 2 → ℂᵐᵒᵖ))) = 2 ∧
      K0.finrankEquiv ℂ
        (K0.map (starRingEnd ℂ) (K0.of ℂ (Fin 2 → ℂᵐᵒᵖ))) = 2 := by
  simp only [complex_scalar_maps_eq_id.2.1, complex_scalar_maps_eq_id.2.2.2,
    AddMonoidHom.id_apply, ProjectiveClass.finrankEquiv_of_module,
    K0.finrankEquiv_of_module, Module.finrank_fin_fun, Nat.cast_ofNat]
  exact ⟨True.intro, True.intro, True.intro, True.intro⟩

private theorem complex_conjugate_integer_coordinates (z : ℤ) :
    K0.map (starRingEnd ℂ) (z • K0.of ℂ ℂᵐᵒᵖ) = z • K0.of ℂ ℂᵐᵒᵖ ∧
      K0.finrankEquiv ℂ (K0.map (starRingEnd ℂ) (z • K0.of ℂ ℂᵐᵒᵖ)) = z := by
  rw [complex_scalar_maps_eq_id.2.2.2, AddMonoidHom.id_apply]
  refine ⟨rfl, ?_⟩
  simpa only [K0.finrankEquiv_symm_apply] using
    (integer_inverse_and_dimension ℂ z).2.1

private theorem complex_conjugate_negative_three :
    K0.map (starRingEnd ℂ) ((-3 : ℤ) • K0.of ℂ ℂᵐᵒᵖ) =
        (-3 : ℤ) • K0.of ℂ ℂᵐᵒᵖ ∧
      K0.finrankEquiv ℂ
        (K0.map (starRingEnd ℂ) ((-3 : ℤ) • K0.of ℂ ℂᵐᵒᵖ)) = -3 := by
  exact complex_conjugate_integer_coordinates (-3)

end ComplexScalarMaps

section RationalComplexExtension

-- Every rational cast has imaginary part zero, so I has no scalar preimage.
private theorem rational_complex_not_surjective :
    ¬ Function.Surjective (Rat.castHom ℂ) := by
  intro surjective
  obtain ⟨q, equality⟩ := surjective Complex.I
  have coordinate : (0 : ℝ) = 1 := by
    simpa only [Rat.coe_castHom, Complex.ratCast_im, Complex.I_im] using
      congrArg Complex.im equality
  exact zero_ne_one coordinate

private theorem rational_complex_maps_bijective :
    ¬ Function.Surjective (Rat.castHom ℂ) ∧
      Function.Bijective (ProjectiveClass.map (Rat.castHom ℂ)) ∧
      Function.Bijective (K0.map (Rat.castHom ℂ)) := by
  exact ⟨rational_complex_not_surjective, ProjectiveClass.map_bijective (Rat.castHom ℂ),
    K0.map_bijective (Rat.castHom ℂ)⟩

-- Neither inverse uses a complex-to-rational ring homomorphism.
private theorem rational_complex_plane_coordinates :
    let e := AddEquiv.ofBijective (ProjectiveClass.map (Rat.castHom ℂ))
      (ProjectiveClass.map_bijective (Rat.castHom ℂ))
    ProjectiveClass.map (Rat.castHom ℂ) (ProjectiveClass.of ℚ (Fin 2 → ℚᵐᵒᵖ)) =
        ProjectiveClass.of ℂ (Fin 2 → ℂᵐᵒᵖ) ∧
      e.symm (ProjectiveClass.of ℂ (Fin 2 → ℂᵐᵒᵖ)) =
        ProjectiveClass.of ℚ (Fin 2 → ℚᵐᵒᵖ) ∧
      ProjectiveClass.finrankEquiv ℂ
        (ProjectiveClass.map (Rat.castHom ℂ)
          (ProjectiveClass.of ℚ (Fin 2 → ℚᵐᵒᵖ))) = 2 ∧
      ProjectiveClass.finrankEquiv ℚ
        (e.symm (ProjectiveClass.of ℂ (Fin 2 → ℂᵐᵒᵖ))) = 2 := by
  simpa only [AddEquiv.ofBijective_apply] using
    (scalar_map_class_coordinates (Rat.castHom ℂ) 2).2

private theorem rational_complex_integer_coordinates (z : ℤ) :
    let e := AddEquiv.ofBijective (K0.map (Rat.castHom ℂ))
      (K0.map_bijective (Rat.castHom ℂ))
    K0.map (Rat.castHom ℂ) (z • K0.of ℚ ℚᵐᵒᵖ) = z • K0.of ℂ ℂᵐᵒᵖ ∧
      e.symm (z • K0.of ℂ ℂᵐᵒᵖ) = z • K0.of ℚ ℚᵐᵒᵖ ∧
      K0.finrankEquiv ℂ (K0.map (Rat.castHom ℂ) (z • K0.of ℚ ℚᵐᵒᵖ)) = z ∧
      K0.finrankEquiv ℚ (e.symm (z • K0.of ℂ ℂᵐᵒᵖ)) = z := by
  simpa only [AddEquiv.ofBijective_apply] using
    (scalar_map_integer_coordinates (Rat.castHom ℂ) z).2

private theorem rational_complex_negative_three :
    K0.map (Rat.castHom ℂ) ((-3 : ℤ) • K0.of ℚ ℚᵐᵒᵖ) =
        (-3 : ℤ) • K0.of ℂ ℂᵐᵒᵖ ∧
      K0.finrankEquiv ℂ
        (K0.map (Rat.castHom ℂ) ((-3 : ℤ) • K0.of ℚ ℚᵐᵒᵖ)) = -3 ∧
      (AddEquiv.ofBijective (K0.map (Rat.castHom ℂ))
        (K0.map_bijective (Rat.castHom ℂ))).symm
          ((-3 : ℤ) • K0.of ℂ ℂᵐᵒᵖ) = (-3 : ℤ) • K0.of ℚ ℚᵐᵒᵖ := by
  have coordinates := rational_complex_integer_coordinates (-3)
  exact ⟨coordinates.1, coordinates.2.2.1, coordinates.2.1⟩

end RationalComplexExtension

section QuaternionScalarLift

-- Scalar, lifted scalar, and lifted plane live in Type 0, Type 1, and Type 2.
-- Noncommutativity is witnessed by the existing real quaternion constructors.
private theorem quaternion_scalar_lift_maps_bijective :
    quaternionI * quaternionJ ≠ quaternionJ * quaternionI ∧
      Function.Bijective
        (ProjectiveClass.map
          (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom) ∧
      Function.Bijective
        (K0.map
          (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom) := by
  exact ⟨quaternion_noncommutative, ProjectiveClass.map_bijective _, K0.map_bijective _⟩

private theorem quaternion_scalar_lift_plane :
    ProjectiveClass.map
        (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom
        (ProjectiveClass.of (Quaternion ℝ) (Fin 2 → (Quaternion ℝ)ᵐᵒᵖ)) =
      ProjectiveClass.of LiftedQuaternion LiftedQuaternionPlane ∧
      K0.map
          (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom
          (K0.of (Quaternion ℝ) (Fin 2 → (Quaternion ℝ)ᵐᵒᵖ)) =
        K0.of LiftedQuaternion LiftedQuaternionPlane ∧
      ProjectiveClass.finrankEquiv LiftedQuaternion
        (ProjectiveClass.map
          (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom
          (ProjectiveClass.of (Quaternion ℝ) (Fin 2 → (Quaternion ℝ)ᵐᵒᵖ))) = 2 ∧
      K0.finrankEquiv LiftedQuaternion
        (K0.map
          (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom
          (K0.of (Quaternion ℝ) (Fin 2 → (Quaternion ℝ)ᵐᵒᵖ))) = 2 := by
  have classes : ProjectiveClass.map
      (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom
      (ProjectiveClass.of (Quaternion ℝ) (Fin 2 → (Quaternion ℝ)ᵐᵒᵖ)) =
      ProjectiveClass.of LiftedQuaternion LiftedQuaternionPlane := by
    simpa only [AddEquiv.ofBijective_apply, LiftedQuaternionPlane,
      ProjectiveClass.of_ulift] using
      (scalar_map_class_coordinates
        (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom 2).2.1
  have groups : K0.map
      (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom
      (K0.of (Quaternion ℝ) (Fin 2 → (Quaternion ℝ)ᵐᵒᵖ)) =
      K0.of LiftedQuaternion LiftedQuaternionPlane := by
    rw [← K0.ofClass_of (Quaternion ℝ) (Fin 2 → (Quaternion ℝ)ᵐᵒᵖ),
      K0.map_ofClass, classes, K0.ofClass_of]
  refine ⟨classes, groups, ?_, ?_⟩
  · rw [classes]
    exact lifted_quaternion_plane_dimension.1
  · rw [groups]
    exact lifted_quaternion_plane_dimension.2

private theorem quaternion_scalar_lift_plane_preimages :
    let e := AddEquiv.ofBijective
      (ProjectiveClass.map
        (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom)
      (ProjectiveClass.map_bijective
        (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom)
    let f := AddEquiv.ofBijective
      (K0.map (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom)
      (K0.map_bijective
        (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom)
    e.symm (ProjectiveClass.of LiftedQuaternion LiftedQuaternionPlane) =
        ProjectiveClass.of (Quaternion ℝ) (Fin 2 → (Quaternion ℝ)ᵐᵒᵖ) ∧
      f.symm (K0.of LiftedQuaternion LiftedQuaternionPlane) =
        K0.of (Quaternion ℝ) (Fin 2 → (Quaternion ℝ)ᵐᵒᵖ) ∧
      ProjectiveClass.finrankEquiv (Quaternion ℝ)
        (e.symm (ProjectiveClass.of LiftedQuaternion LiftedQuaternionPlane)) = 2 ∧
      K0.finrankEquiv (Quaternion ℝ)
        (f.symm (K0.of LiftedQuaternion LiftedQuaternionPlane)) = 2 := by
  have classes := (scalar_map_class_coordinates
    (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom 2).2.2.1
  have groups :
      (AddEquiv.ofBijective
        (K0.map (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom)
        (K0.map_bijective
          (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom)).symm
          (K0.of LiftedQuaternion LiftedQuaternionPlane) =
        K0.of (Quaternion ℝ) (Fin 2 → (Quaternion ℝ)ᵐᵒᵖ) := by
    let f := AddEquiv.ofBijective
      (K0.map (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom)
      (K0.map_bijective
        (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom)
    have forward (x : K0 (Quaternion ℝ)) :
        f x = K0.map
          (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom x :=
      AddEquiv.ofBijective_apply
        (K0.map (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom)
        (K0.map_bijective
          (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom) x
    apply f.injective
    rw [f.apply_symm_apply, forward, quaternion_scalar_lift_plane.2.1]
  have classes' :
      (AddEquiv.ofBijective
        (ProjectiveClass.map
          (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom)
        (ProjectiveClass.map_bijective
          (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom)).symm
          (ProjectiveClass.of LiftedQuaternion LiftedQuaternionPlane) =
        ProjectiveClass.of (Quaternion ℝ) (Fin 2 → (Quaternion ℝ)ᵐᵒᵖ) := by
    rw [← lifted_quaternion_plane_inverse.1, ProjectiveClass.finrankEquiv_symm_apply]
    exact classes
  refine ⟨classes', groups, ?_, ?_⟩
  · rw [classes']
    exact quaternion_plane_dimension.1
  · rw [groups]
    exact quaternion_plane_dimension.2

private theorem quaternion_scalar_lift_integer_coordinates (z : ℤ) :
    let e := AddEquiv.ofBijective
      (K0.map (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom)
      (K0.map_bijective
        (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom)
    K0.map (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom
        (z • K0.of (Quaternion ℝ) (Quaternion ℝ)ᵐᵒᵖ) =
      z • K0.of LiftedQuaternion LiftedQuaternionᵐᵒᵖ ∧
      e.symm (z • K0.of LiftedQuaternion LiftedQuaternionᵐᵒᵖ) =
        z • K0.of (Quaternion ℝ) (Quaternion ℝ)ᵐᵒᵖ ∧
      K0.finrankEquiv LiftedQuaternion
        (K0.map (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom
          (z • K0.of (Quaternion ℝ) (Quaternion ℝ)ᵐᵒᵖ)) = z ∧
      K0.finrankEquiv (Quaternion ℝ)
        (e.symm (z • K0.of LiftedQuaternion LiftedQuaternionᵐᵒᵖ)) = z := by
  simpa only [AddEquiv.ofBijective_apply] using
    (scalar_map_integer_coordinates
      (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom z).2

private theorem quaternion_scalar_lift_negative_three :
    K0.map (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom
        ((-3 : ℤ) • K0.of (Quaternion ℝ) (Quaternion ℝ)ᵐᵒᵖ) =
      (-3 : ℤ) • K0.of LiftedQuaternion LiftedQuaternionᵐᵒᵖ ∧
      K0.finrankEquiv LiftedQuaternion
        (K0.map (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom
          ((-3 : ℤ) • K0.of (Quaternion ℝ) (Quaternion ℝ)ᵐᵒᵖ)) = -3 ∧
      (AddEquiv.ofBijective
        (K0.map (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom)
        (K0.map_bijective
          (ULift.ringEquiv : LiftedQuaternion ≃+* Quaternion ℝ).symm.toRingHom)).symm
          ((-3 : ℤ) • K0.of LiftedQuaternion LiftedQuaternionᵐᵒᵖ) =
        (-3 : ℤ) • K0.of (Quaternion ℝ) (Quaternion ℝ)ᵐᵒᵖ := by
  have coordinates := quaternion_scalar_lift_integer_coordinates (-3)
  exact ⟨coordinates.1, coordinates.2.2.1, coordinates.2.1⟩

end QuaternionScalarLift

section ZeroRingScalarBoundary

-- These target maps are Ring-general, not division-ring maps.
private theorem rational_zero_ring_maps_collapse (a : ProjectiveClass ℚ) (x : K0 ℚ) :
    ProjectiveClass.map (algebraMap ℚ PUnit.{u + 1} : ℚ →+* PUnit.{u + 1}) a = 0 ∧
      K0.map (algebraMap ℚ PUnit.{u + 1} : ℚ →+* PUnit.{u + 1}) x = 0 := by
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

-- All source coordinates retain their usual dimensions but have zero images.
private theorem rational_zero_ring_coordinate_collapse (n : ℕ) (z : ℤ) :
    ProjectiveClass.map (algebraMap ℚ PUnit.{u + 1} : ℚ →+* PUnit.{u + 1})
        (ProjectiveClass.of ℚ (Fin n → ℚᵐᵒᵖ)) = 0 ∧
      K0.map (algebraMap ℚ PUnit.{u + 1} : ℚ →+* PUnit.{u + 1})
        (z • K0.of ℚ ℚᵐᵒᵖ) = 0 ∧
      ProjectiveClass.finrankEquiv ℚ (ProjectiveClass.of ℚ (Fin n → ℚᵐᵒᵖ)) = n ∧
      K0.finrankEquiv ℚ (z • K0.of ℚ ℚᵐᵒᵖ) = z := by
  refine ⟨Subsingleton.elim _ _, Subsingleton.elim _ _,
    (coordinate_dimension_and_inverse ℚ n).1, ?_⟩
  simpa only [K0.finrankEquiv_symm_apply] using
    (integer_inverse_and_dimension ℚ z).2.1

private theorem rational_zero_ring_maps_not_injective :
    ¬ Function.Injective
        (ProjectiveClass.map (algebraMap ℚ PUnit.{u + 1} : ℚ →+* PUnit.{u + 1})) ∧
      ¬ Function.Injective
        (K0.map (algebraMap ℚ PUnit.{u + 1} : ℚ →+* PUnit.{u + 1})) := by
  constructor
  · intro injective
    have collision :
        ProjectiveClass.map (algebraMap ℚ PUnit.{u + 1} : ℚ →+* PUnit.{u + 1})
            (ProjectiveClass.of ℚ ℚᵐᵒᵖ) =
          ProjectiveClass.map (algebraMap ℚ PUnit.{u + 1} : ℚ →+* PUnit.{u + 1}) 0 :=
      Subsingleton.elim _ _
    have dimensions := congrArg (ProjectiveClass.finrankEquiv ℚ) (injective collision)
    have impossible : (1 : ℕ) = 0 := by
      simpa only [ProjectiveClass.finrankEquiv_of_self, map_zero] using dimensions
    exact one_ne_zero impossible
  · intro injective
    have collision :
        K0.map (algebraMap ℚ PUnit.{u + 1} : ℚ →+* PUnit.{u + 1})
            (K0.of ℚ ℚᵐᵒᵖ) =
          K0.map (algebraMap ℚ PUnit.{u + 1} : ℚ →+* PUnit.{u + 1}) 0 :=
      Subsingleton.elim _ _
    have dimensions := congrArg (K0.finrankEquiv ℚ) (injective collision)
    have impossible : (1 : ℤ) = 0 := by
      simpa only [K0.finrankEquiv_of_self, map_zero] using dimensions
    exact one_ne_zero impossible

private theorem rational_zero_ring_negative_three :
    K0.map (algebraMap ℚ PUnit.{u + 1} : ℚ →+* PUnit.{u + 1})
        ((-3 : ℤ) • K0.of ℚ ℚᵐᵒᵖ) = 0 ∧
      K0.finrankEquiv ℚ ((-3 : ℤ) • K0.of ℚ ℚᵐᵒᵖ) = -3 ∧
      (-3 : ℤ) • K0.of ℚ ℚᵐᵒᵖ ≠ 0 := by
  refine ⟨Subsingleton.elim _ _, rational_negative_three.2, ?_⟩
  intro equality
  have dimensions : (-3 : ℤ) = 0 := by
    simpa only [rational_negative_three.2, map_zero] using
      congrArg (K0.finrankEquiv ℚ) equality
  exact (by decide : (-3 : ℤ) ≠ 0) dimensions

end ZeroRingScalarBoundary

section MatrixScalarMaps

-- Nonzero diagonal matrix units have zero product in this ring.
private theorem matrix_diagonal_units_zero_product :
    Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) ≠ 0 ∧
      Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) ≠ 0 ∧
      Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) *
        Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro equality
    have coordinate : (1 : ℂ) = 0 := by
      simpa only [Matrix.single_apply_same, Matrix.zero_apply] using
        congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) equality
    exact one_ne_zero coordinate
  · intro equality
    have coordinate : (1 : ℂ) = 0 := by
      simpa only [Matrix.single_apply_same, Matrix.zero_apply] using
        congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1) equality
    exact one_ne_zero coordinate
  · apply Matrix.single_mul_single_of_ne
    decide

-- The two orders of the off-diagonal product give unequal diagonal units.
private theorem matrix_off_diagonal_units_noncommutative :
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) *
        Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) =
      Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) ∧
      Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) *
          Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) =
        Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) ∧
      Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) ≠
        Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) ∧
      Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) *
          Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) ≠
        Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) *
          Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) := by
  have forward : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) *
      Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) =
      Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) := by
    simp only [Matrix.single_mul_single_same, one_mul]
  have backward : Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) *
      Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) =
      Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) := by
    simp only [Matrix.single_mul_single_same, one_mul]
  have diagonal_ne : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) ≠
      Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) := by
    intro equality
    have coordinate : (1 : ℂ) = 0 := by
      simpa only [Matrix.single_apply_same,
        Matrix.single_apply_of_row_ne (by decide : (1 : Fin 2) ≠ 0)] using
        congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) equality
    exact one_ne_zero coordinate
  refine ⟨forward, backward, diagonal_ne, ?_⟩
  intro equality
  exact diagonal_ne (forward.symm.trans (equality.trans backward))

-- Scalar diagonals distinguish the embedding from its conjugate composite.
private theorem matrix_scalar_homs_distinct :
    let S := Matrix (Fin 2) (Fin 2) ℂ
    let φ : ℂ →+* S := algebraMap ℂ S
    let ψ : ℂ →+* S := φ.comp (starRingEnd ℂ)
    φ Complex.I 0 0 = Complex.I ∧
      ψ Complex.I 0 0 = -Complex.I ∧ φ ≠ ψ := by
  let S := Matrix (Fin 2) (Fin 2) ℂ
  let φ : ℂ →+* S := algebraMap ℂ S
  let ψ : ℂ →+* S := φ.comp (starRingEnd ℂ)
  have standard : φ Complex.I 0 0 = Complex.I := by
    dsimp only [φ, S]
    rw [Matrix.algebraMap_matrix_apply, ite_eq_left rfl, Algebra.algebraMap_self_apply]
  have conjugate : ψ Complex.I 0 0 = -Complex.I := by
    dsimp only [ψ, φ, S]
    rw [RingHom.comp_apply, Complex.conj_I, Matrix.algebraMap_matrix_apply,
      ite_eq_left rfl, Algebra.algebraMap_self_apply]
  refine ⟨standard, conjugate, ?_⟩
  intro equality
  have imaginary : Complex.I = -Complex.I := by
    exact standard.symm.trans
      ((congrArg (fun f : ℂ →+* S => f Complex.I 0 0) equality).trans conjugate)
  have coordinate : (1 : ℝ) = -1 := by
    simpa only [Complex.I_im, Complex.neg_im] using congrArg Complex.im imaginary
  exact one_ne_zero (CharZero.eq_neg_self_iff.mp coordinate)

-- Whole induced maps agree despite distinct scalar maps and ring boundaries.
private theorem matrix_scalar_maps_eq :
    let S := Matrix (Fin 2) (Fin 2) ℂ
    let φ : ℂ →+* S := algebraMap ℂ S
    let ψ : ℂ →+* S := φ.comp (starRingEnd ℂ)
    φ ≠ ψ ∧
      ProjectiveClass.map φ = ProjectiveClass.map ψ ∧
      K0.map φ = K0.map ψ ∧
      Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) ≠ 0 ∧
      Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) ≠ 0 ∧
      Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) *
        Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) = 0 ∧
      Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) *
          Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) ≠
        Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ) *
          Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ) := by
  let S := Matrix (Fin 2) (Fin 2) ℂ
  let φ : ℂ →+* S := algebraMap ℂ S
  let ψ : ℂ →+* S := φ.comp (starRingEnd ℂ)
  exact ⟨matrix_scalar_homs_distinct.2.2,
    ProjectiveClass.map_eq_map φ ψ, K0.map_eq_map φ ψ,
    matrix_diagonal_units_zero_product.1, matrix_diagonal_units_zero_product.2.1,
    matrix_diagonal_units_zero_product.2.2,
    matrix_off_diagonal_units_noncommutative.2.2.2⟩

-- Coordinate extension computes free classes without a target dimension map.
private theorem matrix_scalar_class_image (n : ℕ) :
    let S := Matrix (Fin 2) (Fin 2) ℂ
    ProjectiveClass.map (algebraMap ℂ S)
        (ProjectiveClass.of ℂ (Fin n → ℂᵐᵒᵖ)) =
      ProjectiveClass.of S (Fin n → Sᵐᵒᵖ) := by
  let S := Matrix (Fin 2) (Fin 2) ℂ
  let φ : ℂ →+* S := algebraMap ℂ S
  dsimp only
  rw [ProjectiveClass.map_of]
  exact ProjectiveClass.of_eq_of_equiv S _
    ((ModuleCat.RightExtension.mapLinearEquiv φ
      (Module.rightFreeCoordEquiv ℂ (Fin n))).trans
      ((ModuleCat.RightExtension.rightFreeLinearEquiv φ (Fin n)).trans
        (Module.rightFreeCoordEquiv S (Fin n)).symm))

private theorem matrix_scalar_class_coordinates (n : ℕ) :
    let S := Matrix (Fin 2) (Fin 2) ℂ
    let φ : ℂ →+* S := algebraMap ℂ S
    let ψ : ℂ →+* S := φ.comp (starRingEnd ℂ)
    ProjectiveClass.map φ (ProjectiveClass.of ℂ (Fin n → ℂᵐᵒᵖ)) =
        ProjectiveClass.of S (Fin n → Sᵐᵒᵖ) ∧
      ProjectiveClass.map ψ (ProjectiveClass.of ℂ (Fin n → ℂᵐᵒᵖ)) =
        ProjectiveClass.of S (Fin n → Sᵐᵒᵖ) ∧
      ProjectiveClass.finrankEquiv ℂ (ProjectiveClass.of ℂ (Fin n → ℂᵐᵒᵖ)) = n := by
  let S := Matrix (Fin 2) (Fin 2) ℂ
  let φ : ℂ →+* S := algebraMap ℂ S
  let ψ : ℂ →+* S := φ.comp (starRingEnd ℂ)
  have image : ProjectiveClass.map φ (ProjectiveClass.of ℂ (Fin n → ℂᵐᵒᵖ)) =
      ProjectiveClass.of S (Fin n → Sᵐᵒᵖ) := matrix_scalar_class_image n
  refine ⟨image, ?_, (coordinate_dimension_and_inverse ℂ n).1⟩
  rw [← matrix_scalar_maps_eq.2.1]
  exact image

private theorem matrix_scalar_plane :
    let S := Matrix (Fin 2) (Fin 2) ℂ
    let φ : ℂ →+* S := algebraMap ℂ S
    let ψ : ℂ →+* S := φ.comp (starRingEnd ℂ)
    ProjectiveClass.map φ (ProjectiveClass.of ℂ (Fin 2 → ℂᵐᵒᵖ)) =
        ProjectiveClass.of S (Fin 2 → Sᵐᵒᵖ) ∧
      ProjectiveClass.map ψ (ProjectiveClass.of ℂ (Fin 2 → ℂᵐᵒᵖ)) =
        ProjectiveClass.of S (Fin 2 → Sᵐᵒᵖ) ∧
      ProjectiveClass.finrankEquiv ℂ (ProjectiveClass.of ℂ (Fin 2 → ℂᵐᵒᵖ)) = 2 := by
  exact matrix_scalar_class_coordinates 2

-- The regular image follows from the one-coordinate class calculation.
-- Additivity then computes every signed multiple, with dimension only at source.
private theorem matrix_scalar_integer_coordinates (z : ℤ) :
    let S := Matrix (Fin 2) (Fin 2) ℂ
    let φ : ℂ →+* S := algebraMap ℂ S
    let ψ : ℂ →+* S := φ.comp (starRingEnd ℂ)
    K0.map φ (z • K0.of ℂ ℂᵐᵒᵖ) = z • K0.of S Sᵐᵒᵖ ∧
      K0.map ψ (z • K0.of ℂ ℂᵐᵒᵖ) = z • K0.of S Sᵐᵒᵖ ∧
      K0.finrankEquiv ℂ (z • K0.of ℂ ℂᵐᵒᵖ) = z := by
  let S := Matrix (Fin 2) (Fin 2) ℂ
  let φ : ℂ →+* S := algebraMap ℂ S
  let ψ : ℂ →+* S := φ.comp (starRingEnd ℂ)
  have classes : ProjectiveClass.map φ (ProjectiveClass.of ℂ ℂᵐᵒᵖ) =
      ProjectiveClass.of S Sᵐᵒᵖ := by
    simpa only [ProjectiveClass.of_fin_fun_eq_nsmul, one_nsmul] using
      matrix_scalar_class_image 1
  have regular : K0.map φ (K0.of ℂ ℂᵐᵒᵖ) = K0.of S Sᵐᵒᵖ := by
    rw [← K0.ofClass_of ℂ ℂᵐᵒᵖ, K0.map_ofClass, classes, K0.ofClass_of]
  have image : K0.map φ (z • K0.of ℂ ℂᵐᵒᵖ) = z • K0.of S Sᵐᵒᵖ := by
    rw [map_zsmul, regular]
  refine ⟨image, ?_, ?_⟩
  · rw [← matrix_scalar_maps_eq.2.2.1]
    exact image
  · simpa only [K0.finrankEquiv_symm_apply] using
      (integer_inverse_and_dimension ℂ z).2.1

private theorem matrix_scalar_negative_three :
    let S := Matrix (Fin 2) (Fin 2) ℂ
    let φ : ℂ →+* S := algebraMap ℂ S
    let ψ : ℂ →+* S := φ.comp (starRingEnd ℂ)
    K0.map φ ((-3 : ℤ) • K0.of ℂ ℂᵐᵒᵖ) =
        (-3 : ℤ) • K0.of S Sᵐᵒᵖ ∧
      K0.map ψ ((-3 : ℤ) • K0.of ℂ ℂᵐᵒᵖ) =
        (-3 : ℤ) • K0.of S Sᵐᵒᵖ ∧
      (K0.finrankEquiv ℂ).symm (-3 : ℤ) = (-3 : ℤ) • K0.of ℂ ℂᵐᵒᵖ ∧
      K0.finrankEquiv ℂ ((-3 : ℤ) • K0.of ℂ ℂᵐᵒᵖ) = -3 ∧
      (-3 : ℤ) • K0.of ℂ ℂᵐᵒᵖ ≠ 0 := by
  have coordinates := matrix_scalar_integer_coordinates (-3)
  refine ⟨coordinates.1, coordinates.2.1,
    (integer_inverse_and_dimension ℂ (-3)).1, coordinates.2.2, ?_⟩
  intro equality
  have dimensions : (-3 : ℤ) = 0 := by
    simpa only [coordinates.2.2, map_zero] using
      congrArg (K0.finrankEquiv ℂ) equality
  exact (by decide : (-3 : ℤ) ≠ 0) dimensions

end MatrixScalarMaps

section RightDuality

-- `rational_zero_ring_negative_three` already proves the signed regular
-- generator is nonzero; `rational_negative_three` computes its coordinate.
-- Carrier lifting preserves this same generator by the existing `K0.of_ulift`.
-- No injectivity assertion about the general completion map is needed.
private theorem rational_lifted_signed_regular_dual :
    K0.dualEquiv ℚ ((-3 : ℤ) • K0.of ℚ (ULift.{v + 1} ℚᵐᵒᵖ)) =
        (-3 : ℤ) • K0.of ℚᵐᵒᵖ (ℚᵐᵒᵖ)ᵐᵒᵖ ∧
      K0.dualEquiv ℚ ((-3 : ℤ) • K0.of ℚ (ULift.{v + 1} ℚᵐᵒᵖ)) ≠ 0 ∧
      (K0.dualEquiv ℚ).symm ((-3 : ℤ) • K0.of ℚᵐᵒᵖ (ℚᵐᵒᵖ)ᵐᵒᵖ) =
        (-3 : ℤ) • K0.of ℚ (ULift.{v + 1} ℚᵐᵒᵖ) := by
  have source : K0.of ℚ ℚ = K0.of ℚ ℚᵐᵒᵖ :=
    K0.of_eq_of_equiv ℚ ℚ (MulOpposite.opLinearEquiv ℚᵐᵒᵖ)
  have target : K0.of ℚᵐᵒᵖ ℚᵐᵒᵖ = K0.of ℚᵐᵒᵖ (ℚᵐᵒᵖ)ᵐᵒᵖ :=
    K0.of_eq_of_equiv ℚᵐᵒᵖ ℚᵐᵒᵖ (MulOpposite.opLinearEquiv (ℚᵐᵒᵖ)ᵐᵒᵖ)
  have regular : K0.dualEquiv ℚ (K0.of ℚ ℚᵐᵒᵖ) =
      K0.of ℚᵐᵒᵖ (ℚᵐᵒᵖ)ᵐᵒᵖ := by
    rw [← source, K0.dualEquiv_regular, target]
  have image :
      K0.dualEquiv ℚ ((-3 : ℤ) • K0.of ℚ (ULift.{v + 1} ℚᵐᵒᵖ)) =
        (-3 : ℤ) • K0.of ℚᵐᵒᵖ (ℚᵐᵒᵖ)ᵐᵒᵖ := by
    rw [map_zsmul, K0.of_ulift, regular]
  have source_ne : (-3 : ℤ) • K0.of ℚ (ULift.{v + 1} ℚᵐᵒᵖ) ≠ 0 := by
    simpa only [K0.of_ulift] using rational_zero_ring_negative_three.{0}.2.2
  refine ⟨image, ?_, ?_⟩
  · intro equality
    apply source_ne
    apply (K0.dualEquiv ℚ).injective
    simpa only [map_zero] using equality
  · rw [← image]
    exact (K0.dualEquiv ℚ).symm_apply_apply _

-- PUnit is separately a zero module over a nonzero division ring and a
-- coefficient ring with 0 = 1, as in the existing zero-module dimension and
-- zero-ring scalar-boundary examples. Duality accepts both interpretations.
private theorem punit_dual_boundaries :
    ProjectiveClass.dualEquiv ℚ (ProjectiveClass.of ℚ PUnit.{v + 1}) = 0 ∧
      K0.dualEquiv PUnit.{u + 1}
          (K0.of PUnit.{u + 1} PUnit.{u + 1}ᵐᵒᵖ) = 0 := by
  constructor
  · rw [ProjectiveClass.of_zero, map_zero]
  · exact Subsingleton.elim _ _

end RightDuality

end ProjectiveModulesTests.K0RankClient
