/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Rank
import ProjectiveModules.KTheory.ScalarExtension
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

end ProjectiveModulesTests.K0RankClient
