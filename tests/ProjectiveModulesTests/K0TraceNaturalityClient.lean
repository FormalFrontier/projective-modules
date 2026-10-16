/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules
import ProjectiveModules.Module.RightExtensionFree
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import GeneralLinearGroups.AdditiveCommutator
import Mathlib.Tactic.NormNum

/-!
# Scalar extension and trace for the integer regular module modulo two

The noninjective unital map `ℤ →+* ZMod 2` induces Mathlib's additive quotient
map on commutator quotients. Both unit classes are nonzero, while the nonzero
integer class of `2` maps to zero. The regular right-module K₀ generator has
trace the unit class. Its scalar extension is identified with the regular
right `ZMod 2`-module, so the two trace values can be computed independently.
-/

set_option warningAsError true

universe uR uS uT

namespace ProjectiveModulesTests.K0TraceNaturalityClient

open KTheory

private theorem commutators_le_comap {R : Type uR} {S : Type uS}
    [Ring R] [Ring S] (f : R →+* S) :
    Ring.additiveCommutators R ≤
      (Ring.additiveCommutators S).comap f.toAddMonoidHom := by
  change AddSubgroup.closure {x : R | ∃ a b : R, x = a * b - b * a} ≤ _
  apply (AddSubgroup.closure_le _).2
  rintro x ⟨a, b, rfl⟩
  change f (a * b - b * a) ∈ Ring.additiveCommutators S
  simpa only [map_sub, map_mul] using
    Ring.commutator_mem_additiveCommutators (f a) (f b)

-- The stock quotient constructor retains its characteristic identity and
-- composition API; no separate quotient-map structure is needed.
private theorem commutatorQuotient_map_id (R : Type uR) [Ring R] :
    QuotientAddGroup.map (Ring.additiveCommutators R) (Ring.additiveCommutators R)
      (RingHom.id R).toAddMonoidHom (commutators_le_comap (RingHom.id R)) =
        AddMonoidHom.id (R ⧸ Ring.additiveCommutators R) := by
  exact QuotientAddGroup.map_id (Ring.additiveCommutators R) _

private theorem commutatorQuotient_map_comp
    {R : Type uR} {S : Type uS} {T : Type uT} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) :
    (QuotientAddGroup.map (Ring.additiveCommutators S) (Ring.additiveCommutators T)
      g.toAddMonoidHom (commutators_le_comap g)).comp
      (QuotientAddGroup.map (Ring.additiveCommutators R) (Ring.additiveCommutators S)
        f.toAddMonoidHom (commutators_le_comap f)) =
      QuotientAddGroup.map (Ring.additiveCommutators R) (Ring.additiveCommutators T)
        (g.comp f).toAddMonoidHom (commutators_le_comap (g.comp f)) := by
  exact QuotientAddGroup.map_comp_map (Ring.additiveCommutators R)
    (Ring.additiveCommutators S) (Ring.additiveCommutators T)
    f.toAddMonoidHom g.toAddMonoidHom _ _ _

/-- The canonical unital map from the integers to the field with two elements. -/
def modTwo : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)

/-- Reduction modulo two is not injective. -/
theorem modTwo_not_injective : ¬ Function.Injective modTwo := by
  intro h
  have h20 : (2 : ℤ) = 0 := h (by
    simpa only [map_ofNat modTwo 2, modTwo.map_zero] using
      (show (2 : ZMod 2) = 0 by decide))
  norm_num at h20

/-- The additive map induced by reduction modulo two on commutator quotients. -/
def modTwoHH0 :
    (ℤ ⧸ Ring.additiveCommutators ℤ) →+
      (ZMod 2 ⧸ Ring.additiveCommutators (ZMod 2)) :=
  QuotientAddGroup.map (Ring.additiveCommutators ℤ)
    (Ring.additiveCommutators (ZMod 2)) modTwo.toAddMonoidHom
    (commutators_le_comap modTwo)

/-- The induced additive map sends an integer class to its reduced class. -/
theorem modTwoHH0_mk (n : ℤ) :
    modTwoHH0 (QuotientAddGroup.mk' (Ring.additiveCommutators ℤ) n) =
      QuotientAddGroup.mk' (Ring.additiveCommutators (ZMod 2)) (modTwo n) := by
  exact QuotientAddGroup.map_mk' (Ring.additiveCommutators ℤ)
    (Ring.additiveCommutators (ZMod 2)) modTwo.toAddMonoidHom _ n

private theorem commutators_eq_bot (A : Type uR) [CommRing A] :
    Ring.additiveCommutators A = ⊥ := by
  apply le_antisymm ?_ bot_le
  change AddSubgroup.closure {x : A | ∃ a b : A, x = a * b - b * a} ≤ ⊥
  apply (AddSubgroup.closure_le _).2
  rintro x ⟨a, b, rfl⟩
  change a * b - b * a = 0
  rw [mul_comm a b, sub_self]

private theorem quotient_mk_ne_zero (A : Type uR) [CommRing A] (a : A) (ha : a ≠ 0) :
    QuotientAddGroup.mk' (Ring.additiveCommutators A) a ≠ 0 := by
  intro h
  apply ha
  have ha' := (QuotientAddGroup.eq_zero_iff a).mp h
  simpa only [commutators_eq_bot A, AddSubgroup.mem_bot] using ha'

/-- The unit class in the integer additive commutator quotient is nonzero. -/
theorem integer_unit_class_ne_zero :
    QuotientAddGroup.mk' (Ring.additiveCommutators ℤ) 1 ≠ 0 :=
  quotient_mk_ne_zero ℤ 1 one_ne_zero

/-- The unit class in the target additive commutator quotient is nonzero. -/
public theorem modTwo_unit_class_ne_zero :
    QuotientAddGroup.mk' (Ring.additiveCommutators (ZMod 2)) 1 ≠ 0 :=
  quotient_mk_ne_zero (ZMod 2) 1 one_ne_zero

/-- The class of the integer `2` is nonzero before reduction. -/
theorem integer_two_class_ne_zero :
    QuotientAddGroup.mk' (Ring.additiveCommutators ℤ) 2 ≠ 0 :=
  quotient_mk_ne_zero ℤ 2 (by norm_num)

/-- The nonzero source class of `2` is killed by the induced map. -/
theorem modTwoHH0_two :
    modTwoHH0 (QuotientAddGroup.mk' (Ring.additiveCommutators ℤ) 2) = 0 := by
  rw [modTwoHH0_mk]
  have h2 : modTwo (2 : ℤ) = 0 := by
    simpa only [map_ofNat modTwo 2] using (show (2 : ZMod 2) = 0 by decide)
  rw [h2, map_zero]

/-- The regular right-module generator of the integer K₀ group. -/
noncomputable def regularGenerator : K0 ℤ := K0.of ℤ ℤ

/-- Scalar extension of the regular integer module is the regular target module. -/
noncomputable def modTwoRegularEquiv :
    ModuleCat.RightExtension.Obj modTwo ℤ ≃ₗ[(ZMod 2)ᵐᵒᵖ] ZMod 2 :=
  (ModuleCat.RightExtension.mapLinearEquiv modTwo
    (LinearEquiv.funUnique (Fin 1) ℤᵐᵒᵖ ℤ).symm).trans
    ((ModuleCat.RightExtension.rightFreeLinearEquiv modTwo (Fin 1)).trans
      (LinearEquiv.funUnique (Fin 1) (ZMod 2)ᵐᵒᵖ (ZMod 2)))

/-- The scalar-extension equivalence evaluates a pure tensor by multiplication. -/
theorem modTwoRegularEquiv_tmul (n : ℤ) (s : ZMod 2) :
    modTwoRegularEquiv (ModuleCat.RightExtension.tmul modTwo n s) = modTwo n * s := by
  change (ModuleCat.RightExtension.rightFreeLinearEquiv modTwo (Fin 1)
    (ModuleCat.RightExtension.mapLinearEquiv modTwo
      (LinearEquiv.funUnique (Fin 1) ℤᵐᵒᵖ ℤ).symm
      (ModuleCat.RightExtension.tmul modTwo n s))) default = modTwo n * s
  rw [ModuleCat.RightExtension.mapLinearEquiv_tmul,
    ModuleCat.RightExtension.rightFreeLinearEquiv_tmul]
  rfl

/-- The K₀ map uses the scalar-extended module as its module-class representative. -/
theorem map_regularGenerator_extension :
    K0.map modTwo regularGenerator =
      K0.of (ZMod 2) (ModuleCat.RightExtension.Obj modTwo ℤ) :=
  K0.map_of modTwo ℤ

/-- The regular generator maps to the regular target generator. -/
theorem map_regularGenerator :
    K0.map modTwo regularGenerator = K0.of (ZMod 2) (ZMod 2) := by
  rw [map_regularGenerator_extension]
  exact K0.of_eq_of_equiv (ZMod 2) (ModuleCat.RightExtension.Obj modTwo ℤ)
    modTwoRegularEquiv

private theorem regular_trace (R : Type uR) [Ring R] :
    K0.traceModCommutators R (K0.of R R) =
      QuotientAddGroup.mk' (Ring.additiveCommutators R) 1 :=
  (K0.traceModCommutators_ofClass R (ProjectiveClass.of R R)).trans
    (ProjectiveClass.traceModCommutators_of_self R)

/-- The source regular generator has trace the integer unit class. -/
theorem trace_regularGenerator :
    K0.traceModCommutators ℤ regularGenerator =
      QuotientAddGroup.mk' (Ring.additiveCommutators ℤ) 1 :=
  regular_trace ℤ

/-- The scalar-extended regular generator has trace the target unit class. -/
theorem trace_map_regularGenerator :
    K0.traceModCommutators (ZMod 2) (K0.map modTwo regularGenerator) =
      QuotientAddGroup.mk' (Ring.additiveCommutators (ZMod 2)) 1 := by
  rw [map_regularGenerator, regular_trace]

/-- Naturality of the trace for reduction modulo two on the regular generator. -/
theorem regular_trace_square :
    K0.traceModCommutators (ZMod 2) (K0.map modTwo regularGenerator) =
      modTwoHH0 (K0.traceModCommutators ℤ regularGenerator) := by
  exact K0.traceModCommutators_map modTwo regularGenerator

/-- The regular generator is nonzero, as detected by its source trace. -/
theorem regularGenerator_ne_zero : regularGenerator ≠ 0 := by
  intro h
  apply integer_unit_class_ne_zero
  rw [← trace_regularGenerator, h, map_zero]

/-- The scalar-extended regular generator is nonzero, as detected by its target trace. -/
theorem map_regularGenerator_ne_zero : K0.map modTwo regularGenerator ≠ 0 := by
  intro h
  apply modTwo_unit_class_ne_zero
  rw [← trace_map_regularGenerator, h, map_zero]

end ProjectiveModulesTests.K0TraceNaturalityClient
