/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.RightExtensionConjugacy
public import ProjectiveModulesTests.RightExtensionConjugacyClient

/-!
# Observations of inner comparisons of right scalar extensions

The diagonal embeddings of `ℤ × ℤ` into two-by-two integer matrices give a
noncentral comparison on the principal ideal of one. Principal-ideal evaluation
detects its forward and inverse images, movement of a nonzero generator, source
balancing and the fixed right target action. The same observations persist with
three independent scalar and module-carrier lifts.

Unit-one, empty-coordinate and zero-ring comparisons use unital coefficient
maps and the module producers of `RightExtensionConjugacyClient`.

## Formalization references

These examples reuse the matrix unit, conjugation, principal-ideal evaluation
and lifted-module data of `RightExtensionConjugacyClient`. The comparison and
its characteristic laws are from `ModuleCat.RightExtension`; their balanced
tensor and semilinear approach includes the contributions of Prism and Lens.
Mathlib supplies the opposite-module, linear-equivalence and unit interfaces.
-/

@[expose] public section

noncomputable section

namespace ProjectiveModulesTests.RightExtensionConjugacyApi

open ModuleCat.RightExtension MulOpposite
open ProjectiveModulesTests.RightExtensionConjugacy

universe uR uS uM a b c

section Identity

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (f : R →+* S) (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- The unit-one comparison fixes every element of an arbitrary extension. -/
theorem unit_one_apply (x : Obj f M) :
    innerLinearEquiv f f 1 (fun r => SemiconjBy.one_left (f r)) M x = x := by
  rw [innerLinearEquiv_one]
  exact LinearEquiv.refl_apply x

end Identity

/-- Identity extension evaluates the unit-one comparison at the ideal generator. -/
theorem principal_unit_one :
    idLinearEquiv R0 P
      (innerLinearEquiv (RingHom.id R0) (RingHom.id R0) 1
        (fun r => SemiconjBy.one_left r) P (tmul (RingHom.id R0) q 1)) = q := by
  rw [unit_one_apply]
  exact principal_identity.1

/-- The comparison between the two diagonal coefficient maps. -/
abbrev κ : Obj φ0 P ≃ₗ[S0ᵐᵒᵖ] Obj ψ0 P :=
  innerLinearEquiv φ0 ψ0 u0 coefficient_semiconj P

/-- Evaluation of a forward image retains the prescribed left multiplication. -/
theorem comparison_observe (m : P) (s : S0) :
    observe ψ0 (κ (tmul φ0 m s)) = op (ψ0 (unop m.val) * (U * s)) := by
  rw [innerLinearEquiv_tmul, observe_tmul]

/-- Forward evaluation at the principal generator is the coefficient `U * s`. -/
theorem comparison_observe_q (s : S0) :
    observe ψ0 (κ (tmul φ0 q s)) = op (U * s) := by
  rw [innerLinearEquiv_tmul, observe_q]

/-- Inverse evaluation uses the same transposition, which is self-inverse. -/
theorem inverse_observe_q (s : S0) :
    observe φ0 (κ.symm (tmul ψ0 q s)) = op (U * s) := by
  rw [innerLinearEquiv_symm_tmul, u0_inv, observe_q]

/-- The forward comparison commutes with insertion by the principal-ideal observers. -/
theorem comparison_observer_inverse (s : S0) :
    κ ((observe φ0).symm (op s)) = (observe ψ0).symm (op (U * s)) := by
  rw [observe_inverse, unop_op, innerLinearEquiv_tmul, observe_inverse, unop_op]

/-- Restricting the comparison to the semilinear generator has observation `U`. -/
theorem comparison_generator_observe :
    observe ψ0 (toSemilinear φ0 κ.toLinearMap q) = op U := by
  rw [toSemilinear_innerLinearEquiv, observe_q]

/-- The canonical one-generator has the same observed forward image. -/
theorem comparison_tmulOne_observe :
    observe ψ0 (κ (tmulOne φ0 q)) = op U := by
  rw [innerLinearEquiv_tmulOne, observe_q]

/-- Both directions send a one-generator to the tensor with coefficient `U`. -/
theorem comparison_generators :
    κ (tmul φ0 q 1) = tmul ψ0 q U ∧
      κ.symm (tmul ψ0 q 1) = tmul φ0 q U := by
  constructor
  · rw [innerLinearEquiv_tmul, mul_one]
  · rw [innerLinearEquiv_symm_tmul, u0_inv, mul_one]

/-- Inverting the comparison agrees as a whole equivalence with the inverse unit. -/
theorem comparison_inverse :
    κ.symm = innerLinearEquiv ψ0 φ0 u0⁻¹
      (fun r => (coefficient_semiconj r).units_inv_symm_left) P :=
  innerLinearEquiv_symm φ0 ψ0 u0 coefficient_semiconj

/-- The inverse comparison recovers the surviving source one-generator. -/
theorem comparison_inverse_generator :
    κ.symm (tmul ψ0 q U) = tmul φ0 q 1 := by
  rw [innerLinearEquiv_symm_tmul]
  rw [u0.inv_mul]

/-- Principal-ideal evaluation detects survival, a nonzero image and target movement. -/
theorem comparison_surviving_movement :
    tmul φ0 q (1 : S0) ≠ 0 ∧ κ (tmul φ0 q (1 : S0)) ≠ 0 ∧
      κ (tmul φ0 q (1 : S0)) ≠ tmul ψ0 q (1 : S0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have he := congrArg (observe φ0) h
    rw [observe_q, _root_.map_zero] at he
    exact target_one_ne_zero (congrArg unop he)
  · intro h
    have he := congrArg (observe ψ0) h
    rw [comparison_observe_q, mul_one, _root_.map_zero] at he
    exact U_ne_zero (congrArg unop he)
  · intro h
    have he := congrArg (observe ψ0) h
    rw [comparison_observe_q, mul_one, observe_q] at he
    exact U_ne_one (congrArg unop he)

/-- Fixed right scalars act after the left unit; evaluation sees `U * (s * t)`. -/
theorem comparison_right_action (s t : S0) :
    κ (op t • tmul φ0 q s) = op t • κ (tmul φ0 q s) ∧
      observe ψ0 (κ (op t • tmul φ0 q s)) = op (U * (s * t)) := by
  constructor
  · exact innerLinearEquiv_smul φ0 ψ0 u0 coefficient_semiconj _ _
  · rw [tmul_smul, comparison_observe_q]
    rfl

/-- The noncentral scalar test observes the comparison at the matrix unit `(0,0)`. -/
theorem comparison_noncentral_scalar :
    observe ψ0 (κ (op (Matrix.single 0 0 1 : S0) • tmul φ0 q 1)) =
        op (Matrix.single 1 0 1) ∧
      observe ψ0 (κ (op (Matrix.single 0 0 1 : S0) • tmul φ0 q 1)) ≠
        observe ψ0 (tmul ψ0 q (Matrix.single 0 0 1 * U)) := by
  constructor
  · rw [ModuleCat.RightExtension.innerLinearEquiv_smul, comparison_generators.1]
    exact wrong_order_right_action_observed.2
  · rw [ModuleCat.RightExtension.tmul_smul, _root_.op_smul_eq_mul, one_mul,
      comparison_observe_q, observe_q]
    intro h
    exact permutation_order.2.2 (congrArg unop h)

/-- The inverse is linear for those same fixed right scalars. -/
theorem inverse_right_action (s t : S0) :
    κ.symm (op t • tmul ψ0 q s) = op t • κ.symm (tmul ψ0 q s) ∧
      observe φ0 (κ.symm (op t • tmul ψ0 q s)) = op (U * (s * t)) := by
  constructor
  · exact κ.symm.map_smul _ _
  · rw [tmul_smul, inverse_observe_q]
    rfl

/-- Images of general pure tensors are reconstructed from their one-generator images. -/
theorem comparison_reconstruction (m : P) (s : S0) :
    κ (tmul φ0 m s) = op s • κ (tmul φ0 m 1) :=
  innerLinearEquiv_tmul_eq_smul φ0 ψ0 u0 coefficient_semiconj m s

/-- Balancing holds for the comparison's images and has the expected observation. -/
theorem comparison_balancing (r : R0) (s : S0) :
    κ (tmul φ0 (op r • q) s) = κ (tmul φ0 q (φ0 r * s)) ∧
      observe ψ0 (κ (tmul φ0 (op r • q) s)) = op (U * (φ0 r * s)) := by
  constructor
  · rw [innerLinearEquiv_tmul, innerLinearEquiv_tmul]
    exact innerLinearEquiv_balance φ0 ψ0 u0 coefficient_semiconj r q s
  · rw [smul_tmul, comparison_observe_q]

/-- One-generator values determine every application of a right-linear comparison. -/
theorem comparison_determined (F : Obj φ0 P →ₗ[S0ᵐᵒᵖ] Obj ψ0 P)
    (H : ∀ m, F (tmul φ0 m 1) = tmul ψ0 m U) :
    F = κ.toLinearMap ∧ ∀ x, observe ψ0 (F x) = observe ψ0 (κ x) := by
  constructor
  · exact (innerLinearEquiv_toLinearMap_eq_iff φ0 ψ0 u0 coefficient_semiconj F).2 H
  · intro x
    exact congrArg (observe ψ0)
      (innerLinearEquiv_apply_eq φ0 ψ0 u0 coefficient_semiconj F H x).symm

example (e : Obj φ0 P ≃ₗ[S0ᵐᵒᵖ] Obj ψ0 P)
    (H : ∀ m, e (tmul φ0 m 1) = tmul ψ0 m U) : e = κ :=
  (innerLinearEquiv_eq_iff φ0 ψ0 u0 coefficient_semiconj e).2 H

-- These independent obstructions are imported without the inner comparison.
example : ¬ ∃ F : Obj φ0 P → Obj ψ0 P,
    ∀ m s, F (tmul φ0 m s) = tmul ψ0 m (s * U) :=
  no_wrong_order_function

example : ¬ ∃ F : Obj φ0 P →ₗ[S0ᵐᵒᵖ] Obj ψ0 P,
    F (tmul φ0 q 1) = tmul ψ0 q U ∧
    F (tmul φ0 q (Matrix.single 0 0 1)) = tmul ψ0 q (Matrix.single 0 0 1 * U) :=
  no_wrong_order_linear_map

example : φ0 ≠ ψ0 ∧ ¬ ∀ A : S0, Commute U A :=
  ⟨coefficient_maps_ne, U_not_central⟩

section ZeroBoundaries

/-- The comparison on empty coordinates has zero forward and inverse images. -/
theorem empty_comparison (x : Obj φ0 EmptyCoordinates) (y : Obj ψ0 EmptyCoordinates) :
    innerLinearEquiv φ0 ψ0 u0 coefficient_semiconj EmptyCoordinates x = 0 ∧
      (innerLinearEquiv φ0 ψ0 u0 coefficient_semiconj EmptyCoordinates).symm y = 0 :=
  ⟨empty_extension_zero ψ0 _, empty_extension_zero φ0 _⟩

example :
    innerLinearEquiv φ0 ψ0 u0 coefficient_semiconj emptyObject
      (tmul φ0 (0 : emptyObject) 1) = 0 :=
  empty_extension_zero ψ0 _

/-- The unit-one comparison into the zero target vanishes in both directions. -/
theorem zero_target_comparison (x : Obj zeroTarget P) :
    innerLinearEquiv zeroTarget zeroTarget 1
        (fun r => SemiconjBy.one_left (zeroTarget r)) P x = 0 ∧
      (innerLinearEquiv zeroTarget zeroTarget 1
        (fun r => SemiconjBy.one_left (zeroTarget r)) P).symm x = 0 := by
  simpa only [innerLinearEquiv_one, LinearEquiv.refl_symm, LinearEquiv.refl_apply] using
    (show x = 0 ∧ x = 0 from ⟨zero_target_extension P x, zero_target_extension P x⟩)

/-- Identity extension with zero source, target and module gives a zero comparison. -/
theorem all_zero_comparison (x : Obj (RingHom.id PUnit.{1}) PUnit.{1}) :
    innerLinearEquiv (RingHom.id PUnit.{1}) (RingHom.id PUnit.{1}) 1
        (fun r => SemiconjBy.one_left r) PUnit.{1} x = 0 ∧
      (innerLinearEquiv (RingHom.id PUnit.{1}) (RingHom.id PUnit.{1}) 1
        (fun r => SemiconjBy.one_left r) PUnit.{1}).symm x = 0 := by
  simpa only [innerLinearEquiv_one, LinearEquiv.refl_symm, LinearEquiv.refl_apply] using
    (show x = 0 ∧ x = 0 from
      ⟨all_zero_extension PUnit.{1} x, all_zero_extension PUnit.{1} x⟩)

example : ¬ Nonempty (PUnit.{1} →+* S0) := no_zero_source_map

end ZeroBoundaries

namespace IndependentLifts

open ProjectiveModulesTests.RightExtensionConjugacy.Lift

-- Use the same canonical pullback and carrier-lift actions as the observations.
attribute [local instance] RightExtensionConjugacy.Lift.lowModule
  RightExtensionConjugacy.Lift.carrierModule

/-- Comparison with independent source, target and module-carrier lifts.
Both extension carriers have universe `max c b`, without the source level `a`. -/
abbrev κ : SourceObj.{a,b,c} ≃ₗ[Shat.{b}ᵐᵒᵖ] TargetObj.{a,b,c} :=
  innerLinearEquiv φhat.{a,b} ψhat.{a,b} uhat.{b}
    RightExtensionConjugacy.Lift.coefficient_semiconj.{a,b} Mhat.{c}

/-- Pure-tensor comparison with three independent universes. -/
theorem comparison_tmul (m : Mhat.{c}) (s : Shat.{b}) :
    κ.{a,b,c} (tmul φhat.{a,b} m s) = tmul ψhat.{a,b} m ((uhat.{b} : Shat.{b}) * s) :=
  innerLinearEquiv_tmul (M := Mhat.{c}) φhat.{a,b} ψhat.{a,b} uhat.{b}
    RightExtensionConjugacy.Lift.coefficient_semiconj.{a,b} m s

/-- The inverse pure-tensor law retains those same three independent universes. -/
theorem inverse_tmul (m : Mhat.{c}) (s : Shat.{b}) :
    κ.{a,b,c}.symm (tmul ψhat.{a,b} m s) =
      tmul φhat.{a,b} m ((↑uhat.{b}⁻¹ : Shat.{b}) * s) :=
  innerLinearEquiv_symm_tmul (M := Mhat.{c}) φhat.{a,b} ψhat.{a,b} uhat.{b}
    RightExtensionConjugacy.Lift.coefficient_semiconj.{a,b} m s

/-- Target-down evaluation of a forward image has the low matrix formula. -/
theorem comparison_observe_down (m : Mhat.{c}) (s : Shat.{b}) :
    dS.{b} (unop (RightExtensionConjugacy.Lift.observe.{a,b,c} ψ0
      (κ.{a,b,c} (tmul φhat.{a,b} m s)))) =
        ψ0 (unop m.down) * (U * dS.{b} s) := by
  rw [comparison_tmul.{a,b,c}, RightExtensionConjugacy.Lift.observe_down.{a,b,c},
    map_mul, RightExtensionConjugacy.Lift.unit_down.{b}]

/-- Evaluation of the forward image of a lifted principal generator. -/
theorem comparison_observe_q (s : Shat.{b}) :
    RightExtensionConjugacy.Lift.observe.{a,b,c} ψ0
      (κ.{a,b,c} (tmul φhat.{a,b} qhat.{c} s)) = op ((uhat.{b} : Shat.{b}) * s) := by
  rw [comparison_tmul.{a,b,c}, RightExtensionConjugacy.Lift.observe_q.{a,b,c}]

/-- Evaluation of the inverse image uses the inverse transported unit. -/
theorem inverse_observe_q (s : Shat.{b}) :
    RightExtensionConjugacy.Lift.observe.{a,b,c} φ0
      (κ.{a,b,c}.symm (tmul ψhat.{a,b} qhat.{c} s)) =
        op ((↑uhat.{b}⁻¹ : Shat.{b}) * s) := by
  rw [inverse_tmul.{a,b,c}, RightExtensionConjugacy.Lift.observe_q.{a,b,c}]

/-- The inverse comparison recovers the lifted source generator and its observation. -/
theorem comparison_inverse_generator :
    κ.{a,b,c}.symm (tmul ψhat.{a,b} qhat.{c} (uhat.{b} : Shat.{b})) =
        tmul φhat.{a,b} qhat.{c} 1 ∧
      dS.{b} (unop (RightExtensionConjugacy.Lift.observe.{a,b,c} φ0
        (κ.{a,b,c}.symm (tmul ψhat.{a,b} qhat.{c} (uhat.{b} : Shat.{b}))))) = 1 := by
  constructor
  · rw [inverse_tmul.{a,b,c}, uhat.{b}.inv_mul]
  · rw [inverse_observe_q.{a,b,c}, uhat.{b}.inv_mul, unop_op, map_one]

/-- Independent lifts preserve the observed nonzero image and its target movement. -/
theorem comparison_surviving_movement :
    tmul φhat.{a,b} qhat.{c} (1 : Shat.{b}) ≠ 0 ∧
      κ.{a,b,c} (tmul φhat.{a,b} qhat.{c} (1 : Shat.{b})) ≠ 0 ∧
      κ.{a,b,c} (tmul φhat.{a,b} qhat.{c} (1 : Shat.{b})) ≠
        tmul ψhat.{a,b} qhat.{c} (1 : Shat.{b}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have he := congrArg (fun x : SourceObj.{a,b,c} =>
      dS.{b} (unop (RightExtensionConjugacy.Lift.observe.{a,b,c} φ0 x))) h
    rw [RightExtensionConjugacy.Lift.observe_q.{a,b,c}, _root_.map_zero,
      unop_op, unop_zero, map_one, _root_.map_zero] at he
    exact target_one_ne_zero he
  · intro h
    have he := congrArg (fun x : TargetObj.{a,b,c} =>
      dS.{b} (unop (RightExtensionConjugacy.Lift.observe.{a,b,c} ψ0 x))) h
    rw [comparison_observe_q.{a,b,c}, mul_one, _root_.map_zero, unop_op, unop_zero,
      RightExtensionConjugacy.Lift.unit_down.{b}, _root_.map_zero] at he
    exact U_ne_zero he
  · intro h
    have he := congrArg (fun x : TargetObj.{a,b,c} =>
      dS.{b} (unop (RightExtensionConjugacy.Lift.observe.{a,b,c} ψ0 x))) h
    rw [comparison_observe_q.{a,b,c}, mul_one, RightExtensionConjugacy.Lift.observe_q.{a,b,c},
      unop_op, unop_op, RightExtensionConjugacy.Lift.unit_down.{b}, map_one] at he
    exact U_ne_one he

/-- Fixed lifted right scalars have the same order after target-down evaluation. -/
theorem comparison_right_action (s t : Shat.{b}) :
    κ.{a,b,c} (op t • tmul φhat.{a,b} qhat.{c} s) =
        op t • κ.{a,b,c} (tmul φhat.{a,b} qhat.{c} s) ∧
      dS.{b} (unop (RightExtensionConjugacy.Lift.observe.{a,b,c} ψ0
        (κ.{a,b,c} (op t • tmul φhat.{a,b} qhat.{c} s)))) =
          U * (dS.{b} s * dS.{b} t) := by
  constructor
  · exact innerLinearEquiv_smul (M := Mhat.{c}) φhat.{a,b} ψhat.{a,b} uhat.{b}
      RightExtensionConjugacy.Lift.coefficient_semiconj.{a,b} (op t)
      (tmul φhat.{a,b} qhat.{c} s)
  · rw [tmul_smul (M := Mhat.{c}) φhat.{a,b}, comparison_observe_q.{a,b,c},
      unop_op, map_mul, RightExtensionConjugacy.Lift.unit_down.{b}]
    simp only [MulOpposite.smul_eq_mul_unop, unop_op, map_mul]

/-- Lifted source balancing is respected by the comparison on pure tensors. -/
theorem comparison_balancing (r : Rhat.{a}) (m : Mhat.{c}) (s : Shat.{b}) :
    κ.{a,b,c} (tmul φhat.{a,b} (op r • m) s) =
      κ.{a,b,c} (tmul φhat.{a,b} m (φhat.{a,b} r * s)) := by
  rw [comparison_tmul.{a,b,c}, comparison_tmul.{a,b,c}]
  exact innerLinearEquiv_balance (M := Mhat.{c}) φhat.{a,b} ψhat.{a,b} uhat.{b}
    RightExtensionConjugacy.Lift.coefficient_semiconj.{a,b} r m s

/-- Target-down evaluation sees the same permutation matrix on a one-generator. -/
theorem comparison_generator_down :
    dS.{b} (unop (RightExtensionConjugacy.Lift.observe.{a,b,c} ψ0
      (κ.{a,b,c} (tmul φhat.{a,b} qhat.{c} (1 : Shat.{b}))))) = U := by
  rw [comparison_observe_q.{a,b,c}, mul_one, unop_op,
    RightExtensionConjugacy.Lift.unit_down.{b}]

/-- Each isolated universe lift has survival, movement, observation and inverse recovery. -/
theorem comparison_controls :
    tmul φhat.{a,b} qhat.{c} (1 : Shat.{b}) ≠ 0 ∧
      κ.{a,b,c} (tmul φhat.{a,b} qhat.{c} (1 : Shat.{b})) ≠ 0 ∧
      κ.{a,b,c} (tmul φhat.{a,b} qhat.{c} (1 : Shat.{b})) ≠
        tmul ψhat.{a,b} qhat.{c} (1 : Shat.{b}) ∧
      dS.{b} (unop (RightExtensionConjugacy.Lift.observe.{a,b,c} ψ0
        (κ.{a,b,c} (tmul φhat.{a,b} qhat.{c} (1 : Shat.{b}))))) = U ∧
      κ.{a,b,c}.symm (tmul ψhat.{a,b} qhat.{c} (uhat.{b} : Shat.{b})) =
        tmul φhat.{a,b} qhat.{c} 1 :=
  ⟨(comparison_surviving_movement.{a,b,c}).1,
    (comparison_surviving_movement.{a,b,c}).2.1,
    (comparison_surviving_movement.{a,b,c}).2.2, comparison_generator_down.{a,b,c},
    (comparison_inverse_generator.{a,b,c}).1⟩

example :
    tmul φhat.{1,0} qhat.{0} (1 : Shat.{0}) ≠ 0 ∧
      κ.{1,0,0} (tmul φhat.{1,0} qhat.{0} (1 : Shat.{0})) ≠ 0 ∧
      κ.{1,0,0} (tmul φhat.{1,0} qhat.{0} (1 : Shat.{0})) ≠
        tmul ψhat.{1,0} qhat.{0} (1 : Shat.{0}) ∧
      dS.{0} (unop (RightExtensionConjugacy.Lift.observe.{1,0,0} ψ0
        (κ.{1,0,0} (tmul φhat.{1,0} qhat.{0} (1 : Shat.{0}))))) = U ∧
      κ.{1,0,0}.symm (tmul ψhat.{1,0} qhat.{0} (uhat.{0} : Shat.{0})) =
        tmul φhat.{1,0} qhat.{0} 1 :=
  comparison_controls.{1,0,0}

example :
    tmul φhat.{0,1} qhat.{0} (1 : Shat.{1}) ≠ 0 ∧
      κ.{0,1,0} (tmul φhat.{0,1} qhat.{0} (1 : Shat.{1})) ≠ 0 ∧
      κ.{0,1,0} (tmul φhat.{0,1} qhat.{0} (1 : Shat.{1})) ≠
        tmul ψhat.{0,1} qhat.{0} (1 : Shat.{1}) ∧
      dS.{1} (unop (RightExtensionConjugacy.Lift.observe.{0,1,0} ψ0
        (κ.{0,1,0} (tmul φhat.{0,1} qhat.{0} (1 : Shat.{1}))))) = U ∧
      κ.{0,1,0}.symm (tmul ψhat.{0,1} qhat.{0} (uhat.{1} : Shat.{1})) =
        tmul φhat.{0,1} qhat.{0} 1 :=
  comparison_controls.{0,1,0}

example :
    tmul φhat.{0,0} qhat.{1} (1 : Shat.{0}) ≠ 0 ∧
      κ.{0,0,1} (tmul φhat.{0,0} qhat.{1} (1 : Shat.{0})) ≠ 0 ∧
      κ.{0,0,1} (tmul φhat.{0,0} qhat.{1} (1 : Shat.{0})) ≠
        tmul ψhat.{0,0} qhat.{1} (1 : Shat.{0}) ∧
      dS.{0} (unop (RightExtensionConjugacy.Lift.observe.{0,0,1} ψ0
        (κ.{0,0,1} (tmul φhat.{0,0} qhat.{1} (1 : Shat.{0}))))) = U ∧
      κ.{0,0,1}.symm (tmul ψhat.{0,0} qhat.{1} (uhat.{0} : Shat.{0})) =
        tmul φhat.{0,0} qhat.{1} 1 :=
  comparison_controls.{0,0,1}

example : ¬ ∃ F : SourceObj.{a,b,c} → TargetObj.{a,b,c},
    ∀ (m : Mhat.{c}) (s : Shat.{b}),
      F (tmul (M := Mhat.{c}) φhat.{a,b} m s) =
        tmul (M := Mhat.{c}) ψhat.{a,b} m (s * (uhat.{b} : Shat.{b})) :=
  RightExtensionConjugacy.Lift.no_wrong_order_function.{a,b,c}

example : ¬ ∃ F : SourceObj.{a,b,c} →ₗ[Shat.{b}ᵐᵒᵖ] TargetObj.{a,b,c},
    F (tmul (M := Mhat.{c}) φhat.{a,b} qhat.{c} (1 : Shat.{b})) =
        tmul (M := Mhat.{c}) ψhat.{a,b} qhat.{c} (uhat.{b} : Shat.{b}) ∧
      F (tmul (M := Mhat.{c}) φhat.{a,b} qhat.{c}
        (dS.{b}.symm (Matrix.single 0 0 1 : S0))) =
          tmul (M := Mhat.{c}) ψhat.{a,b} qhat.{c}
            (dS.{b}.symm (Matrix.single 0 0 1 : S0) * (uhat.{b} : Shat.{b})) :=
  RightExtensionConjugacy.Lift.no_wrong_order_linear_map.{a,b,c}

end IndependentLifts

end ProjectiveModulesTests.RightExtensionConjugacyApi
