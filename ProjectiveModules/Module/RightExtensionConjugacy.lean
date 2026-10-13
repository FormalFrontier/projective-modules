/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.RightExtension
public import Mathlib.Algebra.Group.Semiconj.Units
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.Algebra.Ring.Action.Group

/-!
# Right scalar extension under inner conjugacy

Let `φ ψ : R →+* S` be homomorphisms of arbitrary rings and let `u : Sˣ`
satisfy `SemiconjBy (u : S) (φ r) (ψ r)` for every `r`. Left multiplication
by `u` on the coefficient factor induces a fixed-right-`S`-linear equivalence
between the two extensions of any right `R`-module. Its formula is
`m ⊗_φ s ↦ m ⊗_ψ (u * s)`; the inverse uses `u⁻¹`.

The multiplication order matters: balancing uses
`ψ r * (u * s) = u * (φ r * s)`, and right linearity uses
`u * (s * t) = (u * s) * t`. Neither ring is required to be commutative,
and the unit is not required to be central. The source scalar, target scalar
and module carrier universes are independent; both extensions have carrier
universe `max uM uS`.

## Formalization references

The construction reuses the balanced-tensor and semilinear universal APIs of
`BalancedTensorProduct` and `ModuleCat.RightExtension`, contributed by Prism
and Lens. Mathlib supplies semiconjugation by units, the `ConjAct` conjugation
action, and the linear-equivalence interfaces. In particular, the canonical
inner specialization uses Mathlib's conjugation action and its ring equivalence,
not a separate inner-automorphism construction.
-/

@[expose] public section

universe uR uS uM

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (φ ψ : R →+* S) (u : Sˣ)
variable (h : ∀ r : R, SemiconjBy (u : S) (φ r) (ψ r))

section Construction

variable {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M]

private def innerGenerator : M →ₛₗ[RingHom.op φ] Obj ψ M where
  toFun m := MulOpposite.op (u : S) • tmulOne ψ m
  map_add' m n := by
    rw [(tmulOne ψ).map_add, smul_add]
  map_smul' r m := by
    rw [(tmulOne ψ).map_smulₛₗ, ← mul_smul, ← mul_smul]
    congr 1
    change MulOpposite.op (ψ (MulOpposite.unop r) * (u : S)) =
      MulOpposite.op ((u : S) * φ (MulOpposite.unop r))
    exact congrArg MulOpposite.op (h (MulOpposite.unop r)).eq.symm

private theorem innerGenerator_apply (m : M) :
    innerGenerator φ ψ u h m = tmul ψ m (u : S) := by
  change MulOpposite.op (u : S) • tmul ψ m 1 = tmul ψ m (u : S)
  rw [tmul_smul]
  simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, one_mul]

private def innerMap : Obj φ M →ₗ[Sᵐᵒᵖ] Obj ψ M :=
  fromSemilinear φ (innerGenerator φ ψ u h)

private theorem innerMap_tmul (m : M) (s : S) :
    innerMap φ ψ u h (tmul φ m s) = tmul ψ m ((u : S) * s) := by
  rw [innerMap, fromSemilinear_tmul, innerGenerator_apply, tmul_smul]
  rfl

end Construction

/-- A unit intertwining two coefficient homomorphisms induces a right-linear
comparison of their scalar extensions. It multiplies the coefficient factor
on the left by the unit, without changing the right target scalars. -/
noncomputable def innerLinearEquiv (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    Obj φ M ≃ₗ[Sᵐᵒᵖ] Obj ψ M where
  __ := private LinearEquiv.ofLinearMap
    (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids)
    (innerMap (M := M) φ ψ u h)
    (innerMap (M := M) ψ φ u⁻¹ (fun r => (h r).units_inv_symm_left))
    (by
      apply linearMap_ext (M := M) ψ
      intro m s
      rw [LinearMap.comp_apply, innerMap_tmul, innerMap_tmul, LinearMap.id_apply,
        ← mul_assoc, u.mul_inv, one_mul])
    (by
      apply linearMap_ext (M := M) φ
      intro m s
      rw [LinearMap.comp_apply, innerMap_tmul, innerMap_tmul, LinearMap.id_apply,
        ← mul_assoc, u.inv_mul, one_mul])

variable {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- The inner comparison multiplies a pure tensor's coefficient on the left. -/
@[simp]
theorem innerLinearEquiv_tmul (m : M) (s : S) :
    innerLinearEquiv φ ψ u h M (tmul φ m s) = tmul ψ m ((u : S) * s) :=
  innerMap_tmul φ ψ u h m s

/-- The inverse inner comparison multiplies the coefficient by the inverse unit. -/
@[simp]
theorem innerLinearEquiv_symm_tmul (m : M) (s : S) :
    (innerLinearEquiv φ ψ u h M).symm (tmul ψ m s) =
      tmul φ m ((↑u⁻¹ : S) * s) :=
  innerMap_tmul ψ φ u⁻¹ (fun r => (h r).units_inv_symm_left) m s

/-- Reversing the coefficient maps and inverting the unit gives the whole inverse
linear equivalence. -/
theorem innerLinearEquiv_symm :
    (innerLinearEquiv φ ψ u h M).symm =
      innerLinearEquiv ψ φ u⁻¹ (fun r => (h r).units_inv_symm_left) M := by
  apply LinearEquiv.toLinearMap_injective
  apply linearMap_ext ψ
  intro m s
  simp only [LinearEquiv.coe_coe, innerLinearEquiv_symm_tmul, innerLinearEquiv_tmul]

/-- Restriction of the inner comparison to one-generators is the semilinear map
`m ↦ m ⊗_ψ u`. -/
@[simp]
theorem toSemilinear_innerLinearEquiv (m : M) :
    toSemilinear φ (innerLinearEquiv φ ψ u h M).toLinearMap m =
      tmul ψ m (u : S) := by
  rw [toSemilinear_apply]
  simp only [LinearEquiv.coe_coe, innerLinearEquiv_tmul, mul_one]

/-- The canonical semilinear generator is sent to the tensor with coefficient `u`. -/
@[simp]
theorem innerLinearEquiv_tmulOne (m : M) :
    innerLinearEquiv φ ψ u h M (tmulOne φ m) = tmul ψ m (u : S) := by
  rw [tmulOne_apply, innerLinearEquiv_tmul, mul_one]

/-- The comparison is linear for the fixed right target action, not for a
conjugated target action. -/
theorem innerLinearEquiv_smul (t : Sᵐᵒᵖ) (x : Obj φ M) :
    innerLinearEquiv φ ψ u h M (t • x) = t • innerLinearEquiv φ ψ u h M x :=
  (innerLinearEquiv φ ψ u h M).map_smul t x

/-- Every pure-tensor image is reconstructed from its one-generator image by
right scalar multiplication. -/
theorem innerLinearEquiv_tmul_eq_smul (m : M) (s : S) :
    innerLinearEquiv φ ψ u h M (tmul φ m s) =
      MulOpposite.op s • innerLinearEquiv φ ψ u h M (tmul φ m 1) := by
  rw [innerLinearEquiv_tmul, innerLinearEquiv_tmul, mul_one, tmul_smul]
  rfl

include h in
/-- The prescribed images respect source balancing, with the coefficient order
forced by semiconjugation. -/
theorem innerLinearEquiv_balance (r : R) (m : M) (s : S) :
    tmul ψ (MulOpposite.op r • m) ((u : S) * s) =
      tmul ψ m ((u : S) * (φ r * s)) := by
  rw [smul_tmul, ← mul_assoc, ← (h r).eq, mul_assoc]

/-- The universal property characterizes the comparison among right-linear maps
by its values on one-generators. -/
theorem innerLinearEquiv_toLinearMap_eq_iff
    (F : Obj φ M →ₗ[Sᵐᵒᵖ] Obj ψ M) :
    F = (innerLinearEquiv φ ψ u h M).toLinearMap ↔
      ∀ m, F (tmul φ m 1) = tmul ψ m (u : S) := by
  constructor
  · rintro rfl m
    simp only [LinearEquiv.coe_coe, innerLinearEquiv_tmul, mul_one]
  · intro H
    apply (linearMapEquiv φ).injective
    apply LinearMap.ext
    intro m
    change toSemilinear φ F m =
      toSemilinear φ (innerLinearEquiv φ ψ u h M).toLinearMap m
    rw [toSemilinear_apply, toSemilinear_innerLinearEquiv]
    exact H m

/-- A right-linear equivalence is the inner comparison exactly when it has the
specified values on one-generators. -/
theorem innerLinearEquiv_eq_iff (e : Obj φ M ≃ₗ[Sᵐᵒᵖ] Obj ψ M) :
    e = innerLinearEquiv φ ψ u h M ↔
      ∀ m, e (tmul φ m 1) = tmul ψ m (u : S) := by
  constructor
  · rintro rfl m
    rw [innerLinearEquiv_tmul, mul_one]
  · intro H
    apply LinearEquiv.toLinearMap_injective
    exact (innerLinearEquiv_toLinearMap_eq_iff φ ψ u h e.toLinearMap).2 H

/-- Any right-linear extension of the specified one-generator prescription
agrees with the comparison on every element. -/
theorem innerLinearEquiv_apply_eq
    (F : Obj φ M →ₗ[Sᵐᵒᵖ] Obj ψ M)
    (H : ∀ m, F (tmul φ m 1) = tmul ψ m (u : S)) (x : Obj φ M) :
    innerLinearEquiv φ ψ u h M x = F x := by
  exact LinearMap.congr_fun
    ((innerLinearEquiv_toLinearMap_eq_iff φ ψ u h F).2 H).symm x

/-- The comparison for the unit `1` and its canonical identity relation is the
identity linear equivalence. -/
@[simp]
theorem innerLinearEquiv_one :
    innerLinearEquiv φ φ 1 (fun r => SemiconjBy.one_left (φ r)) M =
      LinearEquiv.refl Sᵐᵒᵖ (Obj φ M) := by
  apply LinearEquiv.toLinearMap_injective
  apply linearMap_ext φ
  intro m s
  simp

-- The canonical inner specialization uses the existing conjugation action.
example (m : M) (s : S) :
    innerLinearEquiv φ
        ((MulSemiringAction.toRingEquiv (ConjAct Sˣ) S (ConjAct.toConjAct u)).toRingHom.comp φ)
        u (fun r => by
          change SemiconjBy (u : S) (φ r) ((ConjAct.toConjAct u) • φ r)
          simpa only [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
            using Units.mk_semiconjBy u (φ r)) M (tmul φ m s) =
      tmul
        ((MulSemiringAction.toRingEquiv (ConjAct Sˣ) S (ConjAct.toConjAct u)).toRingHom.comp φ)
        m ((u : S) * s) := by
  apply innerLinearEquiv_tmul

end ModuleCat.RightExtension
