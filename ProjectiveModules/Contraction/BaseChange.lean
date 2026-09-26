/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import ProjectiveModules.Dual.BaseChange

/-!
# Evaluation pairings of finite projective modules and base change

This file proves that the domain of the canonical evaluation pairing commutes
with scalar extension for finite projective modules. It also identifies the
scalar-extended evaluation map with evaluation after base change.
-/

@[expose] public section

open TensorProduct

namespace IsBaseChange

open Module LinearEquiv

variable {R : Type*} [CommRing R]
  {V : Type*} [AddCommGroup V] [Module R V]
  {W : Type*} [AddCommGroup W] [Module R W]
  {A : Type*} [CommRing A] [Algebra R A] [Module A W] [IsScalarTower R A W]
  {j : V →ₗ[R] W} (ibc : IsBaseChange A j)
  [Module.Finite R V] [Projective R V]

/-- Scalar extension of `Dual R V ⊗[R] V` is canonically equivalent to
`Dual A W ⊗[A] W` when `W` is a supplied scalar extension of the finite
projective module `V`. -/
noncomputable def contractBaseChangeEquivOfProjective :
    A ⊗[R] (Dual R V ⊗[R] V) ≃ₗ[A] Dual A W ⊗[A] W :=
  (AlgebraTensorModule.assoc R R A A (Dual R V) V).symm.trans
    (AlgebraTensorModule.congr (toDualBaseChangeOfProjective ibc)
        (LinearEquiv.refl R V) |>.trans
      (ibc.tensorEquiv (Dual A W)).symm)

/-- The canonical map from the domain of evaluation to its supplied scalar
extension. -/
noncomputable def toContractBaseChangeOfProjective :
    (Dual R V ⊗[R] V) →ₗ[R] Dual A W ⊗[A] W :=
  (contractBaseChangeEquivOfProjective ibc).toLinearMap.restrictScalars R ∘ₗ
    TensorProduct.mk R A (Dual R V ⊗[R] V) 1

@[simp] theorem toContractBaseChangeOfProjective_tmul
    (f : Dual R V) (v : V) :
    toContractBaseChangeOfProjective ibc (f ⊗ₜ[R] v) =
      ibc.toDual f ⊗ₜ[A] j v := by
  simp [toContractBaseChangeOfProjective, contractBaseChangeEquivOfProjective,
    IsBaseChange.tensorEquiv]

/-- The tensor product of a finite projective module with its dual commutes
with scalar extension, using the canonical maps on both factors. -/
theorem contract_of_projective :
    IsBaseChange A (toContractBaseChangeOfProjective ibc) := by
  apply of_equiv (contractBaseChangeEquivOfProjective ibc)
  intro x
  rfl

/-- The canonical evaluation pairing is compatible with finite-projective
base change. -/
theorem contractLeft_comp_toContractBaseChangeOfProjective :
    (contractLeft A W).restrictScalars R ∘ₗ
        toContractBaseChangeOfProjective ibc =
      Algebra.linearMap R A ∘ₗ contractLeft R V := by
  ext f v
  simp [toDual_comp_apply]

end IsBaseChange
