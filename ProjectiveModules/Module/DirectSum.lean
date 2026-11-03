/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod

/-!
# Binary internal direct sums

A Boolean-indexed family of submodules is an internal direct sum exactly when
its canonical map from the product is bijective. The criterion uses no additive
inverses.
-/

@[expose] public section

open scoped DirectSum

universe u v

namespace DirectSum

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- A binary family is internal if and only if the canonical coproduct map is
bijective. The `true` summand is the first factor of the product. -/
theorem isInternal_bool_iff_bijective_coprod (P Q : Submodule R M) :
    IsInternal (fun b : Bool => cond b P Q) ↔
      Function.Bijective (LinearMap.coprod P.subtype Q.subtype) := by
  let A : Bool → Type v := fun b => ↥(cond b P Q)
  let e : (⨁ b : Bool, A b) ≃ₗ[R] P × Q :=
    (((linearEquivFunOnFintype R Bool A).trans
      (LinearEquiv.piCongrLeft' R A finTwoEquiv.symm)).trans
      (LinearEquiv.piFinTwo R (fun i => A (finTwoEquiv i)))).trans
      (LinearEquiv.prodComm R Q P)
  have e_apply (z : ⨁ b : Bool, A b) :
      e z = ((linearEquivFunOnFintype R Bool A) z true,
        (linearEquivFunOnFintype R Bool A) z false) := by
    rfl
  have he : (LinearMap.coprod P.subtype Q.subtype).comp e.toLinearMap =
      coeLinearMap (fun b : Bool => cond b P Q) := by
    apply DirectSum.linearMap_ext
    intro b
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [e_apply, linearEquivFunOnFintype_lof]
    cases b <;> simp [A]
  change Function.Bijective (coeLinearMap (fun b : Bool => cond b P Q)) ↔ _
  rw [← he]
  exact e.toEquiv.bijective_comp (LinearMap.coprod P.subtype Q.subtype)

end DirectSum
