/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Internal direct sums

Each summand of an internal direct sum inherits finite generation or projectivity
from the ambient module, with no restriction on the index type.

A Boolean-indexed family of submodules is an internal direct sum exactly when
its canonical map from the product is bijective. The criterion uses no additive
inverses.
-/

@[expose] public section

open scoped DirectSum

universe u v w

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

variable {I : Type w} {A : I → Submodule R M}

open Classical in
/-- Each summand of an internal direct sum of a finite module is finite. -/
theorem IsInternal.moduleFinite [Module.Finite R M] (h : IsInternal A) (i : I) :
    Module.Finite R (A i) := by
  classical
  let e := LinearEquiv.ofBijective (coeLinearMap A) h
  let r := (component R I (fun i => A i) i).comp e.symm.toLinearMap
  apply Module.Finite.of_surjective r
  intro x
  exact ⟨(x : M), h.ofBijective_coeLinearMap_same x⟩

open Classical in
/-- Each summand of an internal direct sum of a projective module is projective. -/
theorem IsInternal.moduleProjective [Module.Projective R M] (h : IsInternal A) (i : I) :
    Module.Projective R (A i) := by
  classical
  let e := LinearEquiv.ofBijective (coeLinearMap A) h
  let r := (component R I (fun i => A i) i).comp e.symm.toLinearMap
  apply Module.Projective.of_split (A i).subtype r
  apply LinearMap.ext
  intro x
  exact h.ofBijective_coeLinearMap_same x

end DirectSum
