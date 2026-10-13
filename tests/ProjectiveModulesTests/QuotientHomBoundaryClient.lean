/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.QuotientHom
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Boundary cases for quotient linear forms

The bottom quotient of a product of integer matrix rings retains nonzero raw
and opposite-valued forms. Top quotients, empty-index products, the one-element
module and the zero ring supply the zero-source boundaries. A one-element
coefficient module also gives zero forms on a nonzero quotient.

The right integer module modulo the span of `2` is identified with `ZMod 2`
using Mathlib's scalar-restriction and equal-submodule quotient transports.
Its nonzero class of `1` is killed by every integer-valued form. The coordinate
form on the span of `2`, sending `2` to `1`, does not extend to the ambient
right integer module. In particular restriction of forms need not be
surjective, and quotient duality does not assert detection of nonzero points.

## References

The constructions use Mathlib's quotient universal property, same-scalar
opposite equivalence, integer quotient equivalence and singleton coordinate
map. Raw coefficients and ordinary opposite-valued duals are kept distinct.
-/

@[expose] public section

universe uI

namespace ProjectiveModulesTests.QuotientHomBoundaryClient

open MulOpposite

local notation "A" => Matrix (Fin 2) (Fin 2) ℤ
local notation "M" => A × A

/-- The bottom quotient has a raw form taking the values `1` and `E₀₁`,
and the form and its selected quotient point are nonzero. -/
theorem bottom_raw_values :
    let B : Submodule Aᵐᵒᵖ M := ⊥
    let f : M →ₗ[Aᵐᵒᵖ] A := LinearMap.snd Aᵐᵒᵖ A A
    let φ := B.liftQ f bot_le
    let q : A := Matrix.single 0 1 1
    φ (B.mkQ (0, 1)) = 1 ∧ φ (B.mkQ (0, q)) = q ∧
      φ ≠ 0 ∧ B.mkQ (0, 1) ≠ 0 := by
  dsimp only
  refine ⟨by simp, by simp, ?_, ?_⟩
  · intro h
    have hval := LinearMap.congr_fun h
      ((⊥ : Submodule Aᵐᵒᵖ M).mkQ (0, 1))
    have hentry := congrArg (fun a : A => a 0 0) hval
    simp at hentry
  · intro h
    have hval := congrArg
      ((⊥ : Submodule Aᵐᵒᵖ M).liftQ (LinearMap.snd Aᵐᵒᵖ A A) bot_le) h
    have hentry := congrArg (fun a : A => a 0 0) hval
    simp at hentry

/-- Both selected bottom classes are preserved by the quotient-to-module
equivalence, and the class of `E₀₁` is nonzero. -/
theorem bottom_quotient_values :
    let B : Submodule Aᵐᵒᵖ M := ⊥
    let q : A := Matrix.single 0 1 1
    B.quotEquivOfEqBot rfl (B.mkQ (0, 1)) = (0, 1) ∧
      B.quotEquivOfEqBot rfl (B.mkQ (0, q)) = (0, q) ∧
      (B.quotEquivOfEqBot rfl).symm (0, q) = B.mkQ (0, q) ∧
      q ≠ 0 ∧ B.mkQ (0, q) ≠ 0 := by
  dsimp only
  refine ⟨by simp, by simp, rfl, ?_, ?_⟩
  · intro h
    have hentry := congrArg (fun a : A => a 0 1) h
    simp at hentry
  · intro h
    have hval := congrArg
      ((⊥ : Submodule Aᵐᵒᵖ M).quotEquivOfEqBot rfl) h
    have hentry := congrArg (fun x : M => x.2 0 1) hval
    simp at hentry

/-- The ordinary dual of the bottom quotient has the distinct codomain
`Aᵐᵒᵖ` and takes the op-coded values `1` and `E₀₁`. -/
theorem bottom_dual_values :
    let B : Submodule Aᵐᵒᵖ M := ⊥
    let c : A ≃ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ := opLinearEquiv Aᵐᵒᵖ
    let d : Module.Dual Aᵐᵒᵖ M := c.toLinearMap.comp (LinearMap.snd Aᵐᵒᵖ A A)
    let δ := B.liftQ d bot_le
    let q : A := Matrix.single 0 1 1
    δ (B.mkQ (0, 1)) = op (1 : A) ∧ δ (B.mkQ (0, q)) = op q ∧ δ ≠ 0 := by
  dsimp only
  refine ⟨by simp, by simp, ?_⟩
  intro h
  have hval := LinearMap.congr_fun h ((⊥ : Submodule Aᵐᵒᵖ M).mkQ (0, 1))
  have hentry := congrArg (fun a : Aᵐᵒᵖ => (unop a) 0 0) hval
  simp at hentry

/-- The bottom quotient equivalence is the Mathlib quotient-to-module map;
its inverse is `mkQ`, and both form pullbacks are the original forms. -/
theorem bottom_quotient_roundtrips :
    let B : Submodule Aᵐᵒᵖ M := ⊥
    let f : M →ₗ[Aᵐᵒᵖ] A := LinearMap.snd Aᵐᵒᵖ A A
    let c : A ≃ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ := opLinearEquiv Aᵐᵒᵖ
    let d : Module.Dual Aᵐᵒᵖ M := c.toLinearMap.comp f
    (B.liftQ f bot_le).comp B.mkQ = f ∧
      (B.liftQ d bot_le).comp B.mkQ = d ∧
      (B.quotEquivOfEqBot rfl).toLinearMap.comp B.mkQ = LinearMap.id ∧
      B.mkQ.comp (B.quotEquivOfEqBot rfl).toLinearMap = LinearMap.id ∧
      ((B.quotEquivOfEqBot rfl).symm : M →ₗ[Aᵐᵒᵖ] M ⧸ B) = B.mkQ ∧
      f.comp B.subtype = 0 ∧ d.comp B.subtype = 0 := by
  dsimp only
  refine ⟨Submodule.liftQ_mkQ _ _ _, Submodule.liftQ_mkQ _ _ _, ?_, ?_, rfl, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    exact Submodule.quotEquivOfEqBot_apply_mk (⊥ : Submodule Aᵐᵒᵖ M) rfl x
  · apply Submodule.quot_hom_ext
    intro x
    simp
  · apply LinearMap.ext
    intro x
    have hx : (x : M) = 0 := (Submodule.mem_bot Aᵐᵒᵖ).mp x.property
    simp [hx]
  · apply LinearMap.ext
    intro x
    have hx : (x : M) = 0 := (Submodule.mem_bot Aᵐᵒᵖ).mp x.property
    simp [hx]

/-- Bottom descent and pullback satisfy the quotient universal property for
both raw and ordinary dual forms, including uniqueness. -/
theorem bottom_factorization :
    let B : Submodule Aᵐᵒᵖ M := ⊥
    (∀ ψ : (M ⧸ B) →ₗ[Aᵐᵒᵖ] A,
      B.liftQ (ψ.comp B.mkQ) bot_le = ψ) ∧
    (∀ δ : Module.Dual Aᵐᵒᵖ (M ⧸ B),
      B.liftQ (δ.comp B.mkQ) bot_le = δ) ∧
    (∀ ψ χ : (M ⧸ B) →ₗ[Aᵐᵒᵖ] A,
      ψ.comp B.mkQ = χ.comp B.mkQ → ψ = χ) ∧
    (∀ δ ε : Module.Dual Aᵐᵒᵖ (M ⧸ B),
      δ.comp B.mkQ = ε.comp B.mkQ → δ = ε) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ψ
    apply Submodule.linearMap_qext
    exact Submodule.liftQ_mkQ _ _ _
  · intro δ
    apply Submodule.linearMap_qext
    exact Submodule.liftQ_mkQ _ _ _
  · intro ψ χ h
    exact Submodule.linearMap_qext _ h
  · intro δ ε h
    exact Submodule.linearMap_qext _ h

/-- The selected nonzero raw and ordinary forms have unique factors
through the bottom quotient, constructed by quotient descent. -/
theorem bottom_unique_factors :
    let B : Submodule Aᵐᵒᵖ M := ⊥
    let f : M →ₗ[Aᵐᵒᵖ] A := LinearMap.snd Aᵐᵒᵖ A A
    let c : A ≃ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ := opLinearEquiv Aᵐᵒᵖ
    let d : Module.Dual Aᵐᵒᵖ M := c.toLinearMap.comp f
    (∃! ψ : (M ⧸ B) →ₗ[Aᵐᵒᵖ] A, ψ.comp B.mkQ = f) ∧
      (∃! δ : Module.Dual Aᵐᵒᵖ (M ⧸ B), δ.comp B.mkQ = d) := by
  dsimp only
  constructor
  · refine ⟨_, Submodule.liftQ_mkQ _ _ bot_le, ?_⟩
    intro ψ hψ
    apply Submodule.linearMap_qext
    rw [hψ, Submodule.liftQ_mkQ]
  · refine ⟨_, Submodule.liftQ_mkQ _ _ bot_le, ?_⟩
    intro δ hδ
    apply Submodule.linearMap_qext
    rw [hδ, Submodule.liftQ_mkQ]

/-- On the nonzero bottom forms, the quotient-Hom equivalence has exactly
the quotient pullback and descent values in the two coefficient types. -/
theorem bottom_equiv_consistency :
    let B : Submodule Aᵐᵒᵖ M := ⊥
    let f : M →ₗ[Aᵐᵒᵖ] A := LinearMap.snd Aᵐᵒᵖ A A
    let c : A ≃ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ := opLinearEquiv Aᵐᵒᵖ
    let d : Module.Dual Aᵐᵒᵖ M := c.toLinearMap.comp f
    let φ := B.liftQ f bot_le
    let δ := B.liftQ d bot_le
    let er := B.quotientHomEquivKer (S := A) (C := A)
    let ed := B.quotientHomEquivKer (S := A) (C := Aᵐᵒᵖ)
    (er φ).val = f ∧ (ed δ).val = d ∧
      er.symm (er φ) = φ ∧ ed.symm (ed δ) = δ ∧
      er.symm (er φ) (B.mkQ (0, 1)) = 1 ∧
      ed.symm (ed δ) (B.mkQ (0, 1)) = op (1 : A) := by
  dsimp only
  refine ⟨?_, ?_, LinearEquiv.symm_apply_apply _ _,
    LinearEquiv.symm_apply_apply _ _, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    rw [Submodule.quotientHomEquivKer_apply]
    simp
  · apply LinearMap.ext
    intro x
    rw [Submodule.quotientHomEquivKer_apply]
    simp
  · rw [Submodule.quotientHomEquivKer_symm_apply_mkQ,
      Submodule.quotientHomEquivKer_apply]
    simp
  · rw [Submodule.quotientHomEquivKer_symm_apply_mkQ,
      Submodule.quotientHomEquivKer_apply]
    simp

/-- Only the zero raw form and the zero ordinary dual vanish on the
whole nonzero product module. -/
theorem top_vanishing_iff :
    (∀ F : M →ₗ[Aᵐᵒᵖ] A,
      (⊤ : Submodule Aᵐᵒᵖ M) ≤ LinearMap.ker F ↔ F = 0) ∧
    (∀ D : Module.Dual Aᵐᵒᵖ M,
      (⊤ : Submodule Aᵐᵒᵖ M) ≤ LinearMap.ker D ↔ D = 0) := by
  constructor
  · intro F
    constructor
    · intro h
      apply LinearMap.ext
      intro x
      exact LinearMap.mem_ker.mp (h Submodule.mem_top)
    · rintro rfl
      simp
  · intro D
    constructor
    · intro h
      apply LinearMap.ext
      intro x
      exact LinearMap.mem_ker.mp (h Submodule.mem_top)
    · rintro rfl
      simp

/-- Every raw and ordinary quotient form at the top submodule is zero. -/
theorem top_forms_zero :
    (∀ ψ : (M ⧸ (⊤ : Submodule Aᵐᵒᵖ M)) →ₗ[Aᵐᵒᵖ] A, ψ = 0) ∧
    (∀ δ : Module.Dual Aᵐᵒᵖ (M ⧸ (⊤ : Submodule Aᵐᵒᵖ M)), δ = 0) := by
  constructor <;> intro ψ <;> exact Subsingleton.elim _ _

/-- Top descent is zero, its quotient pullback is zero, and the quotient-Hom
correspondences preserve zero in both directions. -/
theorem top_roundtrips :
    let T : Submodule Aᵐᵒᵖ M := ⊤
    let zr : M →ₗ[Aᵐᵒᵖ] A := 0
    let zd : Module.Dual Aᵐᵒᵖ M := 0
    let hr : T ≤ LinearMap.ker zr := by simp [zr]
    let hd : T ≤ LinearMap.ker zd := by simp [zd]
    T.liftQ zr hr = 0 ∧ T.liftQ zd hd = 0 ∧
      (T.liftQ zr hr).comp T.mkQ = zr ∧
      (T.liftQ zd hd).comp T.mkQ = zd ∧
      zr.comp T.subtype = 0 ∧ zd.comp T.subtype = 0 ∧
      T.quotientHomEquivKer (S := A) (C := A) 0 = 0 ∧
      (T.quotientHomEquivKer (S := A) (C := A)).symm 0 = 0 ∧
      T.quotientHomEquivKer (S := A) (C := Aᵐᵒᵖ) 0 = 0 ∧
      (T.quotientHomEquivKer (S := A) (C := Aᵐᵒᵖ)).symm 0 = 0 := by
  dsimp only
  refine ⟨Subsingleton.elim _ _, Subsingleton.elim _ _,
    Submodule.liftQ_mkQ _ _ _, Submodule.liftQ_mkQ _ _ _,
    by simp, by simp, map_zero _, map_zero _, map_zero _, map_zero _⟩

/-- Top quotient descent and uniqueness use the quotient universal
property for all raw and ordinary forms, which are necessarily zero. -/
theorem top_factorization :
    let T : Submodule Aᵐᵒᵖ M := ⊤
    (∀ ψ : (M ⧸ T) →ₗ[Aᵐᵒᵖ] A,
      T.liftQ (ψ.comp T.mkQ)
        (by simpa using LinearMap.ker_le_ker_comp T.mkQ ψ) = ψ) ∧
    (∀ δ : Module.Dual Aᵐᵒᵖ (M ⧸ T),
      T.liftQ (δ.comp T.mkQ)
        (by simpa using LinearMap.ker_le_ker_comp T.mkQ δ) = δ) ∧
    (∀ ψ χ : (M ⧸ T) →ₗ[Aᵐᵒᵖ] A,
      ψ.comp T.mkQ = χ.comp T.mkQ → ψ = χ) ∧
    (∀ δ ε : Module.Dual Aᵐᵒᵖ (M ⧸ T),
      δ.comp T.mkQ = ε.comp T.mkQ → δ = ε) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ψ
    apply Submodule.linearMap_qext
    exact Submodule.liftQ_mkQ _ _ _
  · intro δ
    apply Submodule.linearMap_qext
    exact Submodule.liftQ_mkQ _ _ _
  · intro ψ χ h
    exact Submodule.linearMap_qext _ h
  · intro δ ε h
    exact Submodule.linearMap_qext _ h

/-- An empty-index Pi module has an additive zero; bottom and top
coincide, and every quotient form is zero. -/
theorem empty_index_forms_zero (N : Submodule Aᵐᵒᵖ ((ULift.{uI} Empty) → A)) :
    (⊥ : Submodule Aᵐᵒᵖ ((ULift.{uI} Empty) → A)) = ⊤ ∧
      (∀ ψ : (((ULift.{uI} Empty) → A) ⧸ N) →ₗ[Aᵐᵒᵖ] A, ψ = 0) ∧
      (∀ δ : Module.Dual Aᵐᵒᵖ (((ULift.{uI} Empty) → A) ⧸ N), δ = 0) := by
  refine ⟨?_, fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  ext x
  rw [Subsingleton.elim x 0]
  simp

/-- The empty-index source has zero descent, zero restriction and both
quotient and Hom-space roundtrips, without a module structure on `Empty` itself. -/
theorem empty_index_roundtrips (N : Submodule Aᵐᵒᵖ ((ULift.{uI} Empty) → A)) :
    let zr : ((ULift.{uI} Empty) → A) →ₗ[Aᵐᵒᵖ] A := 0
    let zd : Module.Dual Aᵐᵒᵖ ((ULift.{uI} Empty) → A) := 0
    let hr : N ≤ LinearMap.ker zr := by simp
    let hd : N ≤ LinearMap.ker zd := by simp
    (N.liftQ zr hr).comp N.mkQ = zr ∧
      (N.liftQ zd hd).comp N.mkQ = zd ∧
      zr.comp N.subtype = 0 ∧ zd.comp N.subtype = 0 ∧
      (∀ ψ : (((ULift.{uI} Empty) → A) ⧸ N) →ₗ[Aᵐᵒᵖ] A,
        N.liftQ (ψ.comp N.mkQ)
          (by simp) = ψ) ∧
      (∀ δ : Module.Dual Aᵐᵒᵖ (((ULift.{uI} Empty) → A) ⧸ N),
        N.liftQ (δ.comp N.mkQ)
          (by simp) = δ) ∧
      N.quotientHomEquivKer (S := A) (C := A) 0 = 0 ∧
      (N.quotientHomEquivKer (S := A) (C := A)).symm 0 = 0 ∧
      N.quotientHomEquivKer (S := A) (C := Aᵐᵒᵖ) 0 = 0 ∧
      (N.quotientHomEquivKer (S := A) (C := Aᵐᵒᵖ)).symm 0 = 0 := by
  dsimp only
  refine ⟨Submodule.liftQ_mkQ _ _ _, Submodule.liftQ_mkQ _ _ _,
    by simp, by simp, ?_, ?_, map_zero _, map_zero _, map_zero _, map_zero _⟩
  · intro ψ
    apply Submodule.linearMap_qext
    exact Submodule.liftQ_mkQ _ _ _
  · intro δ
    apply Submodule.linearMap_qext
    exact Submodule.liftQ_mkQ _ _ _

/-- The one-element module over the nonzero matrix ring is allowed;
its submodules have coincident endpoints and zero quotient forms. -/
theorem zero_module_forms_zero (N : Submodule Aᵐᵒᵖ PUnit.{1}) :
    (⊥ : Submodule Aᵐᵒᵖ PUnit.{1}) = ⊤ ∧
      (∀ ψ : (PUnit.{1} ⧸ N) →ₗ[Aᵐᵒᵖ] A, ψ = 0) ∧
      (∀ δ : Module.Dual Aᵐᵒᵖ (PUnit.{1} ⧸ N), δ = 0) := by
  refine ⟨?_, fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  ext x
  rw [Subsingleton.elim x 0]
  simp

/-- Zero-module forms satisfy the quotient factorization and restriction
contracts, and the two quotient-Hom equivalences preserve zero. -/
theorem zero_module_roundtrips (N : Submodule Aᵐᵒᵖ PUnit.{1}) :
    let zr : PUnit.{1} →ₗ[Aᵐᵒᵖ] A := 0
    let zd : Module.Dual Aᵐᵒᵖ PUnit.{1} := 0
    let hr : N ≤ LinearMap.ker zr := by simp
    let hd : N ≤ LinearMap.ker zd := by simp
    (N.liftQ zr hr).comp N.mkQ = zr ∧
      (N.liftQ zd hd).comp N.mkQ = zd ∧
      zr.comp N.subtype = 0 ∧ zd.comp N.subtype = 0 ∧
      (∀ ψ : (PUnit.{1} ⧸ N) →ₗ[Aᵐᵒᵖ] A,
        N.liftQ (ψ.comp N.mkQ)
          (by simp) = ψ) ∧
      (∀ δ : Module.Dual Aᵐᵒᵖ (PUnit.{1} ⧸ N),
        N.liftQ (δ.comp N.mkQ)
          (by simp) = δ) ∧
      N.quotientHomEquivKer (S := A) (C := A) 0 = 0 ∧
      (N.quotientHomEquivKer (S := A) (C := A)).symm 0 = 0 ∧
      N.quotientHomEquivKer (S := A) (C := Aᵐᵒᵖ) 0 = 0 ∧
      (N.quotientHomEquivKer (S := A) (C := Aᵐᵒᵖ)).symm 0 = 0 := by
  dsimp only
  refine ⟨Submodule.liftQ_mkQ _ _ _, Submodule.liftQ_mkQ _ _ _,
    by simp, by simp, ?_, ?_, map_zero _, map_zero _, map_zero _, map_zero _⟩
  · intro ψ
    apply Submodule.linearMap_qext
    exact Submodule.liftQ_mkQ _ _ _
  · intro δ
    apply Submodule.linearMap_qext
    exact Submodule.liftQ_mkQ _ _ _

/-- The zero ring and its one-element module satisfy the quotient-Hom
correspondence with no nontriviality assumption on the ring. -/
theorem zero_ring_forms_zero (N : Submodule PUnit.{1}ᵐᵒᵖ PUnit.{1}) :
    (1 : PUnit.{1}) = 0 ∧ (⊥ : Submodule PUnit.{1}ᵐᵒᵖ PUnit.{1}) = ⊤ ∧
      (∀ ψ : (PUnit.{1} ⧸ N) →ₗ[PUnit.{1}ᵐᵒᵖ] PUnit.{1}, ψ = 0) ∧
      (∀ δ : Module.Dual PUnit.{1}ᵐᵒᵖ (PUnit.{1} ⧸ N), δ = 0) ∧
      N.quotientHomEquivKer (S := PUnit.{1}) (C := PUnit.{1}) 0 = 0 ∧
      (N.quotientHomEquivKer (S := PUnit.{1}) (C := PUnit.{1})).symm 0 = 0 ∧
      N.quotientHomEquivKer (S := PUnit.{1}) (C := PUnit.{1}ᵐᵒᵖ) 0 = 0 ∧
      (N.quotientHomEquivKer (S := PUnit.{1}) (C := PUnit.{1}ᵐᵒᵖ)).symm 0 = 0 := by
  refine ⟨rfl, ?_, fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _,
    map_zero _, map_zero _, map_zero _, map_zero _⟩
  ext x
  rw [Subsingleton.elim x 0]
  simp

/-- The raw and ordinary coefficients of the zero ring remain distinct
but are connected by the same-scalar codec and quotient descent. -/
theorem zero_ring_quotient_roundtrips (N : Submodule PUnit.{1}ᵐᵒᵖ PUnit.{1}) :
    let c : PUnit.{1} ≃ₗ[PUnit.{1}ᵐᵒᵖ] PUnit.{1}ᵐᵒᵖ :=
      opLinearEquiv PUnit.{1}ᵐᵒᵖ
    let zr : PUnit.{1} →ₗ[PUnit.{1}ᵐᵒᵖ] PUnit.{1} := 0
    let zd : Module.Dual PUnit.{1}ᵐᵒᵖ PUnit.{1} := c.toLinearMap.comp zr
    let hr : N ≤ LinearMap.ker zr := by simp
    let hd : N ≤ LinearMap.ker zd := by simp
    (N.liftQ zr hr).comp N.mkQ = zr ∧
      (N.liftQ zd hd).comp N.mkQ = zd ∧
      zr.comp N.subtype = 0 ∧ zd.comp N.subtype = 0 ∧
      (∀ ψ : (PUnit.{1} ⧸ N) →ₗ[PUnit.{1}ᵐᵒᵖ] PUnit.{1},
        N.liftQ (ψ.comp N.mkQ)
          (by simp) = ψ) ∧
      (∀ δ : Module.Dual PUnit.{1}ᵐᵒᵖ (PUnit.{1} ⧸ N),
        N.liftQ (δ.comp N.mkQ)
          (by simp) = δ) := by
  dsimp only
  refine ⟨Submodule.liftQ_mkQ _ _ _, Submodule.liftQ_mkQ _ _ _,
    by simp, by simp, ?_, ?_⟩
  · intro ψ
    apply Submodule.linearMap_qext
    exact Submodule.liftQ_mkQ _ _ _
  · intro δ
    apply Submodule.linearMap_qext
    exact Submodule.liftQ_mkQ _ _ _

/-- A nonzero first-axis quotient can have only zero forms when the
coefficient module, rather than the source module, is one-element. -/
theorem zero_coefficient_nonzero_quotient :
    let f : M →ₗ[Aᵐᵒᵖ] A := LinearMap.snd Aᵐᵒᵖ A A
    let N := LinearMap.ker f
    N.mkQ (0, 1) ≠ 0 ∧
      (∀ ψ : (M ⧸ N) →ₗ[Aᵐᵒᵖ] PUnit.{1}, ψ = 0) ∧
      N.quotientHomEquivKer (S := A) (C := PUnit.{1}) 0 = 0 ∧
      (N.quotientHomEquivKer (S := A) (C := PUnit.{1})).symm 0 = 0 := by
  dsimp only
  refine ⟨?_, fun _ => Subsingleton.elim _ _, map_zero _, map_zero _⟩
  intro h
  have hm := (Submodule.Quotient.mk_eq_zero
    (LinearMap.ker (LinearMap.snd Aᵐᵒᵖ A A))).mp h
  have hv : LinearMap.snd Aᵐᵒᵖ A A (0, 1) = 0 := LinearMap.mem_ker.mp hm
  have hentry := congrArg (fun a : A => a 0 0) hv
  simp at hentry

/-- One-element coefficients satisfy quotient descent, zero restriction and
quotient extensionality even when the quotient is nonzero. -/
theorem zero_coefficient_quotient_roundtrips :
    let f : M →ₗ[Aᵐᵒᵖ] A := LinearMap.snd Aᵐᵒᵖ A A
    let N := LinearMap.ker f
    let z : M →ₗ[Aᵐᵒᵖ] PUnit.{1} := 0
    let hz : N ≤ LinearMap.ker z := by simp [z]
    (N.liftQ z hz).comp N.mkQ = z ∧ z.comp N.subtype = 0 ∧
      (∀ ψ : (M ⧸ N) →ₗ[Aᵐᵒᵖ] PUnit.{1},
        N.liftQ (ψ.comp N.mkQ)
          (by simpa using LinearMap.ker_le_ker_comp N.mkQ ψ) = ψ) ∧
      (∀ ψ χ : (M ⧸ N) →ₗ[Aᵐᵒᵖ] PUnit.{1},
        ψ.comp N.mkQ = χ.comp N.mkQ → ψ = χ) := by
  dsimp only
  refine ⟨Submodule.liftQ_mkQ _ _ _, by simp, ?_, ?_⟩
  · intro ψ
    apply Submodule.linearMap_qext
    exact Submodule.liftQ_mkQ _ _ _
  · intro ψ χ h
    exact Submodule.linearMap_qext _ h

/-- Restriction to integer scalars identifies the right span of `2`
with the usual ideal generated by `2`. -/
theorem span_two_restrictScalars :
    (Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)).restrictScalars ℤ =
      Ideal.span ({(2 : ℤ)} : Set ℤ) := by
  ext z
  change z ∈ Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ) ↔
    z ∈ Ideal.span ({(2 : ℤ)} : Set ℤ)
  rw [Submodule.mem_span_singleton, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨unop a, by simpa [op_smul_eq_mul, mul_comm] using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨op a, by simpa [op_smul_eq_mul, mul_comm] using ha⟩

/-- The class of `1` in the right quotient by the span of `2` maps to
`1` in `ZMod 2` through the scalar-restriction and quotient transports, and is nonzero. -/
theorem torsion_quotient_transports :
    let P : Submodule ℤᵐᵒᵖ ℤ := Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)
    let I : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
    let e0 := Submodule.Quotient.restrictScalarsEquiv ℤ P
    let e1 := Submodule.quotEquivOfEq (P.restrictScalars ℤ) I span_two_restrictScalars
    let e2 := Int.quotientSpanNatEquivZMod 2
    e2 (e1 (e0.symm (P.mkQ 1))) = (1 : ZMod 2) ∧
      e2 (e1 (e0.symm (P.mkQ 2))) = (0 : ZMod 2) ∧ P.mkQ 1 ≠ 0 := by
  dsimp only
  let P : Submodule ℤᵐᵒᵖ ℤ := Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)
  let I : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  let e0 := Submodule.Quotient.restrictScalarsEquiv ℤ P
  let e1 := Submodule.quotEquivOfEq (P.restrictScalars ℤ) I span_two_restrictScalars
  let e2 := Int.quotientSpanNatEquivZMod 2
  change e2 (e1 (e0.symm (P.mkQ 1))) = 1 ∧
    e2 (e1 (e0.symm (P.mkQ 2))) = 0 ∧ P.mkQ 1 ≠ 0
  have h1 : e2 (e1 (e0.symm (P.mkQ 1))) = (1 : ZMod 2) := by
    change e2 (Ideal.Quotient.mk I 1) = 1
    exact map_one e2
  have h2 : e2 (e1 (e0.symm (P.mkQ 2))) = (0 : ZMod 2) := by
    change e2 (Ideal.Quotient.mk I 2) = 0
    calc
      e2 (Ideal.Quotient.mk I 2) = (Int.castRingHom (ZMod 2)) 2 :=
        RingHom.congr_fun (Int.quotientSpanNatEquivZMod_comp_Quotient_mk 2) 2
      _ = (2 : ZMod 2) := by simp
      _ = 0 := ZMod.natCast_self 2
  refine ⟨h1, h2, ?_⟩
  intro h
  have hval := congrArg (fun x => e2 (e1 (e0.symm x))) h
  rw [h1] at hval
  simp at hval

/-- The integer class of `2` is zero in the right quotient by its span. -/
theorem torsion_class_two_zero :
    (Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)).mkQ 2 = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self 2)

/-- The class of `1` in the right integer quotient by the span of `2`
is nonzero. -/
theorem torsion_class_one_ne_zero :
    (Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)).mkQ 1 ≠ 0 :=
  torsion_quotient_transports.2.2

/-- Right integer linearity forces the value at `2` to be twice the
value at `1`. -/
theorem integer_form_two (F : ℤ →ₗ[ℤᵐᵒᵖ] ℤ) : F 2 = 2 * F 1 := by
  calc
    F 2 = F (op (2 : ℤ) • (1 : ℤ)) := by rw [op_smul_eq_mul, one_mul]
    _ = op (2 : ℤ) • F 1 := F.map_smul _ _
    _ = 2 * F 1 := by rw [op_smul_eq_mul, mul_comm]

/-- An integer-valued right linear form vanishing at `2` is zero. -/
theorem integer_form_zero_of_two (F : ℤ →ₗ[ℤᵐᵒᵖ] ℤ) (h : F 2 = 0) : F = 0 := by
  apply LinearMap.ext_ring_op
  have hmul : (2 : ℤ) * F 1 = 0 := (integer_form_two F).symm.trans h
  have h1 : F 1 = 0 := (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  simpa using h1

/-- Every raw integer-valued form on the nonzero right quotient
`ℤ/(2)` is zero, by pullback and quotient extensionality. -/
theorem torsion_raw_forms_zero
    (ψ : (ℤ ⧸ Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)) →ₗ[ℤᵐᵒᵖ] ℤ) :
    ψ = 0 := by
  apply Submodule.linearMap_qext
  have h : (ψ.comp (Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)).mkQ) 2 = 0 := by
    rw [LinearMap.comp_apply, torsion_class_two_zero, map_zero]
  simpa using integer_form_zero_of_two
    (ψ.comp (Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)).mkQ) h

/-- Ordinary duals of `ℤ/(2)` are also zero, using the inverse of the
same-inner-scalar op codec, not an identification of coefficient types. -/
theorem torsion_dual_forms_zero
    (δ : Module.Dual ℤᵐᵒᵖ (ℤ ⧸ Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ))) :
    δ = 0 := by
  let c : ℤ ≃ₗ[ℤᵐᵒᵖ] ℤᵐᵒᵖ := opLinearEquiv ℤᵐᵒᵖ
  have h : c.symm.toLinearMap.comp δ = 0 := torsion_raw_forms_zero _
  apply LinearMap.ext
  intro x
  apply c.symm.injective
  exact (LinearMap.congr_fun h x).trans c.symm.map_zero.symm

/-- The nonzero class of `1` is killed by every raw form and every
ordinary dual form on the same right quotient. -/
theorem torsion_nonzero_point_annihilated :
    let P : Submodule ℤᵐᵒᵖ ℤ := Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)
    ∃ x : ℤ ⧸ P, x ≠ 0 ∧
      (∀ ψ : (ℤ ⧸ P) →ₗ[ℤᵐᵒᵖ] ℤ, ψ x = 0) ∧
      (∀ δ : Module.Dual ℤᵐᵒᵖ (ℤ ⧸ P), δ x = 0) := by
  dsimp only
  refine ⟨_, torsion_class_one_ne_zero, ?_, ?_⟩
  · intro ψ
    rw [torsion_raw_forms_zero ψ]
    rfl
  · intro δ
    rw [torsion_dual_forms_zero δ]
    rfl

/-- The kernel of raw restriction to the right span of `2` consists
only of zero forms, independently of the quotient-Hom equivalence. -/
theorem torsion_raw_kernel_zero
    (F : LinearMap.ker (LinearMap.lcomp ℤ ℤ
      (Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)).subtype)) : F = 0 := by
  apply Subtype.ext
  apply integer_form_zero_of_two
  have hF : F.val.comp (Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)).subtype = 0 :=
    LinearMap.mem_ker.mp F.property
  exact LinearMap.congr_fun hF
    (⟨2, Submodule.mem_span_singleton_self 2⟩ :
      Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ))

/-- The ordinary opposite-valued restriction kernel is zero as well. -/
theorem torsion_dual_kernel_zero
    (D : LinearMap.ker (LinearMap.lcomp ℤ ℤᵐᵒᵖ
      (Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)).subtype)) : D = 0 := by
  apply Subtype.ext
  let c : ℤ ≃ₗ[ℤᵐᵒᵖ] ℤᵐᵒᵖ := opLinearEquiv ℤᵐᵒᵖ
  have hD : D.val.comp (Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)).subtype = 0 :=
    LinearMap.mem_ker.mp D.property
  have htwo : D.val 2 = 0 := LinearMap.congr_fun hD
    (⟨2, Submodule.mem_span_singleton_self 2⟩ :
      Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ))
  have hraw : c.symm.toLinearMap.comp D.val = 0 := by
    apply integer_form_zero_of_two
    change c.symm (D.val 2) = 0
    rw [htwo, map_zero]
  apply LinearMap.ext
  intro x
  apply c.symm.injective
  exact (LinearMap.congr_fun hraw x).trans c.symm.map_zero.symm

/-- The quotient-Hom correspondences agree with zero raw and ordinary
forms and zero annihilating kernels on the nonzero torsion quotient. -/
theorem torsion_equiv_consistency :
    let P : Submodule ℤᵐᵒᵖ ℤ := Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)
    (∀ ψ : (ℤ ⧸ P) →ₗ[ℤᵐᵒᵖ] ℤ,
      P.quotientHomEquivKer (S := ℤ) (C := ℤ) ψ = 0) ∧
    (∀ F : LinearMap.ker (LinearMap.lcomp ℤ ℤ P.subtype),
      (P.quotientHomEquivKer (S := ℤ) (C := ℤ)).symm F = 0) ∧
    (∀ δ : Module.Dual ℤᵐᵒᵖ (ℤ ⧸ P),
      P.quotientHomEquivKer (S := ℤ) (C := ℤᵐᵒᵖ) δ = 0) ∧
    (∀ D : LinearMap.ker (LinearMap.lcomp ℤ ℤᵐᵒᵖ P.subtype),
      (P.quotientHomEquivKer (S := ℤ) (C := ℤᵐᵒᵖ)).symm D = 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ψ
    rw [torsion_raw_forms_zero ψ, map_zero]
  · intro F
    rw [torsion_raw_kernel_zero F, map_zero]
  · intro δ
    rw [torsion_dual_forms_zero δ, map_zero]
  · intro D
    rw [torsion_dual_kernel_zero D, map_zero]

/-- Quotient descent and extensionality also apply to the torsion
quotient; its characteristic bundled values are the same descended values. -/
theorem torsion_quotient_roundtrips :
    let P : Submodule ℤᵐᵒᵖ ℤ := Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)
    (∀ ψ : (ℤ ⧸ P) →ₗ[ℤᵐᵒᵖ] ℤ,
      P.liftQ (ψ.comp P.mkQ)
        (by simpa using LinearMap.ker_le_ker_comp P.mkQ ψ) = ψ) ∧
    (∀ δ : Module.Dual ℤᵐᵒᵖ (ℤ ⧸ P),
      P.liftQ (δ.comp P.mkQ)
        (by simpa using LinearMap.ker_le_ker_comp P.mkQ δ) = δ) ∧
    (∀ ψ : (ℤ ⧸ P) →ₗ[ℤᵐᵒᵖ] ℤ, ∀ z : ℤ,
      (P.quotientHomEquivKer (S := ℤ) (C := ℤ) ψ).val z = 0) ∧
    (∀ D : LinearMap.ker (LinearMap.lcomp ℤ ℤᵐᵒᵖ P.subtype), ∀ z : ℤ,
      (P.quotientHomEquivKer (S := ℤ) (C := ℤᵐᵒᵖ)).symm D (P.mkQ z) = 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ψ
    apply Submodule.linearMap_qext
    exact Submodule.liftQ_mkQ _ _ _
  · intro δ
    apply Submodule.linearMap_qext
    exact Submodule.liftQ_mkQ _ _ _
  · intro ψ z
    rw [Submodule.quotientHomEquivKer_apply, torsion_raw_forms_zero ψ]
    rfl
  · intro D z
    rw [Submodule.quotientHomEquivKer_symm_apply_mkQ, torsion_dual_kernel_zero D]
    rfl

/-- The generator used by the integer singleton coordinate map is nonzero. -/
theorem integer_two_ne_zero : (2 : ℤ) ≠ 0 := by norm_num

/-- The singleton coordinate form on the right span of `2` sends
`2` to `1`, both in its opposite-valued and raw coefficient versions. -/
theorem span_two_coordinate_values :
    let P : Submodule ℤᵐᵒᵖ ℤ := Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)
    let t : P := ⟨2, Submodule.mem_span_singleton_self 2⟩
    let gD : P →ₗ[ℤᵐᵒᵖ] ℤᵐᵒᵖ :=
      (LinearEquiv.coord ℤᵐᵒᵖ ℤ 2 integer_two_ne_zero).toLinearMap
    let c : ℤ ≃ₗ[ℤᵐᵒᵖ] ℤᵐᵒᵖ := opLinearEquiv ℤᵐᵒᵖ
    let g : P →ₗ[ℤᵐᵒᵖ] ℤ := c.symm.toLinearMap.comp gD
    g t = (1 : ℤ) ∧ gD t = (1 : ℤᵐᵒᵖ) := by
  dsimp only
  have h := LinearEquiv.coord_self ℤᵐᵒᵖ ℤ 2 integer_two_ne_zero
  refine ⟨?_, h⟩
  simpa using congrArg unop h

/-- The raw coordinate form `2 ↦ 1` on the right span of `2` cannot
extend to the ambient right integer module: an ambient value at `2` is even. -/
theorem span_two_raw_not_extendible :
    let P : Submodule ℤᵐᵒᵖ ℤ := Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)
    let gD : P →ₗ[ℤᵐᵒᵖ] ℤᵐᵒᵖ :=
      (LinearEquiv.coord ℤᵐᵒᵖ ℤ 2 integer_two_ne_zero).toLinearMap
    let c : ℤ ≃ₗ[ℤᵐᵒᵖ] ℤᵐᵒᵖ := opLinearEquiv ℤᵐᵒᵖ
    let g : P →ₗ[ℤᵐᵒᵖ] ℤ := c.symm.toLinearMap.comp gD
    ¬ ∃ F : ℤ →ₗ[ℤᵐᵒᵖ] ℤ, F.comp P.subtype = g := by
  dsimp only
  rintro ⟨F, hF⟩
  have hval := LinearMap.congr_fun hF
    (⟨2, Submodule.mem_span_singleton_self 2⟩ :
      Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ))
  have htwo : F 2 = 1 := hval.trans span_two_coordinate_values.1
  have heven := integer_form_two F
  omega

/-- The ordinary opposite-valued singleton coordinate form also has
no ambient extension, by postcomposition with the inverse codec. -/
theorem span_two_dual_not_extendible :
    let P : Submodule ℤᵐᵒᵖ ℤ := Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)
    let gD : P →ₗ[ℤᵐᵒᵖ] ℤᵐᵒᵖ :=
      (LinearEquiv.coord ℤᵐᵒᵖ ℤ 2 integer_two_ne_zero).toLinearMap
    ¬ ∃ D : Module.Dual ℤᵐᵒᵖ ℤ, D.comp P.subtype = gD := by
  dsimp only
  rintro ⟨D, hD⟩
  apply span_two_raw_not_extendible
  refine ⟨(opLinearEquiv ℤᵐᵒᵖ : ℤ ≃ₗ[ℤᵐᵒᵖ] ℤᵐᵒᵖ).symm.toLinearMap.comp D, ?_⟩
  rw [LinearMap.comp_assoc, hD]

/-- Raw restriction to the right span of `2` is not surjective. This
is a failure of extension, not of the quotient-to-restriction-kernel correspondence. -/
theorem span_two_raw_restriction_not_surjective :
    ¬ Function.Surjective (LinearMap.lcomp ℤ ℤ
      (Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)).subtype) := by
  intro h
  let gD := (LinearEquiv.coord ℤᵐᵒᵖ ℤ 2 integer_two_ne_zero).toLinearMap
  let c : ℤ ≃ₗ[ℤᵐᵒᵖ] ℤᵐᵒᵖ := opLinearEquiv ℤᵐᵒᵖ
  obtain ⟨F, hF⟩ := h (c.symm.toLinearMap.comp gD)
  exact span_two_raw_not_extendible ⟨F, hF⟩

/-- Ordinary dual restriction to the right span of `2` is likewise
not surjective, witnessed by the singleton coordinate form. -/
theorem span_two_dual_restriction_not_surjective :
    ¬ Function.Surjective (LinearMap.lcomp ℤ ℤᵐᵒᵖ
      (Submodule.span ℤᵐᵒᵖ ({(2 : ℤ)} : Set ℤ)).subtype) := by
  intro h
  obtain ⟨D, hD⟩ := h
    (LinearEquiv.coord ℤᵐᵒᵖ ℤ 2 integer_two_ne_zero).toLinearMap
  exact span_two_dual_not_extendible ⟨D, hD⟩

/-- Zero forms have unique quotient factors at the top submodule,
on the empty-index and one-element modules, over the zero ring, and with
one-element coefficients on the first-axis quotient. -/
theorem zero_boundary_unique_factors
    (NE : Submodule Aᵐᵒᵖ ((ULift.{uI} Empty) → A))
    (NZ : Submodule Aᵐᵒᵖ PUnit.{1})
    (NR : Submodule PUnit.{1}ᵐᵒᵖ PUnit.{1}) :
    (∃! ψ : (M ⧸ (⊤ : Submodule Aᵐᵒᵖ M)) →ₗ[Aᵐᵒᵖ] A,
      ψ.comp (⊤ : Submodule Aᵐᵒᵖ M).mkQ = 0) ∧
    (∃! δ : Module.Dual Aᵐᵒᵖ (M ⧸ (⊤ : Submodule Aᵐᵒᵖ M)),
      δ.comp (⊤ : Submodule Aᵐᵒᵖ M).mkQ = 0) ∧
    (∃! ψ : (((ULift.{uI} Empty) → A) ⧸ NE) →ₗ[Aᵐᵒᵖ] A,
      ψ.comp NE.mkQ = 0) ∧
    (∃! δ : Module.Dual Aᵐᵒᵖ (((ULift.{uI} Empty) → A) ⧸ NE),
      δ.comp NE.mkQ = 0) ∧
    (∃! ψ : (PUnit.{1} ⧸ NZ) →ₗ[Aᵐᵒᵖ] A, ψ.comp NZ.mkQ = 0) ∧
    (∃! δ : Module.Dual Aᵐᵒᵖ (PUnit.{1} ⧸ NZ), δ.comp NZ.mkQ = 0) ∧
    (∃! ψ : (PUnit.{1} ⧸ NR) →ₗ[PUnit.{1}ᵐᵒᵖ] PUnit.{1}, ψ.comp NR.mkQ = 0) ∧
    (∃! δ : Module.Dual PUnit.{1}ᵐᵒᵖ (PUnit.{1} ⧸ NR), δ.comp NR.mkQ = 0) ∧
    (∃! ψ : (M ⧸ LinearMap.ker (LinearMap.snd Aᵐᵒᵖ A A)) →ₗ[Aᵐᵒᵖ] PUnit.{1},
      ψ.comp (LinearMap.ker (LinearMap.snd Aᵐᵒᵖ A A)).mkQ = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨0, by simp, ?_⟩
    intro ψ hψ
    apply Submodule.linearMap_qext
    simpa using hψ
  · refine ⟨0, by simp, ?_⟩
    intro δ hδ
    apply Submodule.linearMap_qext
    simpa using hδ
  · refine ⟨0, by simp, ?_⟩
    intro ψ hψ
    apply NE.linearMap_qext
    simpa using hψ
  · refine ⟨0, by simp, ?_⟩
    intro δ hδ
    apply NE.linearMap_qext
    simpa using hδ
  · refine ⟨0, by simp, ?_⟩
    intro ψ hψ
    apply NZ.linearMap_qext
    simpa using hψ
  · refine ⟨0, by simp, ?_⟩
    intro δ hδ
    apply NZ.linearMap_qext
    simpa using hδ
  · refine ⟨0, by simp, ?_⟩
    intro ψ hψ
    apply NR.linearMap_qext
    simpa using hψ
  · refine ⟨0, by simp, ?_⟩
    intro δ hδ
    apply NR.linearMap_qext
    simpa using hδ
  · refine ⟨0, by simp, ?_⟩
    intro ψ hψ
    apply Submodule.linearMap_qext
    simpa using hψ

/-- Quotient extensionality applies in each zero-source configuration,
with both raw and ordinary coefficient types. -/
theorem zero_source_extensionality
    (NE : Submodule Aᵐᵒᵖ ((ULift.{uI} Empty) → A))
    (NZ : Submodule Aᵐᵒᵖ PUnit.{1})
    (NR : Submodule PUnit.{1}ᵐᵒᵖ PUnit.{1}) :
    (∀ ψ χ : (((ULift.{uI} Empty) → A) ⧸ NE) →ₗ[Aᵐᵒᵖ] A,
      ψ.comp NE.mkQ = χ.comp NE.mkQ → ψ = χ) ∧
    (∀ δ ε : Module.Dual Aᵐᵒᵖ (((ULift.{uI} Empty) → A) ⧸ NE),
      δ.comp NE.mkQ = ε.comp NE.mkQ → δ = ε) ∧
    (∀ ψ χ : (PUnit.{1} ⧸ NZ) →ₗ[Aᵐᵒᵖ] A,
      ψ.comp NZ.mkQ = χ.comp NZ.mkQ → ψ = χ) ∧
    (∀ δ ε : Module.Dual Aᵐᵒᵖ (PUnit.{1} ⧸ NZ),
      δ.comp NZ.mkQ = ε.comp NZ.mkQ → δ = ε) ∧
    (∀ ψ χ : (PUnit.{1} ⧸ NR) →ₗ[PUnit.{1}ᵐᵒᵖ] PUnit.{1},
      ψ.comp NR.mkQ = χ.comp NR.mkQ → ψ = χ) ∧
    (∀ δ ε : Module.Dual PUnit.{1}ᵐᵒᵖ (PUnit.{1} ⧸ NR),
      δ.comp NR.mkQ = ε.comp NR.mkQ → δ = ε) := by
  exact ⟨fun _ _ h => NE.linearMap_qext h, fun _ _ h => NE.linearMap_qext h,
    fun _ _ h => NZ.linearMap_qext h, fun _ _ h => NZ.linearMap_qext h,
    fun _ _ h => NR.linearMap_qext h, fun _ _ h => NR.linearMap_qext h⟩

end ProjectiveModulesTests.QuotientHomBoundaryClient
