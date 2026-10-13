/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import ProjectiveModules.Module.QuotientHom
public import ProjectiveModulesTests.IdempotentSpanSemiringClient
public import ProjectiveModulesTests.RightIdealRingConstructorClient
import Mathlib.Tactic.NormNum

/-!
# Quotient Hom with independently lifted scalars, sources and coefficients

The first-axis quotient of two copies of `M₂(ℤ)` has nonzero right-linear
forms. These examples separate the universes of the inner scalar, source,
coefficient and outer scalar in `Submodule.quotientHomEquivKer`.

The source lift has levels `(0, 1)`. The scalar lift has levels `(1, 0)`:
its source is the original matrix pair, not a pair of lifted matrices.
Its source and low coefficient actions are the pullbacks along the opposite
of `ULift.ringEquiv`. The canonical high coefficients retain the right-regular
and regular-opposite actions. The scalar-tower and coefficient-action
identifications are proved with Mathlib's existing pullback operations.

The raw matrix coefficient and its opposite coefficient are kept distinct.
In both relative-universe examples, left multiplication by `E₀₀` fixes the
nonzero value `E₀₁`, whereas multiplication in the opposite order kills it.
Left multiplication also moves the identity-valued form to a different
nonzero form. An independent lifted-index example is separate from these
relative-universe examples.

## Limitations

The independently lifted generic coefficients use outer scalar `ℤ`. No
outer-matrix linearity is inferred from a coefficient `ULift.moduleEquiv`.
The high outer-scalar example instead uses the pullback of integer scalar
multiplication along `ULift ℤ → ℤ`, and doubling moves a nonzero form.

## References

The constructions reuse Mathlib's `Submodule.liftQ`, quotient extensionality,
`LinearMap.restrictScalars`, `Module.compHom`, `ULift.moduleEquiv`, and
`MulOpposite.opLinearEquiv`. The matrix units and their multiplication and
nonzero certificates are reused from the integer matrix right-ideal clients.
-/

@[expose] public section

universe uI uR uM uC uA uS

noncomputable section

namespace ProjectiveModulesTests.QuotientHomUniverseClient

open MulOpposite
open ProjectiveModulesTests.IdempotentSpanSemiringClient
open ProjectiveModulesTests.RightIdealRingConstructorClient

local notation "R" => IntMatrix

local notation "p" => intE11
local notation "q" => intE01

private theorem pq : p * q = q := intE11_mul_e01
private theorem qp : q * p = 0 := intE01_mul_e11
private theorem p_ne_zero : p ≠ 0 := intE11_proper_generator.1
private theorem q_ne_zero : q ≠ 0 := intE01_ne_zero
private theorem p_ne_one : p ≠ 1 := intE11_proper_generator.2
private theorem q_ne_one : q ≠ 1 := by
  intro h
  have := congrArg (fun a : R => a 0 0) h
  simp [intE01] at this
private theorem p_ne_q : p ≠ q := by
  intro h
  have := congrArg (fun a : R => a 0 0) h
  simp [intE11, intE01] at this

private theorem separated_triple {X : Type*} [Zero X] (F : R → X)
    (hF : Function.Injective F) (h0 : F 0 = 0) :
    F 1 ≠ 0 ∧ F p ≠ 0 ∧ F q ≠ 0 ∧
      F 1 ≠ F p ∧ F 1 ≠ F q ∧ F p ≠ F q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact one_ne_zero (hF (h.trans h0.symm))
  · intro h
    exact p_ne_zero (hF (h.trans h0.symm))
  · intro h
    exact q_ne_zero (hF (h.trans h0.symm))
  · intro h
    exact p_ne_one (hF h).symm
  · intro h
    exact q_ne_one (hF h).symm
  · intro h
    exact p_ne_q (hF h)

private theorem restriction_zero
    {A : Type uA} {S : Type uS} {M : Type uM} {C : Type uC}
    [Ring A] [Semiring S] [AddCommGroup M] [AddCommGroup C]
    [Module A M] [Module A C] [Module S C] [SMulCommClass A S C]
    (P : Submodule A M) (f : M →ₗ[A] C) (hf : P ≤ LinearMap.ker f) :
    f ∈ LinearMap.ker (LinearMap.lcomp S C P.subtype) := by
  change f.comp P.subtype = 0
  exact LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hf

private theorem factor_controls
    {A : Type uA} {S : Type uS} {M : Type uM} {C : Type uC}
    [Ring A] [Semiring S] [AddCommGroup M] [AddCommGroup C]
    [Module A M] [Module A C] [Module S C] [SMulCommClass A S C]
    (P : Submodule A M) (f : M →ₗ[A] C) (hf : P ≤ LinearMap.ker f) :
    (P.liftQ f hf).comp P.mkQ = f ∧
      f.comp P.subtype = 0 ∧
      P.quotientHomEquivKer (S := S) (C := C) (P.liftQ f hf) =
        ⟨f, restriction_zero (S := S) P f hf⟩ ∧
      (P.quotientHomEquivKer (S := S) (C := C)).symm
        ⟨f, restriction_zero (S := S) P f hf⟩ = P.liftQ f hf ∧
      ∀ ψ : (M ⧸ P) →ₗ[A] C, ψ.comp P.mkQ = f → ψ = P.liftQ f hf := by
  refine ⟨P.liftQ_mkQ f hf, LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hf,
    ?_, ?_, ?_⟩
  · apply Subtype.ext
    apply LinearMap.ext
    intro x
    simp [Submodule.quotientHomEquivKer_apply]
  · apply P.linearMap_qext
    apply LinearMap.ext
    intro x
    exact P.quotientHomEquivKer_symm_apply_mkQ
      ⟨f, restriction_zero (S := S) P f hf⟩ x
  · intro ψ hψ
    apply P.linearMap_qext
    exact hψ.trans (P.liftQ_mkQ f hf).symm

private theorem factor_value_ne_zero
    {A : Type uA} {M : Type uM} {C : Type uC}
    [Ring A] [AddCommGroup M] [AddCommGroup C] [Module A M] [Module A C]
    (P : Submodule A M) (f : M →ₗ[A] C) (hf : P ≤ LinearMap.ker f)
    (x : M) (hx : f x ≠ 0) : P.mkQ x ≠ 0 ∧ P.liftQ f hf ≠ 0 := by
  constructor
  · intro h
    apply hx
    have hv := congrArg (P.liftQ f hf) h
    simpa using hv
  · intro h
    apply hx
    have hv := LinearMap.congr_fun h (P.mkQ x)
    simpa using hv

namespace LiftedSource

private abbrev f : (ULift.{1} (R × R)) →ₗ[Rᵐᵒᵖ] R :=
  (LinearMap.snd Rᵐᵒᵖ R R).comp
    (ULift.moduleEquiv : (ULift.{1} (R × R)) ≃ₗ[Rᵐᵒᵖ] (R × R)).toLinearMap
private abbrev P : Submodule Rᵐᵒᵖ (ULift.{1} (R × R)) := LinearMap.ker f
private abbrev c : R ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ := MulOpposite.opLinearEquiv Rᵐᵒᵖ
private abbrev fa (a : R) : (ULift.{1} (R × R)) →ₗ[Rᵐᵒᵖ] R :=
  (LinearMap.mulLeft Rᵐᵒᵖ a).comp f
private abbrev da (a : R) : Module.Dual Rᵐᵒᵖ (ULift.{1} (R × R)) := c.toLinearMap.comp (fa a)
private theorem ha (a : R) : P ≤ LinearMap.ker (fa a) :=
  LinearMap.ker_le_ker_comp f (LinearMap.mulLeft Rᵐᵒᵖ a)
private theorem hda (a : R) : P ≤ LinearMap.ker (da a) :=
  (ha a).trans (LinearMap.ker_le_ker_comp (fa a) c.toLinearMap)
private abbrev φa (a : R) : ((ULift.{1} (R × R)) ⧸ P) →ₗ[Rᵐᵒᵖ] R := P.liftQ (fa a) (ha a)
private abbrev δa (a : R) : Module.Dual Rᵐᵒᵖ ((ULift.{1} (R × R)) ⧸ P) := P.liftQ (da a) (hda a)
private abbrev w : (ULift.{1} (R × R)) ⧸ P := P.mkQ (ULift.up (0, 1))
private abbrev φ : ((ULift.{1} (R × R)) ⧸ P) →ₗ[Rᵐᵒᵖ] R := P.liftQ f le_rfl
private abbrev d : Module.Dual Rᵐᵒᵖ (ULift.{1} (R × R)) := c.toLinearMap.comp f
private theorem hd : P ≤ LinearMap.ker d := LinearMap.ker_le_ker_comp f c.toLinearMap
private abbrev δ : Module.Dual Rᵐᵒᵖ ((ULift.{1} (R × R)) ⧸ P) := P.liftQ d hd

private theorem fa_apply (a x y : R) : fa a (ULift.up (x, y)) = a * y := rfl
private theorem da_apply (a x y : R) : da a (ULift.up (x, y)) = op (a * y) := rfl
private theorem φa_apply (a x y : R) :
    φa a (P.mkQ (ULift.up (x, y))) = a * y := rfl
private theorem δa_apply (a x y : R) :
    δa a (P.mkQ (ULift.up (x, y))) = op (a * y) := rfl

/-- The source is in universe one and its right scalar ring is in universe zero. -/
theorem source_action (a x y : R) :
    let M := ULift.{1} (R × R)
    op a • (ULift.up (x, y) : M) = ULift.up (x * a, y * a) := rfl

/-- The lifted first-axis quotient has nonzero raw and ordinary coefficient forms. -/
theorem quotient_values :
    let M := ULift.{1} (R × R)
    let f : M →ₗ[Rᵐᵒᵖ] R :=
      (LinearMap.snd Rᵐᵒᵖ R R).comp
        (ULift.moduleEquiv : M ≃ₗ[Rᵐᵒᵖ] (R × R)).toLinearMap
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    let c : R ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ := MulOpposite.opLinearEquiv Rᵐᵒᵖ
    let w : M ⧸ P := P.mkQ (ULift.up (0, 1))
    let φ : (M ⧸ P) →ₗ[Rᵐᵒᵖ] R := P.liftQ f le_rfl
    let d : Module.Dual Rᵐᵒᵖ M := c.toLinearMap.comp f
    let hd : P ≤ LinearMap.ker d := LinearMap.ker_le_ker_comp f c.toLinearMap
    let δ : Module.Dual Rᵐᵒᵖ (M ⧸ P) := P.liftQ d hd
    φ w = (1 : R) ∧ φ (P.mkQ (ULift.up (0, q))) = q ∧
      δ w = op (1 : R) ∧ δ (P.mkQ (ULift.up (0, q))) = op q ∧
      w ≠ 0 ∧ φ ≠ 0 ∧ δ ≠ 0 := by
  dsimp only
  have hr := factor_value_ne_zero P f le_rfl (ULift.up (0, 1))
    (by change (1 : R) ≠ 0; exact one_ne_zero)
  have ho := factor_value_ne_zero P d hd (ULift.up (0, 1))
    (by change op (1 : R) ≠ 0; simp)
  exact ⟨rfl, rfl, rfl, rfl, hr.1, hr.2, ho.2⟩

/-- The kernel consists precisely of lifted first-axis elements. -/
theorem kernel_membership (z : (ULift.{1} (R × R))) :
    let M := ULift.{1} (R × R)
    let f : M →ₗ[Rᵐᵒᵖ] R :=
      (LinearMap.snd Rᵐᵒᵖ R R).comp
        (ULift.moduleEquiv : M ≃ₗ[Rᵐᵒᵖ] (R × R)).toLinearMap
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    z ∈ P ↔ z.down.2 = 0 := Iff.rfl

/-- The original lifted projection and its op-coded form satisfy both API directions. -/
theorem projection_correspondence :
    let M := ULift.{1} (R × R)
    let f : M →ₗ[Rᵐᵒᵖ] R :=
      (LinearMap.snd Rᵐᵒᵖ R R).comp
        (ULift.moduleEquiv : M ≃ₗ[Rᵐᵒᵖ] (R × R)).toLinearMap
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    let c : R ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ := MulOpposite.opLinearEquiv Rᵐᵒᵖ
    let φ : (M ⧸ P) →ₗ[Rᵐᵒᵖ] R := P.liftQ f le_rfl
    let d : Module.Dual Rᵐᵒᵖ M := c.toLinearMap.comp f
    let hd : P ≤ LinearMap.ker d := LinearMap.ker_le_ker_comp f c.toLinearMap
    let δ : Module.Dual Rᵐᵒᵖ (M ⧸ P) := P.liftQ d hd
    φ.comp P.mkQ = f ∧ δ.comp P.mkQ = d ∧
      f.comp P.subtype = 0 ∧ d.comp P.subtype = 0 ∧
      P.quotientHomEquivKer (S := R) (C := R) φ =
        ⟨f, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ ∧
      (P.quotientHomEquivKer (S := R) (C := R)).symm
        ⟨f, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ = φ ∧
      P.quotientHomEquivKer (S := R) (C := Rᵐᵒᵖ) δ =
        ⟨d, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hd)⟩ ∧
      (P.quotientHomEquivKer (S := R) (C := Rᵐᵒᵖ)).symm
        ⟨d, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hd)⟩ = δ := by
  dsimp only
  have hr := factor_controls (S := R) P f le_rfl
  have ho := factor_controls (S := R) P d hd
  exact ⟨hr.1, ho.1, hr.2.1, ho.2.1, hr.2.2.1, hr.2.2.2.1,
    ho.2.2.1, ho.2.2.2.1⟩

/-- Forward and inverse controls use the raw coefficient, not the ordinary dual. -/
theorem raw_correspondence (a : R) :
    let M := ULift.{1} (R × R)
    let f : M →ₗ[Rᵐᵒᵖ] R :=
      (LinearMap.snd Rᵐᵒᵖ R R).comp
        (ULift.moduleEquiv : M ≃ₗ[Rᵐᵒᵖ] (R × R)).toLinearMap
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    let fa (a : R) : M →ₗ[Rᵐᵒᵖ] R :=
      (LinearMap.mulLeft Rᵐᵒᵖ a).comp f
    let ha (a : R) : P ≤ LinearMap.ker (fa a) :=
      LinearMap.ker_le_ker_comp f (LinearMap.mulLeft Rᵐᵒᵖ a)
    let φa (a : R) : (M ⧸ P) →ₗ[Rᵐᵒᵖ] R := P.liftQ (fa a) (ha a)
    (φa a).comp P.mkQ = fa a ∧
      (fa a).comp P.subtype = 0 ∧
      P.quotientHomEquivKer (S := R) (C := R) (φa a) =
        ⟨fa a, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp (ha a))⟩ ∧
      (P.quotientHomEquivKer (S := R) (C := R)).symm
        ⟨fa a, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp (ha a))⟩ = φa a ∧
      ∀ ψ : (M ⧸ P) →ₗ[Rᵐᵒᵖ] R,
        ψ.comp P.mkQ = fa a → ψ = φa a :=
  factor_controls (S := R) P (fa a) (ha a)

/-- Ordinary dual forms have their own forward and inverse controls. -/
theorem ordinary_correspondence (a : R) :
    let M := ULift.{1} (R × R)
    let f : M →ₗ[Rᵐᵒᵖ] R :=
      (LinearMap.snd Rᵐᵒᵖ R R).comp
        (ULift.moduleEquiv : M ≃ₗ[Rᵐᵒᵖ] (R × R)).toLinearMap
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    let c : R ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ := MulOpposite.opLinearEquiv Rᵐᵒᵖ
    let fa (a : R) : M →ₗ[Rᵐᵒᵖ] R :=
      (LinearMap.mulLeft Rᵐᵒᵖ a).comp f
    let da (a : R) : Module.Dual Rᵐᵒᵖ M := c.toLinearMap.comp (fa a)
    let ha (a : R) : P ≤ LinearMap.ker (fa a) :=
      LinearMap.ker_le_ker_comp f (LinearMap.mulLeft Rᵐᵒᵖ a)
    let hda (a : R) : P ≤ LinearMap.ker (da a) :=
      (ha a).trans (LinearMap.ker_le_ker_comp (fa a) c.toLinearMap)
    let δa (a : R) : Module.Dual Rᵐᵒᵖ (M ⧸ P) := P.liftQ (da a) (hda a)
    (δa a).comp P.mkQ = da a ∧
      (da a).comp P.subtype = 0 ∧
      P.quotientHomEquivKer (S := R) (C := Rᵐᵒᵖ) (δa a) =
        ⟨da a, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp (hda a))⟩ ∧
      (P.quotientHomEquivKer (S := R) (C := Rᵐᵒᵖ)).symm
        ⟨da a, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp (hda a))⟩ = δa a ∧
      ∀ δ : Module.Dual Rᵐᵒᵖ (M ⧸ P),
        δ.comp P.mkQ = da a → δ = δa a :=
  factor_controls (S := R) P (da a) (hda a)

/-- The inverse correspondence at the upper-right form has a nonzero value. -/
theorem inverse_upper_right :
    let M := ULift.{1} (R × R)
    let f : M →ₗ[Rᵐᵒᵖ] R :=
      (LinearMap.snd Rᵐᵒᵖ R R).comp
        (ULift.moduleEquiv : M ≃ₗ[Rᵐᵒᵖ] (R × R)).toLinearMap
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    let c : R ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ := MulOpposite.opLinearEquiv Rᵐᵒᵖ
    let fa (a : R) : M →ₗ[Rᵐᵒᵖ] R :=
      (LinearMap.mulLeft Rᵐᵒᵖ a).comp f
    let da (a : R) : Module.Dual Rᵐᵒᵖ M := c.toLinearMap.comp (fa a)
    let ha (a : R) : P ≤ LinearMap.ker (fa a) :=
      LinearMap.ker_le_ker_comp f (LinearMap.mulLeft Rᵐᵒᵖ a)
    let hda (a : R) : P ≤ LinearMap.ker (da a) :=
      (ha a).trans (LinearMap.ker_le_ker_comp (fa a) c.toLinearMap)
    let w : M ⧸ P := P.mkQ (ULift.up (0, 1))
    (P.quotientHomEquivKer (S := R) (C := R)).symm
        ⟨fa q, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp (ha q))⟩ w = q ∧
      (P.quotientHomEquivKer (S := R) (C := Rᵐᵒᵖ)).symm
        ⟨da q, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp (hda q))⟩ w = op q ∧ q ≠ 0 := by
  dsimp only
  rw [(raw_correspondence q).2.2.2.1, (ordinary_correspondence q).2.2.2.1]
  exact ⟨by change q * 1 = q; exact mul_one q,
    by change op (q * 1) = op q; exact congrArg op (mul_one q), q_ne_zero⟩

/-- The left coefficient action and the reversed multiplication give different values. -/
theorem coefficient_order :
    let M := ULift.{1} (R × R)
    let f : M →ₗ[Rᵐᵒᵖ] R :=
      (LinearMap.snd Rᵐᵒᵖ R R).comp
        (ULift.moduleEquiv : M ≃ₗ[Rᵐᵒᵖ] (R × R)).toLinearMap
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    let c : R ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ := MulOpposite.opLinearEquiv Rᵐᵒᵖ
    let fa (a : R) : M →ₗ[Rᵐᵒᵖ] R :=
      (LinearMap.mulLeft Rᵐᵒᵖ a).comp f
    let da (a : R) : Module.Dual Rᵐᵒᵖ M := c.toLinearMap.comp (fa a)
    let ha (a : R) : P ≤ LinearMap.ker (fa a) :=
      LinearMap.ker_le_ker_comp f (LinearMap.mulLeft Rᵐᵒᵖ a)
    let hda (a : R) : P ≤ LinearMap.ker (da a) :=
      (ha a).trans (LinearMap.ker_le_ker_comp (fa a) c.toLinearMap)
    let φa (a : R) : (M ⧸ P) →ₗ[Rᵐᵒᵖ] R := P.liftQ (fa a) (ha a)
    let δa (a : R) : Module.Dual Rᵐᵒᵖ (M ⧸ P) := P.liftQ (da a) (hda a)
    let w : M ⧸ P := P.mkQ (ULift.up (0, 1))
    (p • fa q) (ULift.up (0, 1)) = q ∧
      fa q (ULift.up (0, 1)) * p = 0 ∧
      (p • da q) (ULift.up (0, 1)) = op q ∧
      op (unop (da q (ULift.up (0, 1))) * p) = 0 ∧
      (p • φa q) w = q ∧ (p • δa q) w = op q ∧ q ≠ 0 := by
  dsimp only
  change p * (q * 1) = q ∧ (q * 1) * p = 0 ∧
    op (p * (q * 1)) = op q ∧ op ((q * 1) * p) = 0 ∧
    p * (q * 1) = q ∧ op (p * (q * 1)) = op q ∧ q ≠ 0
  simp [pq, qp, q_ne_zero]

/-- The diagonal unit moves the identity-valued form to a distinct nonzero form. -/
theorem coefficient_movement :
    let M := ULift.{1} (R × R)
    let f : M →ₗ[Rᵐᵒᵖ] R :=
      (LinearMap.snd Rᵐᵒᵖ R R).comp
        (ULift.moduleEquiv : M ≃ₗ[Rᵐᵒᵖ] (R × R)).toLinearMap
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    let c : R ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ := MulOpposite.opLinearEquiv Rᵐᵒᵖ
    let fa (a : R) : M →ₗ[Rᵐᵒᵖ] R :=
      (LinearMap.mulLeft Rᵐᵒᵖ a).comp f
    let da (a : R) : Module.Dual Rᵐᵒᵖ M := c.toLinearMap.comp (fa a)
    let ha (a : R) : P ≤ LinearMap.ker (fa a) :=
      LinearMap.ker_le_ker_comp f (LinearMap.mulLeft Rᵐᵒᵖ a)
    let hda (a : R) : P ≤ LinearMap.ker (da a) :=
      (ha a).trans (LinearMap.ker_le_ker_comp (fa a) c.toLinearMap)
    let φa (a : R) : (M ⧸ P) →ₗ[Rᵐᵒᵖ] R := P.liftQ (fa a) (ha a)
    let δa (a : R) : Module.Dual Rᵐᵒᵖ (M ⧸ P) := P.liftQ (da a) (hda a)
    let w : M ⧸ P := P.mkQ (ULift.up (0, 1))
    p • fa 1 = fa p ∧ fa p ≠ fa 1 ∧ fa p ≠ 0 ∧
      p • da 1 = da p ∧ da p ≠ da 1 ∧ da p ≠ 0 ∧
      (p • φa 1) w = p ∧ φa p ≠ φa 1 ∧ φa p ≠ 0 ∧
      (p • δa 1) w = op p ∧ δa p ≠ δa 1 ∧ δa p ≠ 0 := by
  dsimp only
  have hfr : fa p ≠ fa 1 := by
    intro h
    exact p_ne_one (by simpa [fa_apply] using LinearMap.congr_fun h (ULift.up (0, 1)))
  have hfd : da p ≠ da 1 := by
    intro h
    apply p_ne_one
    simpa [da_apply] using congrArg unop (LinearMap.congr_fun h (ULift.up (0, 1)))
  have hφ : φa p ≠ φa 1 := by
    intro h
    exact p_ne_one (by simpa [w, φa_apply] using LinearMap.congr_fun h w)
  have hδ : δa p ≠ δa 1 := by
    intro h
    apply p_ne_one
    simpa [w, δa_apply] using congrArg unop (LinearMap.congr_fun h w)
  have hnφ := (factor_value_ne_zero P (fa p) (ha p) (ULift.up (0, 1))
    (by simpa [fa_apply] using p_ne_zero)).2
  have hnδ := (factor_value_ne_zero P (da p) (hda p) (ULift.up (0, 1))
    (by simpa [da_apply] using p_ne_zero)).2
  refine ⟨?_, hfr, ?_, ?_, hfd, ?_, ?_, hφ, hnφ, ?_, hδ, hnδ⟩
  · apply LinearMap.ext
    intro x
    change p * (1 * x.down.2) = p * x.down.2
    simp
  · intro h
    exact p_ne_zero (by simpa [fa_apply] using LinearMap.congr_fun h (ULift.up (0, 1)))
  · apply LinearMap.ext
    intro x
    change op (p * (1 * x.down.2)) = op (p * x.down.2)
    simp
  · intro h
    apply p_ne_zero
    simpa [da_apply] using congrArg unop (LinearMap.congr_fun h (ULift.up (0, 1)))
  · change p * (1 * 1) = p
    simp
  · change op (p * (1 * 1)) = op p
    simp

private theorem family_injective :
    Function.Injective fa ∧ Function.Injective da ∧
      Function.Injective φa ∧ Function.Injective δa := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h
    simpa [fa_apply] using LinearMap.congr_fun h (ULift.up (0, 1))
  · intro a b h
    simpa [da_apply] using congrArg unop (LinearMap.congr_fun h (ULift.up (0, 1)))
  · intro a b h
    simpa [w, φa_apply] using LinearMap.congr_fun h w
  · intro a b h
    simpa [w, δa_apply] using congrArg unop (LinearMap.congr_fun h w)

/-- Identity, diagonal-unit and upper-right-unit forms are nonzero and pairwise distinct. -/
theorem unit_forms_distinct :
    let M := ULift.{1} (R × R)
    let f : M →ₗ[Rᵐᵒᵖ] R :=
      (LinearMap.snd Rᵐᵒᵖ R R).comp
        (ULift.moduleEquiv : M ≃ₗ[Rᵐᵒᵖ] (R × R)).toLinearMap
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    let c : R ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ := MulOpposite.opLinearEquiv Rᵐᵒᵖ
    let fa (a : R) : M →ₗ[Rᵐᵒᵖ] R :=
      (LinearMap.mulLeft Rᵐᵒᵖ a).comp f
    let da (a : R) : Module.Dual Rᵐᵒᵖ M := c.toLinearMap.comp (fa a)
    let ha (a : R) : P ≤ LinearMap.ker (fa a) :=
      LinearMap.ker_le_ker_comp f (LinearMap.mulLeft Rᵐᵒᵖ a)
    let hda (a : R) : P ≤ LinearMap.ker (da a) :=
      (ha a).trans (LinearMap.ker_le_ker_comp (fa a) c.toLinearMap)
    let φa (a : R) : (M ⧸ P) →ₗ[Rᵐᵒᵖ] R := P.liftQ (fa a) (ha a)
    let δa (a : R) : Module.Dual Rᵐᵒᵖ (M ⧸ P) := P.liftQ (da a) (hda a)
    (fa 1 ≠ 0 ∧ fa p ≠ 0 ∧ fa q ≠ 0 ∧
      fa 1 ≠ fa p ∧ fa 1 ≠ fa q ∧ fa p ≠ fa q) ∧
      (da 1 ≠ 0 ∧ da p ≠ 0 ∧ da q ≠ 0 ∧
        da 1 ≠ da p ∧ da 1 ≠ da q ∧ da p ≠ da q) ∧
      (φa 1 ≠ 0 ∧ φa p ≠ 0 ∧ φa q ≠ 0 ∧
        φa 1 ≠ φa p ∧ φa 1 ≠ φa q ∧ φa p ≠ φa q) ∧
      (δa 1 ≠ 0 ∧ δa p ≠ 0 ∧ δa q ≠ 0 ∧
        δa 1 ≠ δa p ∧ δa 1 ≠ δa q ∧ δa p ≠ δa q) := by
  dsimp only
  refine ⟨separated_triple fa family_injective.1 ?_,
    separated_triple da family_injective.2.1 ?_,
    separated_triple φa family_injective.2.2.1 ?_,
    separated_triple δa family_injective.2.2.2 ?_⟩
  · apply LinearMap.ext
    intro x
    change (0 : R) * x.down.2 = 0
    simp
  · apply LinearMap.ext
    intro x
    change op ((0 : R) * x.down.2) = 0
    simp
  · apply P.linearMap_qext
    apply LinearMap.ext
    intro x
    change (0 : R) * x.down.2 = 0
    simp
  · apply P.linearMap_qext
    apply LinearMap.ext
    intro x
    change op ((0 : R) * x.down.2) = 0
    simp

/-- Right multiplication by the diagonal unit is not a right-linear form. -/
theorem right_multiplication_not_linear :
    let M := ULift.{1} (R × R)
    let g : M → R := fun z => z.down.2 * p
    ¬ ∀ (s : Rᵐᵒᵖ) (z : M), g (s • z) = s • g z := by
  dsimp only
  intro h
  have hv := h (op q) (ULift.up (0, 1))
  change (1 * q) * p = (1 * p) * q at hv
  have hz : (0 : R) = q := by simpa only [one_mul, qp, pq] using hv
  exact q_ne_zero hz.symm

end LiftedSource

namespace LiftedScalar

local notation "M" => R × R

-- Each stored module is an application of an existing pullback or regular-module provider.
private abbrev downRing : (ULift.{1} R) →+* R :=
  (ULift.ringEquiv : (ULift.{1} R) ≃+* R).toRingHom
private abbrev downRingOp : (ULift.{1} R)ᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
private abbrev productModule : Module (ULift.{1} R)ᵐᵒᵖ M := Module.compHom M downRingOp
private abbrev lowCoefficientModule : Module (ULift.{1} R)ᵐᵒᵖ R := Module.compHom R downRingOp
private abbrev innerCarrierModule : Module (ULift.{1} R)ᵐᵒᵖ Rᵐᵒᵖ :=
  Module.compHom Rᵐᵒᵖ downRingOp
private abbrev rawModule : Module (ULift.{1} R)ᵐᵒᵖ (ULift.{1} R) := Semiring.toOppositeModule
private abbrev ordinaryModule : Module (ULift.{1} R)ᵐᵒᵖ (ULift.{1} R)ᵐᵒᵖ := Semiring.toModule
private abbrev leftRawModule : Module (ULift.{1} R) (ULift.{1} R) := Semiring.toModule
private abbrev leftOrdinaryModule : Module (ULift.{1} R) (ULift.{1} R)ᵐᵒᵖ :=
  @MulOpposite.instModule (ULift.{1} R) (ULift.{1} R) _ _ leftRawModule

private abbrev rawCommutes :
    @SMulCommClass (ULift.{1} R)ᵐᵒᵖ (ULift.{1} R) (ULift.{1} R)
      rawModule.toSMul leftRawModule.toSMul :=
  @Semigroup.opposite_smulCommClass (ULift.{1} R) inferInstance
private abbrev ordinaryCommutes :
    @SMulCommClass (ULift.{1} R)ᵐᵒᵖ (ULift.{1} R) (ULift.{1} R)ᵐᵒᵖ
      ordinaryModule.toSMul leftOrdinaryModule.toSMul :=
  @MulOpposite.instSMulCommClass (ULift.{1} R)ᵐᵒᵖ (ULift.{1} R) (ULift.{1} R)
    rawModule.toSMul leftRawModule.toSMul rawCommutes

attribute [local instance] productModule lowCoefficientModule innerCarrierModule
  rawModule ordinaryModule leftRawModule leftOrdinaryModule rawCommutes ordinaryCommutes

private theorem product_tower : IsScalarTower (ULift.{1} R)ᵐᵒᵖ Rᵐᵒᵖ M :=
  SMul.comp.isScalarTower downRingOp
private theorem coefficient_tower : IsScalarTower (ULift.{1} R)ᵐᵒᵖ Rᵐᵒᵖ R :=
  SMul.comp.isScalarTower downRingOp
private theorem compatible_smul : LinearMap.CompatibleSMul M R (ULift.{1} R)ᵐᵒᵖ Rᵐᵒᵖ := by
  let := product_tower
  let := coefficient_tower
  exact LinearMap.IsScalarTower.compatibleSMul

private abbrev fdown : M →ₗ[(ULift.{1} R)ᵐᵒᵖ] R := by
  letI := compatible_smul
  exact (LinearMap.snd Rᵐᵒᵖ R R).restrictScalars (ULift.{1} R)ᵐᵒᵖ

/-- The pulled-back low source is still the universe-zero matrix pair. -/
theorem source_action (a x y : R) :
    let RH := ULift.{1} R
    let downRing : RH →+* R :=
      (ULift.ringEquiv : RH ≃+* R).toRingHom
    let downRingOp : RHᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
    let productModule : Module RHᵐᵒᵖ M := Module.compHom M downRingOp
    @SMul.smul RHᵐᵒᵖ M productModule.toSMul (op (ULift.up a : RH)) (x, y) = (x * a, y * a) := rfl

/-- The pulled-back low coefficient retains right multiplication. -/
theorem low_coefficient_action (a z : R) :
    let RH := ULift.{1} R
    let downRing : RH →+* R :=
      (ULift.ringEquiv : RH ≃+* R).toRingHom
    let downRingOp : RHᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
    let lowCoefficientModule : Module RHᵐᵒᵖ R := Module.compHom R downRingOp
    @SMul.smul RHᵐᵒᵖ R lowCoefficientModule.toSMul (op (ULift.up a : RH)) z = z * a := rfl

/-- The lifted coefficient action induced by the pullback is the canonical right action. -/
theorem canonical_raw_alignment :
    let RH := ULift.{1} R
    let downRing : RH →+* R :=
      (ULift.ringEquiv : RH ≃+* R).toRingHom
    let downRingOp : RHᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
    let lowCoefficientModule : Module RHᵐᵒᵖ R := Module.compHom R downRingOp
    let rawModule : Module RHᵐᵒᵖ RH := Semiring.toOppositeModule
    rawModule = (@ULift.module' («R» := RHᵐᵒᵖ) («M» := R) _ _ lowCoefficientModule) :=
  Module.ext' _ _ (fun _ _ => rfl)

/-- The op-coded right action agrees with the regular action on the opposite ring. -/
theorem canonical_ordinary_alignment :
    let RH := ULift.{1} R
    let rawModule : Module RHᵐᵒᵖ RH := Semiring.toOppositeModule
    let ordinaryModule : Module RHᵐᵒᵖ RHᵐᵒᵖ := Semiring.toModule
    ordinaryModule = (@MulOpposite.instModule RHᵐᵒᵖ RH _ _ rawModule) :=
  Module.ext' _ _ (fun _ _ => rfl)

private abbrev eCoeff : (ULift.{1} R) ≃ₗ[(ULift.{1} R)ᵐᵒᵖ] R := ULift.moduleEquiv
private abbrev fup : M →ₗ[(ULift.{1} R)ᵐᵒᵖ] (ULift.{1} R) := eCoeff.symm.toLinearMap.comp fdown
private abbrev P : Submodule (ULift.{1} R)ᵐᵒᵖ M := LinearMap.ker fup
private abbrev c : (ULift.{1} R) ≃ₗ[(ULift.{1} R)ᵐᵒᵖ] (ULift.{1} R)ᵐᵒᵖ :=
  @MulOpposite.opLinearEquiv (ULift.{1} R)ᵐᵒᵖ (ULift.{1} R) _ _ rawModule
private abbrev fa (a : R) : M →ₗ[(ULift.{1} R)ᵐᵒᵖ] (ULift.{1} R) :=
  (LinearMap.mulLeft (ULift.{1} R)ᵐᵒᵖ (ULift.up a : (ULift.{1} R))).comp fup
private abbrev da (a : R) : Module.Dual (ULift.{1} R)ᵐᵒᵖ M := c.toLinearMap.comp (fa a)
private theorem ha (a : R) : P ≤ LinearMap.ker (fa a) :=
  LinearMap.ker_le_ker_comp fup (LinearMap.mulLeft (ULift.{1} R)ᵐᵒᵖ (ULift.up a : (ULift.{1} R)))
private theorem hda (a : R) : P ≤ LinearMap.ker (da a) :=
  (ha a).trans (LinearMap.ker_le_ker_comp (fa a) c.toLinearMap)
private abbrev φa (a : R) : (M ⧸ P) →ₗ[(ULift.{1} R)ᵐᵒᵖ] (ULift.{1} R) := P.liftQ (fa a) (ha a)
private abbrev δa (a : R) : Module.Dual (ULift.{1} R)ᵐᵒᵖ (M ⧸ P) := P.liftQ (da a) (hda a)
private abbrev w : M ⧸ P := P.mkQ (0, 1)
private abbrev φ : (M ⧸ P) →ₗ[(ULift.{1} R)ᵐᵒᵖ] (ULift.{1} R) := P.liftQ fup le_rfl
private abbrev d : Module.Dual (ULift.{1} R)ᵐᵒᵖ M := c.toLinearMap.comp fup
private theorem hd : P ≤ LinearMap.ker d := LinearMap.ker_le_ker_comp fup c.toLinearMap
private abbrev δ : Module.Dual (ULift.{1} R)ᵐᵒᵖ (M ⧸ P) := P.liftQ d hd

private theorem fa_apply (a x y : R) : fa a (x, y) = ULift.up (a * y) := rfl
private theorem da_apply (a x y : R) : da a (x, y) = op (ULift.up (a * y) : (ULift.{1} R)) := rfl
private theorem φa_apply (a x y : R) :
    φa a (P.mkQ (x, y)) = ULift.up (a * y) := rfl
private theorem δa_apply (a x y : R) :
    δa a (P.mkQ (x, y)) = op (ULift.up (a * y) : (ULift.{1} R)) := rfl

/-- Restricting the old second projection and lifting its coefficient has the stated value. -/
theorem projection_values (x y : R) :
    let RH := ULift.{1} R
    let downRing : RH →+* R :=
      (ULift.ringEquiv : RH ≃+* R).toRingHom
    let downRingOp : RHᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
    let productModule : Module RHᵐᵒᵖ M := Module.compHom M downRingOp
    let lowCoefficientModule : Module RHᵐᵒᵖ R := Module.compHom R downRingOp
    let innerCarrierModule : Module RHᵐᵒᵖ Rᵐᵒᵖ := Module.compHom Rᵐᵒᵖ downRingOp
    let rawModule : Module RHᵐᵒᵖ RH := Semiring.toOppositeModule
    let productTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := M) downRingOp
    let coefficientTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := R) downRingOp
    let compatible := @LinearMap.IsScalarTower.compatibleSMul («M» := M) (M₂ := R)
        («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ)
      _ _ _ productModule.toSMul _ lowCoefficientModule.toSMul _
      innerCarrierModule.toSMul productTower coefficientTower
    let fdown := @LinearMap.restrictScalars («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ) («M» := M) (M₂ := R)
      _ _ _ _ productModule lowCoefficientModule _ _ compatible
      (LinearMap.snd Rᵐᵒᵖ R R)
    let eCoeff : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH R _ _ rawModule lowCoefficientModule :=
      @ULift.moduleEquiv («R» := RHᵐᵒᵖ) («M» := R) _ _ lowCoefficientModule
    let fup := eCoeff.symm.toLinearMap.comp fdown
    fdown (x, y) = y ∧ fup (x, y) = (ULift.up y : RH) := ⟨rfl, rfl⟩

/-- The kernel is the first axis, under the stored pulled-back action. -/
theorem kernel_first_axis :
    let RH := ULift.{1} R
    let downRing : RH →+* R :=
      (ULift.ringEquiv : RH ≃+* R).toRingHom
    let downRingOp : RHᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
    let productModule : Module RHᵐᵒᵖ M := Module.compHom M downRingOp
    let lowCoefficientModule : Module RHᵐᵒᵖ R := Module.compHom R downRingOp
    let innerCarrierModule : Module RHᵐᵒᵖ Rᵐᵒᵖ := Module.compHom Rᵐᵒᵖ downRingOp
    let rawModule : Module RHᵐᵒᵖ RH := Semiring.toOppositeModule
    let productTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := M) downRingOp
    let coefficientTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := R) downRingOp
    let compatible := @LinearMap.IsScalarTower.compatibleSMul («M» := M) (M₂ := R)
        («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ)
      _ _ _ productModule.toSMul _ lowCoefficientModule.toSMul _
      innerCarrierModule.toSMul productTower coefficientTower
    let fdown := @LinearMap.restrictScalars («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ) («M» := M) (M₂ := R)
      _ _ _ _ productModule lowCoefficientModule _ _ compatible
      (LinearMap.snd Rᵐᵒᵖ R R)
    let eCoeff : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH R _ _ rawModule lowCoefficientModule :=
      @ULift.moduleEquiv («R» := RHᵐᵒᵖ) («M» := R) _ _ lowCoefficientModule
    let fup := eCoeff.symm.toLinearMap.comp fdown
    let P := LinearMap.ker fup
    P = (⊤ : @Submodule RHᵐᵒᵖ R _ _ lowCoefficientModule).prod
      (⊥ : @Submodule RHᵐᵒᵖ R _ _ lowCoefficientModule) := by
  dsimp only
  apply Submodule.ext
  intro z
  change (ULift.up z.2 : ULift.{1} R) = ULift.up 0 ↔
    z.1 ∈ (⊤ : Submodule (ULift.{1} R)ᵐᵒᵖ R) ∧
      z.2 ∈ (⊥ : Submodule (ULift.{1} R)ᵐᵒᵖ R)
  rw [ULift.up_inj]
  simp

/-- A high scalar ring acts on a low source, with nonzero high raw and opposite forms. -/
theorem quotient_values :
    let RH := ULift.{1} R
    let downRing : RH →+* R :=
      (ULift.ringEquiv : RH ≃+* R).toRingHom
    let downRingOp : RHᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
    let productModule : Module RHᵐᵒᵖ M := Module.compHom M downRingOp
    let lowCoefficientModule : Module RHᵐᵒᵖ R := Module.compHom R downRingOp
    let innerCarrierModule : Module RHᵐᵒᵖ Rᵐᵒᵖ := Module.compHom Rᵐᵒᵖ downRingOp
    let rawModule : Module RHᵐᵒᵖ RH := Semiring.toOppositeModule
    let ordinaryModule : Module RHᵐᵒᵖ RHᵐᵒᵖ := Semiring.toModule
    let productTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := M) downRingOp
    let coefficientTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := R) downRingOp
    let compatible := @LinearMap.IsScalarTower.compatibleSMul («M» := M) (M₂ := R)
        («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ)
      _ _ _ productModule.toSMul _ lowCoefficientModule.toSMul _
      innerCarrierModule.toSMul productTower coefficientTower
    let fdown := @LinearMap.restrictScalars («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ) («M» := M) (M₂ := R)
      _ _ _ _ productModule lowCoefficientModule _ _ compatible
      (LinearMap.snd Rᵐᵒᵖ R R)
    let eCoeff : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH R _ _ rawModule lowCoefficientModule :=
      @ULift.moduleEquiv («R» := RHᵐᵒᵖ) («M» := R) _ _ lowCoefficientModule
    let fup := eCoeff.symm.toLinearMap.comp fdown
    let P := LinearMap.ker fup
    let c : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH RHᵐᵒᵖ _ _ rawModule ordinaryModule :=
      @MulOpposite.opLinearEquiv RHᵐᵒᵖ RH _ _ rawModule
    let w := P.mkQ (0, 1)
    let φ := P.liftQ fup le_rfl
    let d := c.toLinearMap.comp fup
    let hd : P ≤ LinearMap.ker d := LinearMap.ker_le_ker_comp fup c.toLinearMap
    let δ := P.liftQ d hd
    φ w = (ULift.up (1 : R) : RH) ∧ φ (P.mkQ (0, q)) = (ULift.up q : RH) ∧
      δ w = op (ULift.up (1 : R) : RH) ∧ δ (P.mkQ (0, q)) = op (ULift.up q : RH) ∧
      w ≠ 0 ∧ φ ≠ 0 ∧ δ ≠ 0 := by
  dsimp only
  have hr := factor_value_ne_zero P fup le_rfl (0, 1)
    (by change (1 : (ULift.{1} R)) ≠ 0; exact one_ne_zero)
  have ho := factor_value_ne_zero P d hd (0, 1)
    (by
      intro h
      exact one_ne_zero (congrArg (fun z : (ULift.{1} R)ᵐᵒᵖ => (unop z).down) h))
  exact ⟨rfl, rfl, rfl, rfl, hr.1, hr.2, ho.2⟩

/-- The high projection factors and their distinct codomains satisfy both API directions. -/
theorem projection_correspondence :
    let RH := ULift.{1} R
    let downRing : RH →+* R :=
      (ULift.ringEquiv : RH ≃+* R).toRingHom
    let downRingOp : RHᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
    let productModule : Module RHᵐᵒᵖ M := Module.compHom M downRingOp
    let lowCoefficientModule : Module RHᵐᵒᵖ R := Module.compHom R downRingOp
    let innerCarrierModule : Module RHᵐᵒᵖ Rᵐᵒᵖ := Module.compHom Rᵐᵒᵖ downRingOp
    let rawModule : Module RHᵐᵒᵖ RH := Semiring.toOppositeModule
    let ordinaryModule : Module RHᵐᵒᵖ RHᵐᵒᵖ := Semiring.toModule
    let leftRawModule : Module RH RH := Semiring.toModule
    let rawCommutes : @SMulCommClass RHᵐᵒᵖ RH RH
        rawModule.toSMul leftRawModule.toSMul :=
      @Semigroup.opposite_smulCommClass RH inferInstance
    let leftOrdinaryModule : Module RH RHᵐᵒᵖ :=
      @MulOpposite.instModule RH RH _ _ leftRawModule
    let ordinaryCommutes : @SMulCommClass RHᵐᵒᵖ RH RHᵐᵒᵖ
        ordinaryModule.toSMul leftOrdinaryModule.toSMul :=
      @MulOpposite.instSMulCommClass RHᵐᵒᵖ RH RH
        rawModule.toSMul leftRawModule.toSMul rawCommutes
    let productTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := M) downRingOp
    let coefficientTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := R) downRingOp
    let compatible := @LinearMap.IsScalarTower.compatibleSMul («M» := M) (M₂ := R)
        («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ)
      _ _ _ productModule.toSMul _ lowCoefficientModule.toSMul _
      innerCarrierModule.toSMul productTower coefficientTower
    let fdown := @LinearMap.restrictScalars («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ) («M» := M) (M₂ := R)
      _ _ _ _ productModule lowCoefficientModule _ _ compatible
      (LinearMap.snd Rᵐᵒᵖ R R)
    let eCoeff : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH R _ _ rawModule lowCoefficientModule :=
      @ULift.moduleEquiv («R» := RHᵐᵒᵖ) («M» := R) _ _ lowCoefficientModule
    let fup := eCoeff.symm.toLinearMap.comp fdown
    let P := LinearMap.ker fup
    let c : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH RHᵐᵒᵖ _ _ rawModule ordinaryModule :=
      @MulOpposite.opLinearEquiv RHᵐᵒᵖ RH _ _ rawModule
    let φ := P.liftQ fup le_rfl
    let d := c.toLinearMap.comp fup
    let hd : P ≤ LinearMap.ker d := LinearMap.ker_le_ker_comp fup c.toLinearMap
    let δ := P.liftQ d hd
    φ.comp P.mkQ = fup ∧ δ.comp P.mkQ = d ∧
      fup.comp P.subtype = 0 ∧ d.comp P.subtype = 0 ∧
      (@Submodule.quotientHomEquivKer RHᵐᵒᵖ RH M RH
        _ _ _ _ productModule rawModule leftRawModule rawCommutes P) φ =
        ⟨fup, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ ∧
      ((@Submodule.quotientHomEquivKer RHᵐᵒᵖ RH M RH
        _ _ _ _ productModule rawModule leftRawModule rawCommutes P)).symm
        ⟨fup, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ = φ ∧
      (@Submodule.quotientHomEquivKer RHᵐᵒᵖ RH M RHᵐᵒᵖ
        _ _ _ _ productModule ordinaryModule leftOrdinaryModule ordinaryCommutes P) δ =
        ⟨d, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hd)⟩ ∧
      ((@Submodule.quotientHomEquivKer RHᵐᵒᵖ RH M RHᵐᵒᵖ
        _ _ _ _ productModule ordinaryModule leftOrdinaryModule ordinaryCommutes P)).symm
        ⟨d, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hd)⟩ = δ := by
  dsimp only
  have hr := factor_controls (S := (ULift.{1} R)) P fup le_rfl
  have ho := @factor_controls (ULift.{1} R)ᵐᵒᵖ (ULift.{1} R) M (ULift.{1} R)ᵐᵒᵖ
    _ _ _ _ productModule ordinaryModule leftOrdinaryModule ordinaryCommutes P d hd
  exact ⟨hr.1, ho.1, hr.2.1, ho.2.1, hr.2.2.1, hr.2.2.2.1,
    ho.2.2.1, ho.2.2.2.1⟩

/-- The raw high coefficient has the forward, inverse and uniqueness controls. -/
theorem raw_correspondence (a : R) :
    let RH := ULift.{1} R
    let downRing : RH →+* R :=
      (ULift.ringEquiv : RH ≃+* R).toRingHom
    let downRingOp : RHᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
    let productModule : Module RHᵐᵒᵖ M := Module.compHom M downRingOp
    let lowCoefficientModule : Module RHᵐᵒᵖ R := Module.compHom R downRingOp
    let innerCarrierModule : Module RHᵐᵒᵖ Rᵐᵒᵖ := Module.compHom Rᵐᵒᵖ downRingOp
    let rawModule : Module RHᵐᵒᵖ RH := Semiring.toOppositeModule
    let leftRawModule : Module RH RH := Semiring.toModule
    let rawCommutes : @SMulCommClass RHᵐᵒᵖ RH RH
        rawModule.toSMul leftRawModule.toSMul :=
      @Semigroup.opposite_smulCommClass RH inferInstance
    let productTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := M) downRingOp
    let coefficientTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := R) downRingOp
    let compatible := @LinearMap.IsScalarTower.compatibleSMul («M» := M) (M₂ := R)
        («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ)
      _ _ _ productModule.toSMul _ lowCoefficientModule.toSMul _
      innerCarrierModule.toSMul productTower coefficientTower
    let fdown := @LinearMap.restrictScalars («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ) («M» := M) (M₂ := R)
      _ _ _ _ productModule lowCoefficientModule _ _ compatible
      (LinearMap.snd Rᵐᵒᵖ R R)
    let eCoeff : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH R _ _ rawModule lowCoefficientModule :=
      @ULift.moduleEquiv («R» := RHᵐᵒᵖ) («M» := R) _ _ lowCoefficientModule
    let fup := eCoeff.symm.toLinearMap.comp fdown
    let P := LinearMap.ker fup
    let fa (a : R) :=
      (LinearMap.mulLeft RHᵐᵒᵖ (ULift.up a : RH)).comp fup
    let ha (a : R) : P ≤ LinearMap.ker (fa a) :=
      LinearMap.ker_le_ker_comp fup (LinearMap.mulLeft RHᵐᵒᵖ (ULift.up a : RH))
    let φa (a : R) := P.liftQ (fa a) (ha a)
    (φa a).comp P.mkQ = fa a ∧
      (fa a).comp P.subtype = 0 ∧
      (@Submodule.quotientHomEquivKer RHᵐᵒᵖ RH M RH
        _ _ _ _ productModule rawModule leftRawModule rawCommutes P) (φa a) =
        ⟨fa a, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp (ha a))⟩ ∧
      ((@Submodule.quotientHomEquivKer RHᵐᵒᵖ RH M RH
        _ _ _ _ productModule rawModule leftRawModule rawCommutes P)).symm
        ⟨fa a, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp (ha a))⟩ = φa a ∧
      ∀ ψ : @LinearMap RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ) (M ⧸ P) RH
          _ _ (@Submodule.Quotient.module RHᵐᵒᵖ M _ _ productModule P) rawModule,
        ψ.comp P.mkQ = fa a → ψ = φa a :=
  factor_controls (S := (ULift.{1} R)) P (fa a) (ha a)

/-- The ordinary high opposite coefficient has separate correspondence controls. -/
theorem ordinary_correspondence (a : R) :
    let RH := ULift.{1} R
    let downRing : RH →+* R :=
      (ULift.ringEquiv : RH ≃+* R).toRingHom
    let downRingOp : RHᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
    let productModule : Module RHᵐᵒᵖ M := Module.compHom M downRingOp
    let lowCoefficientModule : Module RHᵐᵒᵖ R := Module.compHom R downRingOp
    let innerCarrierModule : Module RHᵐᵒᵖ Rᵐᵒᵖ := Module.compHom Rᵐᵒᵖ downRingOp
    let rawModule : Module RHᵐᵒᵖ RH := Semiring.toOppositeModule
    let ordinaryModule : Module RHᵐᵒᵖ RHᵐᵒᵖ := Semiring.toModule
    let leftRawModule : Module RH RH := Semiring.toModule
    let rawCommutes : @SMulCommClass RHᵐᵒᵖ RH RH
        rawModule.toSMul leftRawModule.toSMul :=
      @Semigroup.opposite_smulCommClass RH inferInstance
    let leftOrdinaryModule : Module RH RHᵐᵒᵖ :=
      @MulOpposite.instModule RH RH _ _ leftRawModule
    let ordinaryCommutes : @SMulCommClass RHᵐᵒᵖ RH RHᵐᵒᵖ
        ordinaryModule.toSMul leftOrdinaryModule.toSMul :=
      @MulOpposite.instSMulCommClass RHᵐᵒᵖ RH RH
        rawModule.toSMul leftRawModule.toSMul rawCommutes
    let productTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := M) downRingOp
    let coefficientTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := R) downRingOp
    let compatible := @LinearMap.IsScalarTower.compatibleSMul («M» := M) (M₂ := R)
        («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ)
      _ _ _ productModule.toSMul _ lowCoefficientModule.toSMul _
      innerCarrierModule.toSMul productTower coefficientTower
    let fdown := @LinearMap.restrictScalars («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ) («M» := M) (M₂ := R)
      _ _ _ _ productModule lowCoefficientModule _ _ compatible
      (LinearMap.snd Rᵐᵒᵖ R R)
    let eCoeff : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH R _ _ rawModule lowCoefficientModule :=
      @ULift.moduleEquiv («R» := RHᵐᵒᵖ) («M» := R) _ _ lowCoefficientModule
    let fup := eCoeff.symm.toLinearMap.comp fdown
    let P := LinearMap.ker fup
    let c : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH RHᵐᵒᵖ _ _ rawModule ordinaryModule :=
      @MulOpposite.opLinearEquiv RHᵐᵒᵖ RH _ _ rawModule
    let fa (a : R) :=
      (LinearMap.mulLeft RHᵐᵒᵖ (ULift.up a : RH)).comp fup
    let da (a : R) := c.toLinearMap.comp (fa a)
    let ha (a : R) : P ≤ LinearMap.ker (fa a) :=
      LinearMap.ker_le_ker_comp fup (LinearMap.mulLeft RHᵐᵒᵖ (ULift.up a : RH))
    let hda (a : R) : P ≤ LinearMap.ker (da a) :=
      (ha a).trans (LinearMap.ker_le_ker_comp (fa a) c.toLinearMap)
    let δa (a : R) := P.liftQ (da a) (hda a)
    (δa a).comp P.mkQ = da a ∧
      (da a).comp P.subtype = 0 ∧
      (@Submodule.quotientHomEquivKer RHᵐᵒᵖ RH M RHᵐᵒᵖ
        _ _ _ _ productModule ordinaryModule leftOrdinaryModule ordinaryCommutes P) (δa a) =
        ⟨da a, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp (hda a))⟩ ∧
      ((@Submodule.quotientHomEquivKer RHᵐᵒᵖ RH M RHᵐᵒᵖ
        _ _ _ _ productModule ordinaryModule leftOrdinaryModule ordinaryCommutes P)).symm
        ⟨da a, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp (hda a))⟩ = δa a ∧
      ∀ δ : @LinearMap RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ) (M ⧸ P) RHᵐᵒᵖ
          _ _ (@Submodule.Quotient.module RHᵐᵒᵖ M _ _ productModule P) ordinaryModule,
        δ.comp P.mkQ = da a → δ = δa a :=
  @factor_controls (ULift.{1} R)ᵐᵒᵖ (ULift.{1} R) M (ULift.{1} R)ᵐᵒᵖ
    _ _ _ _ productModule ordinaryModule leftOrdinaryModule ordinaryCommutes P (da a) (hda a)

/-- The high-scalar inverse at the upper-right form is nonzero on the chosen quotient point. -/
theorem inverse_upper_right :
    let RH := ULift.{1} R
    let downRing : RH →+* R :=
      (ULift.ringEquiv : RH ≃+* R).toRingHom
    let downRingOp : RHᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
    let productModule : Module RHᵐᵒᵖ M := Module.compHom M downRingOp
    let lowCoefficientModule : Module RHᵐᵒᵖ R := Module.compHom R downRingOp
    let innerCarrierModule : Module RHᵐᵒᵖ Rᵐᵒᵖ := Module.compHom Rᵐᵒᵖ downRingOp
    let rawModule : Module RHᵐᵒᵖ RH := Semiring.toOppositeModule
    let ordinaryModule : Module RHᵐᵒᵖ RHᵐᵒᵖ := Semiring.toModule
    let leftRawModule : Module RH RH := Semiring.toModule
    let rawCommutes : @SMulCommClass RHᵐᵒᵖ RH RH
        rawModule.toSMul leftRawModule.toSMul :=
      @Semigroup.opposite_smulCommClass RH inferInstance
    let leftOrdinaryModule : Module RH RHᵐᵒᵖ :=
      @MulOpposite.instModule RH RH _ _ leftRawModule
    let ordinaryCommutes : @SMulCommClass RHᵐᵒᵖ RH RHᵐᵒᵖ
        ordinaryModule.toSMul leftOrdinaryModule.toSMul :=
      @MulOpposite.instSMulCommClass RHᵐᵒᵖ RH RH
        rawModule.toSMul leftRawModule.toSMul rawCommutes
    let productTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := M) downRingOp
    let coefficientTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := R) downRingOp
    let compatible := @LinearMap.IsScalarTower.compatibleSMul («M» := M) (M₂ := R)
        («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ)
      _ _ _ productModule.toSMul _ lowCoefficientModule.toSMul _
      innerCarrierModule.toSMul productTower coefficientTower
    let fdown := @LinearMap.restrictScalars («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ) («M» := M) (M₂ := R)
      _ _ _ _ productModule lowCoefficientModule _ _ compatible
      (LinearMap.snd Rᵐᵒᵖ R R)
    let eCoeff : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH R _ _ rawModule lowCoefficientModule :=
      @ULift.moduleEquiv («R» := RHᵐᵒᵖ) («M» := R) _ _ lowCoefficientModule
    let fup := eCoeff.symm.toLinearMap.comp fdown
    let P := LinearMap.ker fup
    let c : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH RHᵐᵒᵖ _ _ rawModule ordinaryModule :=
      @MulOpposite.opLinearEquiv RHᵐᵒᵖ RH _ _ rawModule
    let fa (a : R) :=
      (LinearMap.mulLeft RHᵐᵒᵖ (ULift.up a : RH)).comp fup
    let da (a : R) := c.toLinearMap.comp (fa a)
    let ha (a : R) : P ≤ LinearMap.ker (fa a) :=
      LinearMap.ker_le_ker_comp fup (LinearMap.mulLeft RHᵐᵒᵖ (ULift.up a : RH))
    let hda (a : R) : P ≤ LinearMap.ker (da a) :=
      (ha a).trans (LinearMap.ker_le_ker_comp (fa a) c.toLinearMap)
    let w := P.mkQ (0, 1)
    ((@Submodule.quotientHomEquivKer RHᵐᵒᵖ RH M RH
        _ _ _ _ productModule rawModule leftRawModule rawCommutes P)).symm
        ⟨fa q, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp (ha q))⟩ w = (ULift.up q : RH) ∧
      ((@Submodule.quotientHomEquivKer RHᵐᵒᵖ RH M RHᵐᵒᵖ
        _ _ _ _ productModule ordinaryModule leftOrdinaryModule ordinaryCommutes P)).symm
        ⟨da q, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp (hda q))⟩ w = op (ULift.up q : RH) ∧
      (ULift.up q : RH) ≠ 0 := by
  dsimp only
  rw [(raw_correspondence q).2.2.2.1, (ordinary_correspondence q).2.2.2.1]
  refine ⟨?_, ?_, ?_⟩
  · change (ULift.up (q * 1) : (ULift.{1} R)) = ULift.up q
    exact congrArg ULift.up (mul_one q)
  · change op (ULift.up (q * 1) : (ULift.{1} R)) = op (ULift.up q : (ULift.{1} R))
    exact congrArg (fun a : R => op (ULift.up a : (ULift.{1} R))) (mul_one q)
  · intro h
    exact q_ne_zero (congrArg ULift.down h)

/-- Canonical left multiplication differs from reversed multiplication in both coefficients. -/
theorem coefficient_order :
    let RH := ULift.{1} R
    let downRing : RH →+* R :=
      (ULift.ringEquiv : RH ≃+* R).toRingHom
    let downRingOp : RHᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
    let productModule : Module RHᵐᵒᵖ M := Module.compHom M downRingOp
    let lowCoefficientModule : Module RHᵐᵒᵖ R := Module.compHom R downRingOp
    let innerCarrierModule : Module RHᵐᵒᵖ Rᵐᵒᵖ := Module.compHom Rᵐᵒᵖ downRingOp
    let rawModule : Module RHᵐᵒᵖ RH := Semiring.toOppositeModule
    let ordinaryModule : Module RHᵐᵒᵖ RHᵐᵒᵖ := Semiring.toModule
    let leftRawModule : Module RH RH := Semiring.toModule
    let rawCommutes : @SMulCommClass RHᵐᵒᵖ RH RH
        rawModule.toSMul leftRawModule.toSMul :=
      @Semigroup.opposite_smulCommClass RH inferInstance
    let leftOrdinaryModule : Module RH RHᵐᵒᵖ :=
      @MulOpposite.instModule RH RH _ _ leftRawModule
    let ordinaryCommutes : @SMulCommClass RHᵐᵒᵖ RH RHᵐᵒᵖ
        ordinaryModule.toSMul leftOrdinaryModule.toSMul :=
      @MulOpposite.instSMulCommClass RHᵐᵒᵖ RH RH
        rawModule.toSMul leftRawModule.toSMul rawCommutes
    let productTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := M) downRingOp
    let coefficientTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := R) downRingOp
    let compatible := @LinearMap.IsScalarTower.compatibleSMul («M» := M) (M₂ := R)
        («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ)
      _ _ _ productModule.toSMul _ lowCoefficientModule.toSMul _
      innerCarrierModule.toSMul productTower coefficientTower
    let fdown := @LinearMap.restrictScalars («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ) («M» := M) (M₂ := R)
      _ _ _ _ productModule lowCoefficientModule _ _ compatible
      (LinearMap.snd Rᵐᵒᵖ R R)
    let eCoeff : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH R _ _ rawModule lowCoefficientModule :=
      @ULift.moduleEquiv («R» := RHᵐᵒᵖ) («M» := R) _ _ lowCoefficientModule
    let fup := eCoeff.symm.toLinearMap.comp fdown
    let P := LinearMap.ker fup
    let c : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH RHᵐᵒᵖ _ _ rawModule ordinaryModule :=
      @MulOpposite.opLinearEquiv RHᵐᵒᵖ RH _ _ rawModule
    let fa (a : R) :=
      (LinearMap.mulLeft RHᵐᵒᵖ (ULift.up a : RH)).comp fup
    let da (a : R) := c.toLinearMap.comp (fa a)
    let ha (a : R) : P ≤ LinearMap.ker (fa a) :=
      LinearMap.ker_le_ker_comp fup (LinearMap.mulLeft RHᵐᵒᵖ (ULift.up a : RH))
    let hda (a : R) : P ≤ LinearMap.ker (da a) :=
      (ha a).trans (LinearMap.ker_le_ker_comp (fa a) c.toLinearMap)
    let φa (a : R) := P.liftQ (fa a) (ha a)
    let δa (a : R) := P.liftQ (da a) (hda a)
    let w := P.mkQ (0, 1)
    let rawFormsModule := @LinearMap.module («R» := RHᵐᵒᵖ) (R₂ := RHᵐᵒᵖ)
      (S := RH) («M» := M) (M₂ := RH)
      _ _ _ _ productModule rawModule (RingHom.id RHᵐᵒᵖ) _ leftRawModule rawCommutes
    let ordinaryFormsModule := @LinearMap.module («R» := RHᵐᵒᵖ) (R₂ := RHᵐᵒᵖ)
      (S := RH) («M» := M) (M₂ := RHᵐᵒᵖ)
      _ _ _ _ productModule ordinaryModule (RingHom.id RHᵐᵒᵖ)
      _ leftOrdinaryModule ordinaryCommutes
    let rawQuotientFormsModule := @LinearMap.module («R» := RHᵐᵒᵖ) (R₂ := RHᵐᵒᵖ)
      (S := RH) («M» := M ⧸ P) (M₂ := RH)
      _ _ _ _ (@Submodule.Quotient.module RHᵐᵒᵖ M _ _ productModule P)
      rawModule (RingHom.id RHᵐᵒᵖ) _ leftRawModule rawCommutes
    let ordinaryQuotientFormsModule := @LinearMap.module («R» := RHᵐᵒᵖ) (R₂ := RHᵐᵒᵖ)
      (S := RH) («M» := M ⧸ P) (M₂ := RHᵐᵒᵖ)
      _ _ _ _ (@Submodule.Quotient.module RHᵐᵒᵖ M _ _ productModule P)
      ordinaryModule (RingHom.id RHᵐᵒᵖ) _ leftOrdinaryModule ordinaryCommutes
    (@SMul.smul RH _ rawFormsModule.toSMul (ULift.up p : RH) (fa q)) (0, 1) = (ULift.up q : RH) ∧
      fa q (0, 1) * (ULift.up p : RH) = 0 ∧
      (@SMul.smul RH _ ordinaryFormsModule.toSMul (ULift.up p : RH) (da q)) (0, 1) =
        op (ULift.up q : RH) ∧
      op (unop (da q (0, 1)) * (ULift.up p : RH)) = 0 ∧
      (@SMul.smul RH _ rawQuotientFormsModule.toSMul (ULift.up p : RH) (φa q)) w =
        (ULift.up q : RH) ∧
      (@SMul.smul RH _ ordinaryQuotientFormsModule.toSMul (ULift.up p : RH) (δa q)) w =
        op (ULift.up q : RH) ∧
      (ULift.up q : RH) ≠ 0 := by
  dsimp only
  change (ULift.up (p * (q * 1)) : (ULift.{1} R)) = ULift.up q ∧
    (ULift.up ((q * 1) * p) : (ULift.{1} R)) = 0 ∧
    op (ULift.up (p * (q * 1)) : (ULift.{1} R)) = op (ULift.up q : (ULift.{1} R)) ∧
    op (ULift.up ((q * 1) * p) : (ULift.{1} R)) = 0 ∧
    (ULift.up (p * (q * 1)) : (ULift.{1} R)) = ULift.up q ∧
    op (ULift.up (p * (q * 1)) : (ULift.{1} R)) = op (ULift.up q : (ULift.{1} R)) ∧
    (ULift.up q : (ULift.{1} R)) ≠ 0
  have hpq : (ULift.up (p * (q * 1)) : ULift.{1} R) = ULift.up q :=
    congrArg ULift.up (by simp only [mul_one, pq])
  have hqp : (ULift.up ((q * 1) * p) : ULift.{1} R) = 0 := by
    change (ULift.up ((q * 1) * p) : ULift.{1} R) = ULift.up 0
    exact congrArg ULift.up (by simp only [mul_one, qp])
  have hnq : (ULift.up q : ULift.{1} R) ≠ 0 := fun h =>
    q_ne_zero (congrArg ULift.down h)
  exact ⟨hpq, hqp, congrArg op hpq, congrArg op hqp, hpq, congrArg op hpq, hnq⟩

/-- Left multiplication by the lifted diagonal unit moves all identity-valued forms. -/
theorem coefficient_movement :
    let RH := ULift.{1} R
    let downRing : RH →+* R :=
      (ULift.ringEquiv : RH ≃+* R).toRingHom
    let downRingOp : RHᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
    let productModule : Module RHᵐᵒᵖ M := Module.compHom M downRingOp
    let lowCoefficientModule : Module RHᵐᵒᵖ R := Module.compHom R downRingOp
    let innerCarrierModule : Module RHᵐᵒᵖ Rᵐᵒᵖ := Module.compHom Rᵐᵒᵖ downRingOp
    let rawModule : Module RHᵐᵒᵖ RH := Semiring.toOppositeModule
    let ordinaryModule : Module RHᵐᵒᵖ RHᵐᵒᵖ := Semiring.toModule
    let leftRawModule : Module RH RH := Semiring.toModule
    let rawCommutes : @SMulCommClass RHᵐᵒᵖ RH RH
        rawModule.toSMul leftRawModule.toSMul :=
      @Semigroup.opposite_smulCommClass RH inferInstance
    let leftOrdinaryModule : Module RH RHᵐᵒᵖ :=
      @MulOpposite.instModule RH RH _ _ leftRawModule
    let ordinaryCommutes : @SMulCommClass RHᵐᵒᵖ RH RHᵐᵒᵖ
        ordinaryModule.toSMul leftOrdinaryModule.toSMul :=
      @MulOpposite.instSMulCommClass RHᵐᵒᵖ RH RH
        rawModule.toSMul leftRawModule.toSMul rawCommutes
    let productTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := M) downRingOp
    let coefficientTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := R) downRingOp
    let compatible := @LinearMap.IsScalarTower.compatibleSMul («M» := M) (M₂ := R)
        («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ)
      _ _ _ productModule.toSMul _ lowCoefficientModule.toSMul _
      innerCarrierModule.toSMul productTower coefficientTower
    let fdown := @LinearMap.restrictScalars («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ) («M» := M) (M₂ := R)
      _ _ _ _ productModule lowCoefficientModule _ _ compatible
      (LinearMap.snd Rᵐᵒᵖ R R)
    let eCoeff : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH R _ _ rawModule lowCoefficientModule :=
      @ULift.moduleEquiv («R» := RHᵐᵒᵖ) («M» := R) _ _ lowCoefficientModule
    let fup := eCoeff.symm.toLinearMap.comp fdown
    let P := LinearMap.ker fup
    let c : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH RHᵐᵒᵖ _ _ rawModule ordinaryModule :=
      @MulOpposite.opLinearEquiv RHᵐᵒᵖ RH _ _ rawModule
    let fa (a : R) :=
      (LinearMap.mulLeft RHᵐᵒᵖ (ULift.up a : RH)).comp fup
    let da (a : R) := c.toLinearMap.comp (fa a)
    let ha (a : R) : P ≤ LinearMap.ker (fa a) :=
      LinearMap.ker_le_ker_comp fup (LinearMap.mulLeft RHᵐᵒᵖ (ULift.up a : RH))
    let hda (a : R) : P ≤ LinearMap.ker (da a) :=
      (ha a).trans (LinearMap.ker_le_ker_comp (fa a) c.toLinearMap)
    let φa (a : R) := P.liftQ (fa a) (ha a)
    let δa (a : R) := P.liftQ (da a) (hda a)
    let w := P.mkQ (0, 1)
    let rawFormsModule := @LinearMap.module («R» := RHᵐᵒᵖ) (R₂ := RHᵐᵒᵖ)
      (S := RH) («M» := M) (M₂ := RH)
      _ _ _ _ productModule rawModule (RingHom.id RHᵐᵒᵖ) _ leftRawModule rawCommutes
    let ordinaryFormsModule := @LinearMap.module («R» := RHᵐᵒᵖ) (R₂ := RHᵐᵒᵖ)
      (S := RH) («M» := M) (M₂ := RHᵐᵒᵖ)
      _ _ _ _ productModule ordinaryModule (RingHom.id RHᵐᵒᵖ)
      _ leftOrdinaryModule ordinaryCommutes
    let rawQuotientFormsModule := @LinearMap.module («R» := RHᵐᵒᵖ) (R₂ := RHᵐᵒᵖ)
      (S := RH) («M» := M ⧸ P) (M₂ := RH)
      _ _ _ _ (@Submodule.Quotient.module RHᵐᵒᵖ M _ _ productModule P)
      rawModule (RingHom.id RHᵐᵒᵖ) _ leftRawModule rawCommutes
    let ordinaryQuotientFormsModule := @LinearMap.module («R» := RHᵐᵒᵖ) (R₂ := RHᵐᵒᵖ)
      (S := RH) («M» := M ⧸ P) (M₂ := RHᵐᵒᵖ)
      _ _ _ _ (@Submodule.Quotient.module RHᵐᵒᵖ M _ _ productModule P)
      ordinaryModule (RingHom.id RHᵐᵒᵖ) _ leftOrdinaryModule ordinaryCommutes
    @SMul.smul RH _ rawFormsModule.toSMul (ULift.up p : RH) (fa 1) = fa p ∧
      fa p ≠ fa 1 ∧ fa p ≠ 0 ∧
      @SMul.smul RH _ ordinaryFormsModule.toSMul (ULift.up p : RH) (da 1) = da p ∧
      da p ≠ da 1 ∧ da p ≠ 0 ∧
      (@SMul.smul RH _ rawQuotientFormsModule.toSMul (ULift.up p : RH) (φa 1)) w =
        (ULift.up p : RH) ∧
      φa p ≠ φa 1 ∧ φa p ≠ 0 ∧
      (@SMul.smul RH _ ordinaryQuotientFormsModule.toSMul (ULift.up p : RH) (δa 1)) w =
        op (ULift.up p : RH) ∧
      δa p ≠ δa 1 ∧ δa p ≠ 0 := by
  dsimp only
  have hfr : fa p ≠ fa 1 := by
    intro h
    apply p_ne_one
    have hv := congrArg ULift.down (LinearMap.congr_fun h (0, 1))
    change p * 1 = 1 * 1 at hv
    simpa only [mul_one] using hv
  have hfd : da p ≠ da 1 := by
    intro h
    apply p_ne_one
    have hv := congrArg (fun z : (ULift.{1} R)ᵐᵒᵖ => (unop z).down)
      (LinearMap.congr_fun h (0, 1))
    change p * 1 = 1 * 1 at hv
    simpa only [mul_one] using hv
  have hφ : φa p ≠ φa 1 := by
    intro h
    apply p_ne_one
    have hv := congrArg ULift.down (LinearMap.congr_fun h w)
    change p * 1 = 1 * 1 at hv
    simpa only [mul_one] using hv
  have hδ : δa p ≠ δa 1 := by
    intro h
    apply p_ne_one
    have hv := congrArg (fun z : (ULift.{1} R)ᵐᵒᵖ => (unop z).down)
      (LinearMap.congr_fun h w)
    change p * 1 = 1 * 1 at hv
    simpa only [mul_one] using hv
  have hnφ := (factor_value_ne_zero P (fa p) (ha p) (0, 1)
    (by
      intro h
      have hv := congrArg ULift.down h
      change p * 1 = 0 at hv
      exact p_ne_zero (by simpa only [mul_one] using hv))).2
  have hnδ := (factor_value_ne_zero P (da p) (hda p) (0, 1)
    (by
      intro h
      have hv := congrArg (fun z : (ULift.{1} R)ᵐᵒᵖ => (unop z).down) h
      change p * 1 = 0 at hv
      exact p_ne_zero (by simpa only [mul_one] using hv))).2
  refine ⟨?_, hfr, ?_, ?_, hfd, ?_, ?_, hφ, hnφ, ?_, hδ, hnδ⟩
  · apply LinearMap.ext
    intro x
    change (ULift.up (p * (1 * x.2)) : (ULift.{1} R)) = ULift.up (p * x.2)
    simp
  · intro h
    apply p_ne_zero
    have hv := congrArg ULift.down (LinearMap.congr_fun h (0, 1))
    change p * 1 = 0 at hv
    simpa only [mul_one] using hv
  · apply LinearMap.ext
    intro x
    change op (ULift.up (p * (1 * x.2)) : (ULift.{1} R)) = op (ULift.up (p * x.2) : (ULift.{1} R))
    simp
  · intro h
    apply p_ne_zero
    have hv := congrArg (fun z : (ULift.{1} R)ᵐᵒᵖ => (unop z).down)
      (LinearMap.congr_fun h (0, 1))
    change p * 1 = 0 at hv
    simpa only [mul_one] using hv
  · change (ULift.up (p * (1 * 1)) : (ULift.{1} R)) = ULift.up p
    simp
  · change op (ULift.up (p * (1 * 1)) : (ULift.{1} R)) = op (ULift.up p : (ULift.{1} R))
    simp

/-- A low generic coefficient under high inner scalars uses outer integer scalars. -/
theorem low_coefficient_correspondence :
    let RH := ULift.{1} R
    let downRing : RH →+* R :=
      (ULift.ringEquiv : RH ≃+* R).toRingHom
    let downRingOp : RHᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
    let productModule : Module RHᵐᵒᵖ M := Module.compHom M downRingOp
    let lowCoefficientModule : Module RHᵐᵒᵖ R := Module.compHom R downRingOp
    let innerCarrierModule : Module RHᵐᵒᵖ Rᵐᵒᵖ := Module.compHom Rᵐᵒᵖ downRingOp
    let productTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := M) downRingOp
    let coefficientTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := R) downRingOp
    let compatible := @LinearMap.IsScalarTower.compatibleSMul («M» := M) (M₂ := R)
        («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ)
      _ _ _ productModule.toSMul _ lowCoefficientModule.toSMul _
      innerCarrierModule.toSMul productTower coefficientTower
    let fdown := @LinearMap.restrictScalars («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ) («M» := M) (M₂ := R)
      _ _ _ _ productModule lowCoefficientModule _ _ compatible
      (LinearMap.snd Rᵐᵒᵖ R R)
    let lowCoefficientCommutes := SMul.comp.smulCommClass (α := R) (β := ℤ) downRingOp
    let PCL := LinearMap.ker fdown
    let ΦCL := PCL.liftQ fdown le_rfl
    ΦCL (PCL.mkQ (0, 1)) = (1 : R) ∧ ΦCL ≠ 0 ∧
      ΦCL.comp PCL.mkQ = fdown ∧ fdown.comp PCL.subtype = 0 ∧
      (@Submodule.quotientHomEquivKer RHᵐᵒᵖ ℤ M R
        _ _ _ _ productModule lowCoefficientModule inferInstance lowCoefficientCommutes PCL) ΦCL =
        ⟨fdown, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ ∧
      ((@Submodule.quotientHomEquivKer RHᵐᵒᵖ ℤ M R
        _ _ _ _ productModule lowCoefficientModule inferInstance lowCoefficientCommutes PCL)).symm
        ⟨fdown, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ = ΦCL ∧
      ∀ ψ : @LinearMap RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ) (M ⧸ PCL) R
          _ _ (@Submodule.Quotient.module RHᵐᵒᵖ M _ _ productModule PCL) lowCoefficientModule,
        ψ.comp PCL.mkQ = fdown → ψ = ΦCL := by
  dsimp only
  have h := factor_controls (S := ℤ) (LinearMap.ker fdown) fdown le_rfl
  exact ⟨rfl, (factor_value_ne_zero (LinearMap.ker fdown) fdown le_rfl (0, 1)
    (by change (1 : R) ≠ 0; exact one_ne_zero)).2, h⟩

private theorem family_injective :
    Function.Injective fa ∧ Function.Injective da ∧
      Function.Injective φa ∧ Function.Injective δa := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h
    have hv := congrArg ULift.down (LinearMap.congr_fun h (0, 1))
    change a * 1 = b * 1 at hv
    simpa only [mul_one] using hv
  · intro a b h
    have hv := congrArg (fun z : (ULift.{1} R)ᵐᵒᵖ => (unop z).down)
      (LinearMap.congr_fun h (0, 1))
    change a * 1 = b * 1 at hv
    simpa only [mul_one] using hv
  · intro a b h
    have hv := congrArg ULift.down (LinearMap.congr_fun h w)
    change a * 1 = b * 1 at hv
    simpa only [mul_one] using hv
  · intro a b h
    have hv := congrArg (fun z : (ULift.{1} R)ᵐᵒᵖ => (unop z).down)
      (LinearMap.congr_fun h w)
    change a * 1 = b * 1 at hv
    simpa only [mul_one] using hv

/-- The high-scalar raw and ordinary families at the three matrix units remain separated. -/
theorem unit_forms_distinct :
    let RH := ULift.{1} R
    let downRing : RH →+* R :=
      (ULift.ringEquiv : RH ≃+* R).toRingHom
    let downRingOp : RHᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
    let productModule : Module RHᵐᵒᵖ M := Module.compHom M downRingOp
    let lowCoefficientModule : Module RHᵐᵒᵖ R := Module.compHom R downRingOp
    let innerCarrierModule : Module RHᵐᵒᵖ Rᵐᵒᵖ := Module.compHom Rᵐᵒᵖ downRingOp
    let rawModule : Module RHᵐᵒᵖ RH := Semiring.toOppositeModule
    let ordinaryModule : Module RHᵐᵒᵖ RHᵐᵒᵖ := Semiring.toModule
    let productTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := M) downRingOp
    let coefficientTower := SMul.comp.isScalarTower (α := Rᵐᵒᵖ) (β := R) downRingOp
    let compatible := @LinearMap.IsScalarTower.compatibleSMul («M» := M) (M₂ := R)
        («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ)
      _ _ _ productModule.toSMul _ lowCoefficientModule.toSMul _
      innerCarrierModule.toSMul productTower coefficientTower
    let fdown := @LinearMap.restrictScalars («R» := RHᵐᵒᵖ) (S := Rᵐᵒᵖ) («M» := M) (M₂ := R)
      _ _ _ _ productModule lowCoefficientModule _ _ compatible
      (LinearMap.snd Rᵐᵒᵖ R R)
    let eCoeff : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH R _ _ rawModule lowCoefficientModule :=
      @ULift.moduleEquiv («R» := RHᵐᵒᵖ) («M» := R) _ _ lowCoefficientModule
    let fup := eCoeff.symm.toLinearMap.comp fdown
    let P := LinearMap.ker fup
    let c : @LinearEquiv RHᵐᵒᵖ RHᵐᵒᵖ _ _ (RingHom.id RHᵐᵒᵖ)
        (RingHom.id RHᵐᵒᵖ) _ _ RH RHᵐᵒᵖ _ _ rawModule ordinaryModule :=
      @MulOpposite.opLinearEquiv RHᵐᵒᵖ RH _ _ rawModule
    let fa (a : R) :=
      (LinearMap.mulLeft RHᵐᵒᵖ (ULift.up a : RH)).comp fup
    let da (a : R) := c.toLinearMap.comp (fa a)
    let ha (a : R) : P ≤ LinearMap.ker (fa a) :=
      LinearMap.ker_le_ker_comp fup (LinearMap.mulLeft RHᵐᵒᵖ (ULift.up a : RH))
    let hda (a : R) : P ≤ LinearMap.ker (da a) :=
      (ha a).trans (LinearMap.ker_le_ker_comp (fa a) c.toLinearMap)
    let φa (a : R) := P.liftQ (fa a) (ha a)
    let δa (a : R) := P.liftQ (da a) (hda a)
    (fa 1 ≠ 0 ∧ fa p ≠ 0 ∧ fa q ≠ 0 ∧
      fa 1 ≠ fa p ∧ fa 1 ≠ fa q ∧ fa p ≠ fa q) ∧
      (da 1 ≠ 0 ∧ da p ≠ 0 ∧ da q ≠ 0 ∧
        da 1 ≠ da p ∧ da 1 ≠ da q ∧ da p ≠ da q) ∧
      (φa 1 ≠ 0 ∧ φa p ≠ 0 ∧ φa q ≠ 0 ∧
        φa 1 ≠ φa p ∧ φa 1 ≠ φa q ∧ φa p ≠ φa q) ∧
      (δa 1 ≠ 0 ∧ δa p ≠ 0 ∧ δa q ≠ 0 ∧
        δa 1 ≠ δa p ∧ δa 1 ≠ δa q ∧ δa p ≠ δa q) := by
  dsimp only
  refine ⟨separated_triple fa family_injective.1 ?_,
    separated_triple da family_injective.2.1 ?_,
    separated_triple φa family_injective.2.2.1 ?_,
    separated_triple δa family_injective.2.2.2 ?_⟩
  · apply LinearMap.ext
    intro x
    change (ULift.up ((0 : R) * x.2) : (ULift.{1} R)) = ULift.up 0
    exact congrArg ULift.up (zero_mul x.2)
  · apply LinearMap.ext
    intro x
    change op (ULift.up ((0 : R) * x.2) : (ULift.{1} R)) = op (ULift.up 0 : ULift.{1} R)
    exact congrArg (fun a : R => op (ULift.up a : ULift.{1} R)) (zero_mul x.2)
  · apply P.linearMap_qext
    apply LinearMap.ext
    intro x
    change (ULift.up ((0 : R) * x.2) : (ULift.{1} R)) = ULift.up 0
    exact congrArg ULift.up (zero_mul x.2)
  · apply P.linearMap_qext
    apply LinearMap.ext
    intro x
    change op (ULift.up ((0 : R) * x.2) : (ULift.{1} R)) = op (ULift.up 0 : ULift.{1} R)
    exact congrArg (fun a : R => op (ULift.up a : ULift.{1} R)) (zero_mul x.2)

/-- The corresponding high-coefficient right-multiplication function is not right-linear. -/
theorem right_multiplication_not_linear :
    let RH := ULift.{1} R
    let downRing : RH →+* R :=
      (ULift.ringEquiv : RH ≃+* R).toRingHom
    let downRingOp : RHᵐᵒᵖ →+* Rᵐᵒᵖ := RingHom.op downRing
    let productModule : Module RHᵐᵒᵖ M := Module.compHom M downRingOp
    let g : M → RH := fun z => ULift.up (z.2 * p)
    ¬ ∀ (s : RHᵐᵒᵖ) (z : M), g (@SMul.smul RHᵐᵒᵖ M productModule.toSMul s z) = s • g z := by
  dsimp only
  intro h
  have hv := congrArg ULift.down (h (op (ULift.up q : (ULift.{1} R))) (0, 1))
  change (1 * q) * p = (1 * p) * q at hv
  have hz : (0 : R) = q := by simpa only [one_mul, qp, pq] using hv
  exact q_ne_zero hz.symm

end LiftedScalar

namespace LiftedCoefficient

local notation "M" => R × R

private abbrev f : M →ₗ[Rᵐᵒᵖ] (ULift.{1} R) :=
  (ULift.moduleEquiv : (ULift.{1} R) ≃ₗ[Rᵐᵒᵖ] R).symm.toLinearMap.comp
    (LinearMap.snd Rᵐᵒᵖ R R)
private abbrev P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
private abbrev φ : (M ⧸ P) →ₗ[Rᵐᵒᵖ] (ULift.{1} R) := P.liftQ f le_rfl

/-- A coefficient in universe one gives a nonzero form on a universe-zero quotient. -/
theorem quotient_value :
    let CH := ULift.{1} R
    let f : M →ₗ[Rᵐᵒᵖ] CH :=
      (ULift.moduleEquiv : CH ≃ₗ[Rᵐᵒᵖ] R).symm.toLinearMap.comp
        (LinearMap.snd Rᵐᵒᵖ R R)
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    let φ : (M ⧸ P) →ₗ[Rᵐᵒᵖ] CH := P.liftQ f le_rfl
    φ (P.mkQ (0, 1)) = (ULift.up (1 : R) : CH) ∧
      P.mkQ (0, 1) ≠ 0 ∧ φ ≠ 0 := by
  dsimp only
  have h := factor_value_ne_zero P f le_rfl (0, 1)
    (by change (1 : (ULift.{1} R)) ≠ 0; exact one_ne_zero)
  exact ⟨rfl, h⟩

/-- The high generic coefficient uses outer integer scalars in both directions. -/
theorem correspondence :
    let CH := ULift.{1} R
    let f : M →ₗ[Rᵐᵒᵖ] CH :=
      (ULift.moduleEquiv : CH ≃ₗ[Rᵐᵒᵖ] R).symm.toLinearMap.comp
        (LinearMap.snd Rᵐᵒᵖ R R)
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    let φ : (M ⧸ P) →ₗ[Rᵐᵒᵖ] CH := P.liftQ f le_rfl
    φ.comp P.mkQ = f ∧ f.comp P.subtype = 0 ∧
      P.quotientHomEquivKer (S := ℤ) (C := CH) φ =
        ⟨f, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ ∧
      (P.quotientHomEquivKer (S := ℤ) (C := CH)).symm
        ⟨f, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ = φ ∧
      ∀ ψ : (M ⧸ P) →ₗ[Rᵐᵒᵖ] CH, ψ.comp P.mkQ = f → ψ = φ :=
  factor_controls (S := ℤ) P f le_rfl

/-- The inverse correspondence has the specified nonzero lifted coefficient value. -/
theorem inverse_value :
    let CH := ULift.{1} R
    let f : M →ₗ[Rᵐᵒᵖ] CH :=
      (ULift.moduleEquiv : CH ≃ₗ[Rᵐᵒᵖ] R).symm.toLinearMap.comp
        (LinearMap.snd Rᵐᵒᵖ R R)
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    (P.quotientHomEquivKer (S := ℤ) (C := CH)).symm
        ⟨f, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ (P.mkQ (0, 1)) =
      (ULift.up (1 : R) : CH) := by
  dsimp only
  rw [correspondence.2.2.2.1]
  rfl

end LiftedCoefficient

namespace LiftedIndex

private abbrev f :
    ULift.{uM} (ULift.{uI} ℕ → ULift.{uR} R) →ₗ[(ULift.{uR} R)ᵐᵒᵖ] ULift.{uR} R :=
  (LinearMap.proj («R» := (ULift.{uR} R)ᵐᵒᵖ) (ULift.up 0 : ULift.{uI} ℕ)).comp
    (ULift.moduleEquiv : ULift.{uM} (ULift.{uI} ℕ → ULift.{uR} R) ≃ₗ[(ULift.{uR} R)ᵐᵒᵖ]
      (ULift.{uI} ℕ → ULift.{uR} R)).toLinearMap
private abbrev P : Submodule (ULift.{uR} R)ᵐᵒᵖ
    (ULift.{uM} (ULift.{uI} ℕ → ULift.{uR} R)) := LinearMap.ker f
private abbrev c : ULift.{uR} R ≃ₗ[(ULift.{uR} R)ᵐᵒᵖ] (ULift.{uR} R)ᵐᵒᵖ :=
  MulOpposite.opLinearEquiv (ULift.{uR} R)ᵐᵒᵖ
private abbrev d : Module.Dual (ULift.{uR} R)ᵐᵒᵖ
    (ULift.{uM} (ULift.{uI} ℕ → ULift.{uR} R)) := c.toLinearMap.comp f
private theorem hd : P ≤ LinearMap.ker d := LinearMap.ker_le_ker_comp f c.toLinearMap
private abbrev φ :
    (ULift.{uM} (ULift.{uI} ℕ → ULift.{uR} R) ⧸ P) →ₗ[(ULift.{uR} R)ᵐᵒᵖ] ULift.{uR} R :=
  P.liftQ f le_rfl
private abbrev δ : Module.Dual (ULift.{uR} R)ᵐᵒᵖ
    (ULift.{uM} (ULift.{uI} ℕ → ULift.{uR} R) ⧸ P) := P.liftQ d hd
private abbrev x : ULift.{uM} (ULift.{uI} ℕ → ULift.{uR} R) :=
  ULift.up (fun _ : ULift.{uI} ℕ => (1 : ULift.{uR} R))
private abbrev cC : ULift.{uR} R →ₗ[(ULift.{uR} R)ᵐᵒᵖ] ULift.{uC} (ULift.{uR} R) :=
  (ULift.moduleEquiv : ULift.{uC} (ULift.{uR} R) ≃ₗ[(ULift.{uR} R)ᵐᵒᵖ]
    ULift.{uR} R).symm.toLinearMap
private abbrev fC : ULift.{uM} (ULift.{uI} ℕ → ULift.{uR} R) →ₗ[(ULift.{uR} R)ᵐᵒᵖ]
    ULift.{uC} (ULift.{uR} R) := cC.comp f
private theorem hC : P ≤ LinearMap.ker fC := LinearMap.ker_le_ker_comp f cC
private abbrev φC : (ULift.{uM} (ULift.{uI} ℕ → ULift.{uR} R) ⧸ P) →ₗ[(ULift.{uR} R)ᵐᵒᵖ]
    ULift.{uC} (ULift.{uR} R) := P.liftQ fC hC

/-- Independent index, scalar and source lifts have nonzero raw and ordinary forms. -/
theorem quotient_values :
    let RH := ULift.{uR} R
    let I := ULift.{uI} ℕ
    let M := ULift.{uM} (I → RH)
    let f : M →ₗ[RHᵐᵒᵖ] RH :=
      (LinearMap.proj («R» := RHᵐᵒᵖ) (ULift.up 0 : I)).comp
        (ULift.moduleEquiv : M ≃ₗ[RHᵐᵒᵖ] (I → RH)).toLinearMap
    let P : Submodule RHᵐᵒᵖ M := LinearMap.ker f
    let c : RH ≃ₗ[RHᵐᵒᵖ] RHᵐᵒᵖ := MulOpposite.opLinearEquiv RHᵐᵒᵖ
    let d : Module.Dual RHᵐᵒᵖ M := c.toLinearMap.comp f
    let hd : P ≤ LinearMap.ker d := LinearMap.ker_le_ker_comp f c.toLinearMap
    let φ : (M ⧸ P) →ₗ[RHᵐᵒᵖ] RH := P.liftQ f le_rfl
    let δ : Module.Dual RHᵐᵒᵖ (M ⧸ P) := P.liftQ d hd
    let x : M := ULift.up (fun _ : I => (1 : RH))
    f x = (1 : RH) ∧ φ (P.mkQ x) = (1 : RH) ∧
      δ (P.mkQ x) = op (1 : RH) ∧
      P.mkQ x ≠ 0 ∧ φ ≠ 0 ∧ δ ≠ 0 := by
  dsimp only
  have hr := factor_value_ne_zero P f le_rfl x
    (by change (1 : (ULift.{uR} R)) ≠ 0; exact one_ne_zero)
  have ho := factor_value_ne_zero P d hd x
    (by change op (1 : (ULift.{uR} R)) ≠ 0; simp)
  exact ⟨rfl, rfl, rfl, hr.1, hr.2, ho.2⟩

/-- The independent-index raw form has the quotient-Hom forward and inverse controls. -/
theorem raw_correspondence :
    let RH := ULift.{uR} R
    let I := ULift.{uI} ℕ
    let M := ULift.{uM} (I → RH)
    let f : M →ₗ[RHᵐᵒᵖ] RH :=
      (LinearMap.proj («R» := RHᵐᵒᵖ) (ULift.up 0 : I)).comp
        (ULift.moduleEquiv : M ≃ₗ[RHᵐᵒᵖ] (I → RH)).toLinearMap
    let P : Submodule RHᵐᵒᵖ M := LinearMap.ker f
    let φ : (M ⧸ P) →ₗ[RHᵐᵒᵖ] RH := P.liftQ f le_rfl
    φ.comp P.mkQ = f ∧ f.comp P.subtype = 0 ∧
      P.quotientHomEquivKer (S := RH) (C := RH) φ =
        ⟨f, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ ∧
      (P.quotientHomEquivKer (S := RH) (C := RH)).symm
        ⟨f, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ = φ ∧
      ∀ ψ : (M ⧸ P) →ₗ[RHᵐᵒᵖ] RH, ψ.comp P.mkQ = f → ψ = φ :=
  factor_controls (S := (ULift.{uR} R)) P f le_rfl

/-- The independently lifted ordinary dual has its separate correspondence controls. -/
theorem ordinary_correspondence :
    let RH := ULift.{uR} R
    let I := ULift.{uI} ℕ
    let M := ULift.{uM} (I → RH)
    let f : M →ₗ[RHᵐᵒᵖ] RH :=
      (LinearMap.proj («R» := RHᵐᵒᵖ) (ULift.up 0 : I)).comp
        (ULift.moduleEquiv : M ≃ₗ[RHᵐᵒᵖ] (I → RH)).toLinearMap
    let P : Submodule RHᵐᵒᵖ M := LinearMap.ker f
    let c : RH ≃ₗ[RHᵐᵒᵖ] RHᵐᵒᵖ := MulOpposite.opLinearEquiv RHᵐᵒᵖ
    let d : Module.Dual RHᵐᵒᵖ M := c.toLinearMap.comp f
    let hd : P ≤ LinearMap.ker d := LinearMap.ker_le_ker_comp f c.toLinearMap
    let δ : Module.Dual RHᵐᵒᵖ (M ⧸ P) := P.liftQ d hd
    δ.comp P.mkQ = d ∧ d.comp P.subtype = 0 ∧
      P.quotientHomEquivKer (S := RH) (C := RHᵐᵒᵖ) δ =
        ⟨d, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hd)⟩ ∧
      (P.quotientHomEquivKer (S := RH) (C := RHᵐᵒᵖ)).symm
        ⟨d, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hd)⟩ = δ ∧
      ∀ ψ : Module.Dual RHᵐᵒᵖ (M ⧸ P), ψ.comp P.mkQ = d → ψ = δ :=
  factor_controls (S := (ULift.{uR} R)) P d hd

/-- The raw and ordinary inverse values remain nonzero after the independent index lift. -/
theorem inverse_values :
    let RH := ULift.{uR} R
    let I := ULift.{uI} ℕ
    let M := ULift.{uM} (I → RH)
    let f : M →ₗ[RHᵐᵒᵖ] RH :=
      (LinearMap.proj («R» := RHᵐᵒᵖ) (ULift.up 0 : I)).comp
        (ULift.moduleEquiv : M ≃ₗ[RHᵐᵒᵖ] (I → RH)).toLinearMap
    let P : Submodule RHᵐᵒᵖ M := LinearMap.ker f
    let c : RH ≃ₗ[RHᵐᵒᵖ] RHᵐᵒᵖ := MulOpposite.opLinearEquiv RHᵐᵒᵖ
    let d : Module.Dual RHᵐᵒᵖ M := c.toLinearMap.comp f
    let hd : P ≤ LinearMap.ker d := LinearMap.ker_le_ker_comp f c.toLinearMap
    let x : M := ULift.up (fun _ : I => (1 : RH))
    (P.quotientHomEquivKer (S := RH) (C := RH)).symm
        ⟨f, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ (P.mkQ x) = (1 : RH) ∧
      (P.quotientHomEquivKer (S := RH) (C := RHᵐᵒᵖ)).symm
        ⟨d, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hd)⟩ (P.mkQ x) = op (1 : RH) := by
  dsimp only
  rw [raw_correspondence.2.2.2.1, ordinary_correspondence.2.2.2.1]
  exact ⟨rfl, rfl⟩

/-- A further independent coefficient lift has a nonzero value, with outer scalar `ℤ`. -/
theorem coefficient_value :
    let RH := ULift.{uR} R
    let I := ULift.{uI} ℕ
    let M := ULift.{uM} (I → RH)
    let C := ULift.{uC} RH
    let f : M →ₗ[RHᵐᵒᵖ] RH :=
      (LinearMap.proj («R» := RHᵐᵒᵖ) (ULift.up 0 : I)).comp
        (ULift.moduleEquiv : M ≃ₗ[RHᵐᵒᵖ] (I → RH)).toLinearMap
    let P : Submodule RHᵐᵒᵖ M := LinearMap.ker f
    let x : M := ULift.up (fun _ : I => (1 : RH))
    let cC : RH →ₗ[RHᵐᵒᵖ] C :=
      (ULift.moduleEquiv : C ≃ₗ[RHᵐᵒᵖ] RH).symm.toLinearMap
    let fC : M →ₗ[RHᵐᵒᵖ] C := cC.comp f
    let hC : P ≤ LinearMap.ker fC := LinearMap.ker_le_ker_comp f cC
    let φC : (M ⧸ P) →ₗ[RHᵐᵒᵖ] C := P.liftQ fC hC
    φC (P.mkQ x) = (ULift.up (1 : RH) : C) ∧ φC ≠ 0 := by
  dsimp only
  exact ⟨rfl, (factor_value_ne_zero P fC hC x
    (by
      intro h
      exact one_ne_zero (congrArg ULift.down h))).2⟩

/-- Generic lifted coefficients use the integer-linear correspondence, not an outer-ring codec. -/
theorem coefficient_correspondence :
    let RH := ULift.{uR} R
    let I := ULift.{uI} ℕ
    let M := ULift.{uM} (I → RH)
    let C := ULift.{uC} RH
    let f : M →ₗ[RHᵐᵒᵖ] RH :=
      (LinearMap.proj («R» := RHᵐᵒᵖ) (ULift.up 0 : I)).comp
        (ULift.moduleEquiv : M ≃ₗ[RHᵐᵒᵖ] (I → RH)).toLinearMap
    let P : Submodule RHᵐᵒᵖ M := LinearMap.ker f
    let cC : RH →ₗ[RHᵐᵒᵖ] C :=
      (ULift.moduleEquiv : C ≃ₗ[RHᵐᵒᵖ] RH).symm.toLinearMap
    let fC : M →ₗ[RHᵐᵒᵖ] C := cC.comp f
    let hC : P ≤ LinearMap.ker fC := LinearMap.ker_le_ker_comp f cC
    let φC : (M ⧸ P) →ₗ[RHᵐᵒᵖ] C := P.liftQ fC hC
    φC.comp P.mkQ = fC ∧ fC.comp P.subtype = 0 ∧
      P.quotientHomEquivKer (S := ℤ) (C := C) φC =
        ⟨fC, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hC)⟩ ∧
      (P.quotientHomEquivKer (S := ℤ) (C := C)).symm
        ⟨fC, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hC)⟩ = φC ∧
      ∀ ψ : (M ⧸ P) →ₗ[RHᵐᵒᵖ] C, ψ.comp P.mkQ = fC → ψ = φC :=
  factor_controls (S := ℤ) P fC hC

/-- The inverse with an independent generic coefficient has the lifted identity value. -/
theorem coefficient_inverse_value :
    let RH := ULift.{uR} R
    let I := ULift.{uI} ℕ
    let M := ULift.{uM} (I → RH)
    let C := ULift.{uC} RH
    let f : M →ₗ[RHᵐᵒᵖ] RH :=
      (LinearMap.proj («R» := RHᵐᵒᵖ) (ULift.up 0 : I)).comp
        (ULift.moduleEquiv : M ≃ₗ[RHᵐᵒᵖ] (I → RH)).toLinearMap
    let P : Submodule RHᵐᵒᵖ M := LinearMap.ker f
    let x : M := ULift.up (fun _ : I => (1 : RH))
    let cC : RH →ₗ[RHᵐᵒᵖ] C :=
      (ULift.moduleEquiv : C ≃ₗ[RHᵐᵒᵖ] RH).symm.toLinearMap
    let fC : M →ₗ[RHᵐᵒᵖ] C := cC.comp f
    let hC : P ≤ LinearMap.ker fC := LinearMap.ker_le_ker_comp f cC
    (P.quotientHomEquivKer (S := ℤ) (C := C)).symm
        ⟨fC, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hC)⟩ (P.mkQ x) =
      (ULift.up (1 : RH) : C) := by
  dsimp only
  rw [coefficient_correspondence.2.2.2.1]
  rfl

end LiftedIndex

namespace LiftedInteger

private abbrev f.{vR, vM, vC} : (ULift.{vM} ℤ) →ₗ[(ULift.{vR} ℤ)] (ULift.{vC} ℤ) :=
  (ULift.moduleEquiv.{vR, 0, vC} : (ULift.{vC} ℤ) ≃ₗ[(ULift.{vR} ℤ)] ℤ).symm.toLinearMap.comp
    (ULift.moduleEquiv.{vR, 0, vM} : (ULift.{vM} ℤ) ≃ₗ[(ULift.{vR} ℤ)] ℤ).toLinearMap
private abbrev P.{vR, vM, vC} : Submodule (ULift.{vR} ℤ) (ULift.{vM} ℤ) :=
  LinearMap.ker f.{vR, vM, vC}
private abbrev φ.{vR, vM, vC} :
    ((ULift.{vM} ℤ) ⧸ P.{vR, vM, vC}) →ₗ[(ULift.{vR} ℤ)] (ULift.{vC} ℤ) :=
  (P.{vR, vM, vC}).liftQ f.{vR, vM, vC} le_rfl

/-- Independently lifted integer scalars, source and coefficient give a nonzero quotient form. -/
theorem quotient_value :
    let S₀ := ULift.{uR} ℤ
    let M := ULift.{uM} ℤ
    let C := ULift.{uC} ℤ
    let f : M →ₗ[S₀] C :=
      (ULift.moduleEquiv.{uR, 0, uC} : C ≃ₗ[S₀] ℤ).symm.toLinearMap.comp
        (ULift.moduleEquiv.{uR, 0, uM} : M ≃ₗ[S₀] ℤ).toLinearMap
    let P : Submodule S₀ M := LinearMap.ker f
    let φ : (M ⧸ P) →ₗ[S₀] C := P.liftQ f le_rfl
    f (ULift.up (1 : ℤ)) = (ULift.up (1 : ℤ) : C) ∧
      φ (P.mkQ (ULift.up (1 : ℤ))) = (ULift.up (1 : ℤ) : C) ∧
      P.mkQ (ULift.up (1 : ℤ)) ≠ 0 ∧ φ ≠ 0 := by
  dsimp only
  have h := factor_value_ne_zero P.{uR, uM, uC} f.{uR, uM, uC} le_rfl (ULift.up (1 : ℤ))
    (by change (1 : (ULift.{uC} ℤ)) ≠ 0; exact one_ne_zero)
  exact ⟨rfl, rfl, h⟩

/-- The integer companion has the forward and inverse correspondence over outer `ℤ`. -/
theorem correspondence :
    let S₀ := ULift.{uR} ℤ
    let M := ULift.{uM} ℤ
    let C := ULift.{uC} ℤ
    let f : M →ₗ[S₀] C :=
      (ULift.moduleEquiv.{uR, 0, uC} : C ≃ₗ[S₀] ℤ).symm.toLinearMap.comp
        (ULift.moduleEquiv.{uR, 0, uM} : M ≃ₗ[S₀] ℤ).toLinearMap
    let P : Submodule S₀ M := LinearMap.ker f
    let φ : (M ⧸ P) →ₗ[S₀] C := P.liftQ f le_rfl
    φ.comp P.mkQ = f ∧ f.comp P.subtype = 0 ∧
      P.quotientHomEquivKer (S := ℤ) (C := C) φ =
        ⟨f, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ ∧
      (P.quotientHomEquivKer (S := ℤ) (C := C)).symm
        ⟨f, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ = φ ∧
      ∀ ψ : (M ⧸ P) →ₗ[S₀] C, ψ.comp P.mkQ = f → ψ = φ :=
  factor_controls (S := ℤ) P.{uR, uM, uC} f.{uR, uM, uC} le_rfl

/-- The inverse in the integer companion evaluates to the nonzero lifted identity. -/
theorem inverse_value :
    let S₀ := ULift.{uR} ℤ
    let M := ULift.{uM} ℤ
    let C := ULift.{uC} ℤ
    let f : M →ₗ[S₀] C :=
      (ULift.moduleEquiv.{uR, 0, uC} : C ≃ₗ[S₀] ℤ).symm.toLinearMap.comp
        (ULift.moduleEquiv.{uR, 0, uM} : M ≃ₗ[S₀] ℤ).toLinearMap
    let P : Submodule S₀ M := LinearMap.ker f
    (P.quotientHomEquivKer (S := ℤ) (C := C)).symm
        ⟨f, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ (P.mkQ (ULift.up (1 : ℤ))) =
      (ULift.up (1 : ℤ) : C) := by
  dsimp only
  rw [correspondence.2.2.2.1]
  rfl

end LiftedInteger

namespace LiftedOuterScalar

local notation "M" => R × R

private abbrev downRing : (ULift.{1} ℤ) →+* ℤ :=
  (ULift.ringEquiv : (ULift.{1} ℤ) ≃+* ℤ).toRingHom
private abbrev coefficientModule : Module (ULift.{1} ℤ) R := Module.compHom R downRing
attribute [local instance] coefficientModule

private theorem coefficient_commutes : SMulCommClass Rᵐᵒᵖ (ULift.{1} ℤ) R :=
  SMul.comp.smulCommClass' (α := R) (β := Rᵐᵒᵖ) downRing
attribute [local instance] coefficient_commutes

/-- The stored high outer action is the pullback of integer multiplication. -/
theorem coefficient_action (s : (ULift.{1} ℤ)) (a : R) :
    let SH := ULift.{1} ℤ
    let downRing : SH →+* ℤ :=
      (ULift.ringEquiv : SH ≃+* ℤ).toRingHom
    let coefficientModule : Module SH R := Module.compHom R downRing
    @SMul.smul SH R coefficientModule.toSMul s a = s.down • a := rfl

/-- The non-instance commuting pullback uses precisely the stored coefficient action. -/
theorem commuting_alignment (r : Rᵐᵒᵖ) (s : (ULift.{1} ℤ)) (a : R) :
    let SH := ULift.{1} ℤ
    let downRing : SH →+* ℤ :=
      (ULift.ringEquiv : SH ≃+* ℤ).toRingHom
    let coefficientModule : Module SH R := Module.compHom R downRing
    r • (@SMul.smul SH R coefficientModule.toSMul s a) =
      @SMul.smul SH R coefficientModule.toSMul s (r • a) :=
  @SMulCommClass.smul_comm Rᵐᵒᵖ (ULift.{1} ℤ) R
    inferInstance coefficientModule.toSMul coefficient_commutes r s a

private abbrev f : M →ₗ[Rᵐᵒᵖ] R := LinearMap.snd Rᵐᵒᵖ R R
private abbrev P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
private abbrev φ : (M ⧸ P) →ₗ[Rᵐᵒᵖ] R := P.liftQ f le_rfl
private abbrev w : M ⧸ P := P.mkQ (0, 1)
private abbrev s2 : (ULift.{1} ℤ) := ULift.up 2
private theorem hs2 : P ≤ LinearMap.ker (s2 • f) := by
  intro x hx
  change s2 • f x = 0
  rw [LinearMap.mem_ker.mp hx, smul_zero]

private theorem two_ne_zero : (2 : R) ≠ 0 := by
  intro h
  have he := congrArg (fun a : R => a 0 0) h
  norm_num [Matrix.ofNat_apply] at he
private theorem two_ne_one : (2 : R) ≠ 1 := by
  intro h
  have he := congrArg (fun a : R => a 0 0) h
  norm_num [Matrix.ofNat_apply] at he

/-- The high outer scalar `up 2` moves the projection's value from one to two. -/
theorem doubling_values :
    let SH := ULift.{1} ℤ
    let downRing : SH →+* ℤ :=
      (ULift.ringEquiv : SH ≃+* ℤ).toRingHom
    let f : M →ₗ[Rᵐᵒᵖ] R := LinearMap.snd Rᵐᵒᵖ R R
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    let φ : (M ⧸ P) →ₗ[Rᵐᵒᵖ] R := P.liftQ f le_rfl
    let w : M ⧸ P := P.mkQ (0, 1)
    let s2 : SH := ULift.up 2
    let sf := @SMul.smul SH (M →ₗ[Rᵐᵒᵖ] R)
      (Module.compHom (M →ₗ[Rᵐᵒᵖ] R) downRing).toSMul s2 f
    let sφ := @SMul.smul SH ((M ⧸ P) →ₗ[Rᵐᵒᵖ] R)
      (Module.compHom ((M ⧸ P) →ₗ[Rᵐᵒᵖ] R) downRing).toSMul s2 φ
    sf (0, 1) = (2 : R) ∧ sφ w = (2 : R) ∧
      sf ≠ 0 ∧ sf ≠ f ∧ sφ ≠ 0 ∧ sφ ≠ φ := by
  dsimp only
  let sf := @SMul.smul (ULift.{1} ℤ) (M →ₗ[Rᵐᵒᵖ] R)
    (Module.compHom (M →ₗ[Rᵐᵒᵖ] R) downRing).toSMul s2 f
  let sφ := @SMul.smul (ULift.{1} ℤ) ((M ⧸ P) →ₗ[Rᵐᵒᵖ] R)
    (Module.compHom ((M ⧸ P) →ₗ[Rᵐᵒᵖ] R) downRing).toSMul s2 φ
  have hf : sf (0, 1) = (2 : R) := by
    change (2 : ℤ) • (1 : R) = (2 : R)
    simp
  have hφ : sφ w = (2 : R) := hf
  refine ⟨hf, hφ, ?_, ?_, ?_, ?_⟩
  · intro h
    exact two_ne_zero (hf.symm.trans (LinearMap.congr_fun h (0, 1)))
  · intro h
    exact two_ne_one (hf.symm.trans (LinearMap.congr_fun h (0, 1)))
  · intro h
    exact two_ne_zero (hφ.symm.trans (LinearMap.congr_fun h w))
  · intro h
    exact two_ne_one (hφ.symm.trans (LinearMap.congr_fun h w))

/-- The high outer-scalar correspondence is applied without giving the source that action. -/
theorem correspondence :
    let SH := ULift.{1} ℤ
    let downRing : SH →+* ℤ :=
      (ULift.ringEquiv : SH ≃+* ℤ).toRingHom
    let coefficientModule : Module SH R := Module.compHom R downRing
    let coefficient_commutes : SMulCommClass Rᵐᵒᵖ SH R :=
      SMul.comp.smulCommClass' (α := R) (β := Rᵐᵒᵖ) downRing
    let f : M →ₗ[Rᵐᵒᵖ] R := LinearMap.snd Rᵐᵒᵖ R R
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    let φ : (M ⧸ P) →ₗ[Rᵐᵒᵖ] R := P.liftQ f le_rfl
    φ.comp P.mkQ = f ∧ f.comp P.subtype = 0 ∧
      (@Submodule.quotientHomEquivKer Rᵐᵒᵖ SH M R
        _ _ _ _ inferInstance inferInstance coefficientModule coefficient_commutes P) φ =
        ⟨f, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ ∧
      ((@Submodule.quotientHomEquivKer Rᵐᵒᵖ SH M R
        _ _ _ _ inferInstance inferInstance coefficientModule coefficient_commutes P)).symm
        ⟨f, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp le_rfl)⟩ = φ ∧
      ∀ ψ : (M ⧸ P) →ₗ[Rᵐᵒᵖ] R, ψ.comp P.mkQ = f → ψ = φ :=
  @factor_controls Rᵐᵒᵖ (ULift.{1} ℤ) M R
    _ _ _ _ inferInstance inferInstance coefficientModule coefficient_commutes P f le_rfl

/-- The doubled form has the same controls, so the high outer action is used by the API. -/
theorem doubling_correspondence :
    let SH := ULift.{1} ℤ
    let downRing : SH →+* ℤ :=
      (ULift.ringEquiv : SH ≃+* ℤ).toRingHom
    let coefficientModule : Module SH R := Module.compHom R downRing
    let coefficient_commutes : SMulCommClass Rᵐᵒᵖ SH R :=
      SMul.comp.smulCommClass' (α := R) (β := Rᵐᵒᵖ) downRing
    let f : M →ₗ[Rᵐᵒᵖ] R := LinearMap.snd Rᵐᵒᵖ R R
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    let s2 : SH := ULift.up 2
    let sf := @SMul.smul SH (M →ₗ[Rᵐᵒᵖ] R)
      (Module.compHom (M →ₗ[Rᵐᵒᵖ] R) downRing).toSMul s2 f
    let hs2 : P ≤ LinearMap.ker sf := by
      intro x hx
      change (2 : ℤ) • f x = 0
      rw [LinearMap.mem_ker.mp hx, smul_zero]
    (P.liftQ sf hs2).comp P.mkQ = sf ∧
      sf.comp P.subtype = 0 ∧
      (@Submodule.quotientHomEquivKer Rᵐᵒᵖ SH M R
        _ _ _ _ inferInstance inferInstance coefficientModule coefficient_commutes P)
          (P.liftQ sf hs2) =
        ⟨sf, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hs2)⟩ ∧
      ((@Submodule.quotientHomEquivKer Rᵐᵒᵖ SH M R
        _ _ _ _ inferInstance inferInstance coefficientModule coefficient_commutes P)).symm
        ⟨sf, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hs2)⟩ =
          P.liftQ sf hs2 ∧
      ∀ ψ : (M ⧸ P) →ₗ[Rᵐᵒᵖ] R,
        ψ.comp P.mkQ = sf → ψ = P.liftQ sf hs2 := by
  dsimp only
  let sf := @SMul.smul (ULift.{1} ℤ) (M →ₗ[Rᵐᵒᵖ] R)
    (Module.compHom (M →ₗ[Rᵐᵒᵖ] R) downRing).toSMul s2 f
  have hsf : P ≤ LinearMap.ker sf := by
    intro x hx
    change (2 : ℤ) • f x = 0
    rw [LinearMap.mem_ker.mp hx, smul_zero]
  exact @factor_controls Rᵐᵒᵖ (ULift.{1} ℤ) M R
    _ _ _ _ inferInstance inferInstance coefficientModule coefficient_commutes P sf hsf

/-- Forward and inverse at the moving form compute the nonzero value two. -/
theorem doubling_forward_inverse :
    let SH := ULift.{1} ℤ
    let downRing : SH →+* ℤ :=
      (ULift.ringEquiv : SH ≃+* ℤ).toRingHom
    let coefficientModule : Module SH R := Module.compHom R downRing
    let coefficient_commutes : SMulCommClass Rᵐᵒᵖ SH R :=
      SMul.comp.smulCommClass' (α := R) (β := Rᵐᵒᵖ) downRing
    let f : M →ₗ[Rᵐᵒᵖ] R := LinearMap.snd Rᵐᵒᵖ R R
    let P : Submodule Rᵐᵒᵖ M := LinearMap.ker f
    let φ : (M ⧸ P) →ₗ[Rᵐᵒᵖ] R := P.liftQ f le_rfl
    let w : M ⧸ P := P.mkQ (0, 1)
    let s2 : SH := ULift.up 2
    let sf := @SMul.smul SH (M →ₗ[Rᵐᵒᵖ] R)
      (Module.compHom (M →ₗ[Rᵐᵒᵖ] R) downRing).toSMul s2 f
    let sφ := @SMul.smul SH ((M ⧸ P) →ₗ[Rᵐᵒᵖ] R)
      (Module.compHom ((M ⧸ P) →ₗ[Rᵐᵒᵖ] R) downRing).toSMul s2 φ
    let hs2 : P ≤ LinearMap.ker sf := by
      intro x hx
      change (2 : ℤ) • f x = 0
      rw [LinearMap.mem_ker.mp hx, smul_zero]
    (@Submodule.quotientHomEquivKer Rᵐᵒᵖ SH M R
        _ _ _ _ inferInstance inferInstance coefficientModule coefficient_commutes P) sφ =
        ⟨sf, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hs2)⟩ ∧
      ((@Submodule.quotientHomEquivKer Rᵐᵒᵖ SH M R
        _ _ _ _ inferInstance inferInstance coefficientModule coefficient_commutes P)).symm
        ⟨sf, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hs2)⟩ = sφ ∧
      ((@Submodule.quotientHomEquivKer Rᵐᵒᵖ SH M R
        _ _ _ _ inferInstance inferInstance coefficientModule coefficient_commutes P)).symm
        ⟨sf, (LinearMap.le_ker_iff_comp_subtype_eq_zero.mp hs2)⟩ w = (2 : R) ∧
      (2 : R) ≠ 0 := by
  dsimp only
  let sf := @SMul.smul (ULift.{1} ℤ) (M →ₗ[Rᵐᵒᵖ] R)
    (Module.compHom (M →ₗ[Rᵐᵒᵖ] R) downRing).toSMul s2 f
  let sφ := @SMul.smul (ULift.{1} ℤ) ((M ⧸ P) →ₗ[Rᵐᵒᵖ] R)
    (Module.compHom ((M ⧸ P) →ₗ[Rᵐᵒᵖ] R) downRing).toSMul s2 φ
  have hsf : P ≤ LinearMap.ker sf := by
    intro x hx
    change (2 : ℤ) • f x = 0
    rw [LinearMap.mem_ker.mp hx, smul_zero]
  have hfactor : sφ = P.liftQ sf hsf := by
    apply P.linearMap_qext
    apply LinearMap.ext
    intro x
    rfl
  have hc := @factor_controls Rᵐᵒᵖ (ULift.{1} ℤ) M R
    _ _ _ _ inferInstance inferInstance coefficientModule coefficient_commutes P sf hsf
  let E := @Submodule.quotientHomEquivKer Rᵐᵒᵖ (ULift.{1} ℤ) M R
    _ _ _ _ inferInstance inferInstance coefficientModule coefficient_commutes P
  have hinverse := hc.2.2.2.1.trans hfactor.symm
  refine ⟨(congrArg E hfactor).trans hc.2.2.1, hinverse, ?_, two_ne_zero⟩
  exact (LinearMap.congr_fun hinverse w).trans doubling_values.1

end LiftedOuterScalar

end ProjectiveModulesTests.QuotientHomUniverseClient
