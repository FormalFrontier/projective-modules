/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Module.Opposite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Prod

/-!
# Restriction of raw bidual forms over commutative semirings

A raw bidual form has domain `M →ₗ[R] R`, scalar ring `Rᵐᵒᵖ`, and ordinary
coefficient module `R`. Scalar restriction converts it to the usual commutative
double dual without changing its values. Restriction in the opposite direction
recovers the original form. The two restrictions preserve the canonical
pointwise coefficient actions and identify mixed-scalar evaluation with
`Module.Dual.eval`.

For finite projective modules, the comparison uses `Module.evalEquiv` and the
existing reflexivity instance. For `ℕ × ℕ`, evaluation of the two coordinate
forms has distinct nonzero values, and multiplication by `2` changes the
restricted bidual form. Natural-number coefficients need no additive inverses.

## References

These comparisons use Mathlib's opposite regular module, pointwise modules of
linear maps, scalar restriction, and commutative dual evaluation.
-/

universe uR uM

namespace ProjectiveModulesTests.BidualEvaluationCommutativeClient

section

variable (R : Type uR) (M : Type uM)
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

local notation "H" => M →ₗ[R] R
local notation "B" => H →ₗ[Rᵐᵒᵖ] R
local notation "D" => Module.Dual R (Module.Dual R M)

-- The coefficient and pointwise actions are the parents of the modules used
-- by evaluation and restriction, not independently selected scalar actions.
example : (inferInstance : Module R R).toSMul =
    (Semiring.toModule : Module R R).toSMul := rfl

example : (inferInstance : Module Rᵐᵒᵖ R).toSMul =
    (Semiring.toOppositeModule : Module Rᵐᵒᵖ R).toSMul := rfl

example : (inferInstance : Module Rᵐᵒᵖ H).toSMul =
    (LinearMap.module : Module Rᵐᵒᵖ H).toSMul := rfl

example : (inferInstance : Module R H).toSMul =
    (LinearMap.module : Module R H).toSMul := rfl

example : (inferInstance : Module R B).toSMul =
    (LinearMap.module : Module R B).toSMul := rfl

example : (inferInstance : Module R D).toSMul =
    (LinearMap.module : Module R D).toSMul := rfl

example (a : R) (f : H) (m : M) :
    (@SMul.smul Rᵐᵒᵖ H (inferInstance : Module Rᵐᵒᵖ H).toSMul
      (MulOpposite.op a) f) m = f m * a := rfl

example (a : R) (Φ : B) (f : H) :
    (@SMul.smul R B (inferInstance : Module R B).toSMul a Φ) f = a * Φ f := rfl

-- Coefficient towers lift pointwise to H. The reverse coefficient tower is
-- supplied by the registered IsScalarTower.op_left instance.
example : IsScalarTower R Rᵐᵒᵖ R := inferInstance
example : IsScalarTower Rᵐᵒᵖ R R := inferInstance
example : IsScalarTower R Rᵐᵒᵖ H := inferInstance
example : IsScalarTower Rᵐᵒᵖ R H := inferInstance
example : IsCentralScalar R H := inferInstance
example : LinearMap.CompatibleSMul H R R Rᵐᵒᵖ := inferInstance
example : LinearMap.CompatibleSMul H R Rᵐᵒᵖ R := inferInstance

-- Restriction constructs an R-linear comparison with ordinary coefficients.
example :
    (LinearMap.restrictScalarsₗ
      (R := R) (S := Rᵐᵒᵖ) (M := H) (N := R) (R₁ := R)).comp
        (LinearMap.flip (LinearMap.id : H →ₗ[Rᵐᵒᵖ] H)) =
      Module.Dual.eval R M := by
  apply LinearMap.ext₂
  intro m f
  rfl

-- Both round trips are equalities of bundled maps, not just functions.
example :
    (LinearMap.restrictScalarsₗ
      (R := Rᵐᵒᵖ) (S := R) (M := H) (N := R) (R₁ := R)).comp
        (LinearMap.restrictScalarsₗ
          (R := R) (S := Rᵐᵒᵖ) (M := H) (N := R) (R₁ := R)) =
      (LinearMap.id : B →ₗ[R] B) := by
  apply LinearMap.ext₂
  intro Φ f
  rfl

example :
    (LinearMap.restrictScalarsₗ
      (R := R) (S := Rᵐᵒᵖ) (M := H) (N := R) (R₁ := R)).comp
        (LinearMap.restrictScalarsₗ
          (R := Rᵐᵒᵖ) (S := R) (M := H) (N := R) (R₁ := R)) =
      (LinearMap.id : D →ₗ[R] D) := by
  apply LinearMap.ext₂
  intro Ψ f
  rfl

-- The commutative finite-projective equivalence is already provided by Mathlib.
example [Module.Finite R M] [Module.Projective R M] :
    (LinearMap.restrictScalarsₗ
      (R := R) (S := Rᵐᵒᵖ) (M := H) (N := R) (R₁ := R)).comp
        (LinearMap.flip (LinearMap.id : H →ₗ[Rᵐᵒᵖ] H)) =
      (Module.evalEquiv R M).toLinearMap := by
  apply LinearMap.ext₂
  intro m f
  rfl

example [Module.Finite R M] [Module.Projective R M] :
    (LinearMap.restrictScalarsₗ
      (R := Rᵐᵒᵖ) (S := R) (M := H) (N := R) (R₁ := R)).comp
        (Module.evalEquiv R M).toLinearMap =
      LinearMap.flip (LinearMap.id : H →ₗ[Rᵐᵒᵖ] H) := by
  apply LinearMap.ext₂
  intro m f
  rfl

end

-- Private type controls fix every scalar and carrier slot over ℕ.
example :
    (((ℕ × ℕ) →ₗ[ℕ] ℕ) →ₗ[ℕᵐᵒᵖ] ℕ) →ₗ[ℕ]
      (((ℕ × ℕ) →ₗ[ℕ] ℕ) →ₗ[ℕ] ℕ) :=
  LinearMap.restrictScalarsₗ
    (R := ℕ) (S := ℕᵐᵒᵖ) (M := (ℕ × ℕ) →ₗ[ℕ] ℕ) (N := ℕ) (R₁ := ℕ)

example :
    (((ℕ × ℕ) →ₗ[ℕ] ℕ) →ₗ[ℕ] ℕ) →ₗ[ℕ]
      (((ℕ × ℕ) →ₗ[ℕ] ℕ) →ₗ[ℕᵐᵒᵖ] ℕ) :=
  LinearMap.restrictScalarsₗ
    (R := ℕᵐᵒᵖ) (S := ℕ) (M := (ℕ × ℕ) →ₗ[ℕ] ℕ) (N := ℕ) (R₁ := ℕ)

-- Coordinate values and coefficient movement survive restriction over a
-- commutative semiring without additive inverses.
example :
    let H := (ℕ × ℕ) →ₗ[ℕ] ℕ
    let Φ : H →ₗ[ℕᵐᵒᵖ] ℕ :=
      LinearMap.flip (LinearMap.id : H →ₗ[ℕᵐᵒᵖ] H) (3, 5)
    let c : (H →ₗ[ℕᵐᵒᵖ] ℕ) →ₗ[ℕ] (H →ₗ[ℕ] ℕ) :=
      LinearMap.restrictScalarsₗ
        (R := ℕ) (S := ℕᵐᵒᵖ) (M := H) (N := ℕ) (R₁ := ℕ)
    c Φ (LinearMap.fst ℕ ℕ ℕ) = 3 ∧
      c Φ (LinearMap.snd ℕ ℕ ℕ) = 5 ∧
      c ((2 : ℕ) • Φ) (LinearMap.fst ℕ ℕ ℕ) = 6 ∧
      c ((2 : ℕ) • Φ) ≠ c Φ ∧
      (¬ ∃ n : ℕ, 1 + n = 0) := by
  dsimp only
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro h
    have hval : (6 : ℕ) = 3 := LinearMap.congr_fun h (LinearMap.fst ℕ ℕ ℕ)
    exact (by decide : (6 : ℕ) ≠ 3) hval
  · simp

end ProjectiveModulesTests.BidualEvaluationCommutativeClient
