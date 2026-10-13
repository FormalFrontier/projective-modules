/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.QuotientHom
public import ProjectiveModulesTests.RightIdealRingConstructorClient
public import Mathlib.LinearAlgebra.Prod

/-!
# Quotient forms on a product of integer matrix rings

For `A = M₂(ℤ)`, the kernel of the second projection on the right module
`A × A` is the nonzero proper first axis. Its quotient has the mutually inverse
maps induced by the second projection and the second injection. Left
multiplication of the second coordinate by `a` gives distinct nonzero forms
at `a = 1, E₀₀, E₀₁`, both before and after passage to the quotient.

The raw coefficient `A` and the ordinary dual coefficient `Aᵐᵒᵖ` are treated
separately, using Mathlib's same-scalar `opLinearEquiv` to encode their values.
The quotient-Hom correspondence pulls each quotient form back to its original
form and recovers its `liftQ` factor. Its coefficient
action multiplies on the left: `E₀₀ * E₀₁ = E₀₁ ≠ 0`, whereas the reversed
product is zero. The plain function that multiplies the second coordinate on
the right by `E₀₀` fails right linearity and is not bundled as a linear map.

## References

The integer matrix units and their multiplication and nonzero certificates
are reused from the integer-matrix clients of Projective Modules. The quotient,
projection, injection, multiplication map, opposite-coefficient codec and
quotient extensionality constructions use Mathlib's APIs.
-/

@[expose] public section

namespace ProjectiveModulesTests.QuotientHomMatrixClient

open IdempotentSpanSemiringClient RightIdealRingConstructorClient

/-- The second projection of the product right module. -/
local notation "second" => (LinearMap.snd IntMatrixᵐᵒᵖ IntMatrix IntMatrix)

/-- The first axis, presented as the kernel of the second projection. -/
local notation "firstAxis" => (LinearMap.ker second)

/-- The map induced by the second projection on the first-axis quotient. -/
local notation "quotientSnd" =>
  (Submodule.liftQ (τ₁₂ := RingHom.id IntMatrixᵐᵒᵖ) firstAxis second le_rfl)

/-- The second injection followed by the quotient map. -/
local notation "quotientInr" =>
  (LinearMap.comp
    (σ₁₂ := RingHom.id IntMatrixᵐᵒᵖ) (σ₂₃ := RingHom.id IntMatrixᵐᵒᵖ)
    (σ₁₃ := RingHom.id IntMatrixᵐᵒᵖ) (Submodule.mkQ firstAxis)
    (LinearMap.inr IntMatrixᵐᵒᵖ IntMatrix IntMatrix))

/-- The second projection encoded in the ordinary opposite-valued dual. -/
local notation "ordinarySnd" =>
  (LinearMap.comp
    (σ₁₂ := RingHom.id IntMatrixᵐᵒᵖ) (σ₂₃ := RingHom.id IntMatrixᵐᵒᵖ)
    (σ₁₃ := RingHom.id IntMatrixᵐᵒᵖ)
    (LinearEquiv.toLinearMap (MulOpposite.opLinearEquiv (M := IntMatrix) IntMatrixᵐᵒᵖ)) second)

/-- The ordinary dual form induced by the encoded second projection. -/
local notation "ordinaryQuotientSnd" =>
  (Submodule.liftQ (τ₁₂ := RingHom.id IntMatrixᵐᵒᵖ) firstAxis ordinarySnd
    (LinearMap.ker_le_ker_comp
      (τ₁₂ := RingHom.id IntMatrixᵐᵒᵖ) (τ₂₃ := RingHom.id IntMatrixᵐᵒᵖ)
      (τ₁₃ := RingHom.id IntMatrixᵐᵒᵖ) second
      (LinearEquiv.toLinearMap (MulOpposite.opLinearEquiv (M := IntMatrix) IntMatrixᵐᵒᵖ))))

/-- The injection from the opposite coefficient, decoded by the same-scalar codec. -/
local notation "ordinaryQuotientInr" =>
  (LinearMap.comp
    (σ₁₂ := RingHom.id IntMatrixᵐᵒᵖ) (σ₂₃ := RingHom.id IntMatrixᵐᵒᵖ)
    (σ₁₃ := RingHom.id IntMatrixᵐᵒᵖ) quotientInr
    (LinearEquiv.toLinearMap
      (LinearEquiv.symm (MulOpposite.opLinearEquiv (M := IntMatrix) IntMatrixᵐᵒᵖ))))

/-- The class of the unit in the second coordinate. -/
local notation "quotientPoint" => (Submodule.mkQ firstAxis (0, 1))

/-- The product uses the componentwise right-regular action. -/
theorem right_action (s x y : IntMatrix) :
    (MulOpposite.op s : IntMatrixᵐᵒᵖ) • (x, y) = (x * s, y * s) := rfl

/-- The second projection evaluates to the second coordinate. -/
@[simp]
theorem second_apply (z : IntMatrix × IntMatrix) : second z = z.2 := rfl

/-- Membership in the first axis is exactly vanishing of the second coordinate. -/
@[simp]
theorem firstAxis_mem (z : IntMatrix × IntMatrix) : z ∈ firstAxis ↔ z.2 = 0 :=
  LinearMap.mem_ker

/-- The kernel is exactly the first axis, not the whole product or the zero submodule. -/
theorem firstAxis_eq_prod :
    firstAxis = (⊤ : Submodule IntMatrixᵐᵒᵖ IntMatrix).prod ⊥ := by
  apply Submodule.ext
  intro z
  simp

/-- The first axis contains the nonzero vector `(1,0)`. -/
theorem firstAxis_ne_bot : firstAxis ≠ ⊥ := by
  intro h
  have hx : ((1 : IntMatrix), (0 : IntMatrix)) ∈ firstAxis := by simp
  simp [h] at hx

/-- The second-coordinate unit is not in the first axis. -/
theorem second_unit_not_mem : ((0 : IntMatrix), (1 : IntMatrix)) ∉ firstAxis := by
  simp

/-- The first axis is proper. -/
theorem firstAxis_ne_top : firstAxis ≠ ⊤ := by
  intro h
  apply second_unit_not_mem
  rw [h]
  exact Submodule.mem_top

/-- Both strict bounds on the first-axis submodule hold. -/
theorem firstAxis_strict_bounds : ⊥ < firstAxis ∧ firstAxis < ⊤ :=
  ⟨bot_lt_iff_ne_bot.mpr firstAxis_ne_bot, lt_top_iff_ne_top.mpr firstAxis_ne_top⟩

/-- The raw quotient projection evaluates on representatives to the second coordinate. -/
@[simp]
theorem quotientSnd_apply_mkQ (z : IntMatrix × IntMatrix) :
    quotientSnd ((firstAxis).mkQ z) = z.2 := by
  simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, second_apply]

/-- The quotient injection sends a matrix to the class of `(0,y)`. -/
@[simp]
theorem quotientInr_apply (y : IntMatrix) : quotientInr y = (firstAxis).mkQ (0, y) := rfl

/-- The ordinary projection encodes the second coordinate by `op`. -/
@[simp]
theorem ordinarySnd_apply (z : IntMatrix × IntMatrix) :
    ordinarySnd z = MulOpposite.op z.2 := rfl

/-- The ordinary quotient projection encodes the second coordinate of a representative. -/
@[simp]
theorem ordinaryQuotientSnd_apply_mkQ (z : IntMatrix × IntMatrix) :
    ordinaryQuotientSnd ((firstAxis).mkQ z) = MulOpposite.op z.2 := by
  simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, ordinarySnd_apply]

/-- The ordinary injection decodes a coefficient before forming its quotient class. -/
@[simp]
theorem ordinaryQuotientInr_apply (y : IntMatrixᵐᵒᵖ) :
    ordinaryQuotientInr y = (firstAxis).mkQ (0, MulOpposite.unop y) := rfl

/-- The raw and ordinary `liftQ` factors pull back to their projections. -/
theorem projection_pullbacks :
    (quotientSnd).comp (firstAxis).mkQ = second ∧
      (ordinaryQuotientSnd).comp (firstAxis).mkQ = ordinarySnd :=
  ⟨(firstAxis).liftQ_mkQ second le_rfl,
    (firstAxis).liftQ_mkQ ordinarySnd
      (LinearMap.ker_le_ker_comp
        (τ₁₂ := RingHom.id IntMatrixᵐᵒᵖ) (τ₂₃ := RingHom.id IntMatrixᵐᵒᵖ)
        (τ₁₃ := RingHom.id IntMatrixᵐᵒᵖ) second
        (MulOpposite.opLinearEquiv (M := IntMatrix) IntMatrixᵐᵒᵖ).toLinearMap)⟩

/-- Both projections restrict to zero on the first axis. -/
theorem projection_restrictions :
    (second).comp (firstAxis).subtype = 0 ∧ (ordinarySnd).comp (firstAxis).subtype = 0 :=
  ⟨LinearMap.comp_ker_subtype second,
    LinearMap.le_ker_iff_comp_subtype_eq_zero.mp
      (LinearMap.ker_le_ker_comp
        (τ₁₂ := RingHom.id IntMatrixᵐᵒᵖ) (τ₂₃ := RingHom.id IntMatrixᵐᵒᵖ)
        (τ₁₃ := RingHom.id IntMatrixᵐᵒᵖ) second
        (MulOpposite.opLinearEquiv (M := IntMatrix) IntMatrixᵐᵒᵖ).toLinearMap)⟩

/-- Projection after the second injection is the identity on the raw coefficient. -/
theorem quotientSnd_comp_inr : (quotientSnd).comp quotientInr = LinearMap.id := by
  apply LinearMap.ext
  intro y
  exact quotientSnd_apply_mkQ (0, y)

/-- The second injection after projection is the identity on the quotient. -/
theorem quotientInr_comp_snd : (quotientInr).comp quotientSnd = LinearMap.id := by
  apply (firstAxis).linearMap_qext
  apply LinearMap.ext
  intro z
  change (firstAxis).mkQ (0, z.2) = (firstAxis).mkQ z
  exact (Submodule.Quotient.eq firstAxis).mpr
    (by rw [firstAxis_mem]; exact sub_self z.2)

/-- The encoded projection and decoded injection are inverse on the ordinary coefficient. -/
theorem ordinaryQuotientSnd_comp_inr :
    (ordinaryQuotientSnd).comp ordinaryQuotientInr = LinearMap.id := by
  apply LinearMap.ext
  intro y
  exact (ordinaryQuotientSnd_apply_mkQ (0, MulOpposite.unop y)).trans
    (MulOpposite.op_unop y)

/-- The ordinary projection and injection are inverse on the quotient. -/
theorem ordinaryQuotientInr_comp_snd :
    (ordinaryQuotientInr).comp ordinaryQuotientSnd = LinearMap.id := by
  apply (firstAxis).linearMap_qext
  apply LinearMap.ext
  intro z
  change (firstAxis).mkQ (0, z.2) = (firstAxis).mkQ z
  exact (Submodule.Quotient.eq firstAxis).mpr
    (by rw [firstAxis_mem]; exact sub_self z.2)

/-- The raw quotient projection takes the selected point to the identity matrix. -/
@[simp]
theorem quotientSnd_point : quotientSnd quotientPoint = (1 : IntMatrix) := rfl

/-- The ordinary quotient projection takes the selected point to the encoded identity. -/
@[simp]
theorem ordinaryQuotientSnd_point :
    ordinaryQuotientSnd quotientPoint = MulOpposite.op (1 : IntMatrix) :=
  ordinaryQuotientSnd_apply_mkQ (0, 1)

/-- The class of the second-coordinate unit is nonzero. -/
theorem quotientPoint_ne_zero : quotientPoint ≠ 0 := by
  intro h
  have hz : (1 : IntMatrix) = 0 := by
    simpa only [h, map_zero] using quotientSnd_point.symm
  exact one_ne_zero hz

/-- Both quotient projections and the raw injection are nonzero maps. -/
theorem projection_maps_ne_zero :
    quotientSnd ≠ 0 ∧ ordinaryQuotientSnd ≠ 0 ∧ quotientInr ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hz : (1 : IntMatrix) = 0 := by
      simpa only [quotientSnd_point, LinearMap.zero_apply] using
        LinearMap.congr_fun h quotientPoint
    exact one_ne_zero hz
  · intro h
    have hz : MulOpposite.op (1 : IntMatrix) = 0 := by
      simpa only [ordinaryQuotientSnd_point, LinearMap.zero_apply] using
        LinearMap.congr_fun h quotientPoint
    exact one_ne_zero (congrArg MulOpposite.unop hz)
  · intro h
    apply quotientPoint_ne_zero
    simpa only [quotientInr_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun h (1 : IntMatrix)

/-- Both projections evaluate nontrivially on the class of the upper-right matrix unit. -/
theorem projection_e01_values :
    quotientSnd ((firstAxis).mkQ (0, intE01)) = intE01 ∧
      ordinaryQuotientSnd ((firstAxis).mkQ (0, intE01)) = MulOpposite.op intE01 :=
  ⟨quotientSnd_apply_mkQ (0, intE01), ordinaryQuotientSnd_apply_mkQ (0, intE01)⟩

/-- Quotient extensionality identifies every raw factor of the projection. -/
theorem quotientSnd_unique
    (ψ : ((IntMatrix × IntMatrix) ⧸ firstAxis) →ₗ[IntMatrixᵐᵒᵖ] IntMatrix)
    (h : ψ.comp (firstAxis).mkQ = second) : ψ = quotientSnd :=
  (firstAxis).linearMap_qext (h.trans projection_pullbacks.1.symm)

/-- Quotient extensionality also identifies the ordinary factor without changing coefficients. -/
theorem ordinaryQuotientSnd_unique
    (δ : Module.Dual IntMatrixᵐᵒᵖ ((IntMatrix × IntMatrix) ⧸ firstAxis))
    (h : δ.comp (firstAxis).mkQ = ordinarySnd) : δ = ordinaryQuotientSnd :=
  (firstAxis).linearMap_qext (h.trans projection_pullbacks.2.symm)

/-- The matrix units satisfy the asymmetric products and are distinct from zero and one. -/
theorem matrix_units_control :
    intE11 * intE01 = intE01 ∧ intE01 * intE11 = 0 ∧
      intE11 ≠ 0 ∧ intE01 ≠ 0 ∧ intE11 ≠ 1 ∧ intE11 ≠ intE01 ∧ intE01 ≠ 1 := by
  refine ⟨intE11_mul_e01, intE01_mul_e11, intE11_proper_generator.1,
    intE01_ne_zero, intE11_proper_generator.2, ?_, ?_⟩
  · intro h
    have he : (1 : ℤ) = 0 := by
      simpa [intE11, intE01] using congrArg (fun B : IntMatrix => B 0 0) h
    exact one_ne_zero he
  · intro h
    have he : (0 : ℤ) = 1 := by
      simpa [intE01] using congrArg (fun B : IntMatrix => B 0 0) h
    exact zero_ne_one he

/-- A raw right-linear form multiplying the second coordinate on the left. -/
local notation "rawFamily" =>
  (fun a : IntMatrix => LinearMap.comp
    (σ₁₂ := RingHom.id IntMatrixᵐᵒᵖ) (σ₂₃ := RingHom.id IntMatrixᵐᵒᵖ)
    (σ₁₃ := RingHom.id IntMatrixᵐᵒᵖ) (LinearMap.mulLeft IntMatrixᵐᵒᵖ a) second)

/-- A raw family member evaluates by left multiplication of the second coordinate. -/
@[simp]
theorem rawFamily_apply (a : IntMatrix) (z : IntMatrix × IntMatrix) :
    rawFamily a z = a * z.2 := rfl

/-- Every raw family member vanishes on the first axis. -/
theorem rawFamily_vanish (a : IntMatrix) : firstAxis ≤ LinearMap.ker (rawFamily a) :=
  LinearMap.ker_le_ker_comp
    (τ₁₂ := RingHom.id IntMatrixᵐᵒᵖ) (τ₂₃ := RingHom.id IntMatrixᵐᵒᵖ)
    (τ₁₃ := RingHom.id IntMatrixᵐᵒᵖ) second (LinearMap.mulLeft IntMatrixᵐᵒᵖ a)

/-- The factor of a raw family member, constructed with `liftQ`. -/
local notation "rawFactor" =>
  (fun a : IntMatrix =>
    Submodule.liftQ (τ₁₂ := RingHom.id IntMatrixᵐᵒᵖ) firstAxis (rawFamily a)
      (rawFamily_vanish a))

/-- The opposite-valued encoding of a raw family member. -/
local notation "ordinaryFamily" =>
  (fun a : IntMatrix =>
    LinearMap.comp
      (σ₁₂ := RingHom.id IntMatrixᵐᵒᵖ) (σ₂₃ := RingHom.id IntMatrixᵐᵒᵖ)
      (σ₁₃ := RingHom.id IntMatrixᵐᵒᵖ)
      (LinearEquiv.toLinearMap (MulOpposite.opLinearEquiv (M := IntMatrix) IntMatrixᵐᵒᵖ))
      (rawFamily a))

/-- An ordinary family member encodes the left-multiplication value. -/
@[simp]
theorem ordinaryFamily_apply (a : IntMatrix) (z : IntMatrix × IntMatrix) :
    ordinaryFamily a z = MulOpposite.op (a * z.2) := rfl

/-- Every encoded family member vanishes on the first axis. -/
theorem ordinaryFamily_vanish (a : IntMatrix) :
    firstAxis ≤ LinearMap.ker (ordinaryFamily a) :=
  (rawFamily_vanish a).trans
    (LinearMap.ker_le_ker_comp
      (τ₁₂ := RingHom.id IntMatrixᵐᵒᵖ) (τ₂₃ := RingHom.id IntMatrixᵐᵒᵖ)
      (τ₁₃ := RingHom.id IntMatrixᵐᵒᵖ) (rawFamily a)
      (MulOpposite.opLinearEquiv (M := IntMatrix) IntMatrixᵐᵒᵖ).toLinearMap)

/-- The factor of an ordinary dual family member, constructed with `liftQ`. -/
local notation "ordinaryFactor" =>
  (fun a : IntMatrix =>
    Submodule.liftQ (τ₁₂ := RingHom.id IntMatrixᵐᵒᵖ) firstAxis (ordinaryFamily a)
      (ordinaryFamily_vanish a))

/-- A raw factor evaluates on quotient representatives by the original form. -/
@[simp]
theorem rawFactor_apply_mkQ (a : IntMatrix) (z : IntMatrix × IntMatrix) :
    rawFactor a ((firstAxis).mkQ z) = a * z.2 := by
  simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, rawFamily_apply]

/-- An ordinary factor evaluates on representatives by the original encoded form. -/
@[simp]
theorem ordinaryFactor_apply_mkQ (a : IntMatrix) (z : IntMatrix × IntMatrix) :
    ordinaryFactor a ((firstAxis).mkQ z) = MulOpposite.op (a * z.2) := by
  simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, ordinaryFamily_apply]

/-- The raw factor recovers its coefficient at the selected quotient point. -/
@[simp]
theorem rawFactor_point (a : IntMatrix) : rawFactor a quotientPoint = a := by
  simp only [rawFactor_apply_mkQ, mul_one]

/-- The ordinary factor recovers its encoded coefficient at the selected quotient point. -/
@[simp]
theorem ordinaryFactor_point (a : IntMatrix) :
    ordinaryFactor a quotientPoint = MulOpposite.op a := by
  simp only [ordinaryFactor_apply_mkQ, mul_one]

/-- Each raw factor pulls back to the original left-multiplication form. -/
@[simp]
theorem rawFactor_pullback (a : IntMatrix) :
    (rawFactor a).comp (firstAxis).mkQ = rawFamily a :=
  (firstAxis).liftQ_mkQ (rawFamily a) (rawFamily_vanish a)

/-- Each ordinary factor pulls back to its opposite-valued form. -/
@[simp]
theorem ordinaryFactor_pullback (a : IntMatrix) :
    (ordinaryFactor a).comp (firstAxis).mkQ = ordinaryFamily a :=
  (firstAxis).liftQ_mkQ (ordinaryFamily a) (ordinaryFamily_vanish a)

/-- Both families restrict to zero on the first axis, using their independent vanishing proofs. -/
theorem family_restrictions (a : IntMatrix) :
    (rawFamily a).comp (firstAxis).subtype = 0 ∧
      (ordinaryFamily a).comp (firstAxis).subtype = 0 :=
  ⟨LinearMap.le_ker_iff_comp_subtype_eq_zero.mp (rawFamily_vanish a),
    LinearMap.le_ker_iff_comp_subtype_eq_zero.mp (ordinaryFamily_vanish a)⟩

/-- Uniqueness of the raw family factor follows from quotient extensionality. -/
theorem rawFactor_unique (a : IntMatrix)
    (ψ : ((IntMatrix × IntMatrix) ⧸ firstAxis) →ₗ[IntMatrixᵐᵒᵖ] IntMatrix)
    (h : ψ.comp (firstAxis).mkQ = rawFamily a) : ψ = rawFactor a :=
  (firstAxis).linearMap_qext (h.trans (rawFactor_pullback a).symm)

/-- Uniqueness of the ordinary family factor uses its own coefficient type. -/
theorem ordinaryFactor_unique (a : IntMatrix)
    (δ : Module.Dual IntMatrixᵐᵒᵖ ((IntMatrix × IntMatrix) ⧸ firstAxis))
    (h : δ.comp (firstAxis).mkQ = ordinaryFamily a) : δ = ordinaryFactor a :=
  (firstAxis).linearMap_qext (h.trans (ordinaryFactor_pullback a).symm)

/-- At coefficient one, the families and their factors are the original projection maps. -/
theorem unit_family_identifications :
    rawFamily 1 = second ∧ ordinaryFamily 1 = ordinarySnd ∧
      rawFactor 1 = quotientSnd ∧ ordinaryFactor 1 = ordinaryQuotientSnd := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro z
    simp only [rawFamily_apply, one_mul, second_apply]
  · apply LinearMap.ext
    intro z
    simp only [ordinaryFamily_apply, one_mul, ordinarySnd_apply]
  · apply (firstAxis).linearMap_qext
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, rawFactor_apply_mkQ, one_mul, quotientSnd_apply_mkQ]
  · apply (firstAxis).linearMap_qext
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, ordinaryFactor_apply_mkQ, one_mul,
      ordinaryQuotientSnd_apply_mkQ]

/-- Evaluation at the second-coordinate unit separates the raw family. -/
theorem rawFamily_injective : Function.Injective rawFamily := by
  intro a b h
  simpa using congrArg (fun F => F ((0 : IntMatrix), (1 : IntMatrix))) h

/-- Evaluation and decoding separate the ordinary family. -/
theorem ordinaryFamily_injective : Function.Injective ordinaryFamily := by
  intro a b h
  have he : MulOpposite.op a = MulOpposite.op b := by
    simpa using congrArg (fun F => F ((0 : IntMatrix), (1 : IntMatrix))) h
  exact MulOpposite.op_injective he

/-- Evaluation at the quotient point separates the raw factors. -/
theorem rawFactor_injective : Function.Injective rawFactor := by
  intro a b h
  simpa using congrArg (fun F => F quotientPoint) h

/-- Evaluation and decoding separate the ordinary factors. -/
theorem ordinaryFactor_injective : Function.Injective ordinaryFactor := by
  intro a b h
  have he : MulOpposite.op a = MulOpposite.op b := by
    simpa using congrArg (fun F => F quotientPoint) h
  exact MulOpposite.op_injective he

/-- A nonzero coefficient gives a nonzero raw form. -/
theorem rawFamily_ne_zero {a : IntMatrix} (ha : a ≠ 0) : rawFamily a ≠ 0 := by
  intro h
  apply ha
  simpa using congrArg (fun F => F ((0 : IntMatrix), (1 : IntMatrix))) h

/-- A nonzero coefficient gives a nonzero ordinary dual form. -/
theorem ordinaryFamily_ne_zero {a : IntMatrix} (ha : a ≠ 0) : ordinaryFamily a ≠ 0 := by
  intro h
  have he : MulOpposite.op a = 0 := by
    simpa using congrArg (fun F => F ((0 : IntMatrix), (1 : IntMatrix))) h
  exact ha (congrArg MulOpposite.unop he)

/-- A nonzero coefficient gives a nonzero raw quotient factor. -/
theorem rawFactor_ne_zero {a : IntMatrix} (ha : a ≠ 0) : rawFactor a ≠ 0 := by
  intro h
  apply ha
  simpa using congrArg (fun F => F quotientPoint) h

/-- A nonzero coefficient gives a nonzero ordinary quotient factor. -/
theorem ordinaryFactor_ne_zero {a : IntMatrix} (ha : a ≠ 0) : ordinaryFactor a ≠ 0 := by
  intro h
  have he : MulOpposite.op a = 0 := by
    simpa using congrArg (fun F => F quotientPoint) h
  exact ha (congrArg MulOpposite.unop he)

private theorem one_ne_e11 : (1 : IntMatrix) ≠ intE11 := intE11_proper_generator.2.symm

private theorem one_ne_e01 : (1 : IntMatrix) ≠ intE01 := matrix_units_control.2.2.2.2.2.2.symm

private theorem e11_ne_e01 : intE11 ≠ intE01 := matrix_units_control.2.2.2.2.2.1

/-- The raw forms at `1`, `E₀₀` and `E₀₁` are pairwise distinct and nonzero. -/
theorem raw_family_controls :
    rawFamily 1 ≠ 0 ∧ rawFamily intE11 ≠ 0 ∧ rawFamily intE01 ≠ 0 ∧
      rawFamily 1 ≠ rawFamily intE11 ∧ rawFamily 1 ≠ rawFamily intE01 ∧
      rawFamily intE11 ≠ rawFamily intE01 :=
  ⟨rawFamily_ne_zero one_ne_zero, rawFamily_ne_zero intE11_proper_generator.1,
    rawFamily_ne_zero intE01_ne_zero, fun h => one_ne_e11 (rawFamily_injective h),
    fun h => one_ne_e01 (rawFamily_injective h), fun h => e11_ne_e01 (rawFamily_injective h)⟩

/-- The ordinary forms at the same three coefficients are pairwise distinct and nonzero. -/
theorem ordinary_family_controls :
    ordinaryFamily 1 ≠ 0 ∧ ordinaryFamily intE11 ≠ 0 ∧ ordinaryFamily intE01 ≠ 0 ∧
      ordinaryFamily 1 ≠ ordinaryFamily intE11 ∧ ordinaryFamily 1 ≠ ordinaryFamily intE01 ∧
      ordinaryFamily intE11 ≠ ordinaryFamily intE01 :=
  ⟨ordinaryFamily_ne_zero one_ne_zero, ordinaryFamily_ne_zero intE11_proper_generator.1,
    ordinaryFamily_ne_zero intE01_ne_zero,
    fun h => one_ne_e11 (ordinaryFamily_injective h),
    fun h => one_ne_e01 (ordinaryFamily_injective h),
    fun h => e11_ne_e01 (ordinaryFamily_injective h)⟩

/-- The raw quotient factors at the three coefficients are pairwise distinct and nonzero. -/
theorem raw_factor_controls :
    rawFactor 1 ≠ 0 ∧ rawFactor intE11 ≠ 0 ∧ rawFactor intE01 ≠ 0 ∧
      rawFactor 1 ≠ rawFactor intE11 ∧ rawFactor 1 ≠ rawFactor intE01 ∧
      rawFactor intE11 ≠ rawFactor intE01 :=
  ⟨rawFactor_ne_zero one_ne_zero, rawFactor_ne_zero intE11_proper_generator.1,
    rawFactor_ne_zero intE01_ne_zero, fun h => one_ne_e11 (rawFactor_injective h),
    fun h => one_ne_e01 (rawFactor_injective h), fun h => e11_ne_e01 (rawFactor_injective h)⟩

/-- The ordinary quotient factors at the three coefficients are pairwise distinct and nonzero. -/
theorem ordinary_factor_controls :
    ordinaryFactor 1 ≠ 0 ∧ ordinaryFactor intE11 ≠ 0 ∧ ordinaryFactor intE01 ≠ 0 ∧
      ordinaryFactor 1 ≠ ordinaryFactor intE11 ∧ ordinaryFactor 1 ≠ ordinaryFactor intE01 ∧
      ordinaryFactor intE11 ≠ ordinaryFactor intE01 :=
  ⟨ordinaryFactor_ne_zero one_ne_zero, ordinaryFactor_ne_zero intE11_proper_generator.1,
    ordinaryFactor_ne_zero intE01_ne_zero,
    fun h => one_ne_e11 (ordinaryFactor_injective h),
    fun h => one_ne_e01 (ordinaryFactor_injective h),
    fun h => e11_ne_e01 (ordinaryFactor_injective h)⟩

/-- The pointwise raw action is multiplication on the left. -/
theorem smul_rawFamily (a b : IntMatrix) : a • rawFamily b = rawFamily (a * b) := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.smul_apply, rawFamily_apply, rawFamily_apply, smul_eq_mul]
  exact (mul_assoc a b z.2).symm

/-- The pointwise ordinary action encodes the same left multiplication. -/
theorem smul_ordinaryFamily (a b : IntMatrix) :
    a • ordinaryFamily b = ordinaryFamily (a * b) := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.smul_apply, ordinaryFamily_apply, ordinaryFamily_apply]
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_smul, MulOpposite.unop_op, smul_eq_mul]
  exact (mul_assoc a b z.2).symm

/-- The raw quotient family has the same left coefficient action. -/
theorem smul_rawFactor (a b : IntMatrix) : a • rawFactor b = rawFactor (a * b) := by
  apply (firstAxis).linearMap_qext
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply]
  rw [LinearMap.smul_apply, rawFactor_apply_mkQ, rawFactor_apply_mkQ, smul_eq_mul]
  exact (mul_assoc a b z.2).symm

/-- The ordinary quotient family also has the left coefficient action. -/
theorem smul_ordinaryFactor (a b : IntMatrix) :
    a • ordinaryFactor b = ordinaryFactor (a * b) := by
  apply (firstAxis).linearMap_qext
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply]
  rw [LinearMap.smul_apply, ordinaryFactor_apply_mkQ, ordinaryFactor_apply_mkQ]
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_smul, MulOpposite.unop_op, smul_eq_mul]
  exact (mul_assoc a b z.2).symm

/-- Left multiplication moves the unit raw form to a distinct nonzero matrix-unit form. -/
theorem raw_moving_action :
    intE11 • rawFamily 1 = rawFamily intE11 ∧
      rawFamily intE11 ≠ rawFamily 1 ∧ rawFamily intE11 ≠ 0 ∧
      (intE11 • rawFamily 1) (0, 1) = intE11 := by
  refine ⟨by simpa using smul_rawFamily intE11 1,
    raw_family_controls.2.2.2.1.symm, rawFamily_ne_zero intE11_proper_generator.1, ?_⟩
  change intE11 * (1 * 1) = intE11
  simp

/-- The ordinary form moves from encoded identity to encoded `E₀₀`. -/
theorem ordinary_moving_action :
    intE11 • ordinaryFamily 1 = ordinaryFamily intE11 ∧
      ordinaryFamily intE11 ≠ ordinaryFamily 1 ∧ ordinaryFamily intE11 ≠ 0 ∧
      (intE11 • ordinaryFamily 1) (0, 1) = MulOpposite.op intE11 := by
  refine ⟨by simpa using smul_ordinaryFamily intE11 1,
    ordinary_family_controls.2.2.2.1.symm,
    ordinaryFamily_ne_zero intE11_proper_generator.1, ?_⟩
  apply MulOpposite.unop_injective
  change intE11 * (1 * 1) = intE11
  simp

/-- Both quotient families move their unit form to a distinct nonzero form. -/
theorem quotient_moving_actions :
    intE11 • rawFactor 1 = rawFactor intE11 ∧ rawFactor intE11 ≠ rawFactor 1 ∧
      rawFactor intE11 ≠ 0 ∧ intE11 • ordinaryFactor 1 = ordinaryFactor intE11 ∧
      ordinaryFactor intE11 ≠ ordinaryFactor 1 ∧ ordinaryFactor intE11 ≠ 0 ∧
      (intE11 • rawFactor 1) quotientPoint = intE11 ∧
      (intE11 • ordinaryFactor 1) quotientPoint = MulOpposite.op intE11 := by
  refine ⟨by simpa using smul_rawFactor intE11 1,
    raw_factor_controls.2.2.2.1.symm, rawFactor_ne_zero intE11_proper_generator.1,
    by simpa using smul_ordinaryFactor intE11 1,
    ordinary_factor_controls.2.2.2.1.symm,
    ordinaryFactor_ne_zero intE11_proper_generator.1, ?_, ?_⟩
  · change intE11 * rawFactor 1 quotientPoint = intE11
    simp
  · change MulOpposite.op (intE11 * MulOpposite.unop (ordinaryFactor 1 quotientPoint)) =
      MulOpposite.op intE11
    simp

/-- The raw left coefficient order gives `E₀₁`, while the reversed order gives zero. -/
theorem raw_order_control :
    (intE11 • rawFamily intE01) (0, 1) = intE01 ∧
      rawFamily intE01 (0, 1) * intE11 = 0 := by
  constructor
  · change intE11 * (intE01 * 1) = intE01
    simpa using intE11_mul_e01
  · simpa using intE01_mul_e11

/-- The ordinary action encodes the left order, not the reversed raw order. -/
theorem ordinary_order_control :
    (intE11 • ordinaryFamily intE01) (0, 1) = MulOpposite.op intE01 ∧
      MulOpposite.op (MulOpposite.unop (ordinaryFamily intE01 (0, 1)) * intE11) = 0 := by
  constructor
  · apply MulOpposite.unop_injective
    change intE11 * (intE01 * 1) = intE01
    simpa using intE11_mul_e01
  · simpa using congrArg MulOpposite.op intE01_mul_e11

/-- The quotient factors retain the same asymmetric coefficient order. -/
theorem quotient_order_controls :
    (intE11 • rawFactor intE01) quotientPoint = intE01 ∧
      rawFactor intE01 quotientPoint * intE11 = 0 ∧
      (intE11 • ordinaryFactor intE01) quotientPoint = MulOpposite.op intE01 ∧
      MulOpposite.op (MulOpposite.unop (ordinaryFactor intE01 quotientPoint) * intE11) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change intE11 * rawFactor intE01 quotientPoint = intE01
    simpa using intE11_mul_e01
  · simpa using intE01_mul_e11
  · apply MulOpposite.unop_injective
    change intE11 * MulOpposite.unop (ordinaryFactor intE01 quotientPoint) = intE01
    simpa using intE11_mul_e01
  · simpa using congrArg MulOpposite.op intE01_mul_e11

/-- A plain function that multiplies the second coordinate on the wrong side. -/
local notation "wrongRightFunction" => (fun z : IntMatrix × IntMatrix => Prod.snd z * intE11)

/-- At `op E₀₁` and `(0,1)`, the two sides of right linearity are zero and `E₀₁`. -/
theorem wrongRightFunction_values :
    wrongRightFunction ((MulOpposite.op intE01 : IntMatrixᵐᵒᵖ) • (0, 1)) = 0 ∧
      (MulOpposite.op intE01 : IntMatrixᵐᵒᵖ) • wrongRightFunction (0, 1) = intE01 := by
  constructor
  · change (1 * intE01) * intE11 = 0
    simpa using intE01_mul_e11
  · change (1 * intE11) * intE01 = intE01
    simpa using intE11_mul_e01

/-- The wrong-sided function is not right-linear; it remains an unbundled function. -/
theorem wrongRightFunction_not_linear :
    ¬ ∀ (s : IntMatrixᵐᵒᵖ) (z : IntMatrix × IntMatrix),
      wrongRightFunction (s • z) = s • wrongRightFunction z := by
  intro h
  have he := h (MulOpposite.op intE01) (0, 1)
  rw [wrongRightFunction_values.1, wrongRightFunction_values.2] at he
  exact intE01_ne_zero he.symm

/-- Each raw family member belongs to the fixed kernel of restriction. -/
theorem rawFamily_mem_restrictionKernel (a : IntMatrix) :
    rawFamily a ∈ LinearMap.ker (LinearMap.lcomp IntMatrix IntMatrix (firstAxis).subtype) :=
  LinearMap.mem_ker.mpr (family_restrictions a).1

/-- Each ordinary family member belongs to its opposite-valued restriction kernel. -/
theorem ordinaryFamily_mem_restrictionKernel (a : IntMatrix) :
    ordinaryFamily a ∈
      LinearMap.ker (LinearMap.lcomp IntMatrix IntMatrixᵐᵒᵖ (firstAxis).subtype) :=
  LinearMap.mem_ker.mpr (family_restrictions a).2

/-- The quotient-Hom correspondence sends a raw `liftQ` factor to its form in the kernel. -/
theorem raw_correspondence_forward (a : IntMatrix) :
    ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix)) (rawFactor a) =
      ⟨rawFamily a, rawFamily_mem_restrictionKernel a⟩ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  rw [Submodule.quotientHomEquivKer_apply, rawFactor_apply_mkQ, rawFamily_apply]

/-- The quotient-Hom correspondence recovers exactly the raw `liftQ` factor. -/
theorem raw_correspondence_inverse (a : IntMatrix) :
    ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix)).symm
      ⟨rawFamily a, rawFamily_mem_restrictionKernel a⟩ = rawFactor a := by
  apply (firstAxis).linearMap_qext
  apply LinearMap.ext
  intro z
  exact (Submodule.quotientHomEquivKer_symm_apply_mkQ
    (S := IntMatrix) firstAxis ⟨rawFamily a, rawFamily_mem_restrictionKernel a⟩ z).trans
    ((rawFamily_apply a z).trans (rawFactor_apply_mkQ a z).symm)

/-- The ordinary dual uses the quotient-Hom correspondence with coefficient `Aᵐᵒᵖ`, not `A`. -/
theorem ordinary_correspondence_forward (a : IntMatrix) :
    ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ))
      (ordinaryFactor a) = ⟨ordinaryFamily a, ordinaryFamily_mem_restrictionKernel a⟩ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  rw [Submodule.quotientHomEquivKer_apply, ordinaryFactor_apply_mkQ, ordinaryFamily_apply]

/-- The inverse on an ordinary family member is its opposite-valued `liftQ` factor. -/
theorem ordinary_correspondence_inverse (a : IntMatrix) :
    ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ)).symm
      ⟨ordinaryFamily a, ordinaryFamily_mem_restrictionKernel a⟩ = ordinaryFactor a := by
  apply (firstAxis).linearMap_qext
  apply LinearMap.ext
  intro z
  exact (Submodule.quotientHomEquivKer_symm_apply_mkQ
    (S := IntMatrix) firstAxis ⟨ordinaryFamily a, ordinaryFamily_mem_restrictionKernel a⟩ z).trans
    ((ordinaryFamily_apply a z).trans (ordinaryFactor_apply_mkQ a z).symm)

/-- The inverse raw form at `E₀₁` has nonzero `(0,1)` matrix entry at the quotient point. -/
theorem raw_inverse_e01_entry :
    (((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix)).symm
      ⟨rawFamily intE01, rawFamily_mem_restrictionKernel intE01⟩ quotientPoint) 0 1 = 1 := by
  rw [Submodule.quotientHomEquivKer_symm_apply_mkQ]
  simp [intE01]

/-- Decoding the inverse ordinary form gives the same nonzero matrix entry. -/
theorem ordinary_inverse_e01_entry :
    (MulOpposite.unop
      (((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ)).symm
        ⟨ordinaryFamily intE01, ordinaryFamily_mem_restrictionKernel intE01⟩
        quotientPoint)) 0 1 = 1 := by
  rw [Submodule.quotientHomEquivKer_symm_apply_mkQ]
  simp [intE01]

/-- On the upper-right matrix unit, the raw correspondence identifies the form and its factor;
its inverse has a nonzero value at the quotient point. -/
theorem raw_e01_consumer :
    ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix)) (rawFactor intE01) =
      ⟨rawFamily intE01, rawFamily_mem_restrictionKernel intE01⟩ ∧
      ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix)).symm
        ⟨rawFamily intE01, rawFamily_mem_restrictionKernel intE01⟩ = rawFactor intE01 ∧
      ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix)).symm
        ⟨rawFamily intE01, rawFamily_mem_restrictionKernel intE01⟩ quotientPoint = intE01 ∧
      ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix)).symm
        ⟨rawFamily intE01, rawFamily_mem_restrictionKernel intE01⟩ ≠ 0 ∧ intE01 ≠ 0 := by
  refine ⟨raw_correspondence_forward intE01, raw_correspondence_inverse intE01,
    ?_, ?_, intE01_ne_zero⟩
  · rw [Submodule.quotientHomEquivKer_symm_apply_mkQ]
    simp
  · rw [raw_correspondence_inverse]
    exact rawFactor_ne_zero intE01_ne_zero

/-- On the same matrix unit, the ordinary correspondence identifies its form and factor;
its inverse has a nonzero opposite-valued coefficient. -/
theorem ordinary_e01_consumer :
    ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ))
      (ordinaryFactor intE01) =
      ⟨ordinaryFamily intE01, ordinaryFamily_mem_restrictionKernel intE01⟩ ∧
      ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ)).symm
        ⟨ordinaryFamily intE01, ordinaryFamily_mem_restrictionKernel intE01⟩ =
        ordinaryFactor intE01 ∧
      ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ)).symm
        ⟨ordinaryFamily intE01, ordinaryFamily_mem_restrictionKernel intE01⟩ quotientPoint =
        MulOpposite.op intE01 ∧
      ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ)).symm
        ⟨ordinaryFamily intE01, ordinaryFamily_mem_restrictionKernel intE01⟩ ≠ 0 ∧
      MulOpposite.op intE01 ≠ 0 := by
  refine ⟨ordinary_correspondence_forward intE01, ordinary_correspondence_inverse intE01,
    ?_, ?_, ?_⟩
  · rw [Submodule.quotientHomEquivKer_symm_apply_mkQ]
    simp
  · rw [ordinary_correspondence_inverse]
    exact ordinaryFactor_ne_zero intE01_ne_zero
  · intro h
    exact intE01_ne_zero (congrArg MulOpposite.unop h)

/-- The raw interface has both roundtrips on the nonzero `E₀₁` form. -/
theorem raw_correspondence_roundtrips :
    ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix)).symm
      (((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix))
        (rawFactor intE01)) = rawFactor intE01 ∧
      ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix))
        (((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix)).symm
          ⟨rawFamily intE01, rawFamily_mem_restrictionKernel intE01⟩) =
        ⟨rawFamily intE01, rawFamily_mem_restrictionKernel intE01⟩ :=
  ⟨LinearEquiv.symm_apply_apply _ _, LinearEquiv.apply_symm_apply _ _⟩

/-- Both roundtrips also hold on the nonzero ordinary `E₀₁` form. -/
theorem ordinary_correspondence_roundtrips :
    ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ)).symm
      (((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ))
        (ordinaryFactor intE01)) = ordinaryFactor intE01 ∧
      ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ))
        (((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ)).symm
          ⟨ordinaryFamily intE01, ordinaryFamily_mem_restrictionKernel intE01⟩) =
        ⟨ordinaryFamily intE01, ordinaryFamily_mem_restrictionKernel intE01⟩ :=
  ⟨LinearEquiv.symm_apply_apply _ _, LinearEquiv.apply_symm_apply _ _⟩

/-- The raw correspondence preserves the left action of the noncentral idempotent. -/
theorem raw_correspondence_action :
    ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix))
      (intE11 • rawFactor intE01) =
      intE11 • ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix))
        (rawFactor intE01) :=
  LinearEquiv.map_smul _ _ _

/-- The ordinary correspondence preserves that action on the encoded coefficient. -/
theorem ordinary_correspondence_action :
    ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ))
      (intE11 • ordinaryFactor intE01) =
      intE11 • ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ))
        (ordinaryFactor intE01) :=
  LinearEquiv.map_smul _ _ _

/-- Through the raw forward API, left action gives `E₀₁` and reversed order gives zero. -/
theorem raw_forward_order :
    (((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix))
      (intE11 • rawFactor intE01)).val (0, 1) = intE01 ∧
      (((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix))
        (rawFactor intE01)).val (0, 1) * intE11 = 0 := by
  constructor
  · rw [Submodule.quotientHomEquivKer_apply]
    change intE11 * (intE01 * 1) = intE01
    simpa using intE11_mul_e01
  · rw [Submodule.quotientHomEquivKer_apply]
    simpa using intE01_mul_e11

/-- The ordinary forward API has the same encoded order distinction. -/
theorem ordinary_forward_order :
    (((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ))
      (intE11 • ordinaryFactor intE01)).val (0, 1) = MulOpposite.op intE01 ∧
      MulOpposite.op
        (MulOpposite.unop
          ((((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ))
            (ordinaryFactor intE01)).val (0, 1)) * intE11) = 0 := by
  constructor
  · rw [Submodule.quotientHomEquivKer_apply]
    apply MulOpposite.unop_injective
    change intE11 * (intE01 * 1) = intE01
    simpa using intE11_mul_e01
  · rw [Submodule.quotientHomEquivKer_apply]
    simpa using congrArg MulOpposite.op intE01_mul_e11

/-- The raw inverse API computes left action on a kernel member at the quotient point. -/
theorem raw_inverse_action_value :
    ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix)).symm
      (intE11 • ⟨rawFamily intE01, rawFamily_mem_restrictionKernel intE01⟩)
      quotientPoint = intE01 := by
  rw [Submodule.quotientHomEquivKer_symm_apply_mkQ]
  exact raw_order_control.1

/-- The ordinary inverse API computes the encoded left action at the same point. -/
theorem ordinary_inverse_action_value :
    ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ)).symm
      (intE11 • ⟨ordinaryFamily intE01, ordinaryFamily_mem_restrictionKernel intE01⟩)
      quotientPoint = MulOpposite.op intE01 := by
  rw [Submodule.quotientHomEquivKer_symm_apply_mkQ]
  exact ordinary_order_control.1

/-- The raw forward interface exhibits the nontrivial movement from `1` to `E₀₀`. -/
theorem raw_forward_movement :
    (((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix))
      (intE11 • rawFactor 1)).val (0, 1) = intE11 ∧
      ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix))
        (intE11 • rawFactor 1) ≠
        ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix)) (rawFactor 1) := by
  constructor
  · rw [Submodule.quotientHomEquivKer_apply]
    change intE11 * (1 * 1) = intE11
    simp
  · intro h
    have he := ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix)).injective h
    rw [quotient_moving_actions.1] at he
    exact quotient_moving_actions.2.1 he

/-- The ordinary forward interface exhibits the corresponding encoded movement. -/
theorem ordinary_forward_movement :
    (((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ))
      (intE11 • ordinaryFactor 1)).val (0, 1) = MulOpposite.op intE11 ∧
      ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ))
        (intE11 • ordinaryFactor 1) ≠
        ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ))
          (ordinaryFactor 1) := by
  constructor
  · rw [Submodule.quotientHomEquivKer_apply]
    apply MulOpposite.unop_injective
    change intE11 * (1 * 1) = intE11
    simp
  · intro h
    have he :=
      ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ)).injective h
    rw [quotient_moving_actions.2.2.2.1] at he
    exact quotient_moving_actions.2.2.2.2.1 he

/-- Uniqueness of a raw quotient factor is also visible through the forward correspondence API. -/
theorem raw_unique_through_correspondence (a : IntMatrix)
    (ψ : ((IntMatrix × IntMatrix) ⧸ firstAxis) →ₗ[IntMatrixᵐᵒᵖ] IntMatrix)
    (h : ψ.comp (firstAxis).mkQ = rawFamily a) : ψ = rawFactor a := by
  apply ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrix)).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  rw [Submodule.quotientHomEquivKer_apply, Submodule.quotientHomEquivKer_apply,
    rawFactor_apply_mkQ]
  exact (LinearMap.congr_fun h z).trans (rawFamily_apply a z)

/-- The ordinary version of interface uniqueness retains the opposite-valued codomain. -/
theorem ordinary_unique_through_correspondence (a : IntMatrix)
    (δ : Module.Dual IntMatrixᵐᵒᵖ ((IntMatrix × IntMatrix) ⧸ firstAxis))
    (h : δ.comp (firstAxis).mkQ = ordinaryFamily a) : δ = ordinaryFactor a := by
  apply ((firstAxis).quotientHomEquivKer (S := IntMatrix) (C := IntMatrixᵐᵒᵖ)).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  rw [Submodule.quotientHomEquivKer_apply, Submodule.quotientHomEquivKer_apply,
    ordinaryFactor_apply_mkQ]
  exact (LinearMap.congr_fun h z).trans (ordinaryFamily_apply a z)

end ProjectiveModulesTests.QuotientHomMatrixClient
