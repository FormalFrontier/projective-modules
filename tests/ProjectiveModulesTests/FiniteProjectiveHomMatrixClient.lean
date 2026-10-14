/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.FiniteProjectiveHom
public import ProjectiveModules.Module.RightRegular
public import ProjectiveModulesTests.FiniteProjectiveRestrictionModelClient

/-!
# Left coefficients on forms from a nonfree matrix right ideal

The principal right ideal of the first diagonal unit in `M₂(ℤ)` is finite
projective, nonzero and nonfree. Its inclusion into the ordinary matrix carrier
is linear for the canonical right action, with inner scalar ring `M₂(ℤ)ᵐᵒᵖ`.
The inclusion is obtained from the bundled ideal comparison, the ideal subtype
and Mathlib's same-scalar opposite equivalence. This last equivalence is used
only for inner linearity, not as an outer-linear identification with a dual.

The ordinary matrix carrier also has its canonical left action. Associativity
makes the two actions commute, so forms carry the pointwise left action.
Both finite-projective-source Hom theorems apply to this nonfree source.
The diagonal unit fixes the upper-right value under the left coefficient action,
whereas multiplying that value on the right kills it. The upper-right unit moves
the inclusion. The plain function obtained by multiplying the inclusion's
values on the right fails inner linearity and is not bundled as a linear map.

## References

The matrix units, right-ideal bundle, comparison, generator and upper-right
member are reused from the integer-matrix clients of Projective Modules.
Nonfreeness is reused from its finite-projective restriction model: every vector
has a nonzero right annihilator, contradicting an occupied basis coordinate.
The opposite coefficient equivalence, ideal inclusion and commuting regular
actions use Mathlib's APIs. No commutative idempotent freeness criterion is used.
-/

@[expose] public section

namespace ProjectiveModulesTests.FiniteProjectiveHomMatrixClient

open IdempotentSpanSemiringClient RightIdealRingConstructorClient
open FiniteProjectiveRestrictionModelClient

/-- The inclusion of the bundled matrix right ideal into the ordinary matrix
carrier, linear for the right-regular action by the opposite ring. -/
noncomputable def matrixInclusion : matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix :=
  (MulOpposite.opLinearEquiv (M := IntMatrix) IntMatrixᵐᵒᵖ).symm.toLinearMap.comp
    ((Ideal.span {MulOpposite.op intE11}).subtype.comp
      (IsIdempotentElem.rightSpanFiniteProjectiveLinearEquiv
        intE11_isIdempotent).toLinearMap)

/-- The inclusion decodes the underlying opposite-valued ideal element. -/
@[simp]
theorem matrixInclusion_apply (m : matrixRightIdeal) :
    matrixInclusion m = MulOpposite.unop
      ((Ideal.span {MulOpposite.op intE11}).subtype
        (IsIdempotentElem.rightSpanFiniteProjectiveLinearEquiv
          intE11_isIdempotent m)) := rfl

/-- The inclusion retains distinct elements of the bundled right ideal. -/
theorem matrixInclusion_injective : Function.Injective matrixInclusion := by
  intro x y h
  apply (IsIdempotentElem.rightSpanFiniteProjectiveLinearEquiv
    intE11_isIdempotent).injective
  apply (Ideal.span {MulOpposite.op intE11}).subtype_injective
  apply MulOpposite.unop_injective
  simpa only [matrixInclusion_apply] using h

/-- The principal generator maps to the first diagonal matrix unit. -/
@[simp]
theorem matrixInclusion_generator : matrixInclusion matrixGenerator = intE11 := by
  rw [matrixInclusion_apply, matrixGenerator_coe, MulOpposite.unop_op]

/-- The specified upper-right member maps to the upper-right matrix unit. -/
@[simp]
theorem matrixInclusion_upperRight :
    matrixInclusion matrixUpperRightMember = intE01 := by
  rw [matrixInclusion_apply, matrixUpperRightMember_coe, MulOpposite.unop_op]

/-- Both specified values of the inclusion are nonzero. -/
theorem matrixInclusion_values_nonzero :
    matrixInclusion matrixGenerator ≠ 0 ∧
      matrixInclusion matrixUpperRightMember ≠ 0 := by
  rw [matrixInclusion_generator, matrixInclusion_upperRight]
  exact ⟨intE11_proper_generator.1, intE01_ne_zero⟩

/-- The inclusion is a nonzero element of the right-linear Hom. -/
theorem matrixInclusion_ne_zero : matrixInclusion ≠ 0 := by
  intro h
  apply matrixInclusion_values_nonzero.1
  rw [h, LinearMap.zero_apply]

/-- Inner linearity multiplies values on the right, matching the source's
right action; it is not the outer coefficient action on forms. -/
theorem matrixInclusion_right_smul (s : IntMatrix) (m : matrixRightIdeal) :
    matrixInclusion (MulOpposite.op s • m) = matrixInclusion m * s := by
  rw [map_smul]
  rfl

/-- The canonical outer action on the inclusion multiplies its values on the left. -/
theorem matrixInclusion_smul_apply (s : IntMatrix) (m : matrixRightIdeal) :
    (s • matrixInclusion) m = s * matrixInclusion m := by
  rw [LinearMap.smul_apply, smul_eq_mul]

/-- Left multiplication by the diagonal unit preserves a nonzero value,
whereas the reversed product is zero. -/
theorem matrixInclusion_left_order :
    (intE11 • matrixInclusion) matrixUpperRightMember = intE01 ∧
      (intE11 • matrixInclusion) matrixUpperRightMember ≠ 0 ∧
      matrixInclusion matrixUpperRightMember * intE11 = 0 := by
  rw [matrixInclusion_smul_apply, matrixInclusion_upperRight,
    intE11_mul_e01, intE01_mul_e11]
  exact ⟨rfl, intE01_ne_zero, rfl⟩

/-- The source's right action by the diagonal unit kills the upper-right
member; the left coefficient action on the inclusion has a nonzero value there. -/
theorem matrixInclusion_source_action_boundary :
    matrixInclusion (MulOpposite.op intE11 • matrixUpperRightMember) = 0 ∧
      (intE11 • matrixInclusion) matrixUpperRightMember ≠ 0 := by
  refine ⟨?_, matrixInclusion_left_order.2.1⟩
  rw [matrix_right_action_boundary.1, map_zero]

/-- The upper-right coefficient changes the inclusion, already at its
nonzero principal generator. -/
theorem matrixInclusion_left_moves :
    (intE01 • matrixInclusion) matrixGenerator = 0 ∧
      (intE01 • matrixInclusion) matrixGenerator ≠ matrixInclusion matrixGenerator ∧
      intE01 • matrixInclusion ≠ matrixInclusion := by
  have hzero : (intE01 • matrixInclusion) matrixGenerator = 0 := by
    rw [matrixInclusion_smul_apply, matrixInclusion_generator, intE01_mul_e11]
  have hne : (intE01 • matrixInclusion) matrixGenerator ≠
      matrixInclusion matrixGenerator := by
    rw [hzero, matrixInclusion_generator]
    exact Ne.symm intE11_proper_generator.1
  refine ⟨hzero, hne, ?_⟩
  intro h
  exact hne (congrArg
    (fun f : matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix ↦ f matrixGenerator) h)

/-- Multiplying the inclusion's values on the right by the diagonal unit
fails inner linearity at the generator and the upper-right scalar. -/
theorem matrixInclusion_right_product_not_linear :
    (fun m : matrixRightIdeal ↦ matrixInclusion m * intE11)
        (MulOpposite.op intE01 • matrixGenerator) ≠
      MulOpposite.op intE01 •
        ((fun m : matrixRightIdeal ↦ matrixInclusion m * intE11) matrixGenerator) := by
  dsimp only
  rw [matrixInclusion_right_smul, matrixInclusion_generator,
    intE11_mul_e01, intE01_mul_e11]
  change (0 : IntMatrix) ≠ (intE11 * intE11) * intE01
  rw [intE11_isIdempotent.eq, intE11_mul_e01]
  exact Ne.symm intE01_ne_zero

-- Test registration directly on the existing genuinely nonfree source;
-- the named-producer compatibility control below remains separate.
example : Module.Finite IntMatrix
    (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix) := inferInstance

/-- The right-linear Hom is finite projective and nonzero under its canonical
left matrix action, while its finite-projective source is nonzero and nonfree.
The two Hom closure properties use the projectivity and finiteness theorems
separately; finite generation is expressed by Mathlib's top-submodule API. -/
theorem matrixHom_controls :
    Module.Projective IntMatrix (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix) ∧
      Module.Finite IntMatrix (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix) ∧
      (⊤ : Submodule IntMatrix (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix)).FG ∧
      Nontrivial (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix) ∧
      ¬ Module.Free IntMatrixᵐᵒᵖ matrixRightIdeal ∧
      Nontrivial matrixRightIdeal := by
  have hP : Module.Projective IntMatrix (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix) :=
    Module.Projective.linearMap IntMatrixᵐᵒᵖ IntMatrix matrixRightIdeal IntMatrix
  have hF : Module.Finite IntMatrix (matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix) :=
    Module.Finite.linearMap_of_projective IntMatrixᵐᵒᵖ IntMatrix matrixRightIdeal IntMatrix
  exact ⟨hP, hF, hF.fg_top,
    nontrivial_of_ne matrixInclusion 0 matrixInclusion_ne_zero,
    matrixRightIdeal_not_free, matrixRightIdeal_finite_projective_nontrivial.2.2⟩

end ProjectiveModulesTests.FiniteProjectiveHomMatrixClient
