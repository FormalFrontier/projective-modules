/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Trace
public import ProjectiveModules.Module.FiniteProjectiveHom
public import ProjectiveModules.Module.RightRegular
public import ProjectiveModules.Module.Trace.CommutatorQuotient
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

namespace ProjectiveModulesTests.FiniteProjectiveHomMatrixClient

open IdempotentSpanSemiringClient RightIdealRingConstructorClient
open scoped BigOperators

/-!
## Additive traces of the matrix right ideal

For the canonical right action, projection onto the principal right ideal is
left multiplication by `intE11`. The projection and inclusion are a nonzero
retract pair. The inclusion, transported to the opposite carrier, supplies a
one-element dual family for this right ideal.

The additive trace of its identity is the class of `intE11`, whereas the
identity on the regular matrix module has trace the class of the identity
matrix. Ordinary integer matrix trace descends to the additive commutator
quotient and distinguishes these classes by the integers `1` and `2`.

The projection reuses the idempotent-span retraction of Projective Modules,
with contributions by Formal Frontier Agents including Prism, and Mathlib's
same-scalar opposite equivalence by Eric Wieser. The quotient calculation uses
Mathlib's matrix trace formalization by Johannes Hölzl, Patrick Massot, Casper
Putz and Anne Baanen, and `QuotientAddGroup.lift`, together with the additive
commutator subgroup and matrix cyclicity formalized in General Linear Groups.
The finite-free examples use the column convention of the right-endomorphism
matrix formalization of Projective Modules, with contributions by Prism and
Lens, motivated by Charles A. Weibel, *The K-book*, Exercise I.1.7. The
commutative comparison uses its contraction trace and Mathlib's tensor–Hom and
contraction formalization by Oliver Nash and Antoine Labelle. No source excerpt
is reproduced here.
-/

/-- Projection onto the existing matrix right ideal, transported from the
principal left ideal in the opposite ring. -/
private noncomputable def matrixProjection :
    IntMatrix →ₗ[IntMatrixᵐᵒᵖ] matrixRightIdeal :=
  (IsIdempotentElem.rightSpanFiniteProjectiveLinearEquiv
      intE11_isIdempotent).symm.toLinearMap.comp
    ((IsIdempotentElem.spanProjection (MulOpposite.op intE11)).comp
      (MulOpposite.opLinearEquiv (M := IntMatrix) IntMatrixᵐᵒᵖ).toLinearMap)

/-- The coordinate functional of the principal generator is the inclusion
with its values transported to the opposite carrier. -/
private noncomputable def matrixCoordinate :
    matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrixᵐᵒᵖ :=
  (MulOpposite.opLinearEquiv (M := IntMatrix) IntMatrixᵐᵒᵖ).toLinearMap.comp
    matrixInclusion

private theorem matrixCoordinate_apply (m : matrixRightIdeal) :
    matrixCoordinate m = MulOpposite.op (matrixInclusion m) := rfl

/-- The nonzero inclusion and projection retract the matrix right ideal;
the reverse composite is left multiplication by the diagonal idempotent. -/
private theorem matrixProjection_retract :
    matrixProjection.comp matrixInclusion = LinearMap.id ∧
      matrixInclusion.comp matrixProjection =
        RingEquiv.moduleEndSelfOp (R := IntMatrix) intE11 := by
  have he : IsIdempotentElem (MulOpposite.op intE11) :=
    congrArg (MulOpposite.op : IntMatrix → IntMatrixᵐᵒᵖ) intE11_isIdempotent.eq
  constructor
  · apply LinearMap.ext
    intro m
    apply (IsIdempotentElem.rightSpanFiniteProjectiveLinearEquiv
      intE11_isIdempotent).injective
    change IsIdempotentElem.spanProjection (MulOpposite.op intE11)
        ((Ideal.span {MulOpposite.op intE11}).subtype
          (IsIdempotentElem.rightSpanFiniteProjectiveLinearEquiv
            intE11_isIdempotent m)) =
      IsIdempotentElem.rightSpanFiniteProjectiveLinearEquiv intE11_isIdempotent m
    exact he.spanProjection_apply_coe _
  · apply LinearMap.ext
    intro x
    change MulOpposite.unop
        (IsIdempotentElem.spanProjection (MulOpposite.op intE11)
          (MulOpposite.op x) : IntMatrixᵐᵒᵖ) = intE11 * x
    simp only [IsIdempotentElem.spanProjection_apply, MulOpposite.unop_mul,
      MulOpposite.unop_op]

/-- The generator and its coordinate functional form a one-element dual
family for the right ideal, with coefficients acting on the right. -/
private theorem matrixCoordinate_dualFamily :
    ∀ m : matrixRightIdeal,
      ∑ _i : Fin 1, matrixCoordinate m • matrixGenerator = m := by
  intro m
  rw [Fin.sum_univ_one]
  apply matrixInclusion_injective
  rw [matrixCoordinate_apply, matrixInclusion_right_smul, matrixInclusion_generator]
  calc
    intE11 * matrixInclusion m =
        (matrixInclusion.comp matrixProjection) (matrixInclusion m) :=
      (DFunLike.congr_fun matrixProjection_retract.2 (matrixInclusion m)).symm
    _ = matrixInclusion m :=
      congrArg matrixInclusion (DFunLike.congr_fun matrixProjection_retract.1 m)

/-- The finite-dual-family formula evaluates on the principal generator and
the specified coordinate, rather than vanishing on this nonfree module. -/
private theorem matrixRightIdeal_trace_dualFamily
    (F : Module.End IntMatrixᵐᵒᵖ matrixRightIdeal) :
    LinearMap.traceModCommutators IntMatrix matrixRightIdeal F =
      QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix)
        (∑ _i : Fin 1,
          MulOpposite.unop (matrixCoordinate (F matrixGenerator))) := by
  exact LinearMap.traceModCommutators_eq_sum IntMatrix matrixRightIdeal
    (fun _ : Fin 1 ↦ matrixGenerator) (fun _ ↦ matrixCoordinate)
    matrixCoordinate_dualFamily F

/-- Cyclicity applies to the nonzero inclusion and projection between the
right ideal and the regular matrix module. -/
private theorem matrixProjection_trace_cyclic :
    LinearMap.traceModCommutators IntMatrix matrixRightIdeal
        (matrixProjection.comp matrixInclusion) =
      LinearMap.traceModCommutators IntMatrix IntMatrix
        (matrixInclusion.comp matrixProjection) := by
  exact LinearMap.traceModCommutators_comp_comm IntMatrix matrixRightIdeal
    matrixInclusion matrixProjection

/-- Ordinary integer matrix trace annihilates the additive commutator
subgroup, so the quotient lift has a well-defined additive domain. -/
private theorem matrixCommutators_le_trace_ker :
    Ring.additiveCommutators IntMatrix ≤
      (Matrix.traceAddMonoidHom (Fin 2) ℤ).ker := by
  change AddSubgroup.closure
    {x : IntMatrix | ∃ a b : IntMatrix, x = a * b - b * a} ≤ _
  apply (AddSubgroup.closure_le _).2
  rintro x ⟨a, b, rfl⟩
  change Matrix.trace (a * b - b * a) = 0
  rw [Matrix.trace_sub, Matrix.trace_mul_comm a b, sub_self]

/-- Ordinary integer matrix trace on the additive commutator quotient. -/
private noncomputable def matrixTraceOnAdditiveQuotient :
    (IntMatrix ⧸ Ring.additiveCommutators IntMatrix) →+ ℤ :=
  QuotientAddGroup.lift (Ring.additiveCommutators IntMatrix)
    (Matrix.traceAddMonoidHom (Fin 2) ℤ) matrixCommutators_le_trace_ker

/-- The right ideal's identity and the regular identity have the distinct
classes of the diagonal unit and the identity matrix as their traces. Ordinary
integer trace separates these classes by `1` and `2`; regular left
multiplication by the diagonal unit has the class of that multiplier. -/
private theorem matrixIdentity_trace_nonvacuity :
    LinearMap.traceModCommutators IntMatrix matrixRightIdeal LinearMap.id =
        QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) intE11 ∧
      LinearMap.traceModCommutators IntMatrix IntMatrix LinearMap.id =
        QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) 1 ∧
      LinearMap.traceModCommutators IntMatrix IntMatrix
          (RingEquiv.moduleEndSelfOp (R := IntMatrix) intE11) =
        QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) intE11 ∧
      matrixTraceOnAdditiveQuotient
          (QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) intE11) = 1 ∧
      matrixTraceOnAdditiveQuotient
          (QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) 1) = 2 ∧
      QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) intE11 ≠
        QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) 1 := by
  have hideal :
      LinearMap.traceModCommutators IntMatrix matrixRightIdeal LinearMap.id =
        QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) intE11 := by
    rw [matrixRightIdeal_trace_dualFamily]
    simp only [LinearMap.id_apply, matrixCoordinate_apply, MulOpposite.unop_op,
      Fin.sum_univ_one, matrixInclusion_generator]
  have hregular :
      LinearMap.traceModCommutators IntMatrix IntMatrix LinearMap.id =
        QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) 1 := by
    simpa only [map_one, Module.End.one_eq_id] using
      (LinearMap.traceModCommutators_moduleEndSelfOp IntMatrix (1 : IntMatrix))
  have hdiag : matrixTraceOnAdditiveQuotient
      (QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) intE11) = 1 := by
    change Matrix.trace intE11 = 1
    simp only [intE11, Matrix.trace_single_eq_same]
  have hone : matrixTraceOnAdditiveQuotient
      (QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) 1) = 2 := by
    change Matrix.trace (1 : IntMatrix) = 2
    simp
  refine ⟨hideal, hregular,
    LinearMap.traceModCommutators_moduleEndSelfOp IntMatrix intE11, hdiag, hone, ?_⟩
  intro h
  have hvalues := congrArg matrixTraceOnAdditiveQuotient h
  rw [hdiag, hone] at hvalues
  exact (by decide : (1 : ℤ) ≠ 2) hvalues

/-- A diagonal corner on a two-coordinate free right module agrees with its
coefficient-matrix trace, yielding the nonzero diagonal-unit class. -/
private theorem matrixFree_corner_trace :
    LinearMap.traceModCommutators IntMatrix (Fin 2 → IntMatrix)
        ((Module.rightEndomorphismMatrixEquiv IntMatrix (Fin 2)).symm
          (Matrix.single 0 0 intE11)) =
        QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix)
          (Matrix.trace (Matrix.single 0 0 intE11 : Matrix (Fin 2) (Fin 2) IntMatrix)) ∧
      QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix)
          (Matrix.trace (Matrix.single 0 0 intE11 : Matrix (Fin 2) (Fin 2) IntMatrix)) =
        QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) intE11 := by
  constructor
  · simpa only [RingEquiv.apply_symm_apply] using
      (LinearMap.traceModCommutators_eq_matrix_trace IntMatrix
        ((Module.rightEndomorphismMatrixEquiv IntMatrix (Fin 2)).symm
          (Matrix.single 0 0 intE11)))
  · rw [Matrix.trace_single_eq_same]

/-- On the ordinary integer regular module, the commutative comparison uses
the contraction trace for the very same opposite-scalar module. -/
private theorem integerRegular_trace_comparison :
    LinearMap.traceModCommutators ℤ ℤ
        (RingEquiv.moduleEndSelfOp (R := ℤ) 3) =
        QuotientAddGroup.mk' (Ring.additiveCommutators ℤ)
          (MulOpposite.unop
            (LinearMap.traceOfFiniteProjective ℤᵐᵒᵖ ℤ
              (RingEquiv.moduleEndSelfOp (R := ℤ) 3))) ∧
      LinearMap.traceModCommutators ℤ ℤ
          (RingEquiv.moduleEndSelfOp (R := ℤ) 3) =
        QuotientAddGroup.mk' (Ring.additiveCommutators ℤ) 3 := by
  exact ⟨LinearMap.traceModCommutators_eq_traceOfFiniteProjective ℤ ℤ
      (RingEquiv.moduleEndSelfOp (R := ℤ) 3),
    LinearMap.traceModCommutators_moduleEndSelfOp ℤ 3⟩

/-- Empty free coordinates are permitted: their identity trace agrees with
the empty coefficient-matrix trace and is zero. -/
private theorem matrixEmpty_trace :
    LinearMap.traceModCommutators IntMatrix (Fin 0 → IntMatrix) LinearMap.id =
        QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix)
          (Matrix.trace
            (Module.rightEndomorphismMatrixEquiv IntMatrix (Fin 0) LinearMap.id)) ∧
      LinearMap.traceModCommutators IntMatrix (Fin 0 → IntMatrix) LinearMap.id = 0 := by
  have hmatrix := LinearMap.traceModCommutators_eq_matrix_trace IntMatrix
    (LinearMap.id : Module.End IntMatrixᵐᵒᵖ (Fin 0 → IntMatrix))
  refine ⟨hmatrix, ?_⟩
  rw [hmatrix, Matrix.trace_eq_zero_of_isEmpty, map_zero]

/-!
## Identity traces on projective classes and K₀

The identity trace on the nonfree matrix right ideal has the diagonal-unit
class, while the right regular module has the identity-matrix class. The class
trace and its group-completion extension retain these values. The same integer
matrix-trace homomorphism on the additive quotient separates their K₀ trace
values by `1` and `2`; no injectivity of the completion map is assumed.
-/

/-- Identity trace on the two right-module classes and their completions.
The integer quotient trace separates the nonfree ideal from the regular
module after applying the K₀ trace. -/
private theorem matrixIdentity_class_and_k0_trace :
    KTheory.ProjectiveClass.traceModCommutators IntMatrix
        (KTheory.ProjectiveClass.of IntMatrix matrixRightIdeal) =
        QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) intE11 ∧
      KTheory.ProjectiveClass.traceModCommutators IntMatrix
        (KTheory.ProjectiveClass.of IntMatrix IntMatrix) =
        QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) 1 ∧
      KTheory.K0.traceModCommutators IntMatrix
        (KTheory.K0.ofClass IntMatrix
          (KTheory.ProjectiveClass.of IntMatrix matrixRightIdeal)) =
        QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) intE11 ∧
      KTheory.K0.traceModCommutators IntMatrix
        (KTheory.K0.ofClass IntMatrix
          (KTheory.ProjectiveClass.of IntMatrix IntMatrix)) =
        QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) 1 ∧
      matrixTraceOnAdditiveQuotient
        (KTheory.K0.traceModCommutators IntMatrix
          (KTheory.K0.of IntMatrix matrixRightIdeal)) = 1 ∧
      matrixTraceOnAdditiveQuotient
        (KTheory.K0.traceModCommutators IntMatrix
          (KTheory.K0.of IntMatrix IntMatrix)) = 2 ∧
      KTheory.K0.traceModCommutators IntMatrix
          (KTheory.K0.of IntMatrix matrixRightIdeal) ≠
        KTheory.K0.traceModCommutators IntMatrix
          (KTheory.K0.of IntMatrix IntMatrix) := by
  have hideal :
      KTheory.ProjectiveClass.traceModCommutators IntMatrix
          (KTheory.ProjectiveClass.of IntMatrix matrixRightIdeal) =
        QuotientAddGroup.mk' (Ring.additiveCommutators IntMatrix) intE11 := by
    rw [KTheory.ProjectiveClass.traceModCommutators_of_module]
    exact matrixIdentity_trace_nonvacuity.1
  have hregular := KTheory.ProjectiveClass.traceModCommutators_of_self IntMatrix
  refine ⟨hideal, hregular, ?_, ?_, ?_, ?_, ?_⟩
  · rw [KTheory.K0.traceModCommutators_ofClass, hideal]
  · rw [KTheory.K0.traceModCommutators_ofClass, hregular]
  · simpa only [← KTheory.K0.ofClass_of, KTheory.K0.traceModCommutators_ofClass,
      hideal] using matrixIdentity_trace_nonvacuity.2.2.2.1
  · simpa only [← KTheory.K0.ofClass_of, KTheory.K0.traceModCommutators_ofClass,
      hregular] using matrixIdentity_trace_nonvacuity.2.2.2.2.1
  · simpa only [← KTheory.K0.ofClass_of, KTheory.K0.traceModCommutators_ofClass,
      hideal, hregular] using matrixIdentity_trace_nonvacuity.2.2.2.2.2

/-- The zero module, rather than a zero coefficient ring, gives zero under
both the projective-class trace and its K₀ extension. -/
private theorem matrixZero_class_and_k0_trace :
    KTheory.ProjectiveClass.traceModCommutators IntMatrix
        (KTheory.ProjectiveClass.of IntMatrix PUnit.{1}) = 0 ∧
      KTheory.K0.traceModCommutators IntMatrix
        (KTheory.K0.of IntMatrix PUnit.{1}) = 0 := by
  have hid : (LinearMap.id : Module.End IntMatrixᵐᵒᵖ PUnit.{1}) = 0 :=
    Subsingleton.elim _ _
  have hclass :
      KTheory.ProjectiveClass.traceModCommutators IntMatrix
          (KTheory.ProjectiveClass.of IntMatrix PUnit.{1}) = 0 := by
    rw [KTheory.ProjectiveClass.traceModCommutators_of_module, hid, map_zero]
  refine ⟨hclass, ?_⟩
  rw [← KTheory.K0.ofClass_of, KTheory.K0.traceModCommutators_ofClass, hclass]

end ProjectiveModulesTests.FiniteProjectiveHomMatrixClient
