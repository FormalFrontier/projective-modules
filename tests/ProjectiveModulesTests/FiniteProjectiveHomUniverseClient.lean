/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.FiniteProjectiveHom
public import ProjectiveModules.Module.RightRegular
public import ProjectiveModulesTests.FiniteProjectiveRestrictionUniverseClient
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Matrix-ideal Hom in four independent universes

The principal right ideal of the first diagonal unit in `M₂(ℤ)` is a nonzero,
nonfree finite projective module. Its separately lifted scalar and carrier are
those of `FiniteProjectiveRestrictionUniverseClient.matrixIdealSource`.
The outer scalar ring and the ordinary matrix coefficient are lifted separately
as well. Thus the inner scalar, outer scalar, source and target have four
independent universe parameters.

These verification-only fixtures keep their auxiliary module data private while
checking the public Hom closure theorems in independent coefficient and source
universes; they do not add a module-construction API.

All module data are applications of Mathlib's `Module.compHom` and `ULift`
module providers. Downstairs, the inner action is right multiplication and the
outer action is left multiplication. Their commutation follows from associativity,
not commutativity. Finiteness and projectivity of the coefficient are transported
from its regular module through Mathlib's existing linear equivalences.

The ideal inclusion, followed by unop, is lifted using `ULift.moduleEquiv`.
Its values on the diagonal and upper-right matrix units remain nonzero. Left
multiplication by the diagonal unit fixes the upper-right value, whereas the
reversed product is zero. Left multiplication by the upper-right unit moves the
inclusion to a different map. The two specializations have inner-scalar,
outer-scalar, source and target levels `(1, 2, 0, 3)` and `(0, 1, 3, 2)`.

## References

The matrix ideal, its nonfreeness and its generator and member API are reused
from the finite-projective right-ideal and scalar-restriction clients of
Projective Modules. Scalar pullback, universe lifting, coefficient transport and
the pointwise Hom action use Mathlib's module and linear-equivalence APIs.
-/

section

universe uA uS uM uN

noncomputable section

namespace ProjectiveModulesTests.FiniteProjectiveHomUniverseClient

open MulOpposite
open IdempotentSpanSemiringClient RightIdealRingConstructorClient
open FiniteProjectiveRestrictionUniverseClient

-- Pull back the inner and source actions; the outer lift agrees with `downS`.
private abbrev downA : (ULift.{uA} IntMatrix)ᵐᵒᵖ →+* IntMatrixᵐᵒᵖ :=
  (ULift.ringEquiv : ULift.{uA} IntMatrix ≃+* IntMatrix).op.toRingHom
private abbrev downS : ULift.{uS} IntMatrix →+* IntMatrix :=
  (ULift.ringEquiv : ULift.{uS} IntMatrix ≃+* IntMatrix).toRingHom
private abbrev lowSourceModule : Module (ULift.{uA} IntMatrix)ᵐᵒᵖ matrixRightIdeal :=
  Module.compHom matrixRightIdeal downA
private abbrev lowInnerModule : Module (ULift.{uA} IntMatrix)ᵐᵒᵖ IntMatrix :=
  Module.compHom IntMatrix downA
-- Use the existing lifted regular module so its parent action is the canonical
-- `ULift.smulLeft` action, also used by standalone scalar-action inference.
private abbrev lowOuterModule : Module (ULift.{uS} IntMatrix) IntMatrix :=
  @ULift.module IntMatrix IntMatrix _ _ (inferInstance : Module IntMatrix IntMatrix)
private abbrev innerModule :
    Module (ULift.{uA} IntMatrix)ᵐᵒᵖ (ULift.{uN} IntMatrix) :=
  @ULift.module' (ULift.{uA} IntMatrix)ᵐᵒᵖ IntMatrix _ _ lowInnerModule
private abbrev outerModule : Module (ULift.{uS} IntMatrix) (ULift.{uN} IntMatrix) :=
  @ULift.module' (ULift.{uS} IntMatrix) IntMatrix _ _ lowOuterModule

attribute [local instance] lowSourceModule lowInnerModule lowOuterModule
  innerModule outerModule

private theorem source_alignment :
    (inferInstance : Module (ULift.{uA} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uA, uM}) =
      (@ULift.module' (ULift.{uA} IntMatrix)ᵐᵒᵖ matrixRightIdeal _ _ lowSourceModule) :=
  Module.ext' _ _ (fun _ _ ↦ rfl)

private theorem inner_alignment :
    innerModule.{uA, uN} = Module.compHom (ULift.{uN} IntMatrix) downA.{uA} :=
  Module.ext' _ _ (fun _ _ ↦ rfl)

private theorem outer_alignment :
    outerModule.{uS, uN} = Module.compHom (ULift.{uN} IntMatrix) downS.{uS} :=
  Module.ext' _ _ (fun _ _ ↦ rfl)

-- Pin the proof to the parent actions of the module data required by
-- `LinearMap.module`, rather than re-inferring two standalone `SMul` dictionaries.
private theorem targetCommutes :
    @SMulCommClass (ULift.{uA} IntMatrix)ᵐᵒᵖ (ULift.{uS} IntMatrix)
      (ULift.{uN} IntMatrix)
      innerModule.{uA, uN}.toDistribMulAction.toMulAction.toSMul
      outerModule.{uS, uN}.toDistribMulAction.toMulAction.toSMul where
  smul_comm a s n := congrArg (ULift.up : IntMatrix → ULift.{uN} IntMatrix)
    (mul_assoc s.down n.down (unop a).down)

attribute [local instance] targetCommutes

private theorem restrictionCompatible :
    LinearMap.CompatibleSMul matrixRightIdeal IntMatrix
      (ULift.{uA} IntMatrix)ᵐᵒᵖ IntMatrixᵐᵒᵖ := by
  let : Module (ULift.{uA} IntMatrix)ᵐᵒᵖ IntMatrixᵐᵒᵖ :=
    Module.compHom IntMatrixᵐᵒᵖ downA
  let : IsScalarTower (ULift.{uA} IntMatrix)ᵐᵒᵖ IntMatrixᵐᵒᵖ matrixRightIdeal :=
    SMul.comp.isScalarTower downA
  let : IsScalarTower (ULift.{uA} IntMatrix)ᵐᵒᵖ IntMatrixᵐᵒᵖ IntMatrix :=
    SMul.comp.isScalarTower downA
  exact LinearMap.IsScalarTower.compatibleSMul

private abbrev baseInclusion : matrixRightIdeal →ₗ[IntMatrixᵐᵒᵖ] IntMatrix :=
  (MulOpposite.opLinearEquiv IntMatrixᵐᵒᵖ).symm.toLinearMap.comp
    ((Ideal.span {op intE11}).subtype.comp
      (IsIdempotentElem.rightSpanFiniteProjectiveLinearEquiv
        intE11_isIdempotent).toLinearMap)

private abbrev pulledInclusion :
    matrixRightIdeal →ₗ[(ULift.{uA} IntMatrix)ᵐᵒᵖ] IntMatrix := by
  letI := restrictionCompatible
  exact baseInclusion.restrictScalars (ULift.{uA} IntMatrix)ᵐᵒᵖ

/-- The lifted inclusion of the matrix right ideal into the ordinary matrix carrier.
Both carrier lifts are the existing `ULift.moduleEquiv` maps. -/
def idealInclusion :
    matrixIdealSource.{uA, uM} →ₗ[(ULift.{uA} IntMatrix)ᵐᵒᵖ] ULift.{uN} IntMatrix :=
  (ULift.moduleEquiv :
    ULift.{uN} IntMatrix ≃ₗ[(ULift.{uA} IntMatrix)ᵐᵒᵖ] IntMatrix).symm.toLinearMap.comp
    (pulledInclusion.comp
      (ULift.moduleEquiv :
        matrixIdealSource.{uA, uM} ≃ₗ[(ULift.{uA} IntMatrix)ᵐᵒᵖ]
          matrixRightIdeal).toLinearMap)

/-- The inclusion lifts the ordinary matrix underlying an ideal member. -/
@[simp]
theorem idealInclusion_apply (m : matrixRightIdeal) :
    idealInclusion.{uA, uM, uN} (show matrixIdealSource.{uA, uM} from ULift.up m) =
      ULift.up (unop ((Ideal.span {op intE11}).subtype
        (IsIdempotentElem.rightSpanFiniteProjectiveLinearEquiv
          intE11_isIdempotent m))) :=
  rfl

/-- The source action is the existing pullback right-ideal action. -/
theorem source_action (a : (ULift.{uA} IntMatrix)ᵐᵒᵖ) (m : matrixRightIdeal) :
    a • (show matrixIdealSource.{uA, uM} from ULift.up m) =
      (show matrixIdealSource.{uA, uM} from ULift.up (downA a • m)) :=
  matrixIdealSource_smul a m

/-- The two coefficient actions are right and left multiplication downstairs. -/
theorem coefficient_actions (a : (ULift.{uA} IntMatrix)ᵐᵒᵖ)
    (s : ULift.{uS} IntMatrix) (n : ULift.{uN} IntMatrix) :
    a • n = ULift.up (n.down * (unop a).down) ∧
      s • n = ULift.up (s.down * n.down) ∧
      a • (s • n) = s • (a • n) :=
  ⟨rfl, rfl, targetCommutes.{uA, uS, uN}.smul_comm a s n⟩

/-- The pointwise Hom action is left multiplication on the matrix value downstairs. -/
theorem coefficient_smul_apply (s : ULift.{uS} IntMatrix)
    (f : matrixIdealSource.{uA, uM} →ₗ[(ULift.{uA} IntMatrix)ᵐᵒᵖ] ULift.{uN} IntMatrix)
    (m : matrixIdealSource.{uA, uM}) :
    (s • f) m = ULift.up (s.down * (f m).down) :=
  rfl

/-- The coefficient is finite and projective over its independently lifted outer ring,
by transport from the regular module of that ring. -/
theorem coefficient_finite_projective :
    Module.Finite (ULift.{uS} IntMatrix) (ULift.{uN} IntMatrix) ∧
      Module.Projective (ULift.{uS} IntMatrix) (ULift.{uN} IntMatrix) := by
  let e : ULift.{uS} IntMatrix ≃ₗ[ULift.{uS} IntMatrix] ULift.{uN} IntMatrix :=
    (Module.compHom.toLinearEquiv
      (ULift.ringEquiv : ULift.{uS} IntMatrix ≃+* IntMatrix)).trans
      (ULift.moduleEquiv : ULift.{uN} IntMatrix ≃ₗ[ULift.{uS} IntMatrix] IntMatrix).symm
  exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv' e⟩

-- Direct registration probe with the existing inner/outer/commuting actors.
-- Only the three prerequisite properties are installed, not Hom finiteness.
example : Module.Finite (ULift.{uS} IntMatrix)
    (matrixIdealSource.{uA, uM} →ₗ[(ULift.{uA} IntMatrix)ᵐᵒᵖ] ULift.{uN} IntMatrix) := by
  letI : Module.Finite (ULift.{uA} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uA, uM} :=
    matrixIdealSource_finite_projective.{uA, uM}.1
  letI : Module.Projective (ULift.{uA} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uA, uM} :=
    matrixIdealSource_finite_projective.{uA, uM}.2
  letI : Module.Finite (ULift.{uS} IntMatrix) (ULift.{uN} IntMatrix) :=
    coefficient_finite_projective.{uS, uN}.1
  exact inferInstance

private theorem hom_finite_projective :
    Module.Projective (ULift.{uS} IntMatrix)
        (matrixIdealSource.{uA, uM} →ₗ[(ULift.{uA} IntMatrix)ᵐᵒᵖ] ULift.{uN} IntMatrix) ∧
      Module.Finite (ULift.{uS} IntMatrix)
        (matrixIdealSource.{uA, uM} →ₗ[(ULift.{uA} IntMatrix)ᵐᵒᵖ] ULift.{uN} IntMatrix) := by
  let : Module.Finite (ULift.{uA} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uA, uM} :=
    matrixIdealSource_finite_projective.1
  let : Module.Projective (ULift.{uA} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uA, uM} :=
    matrixIdealSource_finite_projective.2
  let : Module.Finite (ULift.{uS} IntMatrix) (ULift.{uN} IntMatrix) :=
    coefficient_finite_projective.1
  let : Module.Projective (ULift.{uS} IntMatrix) (ULift.{uN} IntMatrix) :=
    coefficient_finite_projective.2
  exact ⟨@Module.Projective.linearMap (ULift.{uA} IntMatrix)ᵐᵒᵖ (ULift.{uS} IntMatrix)
      matrixIdealSource.{uA, uM} (ULift.{uN} IntMatrix) _ _ _ _
      (inferInstance : Module (ULift.{uA} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uA, uM})
      innerModule.{uA, uN} outerModule.{uS, uN} targetCommutes.{uA, uS, uN} _ _ _,
    @Module.Finite.linearMap_of_projective (ULift.{uA} IntMatrix)ᵐᵒᵖ (ULift.{uS} IntMatrix)
      matrixIdealSource.{uA, uM} (ULift.{uN} IntMatrix) _ _ _ _
      (inferInstance : Module (ULift.{uA} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uA, uM})
      innerModule.{uA, uN} outerModule.{uS, uN} targetCommutes.{uA, uS, uN} _ _ _⟩

/-- Both closure theorems apply to the nonfree lifted matrix ideal and to a target
whose regular-module properties are transported independently of the source. -/
theorem ideal_hom_finite_projective :
    Module.Projective (ULift.{uS} IntMatrix)
        (matrixIdealSource.{uA, uM} →ₗ[(ULift.{uA} IntMatrix)ᵐᵒᵖ] ULift.{uN} IntMatrix) ∧
      Module.Finite (ULift.{uS} IntMatrix)
        (matrixIdealSource.{uA, uM} →ₗ[(ULift.{uA} IntMatrix)ᵐᵒᵖ] ULift.{uN} IntMatrix) :=
  hom_finite_projective

/-- The lifted ideal generator is sent to the first diagonal matrix unit. -/
@[simp]
theorem idealInclusion_generator :
    idealInclusion.{uA, uM, uN} sourceGenerator.{uA, uM} =
      (ULift.up intE11 : ULift.{uN} IntMatrix) :=
  congrArg (fun b : IntMatrixᵐᵒᵖ ↦ (ULift.up (unop b) : ULift.{uN} IntMatrix)) matrixGenerator_coe

/-- The lifted upper-right ideal member is sent to the upper-right matrix unit. -/
@[simp]
theorem idealInclusion_upperRight :
    idealInclusion.{uA, uM, uN}
        (show matrixIdealSource.{uA, uM} from ULift.up matrixUpperRightMember) =
      (ULift.up intE01 : ULift.{uN} IntMatrix) :=
  congrArg (fun b : IntMatrixᵐᵒᵖ ↦ (ULift.up (unop b) : ULift.{uN} IntMatrix))
    matrixUpperRightMember_coe

/-- The inclusion is nonzero, and its source is nonzero and not free.
The source properties are those of the separately lifted matrix ideal. -/
theorem idealInclusion_nonzero_nonfree :
    sourceGenerator.{uA, uM} ≠ 0 ∧ idealInclusion.{uA, uM, uN} ≠ 0 ∧
      ¬ Module.Free (ULift.{uA} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uA, uM} := by
  refine ⟨sourceGenerator_ne_zero, ?_, matrixIdealSource_not_free⟩
  intro h
  have hv : (ULift.up intE11 : ULift.{uN} IntMatrix) = 0 := calc
    _ = idealInclusion.{uA, uM, uN}
        (show matrixIdealSource.{uA, uM} from ULift.up matrixGenerator) :=
      idealInclusion_generator.{uA, uM, uN}.symm
    _ = 0 := LinearMap.congr_fun h
      (show matrixIdealSource.{uA, uM} from ULift.up matrixGenerator)
  exact intE11_proper_generator.1 (congrArg ULift.down hv)

/-- Left multiplication fixes a nonzero upper-right inclusion value; the reversed
product is zero. The source member itself remains nonzero after lifting. -/
theorem idealInclusion_left_order :
    ((ULift.up intE11 : ULift.{uS} IntMatrix) • idealInclusion.{uA, uM, uN})
        (show matrixIdealSource.{uA, uM} from ULift.up matrixUpperRightMember) =
          (ULift.up intE01 : ULift.{uN} IntMatrix) ∧
      idealInclusion.{uA, uM, uN}
          (show matrixIdealSource.{uA, uM} from ULift.up matrixUpperRightMember) *
        (ULift.up intE11 : ULift.{uN} IntMatrix) = 0 ∧
      (ULift.up intE01 : ULift.{uN} IntMatrix) ≠ 0 ∧
      (show matrixIdealSource.{uA, uM} from ULift.up matrixUpperRightMember) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [LinearMap.smul_apply, idealInclusion_upperRight]
    change (ULift.up (intE11 * intE01) : ULift.{uN} IntMatrix) = ULift.up intE01
    exact congrArg ULift.up intE11_mul_e01
  · rw [idealInclusion_upperRight]
    change (ULift.up (intE01 * intE11) : ULift.{uN} IntMatrix) = ULift.up 0
    exact congrArg ULift.up intE01_mul_e11
  · intro h
    exact intE01_ne_zero (congrArg ULift.down h)
  · intro h
    exact matrixUpperRightMember_ne_zero (congrArg ULift.down h)

/-- The pointwise left action by the upper-right unit changes the lifted inclusion:
it kills the diagonal value, which was nonzero. -/
theorem idealInclusion_movement :
    ((ULift.up intE01 : ULift.{uS} IntMatrix) • idealInclusion.{uA, uM, uN})
        sourceGenerator.{uA, uM} = 0 ∧
      (ULift.up intE01 : ULift.{uS} IntMatrix) • idealInclusion.{uA, uM, uN} ≠
        idealInclusion.{uA, uM, uN} := by
  have hz : ((ULift.up intE01 : ULift.{uS} IntMatrix) • idealInclusion.{uA, uM, uN})
      sourceGenerator.{uA, uM} = 0 := by
    calc
      _ = ULift.up (intE01 * (idealInclusion.{uA, uM, uN}
          (show matrixIdealSource.{uA, uM} from ULift.up matrixGenerator)).down) :=
        coefficient_smul_apply (ULift.up intE01 : ULift.{uS} IntMatrix)
          idealInclusion.{uA, uM, uN}
          (show matrixIdealSource.{uA, uM} from ULift.up matrixGenerator)
      _ = ULift.up (intE01 * intE11) :=
        congrArg (fun n : ULift.{uN} IntMatrix ↦
          (ULift.up (intE01 * n.down) : ULift.{uN} IntMatrix))
          idealInclusion_generator.{uA, uM, uN}
      _ = 0 := congrArg (ULift.up : IntMatrix → ULift.{uN} IntMatrix) intE01_mul_e11
  refine ⟨hz, ?_⟩
  intro h
  have hv : (0 : ULift.{uN} IntMatrix) = ULift.up intE11 :=
    hz.symm.trans ((LinearMap.congr_fun h
      (show matrixIdealSource.{uA, uM} from ULift.up matrixGenerator)).trans
        idealInclusion_generator.{uA, uM, uN})
  exact intE11_proper_generator.1 (congrArg ULift.down hv.symm)

-- A direct inference test at (uA, uS, uM, uN) = (1, 2, 0, 3),
-- independent of the named-producer controls below.
example : Module.Finite (ULift.{2} IntMatrix)
    (matrixIdealSource.{1, 0} →ₗ[(ULift.{1} IntMatrix)ᵐᵒᵖ] ULift.{3} IntMatrix) := by
  letI : Module.Finite (ULift.{1} IntMatrix)ᵐᵒᵖ matrixIdealSource.{1, 0} :=
    matrixIdealSource_finite_projective.{1, 0}.1
  letI : Module.Projective (ULift.{1} IntMatrix)ᵐᵒᵖ matrixIdealSource.{1, 0} :=
    matrixIdealSource_finite_projective.{1, 0}.2
  letI : Module.Finite (ULift.{2} IntMatrix) (ULift.{3} IntMatrix) :=
    coefficient_finite_projective.{2, 3}.1
  exact inferInstance

/-- Inner scalars in universe one act on a universe-zero nonfree source;
outer scalars and coefficients occupy universes two and three. -/
theorem higher_inner_scalar_control :
    Module.Finite (ULift.{2} IntMatrix) (ULift.{3} IntMatrix) ∧
      Module.Projective (ULift.{2} IntMatrix) (ULift.{3} IntMatrix) ∧
      Module.Projective (ULift.{2} IntMatrix)
        (matrixIdealSource.{1, 0} →ₗ[(ULift.{1} IntMatrix)ᵐᵒᵖ] ULift.{3} IntMatrix) ∧
      Module.Finite (ULift.{2} IntMatrix)
        (matrixIdealSource.{1, 0} →ₗ[(ULift.{1} IntMatrix)ᵐᵒᵖ] ULift.{3} IntMatrix) ∧
      ¬ Module.Free (ULift.{1} IntMatrix)ᵐᵒᵖ matrixIdealSource.{1, 0} ∧
      sourceGenerator.{1, 0} ≠ 0 ∧ idealInclusion.{1, 0, 3} ≠ 0 ∧
      ((ULift.up intE11 : ULift.{2} IntMatrix) • idealInclusion.{1, 0, 3})
        (ULift.up matrixUpperRightMember) = (ULift.up intE01 : ULift.{3} IntMatrix) ∧
      idealInclusion.{1, 0, 3} (ULift.up matrixUpperRightMember) *
        (ULift.up intE11 : ULift.{3} IntMatrix) = 0 ∧
      (ULift.up intE01 : ULift.{3} IntMatrix) ≠ 0 ∧
      ((ULift.up intE01 : ULift.{2} IntMatrix) • idealInclusion.{1, 0, 3})
        sourceGenerator.{1, 0} = 0 ∧
      (ULift.up intE01 : ULift.{2} IntMatrix) • idealInclusion.{1, 0, 3} ≠
        idealInclusion.{1, 0, 3} := by
  exact ⟨coefficient_finite_projective.{2, 3}.1, coefficient_finite_projective.{2, 3}.2,
    ideal_hom_finite_projective.{1, 2, 0, 3}.1, ideal_hom_finite_projective.{1, 2, 0, 3}.2,
    matrixIdealSource_not_free.{1, 0}, sourceGenerator_ne_zero.{1, 0},
    idealInclusion_nonzero_nonfree.{1, 0, 3}.2.1, idealInclusion_left_order.{1, 2, 0, 3}.1,
    idealInclusion_left_order.{1, 2, 0, 3}.2.1, idealInclusion_left_order.{1, 2, 0, 3}.2.2.1,
    idealInclusion_movement.{1, 2, 0, 3}.1, idealInclusion_movement.{1, 2, 0, 3}.2⟩

-- Reverse the independent heights to (uA, uS, uM, uN) = (0, 1, 3, 2)
-- and ask inference directly again, without a Hom-finite witness.
example : Module.Finite (ULift.{1} IntMatrix)
    (matrixIdealSource.{0, 3} →ₗ[(ULift.{0} IntMatrix)ᵐᵒᵖ] ULift.{2} IntMatrix) := by
  letI : Module.Finite (ULift.{0} IntMatrix)ᵐᵒᵖ matrixIdealSource.{0, 3} :=
    matrixIdealSource_finite_projective.{0, 3}.1
  letI : Module.Projective (ULift.{0} IntMatrix)ᵐᵒᵖ matrixIdealSource.{0, 3} :=
    matrixIdealSource_finite_projective.{0, 3}.2
  letI : Module.Finite (ULift.{1} IntMatrix) (ULift.{2} IntMatrix) :=
    coefficient_finite_projective.{1, 2}.1
  exact inferInstance

/-- A universe-three nonfree source maps to a universe-two coefficient;
its inner and outer scalar rings occupy universes zero and one. -/
theorem higher_source_carrier_control :
    Module.Finite (ULift.{1} IntMatrix) (ULift.{2} IntMatrix) ∧
      Module.Projective (ULift.{1} IntMatrix) (ULift.{2} IntMatrix) ∧
      Module.Projective (ULift.{1} IntMatrix)
        (matrixIdealSource.{0, 3} →ₗ[(ULift.{0} IntMatrix)ᵐᵒᵖ] ULift.{2} IntMatrix) ∧
      Module.Finite (ULift.{1} IntMatrix)
        (matrixIdealSource.{0, 3} →ₗ[(ULift.{0} IntMatrix)ᵐᵒᵖ] ULift.{2} IntMatrix) ∧
      ¬ Module.Free (ULift.{0} IntMatrix)ᵐᵒᵖ matrixIdealSource.{0, 3} ∧
      sourceGenerator.{0, 3} ≠ 0 ∧ idealInclusion.{0, 3, 2} ≠ 0 ∧
      ((ULift.up intE11 : ULift.{1} IntMatrix) • idealInclusion.{0, 3, 2})
        (ULift.up matrixUpperRightMember) = (ULift.up intE01 : ULift.{2} IntMatrix) ∧
      idealInclusion.{0, 3, 2} (ULift.up matrixUpperRightMember) *
        (ULift.up intE11 : ULift.{2} IntMatrix) = 0 ∧
      (ULift.up intE01 : ULift.{2} IntMatrix) ≠ 0 ∧
      ((ULift.up intE01 : ULift.{1} IntMatrix) • idealInclusion.{0, 3, 2})
        sourceGenerator.{0, 3} = 0 ∧
      (ULift.up intE01 : ULift.{1} IntMatrix) • idealInclusion.{0, 3, 2} ≠
        idealInclusion.{0, 3, 2} := by
  exact ⟨coefficient_finite_projective.{1, 2}.1, coefficient_finite_projective.{1, 2}.2,
    ideal_hom_finite_projective.{0, 1, 3, 2}.1, ideal_hom_finite_projective.{0, 1, 3, 2}.2,
    matrixIdealSource_not_free.{0, 3}, sourceGenerator_ne_zero.{0, 3},
    idealInclusion_nonzero_nonfree.{0, 3, 2}.2.1, idealInclusion_left_order.{0, 1, 3, 2}.1,
    idealInclusion_left_order.{0, 1, 3, 2}.2.1, idealInclusion_left_order.{0, 1, 3, 2}.2.2.1,
    idealInclusion_movement.{0, 1, 3, 2}.1, idealInclusion_movement.{0, 1, 3, 2}.2⟩

end ProjectiveModulesTests.FiniteProjectiveHomUniverseClient

end -- noncomputable section

end -- section
