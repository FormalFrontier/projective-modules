/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModulesTests.FiniteProjectiveRestrictionModelClient
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift

/-!
# Scalar restriction of matrix ideals in independent universes

The principal right ideal of the first diagonal unit in `M₂(ℤ)` supplies a
nonzero finite-projective module. Lifting its carrier and the scalar ring
separately gives examples of canonical scalar restriction with independent
source-scalar, target-scalar and module universes. The ring maps are identity
maps conjugated by `ULift.ringEquiv`.

Finiteness and projectivity of the source, the restricted regular coefficient
and the restricted ideal are each transported from their respective known
modules by semilinear equivalences. The coefficient carrier has the target
scalar universe; the ideal carrier has the module universe before and after
restriction. The three closed examples separate each of these universes from
the other two.

The restricted doubling map moves a nonzero generator to a nonzero value.
The regular coefficient action computes as right multiplication, and the
idempotent kills the nonzero upper-right member of the ideal.

## References

These examples reuse Mathlib's `ModuleCat.restrictScalars`, `Module.compHom`,
`ULift.ringEquiv` and semilinear transport of finiteness and projectivity,
together with the matrix right-ideal bundle and its public linear-equivalence
and generator API from Projective Modules.
-/

@[expose] public section

universe uR uS uM

noncomputable section

namespace ProjectiveModulesTests.FiniteProjectiveRestrictionUniverseClient

open CategoryTheory ModuleCat
open IdempotentSpanSemiringClient RightIdealRingConstructorClient

/-- The equivalence from the matrix opposite ring to its lifted opposite ring. -/
def matrixScalarEquiv : IntMatrixᵐᵒᵖ ≃+* (ULift.{uR} IntMatrix)ᵐᵒᵖ :=
  (ULift.ringEquiv : ULift.{uR} IntMatrix ≃+* IntMatrix).symm.op

/-- The identity matrix-ring equivalence conjugated by two universe lifts. -/
def matrixIdentityEquiv : ULift.{uR} IntMatrix ≃+* ULift.{uS} IntMatrix :=
  (ULift.ringEquiv : ULift.{uR} IntMatrix ≃+* IntMatrix).trans
    (ULift.ringEquiv : ULift.{uS} IntMatrix ≃+* IntMatrix).symm

/-- The conjugated identity sends a lifted matrix to the same lifted matrix. -/
@[simp]
theorem matrixIdentityEquiv_up (A : IntMatrix) :
    matrixIdentityEquiv.{uR, uS} (ULift.up A) = ULift.up A :=
  rfl

local instance matrixScalarInvPair :
    RingHomInvPair matrixScalarEquiv.{uR}.toRingHom
      matrixScalarEquiv.{uR}.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv matrixScalarEquiv

local instance matrixScalarInvPairSymm :
    RingHomInvPair matrixScalarEquiv.{uR}.symm.toRingHom
      matrixScalarEquiv.{uR}.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm matrixScalarEquiv

/-- The matrix right ideal with its carrier and scalar ring lifted separately. -/
def matrixIdealSource : ModuleCat.{uM} (ULift.{uS} IntMatrix)ᵐᵒᵖ :=
  letI := Module.compHom (ULift.{uM} matrixRightIdeal)
    matrixScalarEquiv.{uS}.symm.toRingHom
  ModuleCat.of (ULift.{uS} IntMatrix)ᵐᵒᵖ (ULift.{uM} matrixRightIdeal)

/-- The source ideal has precisely the chosen lifted ideal carrier. -/
theorem matrixIdealSource_carrier :
    (matrixIdealSource.{uS, uM} : Type uM) = ULift.{uM} matrixRightIdeal :=
  rfl

/-- The canonical semilinear equivalence to the lifted source ideal. -/
def matrixIdealSourceEquiv :
    matrixRightIdeal ≃ₛₗ[matrixScalarEquiv.{uS}.toRingHom]
      matrixIdealSource.{uS, uM} where
  __ := (AddEquiv.ulift : ULift.{uM} matrixRightIdeal ≃+ matrixRightIdeal).symm
  map_smul' _ _ := rfl

/-- The source equivalence lifts an ideal member without changing its value. -/
@[simp]
theorem matrixIdealSourceEquiv_apply (m : matrixRightIdeal) :
    matrixIdealSourceEquiv.{uS, uM} m = ULift.up m :=
  rfl

/-- The source action is the pullback of the given matrix right-ideal action. -/
theorem matrixIdealSource_smul (r : (ULift.{uS} IntMatrix)ᵐᵒᵖ)
    (m : matrixRightIdeal) :
    r • (show matrixIdealSource.{uS, uM} from ULift.up m) =
      (show matrixIdealSource.{uS, uM} from
        ULift.up (matrixScalarEquiv.{uS}.symm r • m)) :=
  rfl

/-- The lifted source ideal is finite projective by semilinear transport. -/
theorem matrixIdealSource_finite_projective :
    isFiniteProjective (ULift.{uS} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uS, uM} :=
  ⟨Module.Finite.of_surjective matrixIdealSourceEquiv.toLinearMap
      matrixIdealSourceEquiv.surjective,
    Module.Projective.of_equiv matrixIdealSourceEquiv⟩

/-- The lifted matrix ideal, bundled as a finite-projective source module. -/
def matrixIdeal : FiniteProjective.{uS, uM} (ULift.{uS} IntMatrix)ᵐᵒᵖ :=
  ⟨matrixIdealSource, matrixIdealSource_finite_projective⟩

/-- The finite-projective bundle has the displayed source module as its object. -/
@[simp]
theorem matrixIdeal_obj : matrixIdeal.{uS, uM}.obj = matrixIdealSource.{uS, uM} :=
  rfl

/-- The canonical restricted regular coefficient has the target scalar carrier. -/
def matrixCoefficient : ModuleCat.{uS} (ULift.{uR} IntMatrix)ᵐᵒᵖ :=
  (ModuleCat.restrictScalars matrixIdentityEquiv.{uR, uS}.toRingHom.op).obj
    (ModuleCat.of (ULift.{uS} IntMatrix)ᵐᵒᵖ (ULift.{uS} IntMatrix)ᵐᵒᵖ)

/-- The coefficient carrier uses the target scalar universe. -/
theorem matrixCoefficient_carrier :
    (matrixCoefficient.{uR, uS} : Type uS) = (ULift.{uS} IntMatrix)ᵐᵒᵖ :=
  rfl

/-- The regular opposite module identifies semilinearly with the coefficient. -/
def matrixCoefficientEquiv :
    IntMatrixᵐᵒᵖ ≃ₛₗ[matrixScalarEquiv.{uR}.toRingHom]
      matrixCoefficient.{uR, uS} where
  __ := matrixScalarEquiv.{uS}.toAddEquiv
  map_smul' _ _ := rfl

/-- The coefficient equivalence lifts the underlying matrix. -/
@[simp]
theorem matrixCoefficientEquiv_apply (A : IntMatrix) :
    matrixCoefficientEquiv.{uR, uS} (MulOpposite.op A) =
      MulOpposite.op (ULift.up A) :=
  rfl

/-- The canonical coefficient is finite projective, independently of the ideal. -/
theorem matrixCoefficient_finite_projective :
    isFiniteProjective (ULift.{uR} IntMatrix)ᵐᵒᵖ matrixCoefficient.{uR, uS} :=
  ⟨Module.Finite.of_surjective matrixCoefficientEquiv.toLinearMap
      matrixCoefficientEquiv.surjective,
    Module.Projective.of_equiv matrixCoefficientEquiv⟩

/-- The stored coefficient action is right multiplication by the image scalar. -/
theorem matrixCoefficient_unop_smul (r : ULift.{uR} IntMatrix)
    (s : ULift.{uS} IntMatrix) :
    MulOpposite.unop (MulOpposite.op r •
      (show matrixCoefficient.{uR, uS} from MulOpposite.op s)) =
        s * matrixIdentityEquiv.{uR, uS} r := by
  let x : ModuleCat.of (ULift.{uS} IntMatrix)ᵐᵒᵖ
      (ULift.{uS} IntMatrix)ᵐᵒᵖ := MulOpposite.op s
  let y : matrixCoefficient.{uR, uS} := MulOpposite.op s
  change MulOpposite.unop (MulOpposite.op r • y) = s * matrixIdentityEquiv r
  exact (congrArg MulOpposite.unop
    (ModuleCat.restrictScalars.smul_def' matrixIdentityEquiv.{uR, uS}.toRingHom.op
      (M := ModuleCat.of (ULift.{uS} IntMatrix)ᵐᵒᵖ (ULift.{uS} IntMatrix)ᵐᵒᵖ)
      (MulOpposite.op r) x)).trans (by rfl)

/-- Right multiplication kills the upper-right unit, whereas left multiplication
by the same image idempotent does not. -/
theorem matrixCoefficient_action_boundary :
    MulOpposite.unop (MulOpposite.op (ULift.up intE11) •
      (show matrixCoefficient.{uR, uS} from MulOpposite.op (ULift.up intE01))) = 0 ∧
      matrixIdentityEquiv.{uR, uS} (ULift.up intE11) * ULift.up intE01 ≠ 0 := by
  constructor
  · rw [matrixCoefficient_unop_smul]
    change ULift.up (intE01 * intE11) = (0 : ULift.{uS} IntMatrix)
    rw [intE01_mul_e11]
    rfl
  · intro h
    have hmul : intE11 * intE01 = 0 := congrArg ULift.down h
    rw [intE11_mul_e01] at hmul
    exact intE01_ne_zero hmul

/-- The matrix ideal restricted by the conjugated identity on opposite rings. -/
def restrictedIdeal : ModuleCat.{uM} (ULift.{uR} IntMatrix)ᵐᵒᵖ :=
  (ModuleCat.restrictScalars matrixIdentityEquiv.{uR, uS}.toRingHom.op).obj
    matrixIdeal.{uS, uM}.obj

/-- Restriction leaves the module carrier in its chosen universe. -/
theorem restrictedIdeal_carrier :
    (restrictedIdeal.{uR, uS, uM} : Type uM) = ULift.{uM} matrixRightIdeal :=
  rfl

/-- The original matrix ideal identifies semilinearly with the restricted ideal. -/
def restrictedIdealEquiv :
    matrixRightIdeal ≃ₛₗ[matrixScalarEquiv.{uR}.toRingHom]
      restrictedIdeal.{uR, uS, uM} where
  __ := (AddEquiv.ulift : ULift.{uM} matrixRightIdeal ≃+ matrixRightIdeal).symm
  map_smul' _ _ := rfl

/-- The restricted-ideal equivalence lifts an ideal member unchanged. -/
@[simp]
theorem restrictedIdealEquiv_apply (m : matrixRightIdeal) :
    restrictedIdealEquiv.{uR, uS, uM} m = ULift.up m :=
  rfl

/-- The restricted ideal is finite projective by its own semilinear equivalence. -/
theorem restrictedIdeal_finite_projective :
    isFiniteProjective (ULift.{uR} IntMatrix)ᵐᵒᵖ restrictedIdeal.{uR, uS, uM} :=
  ⟨Module.Finite.of_surjective restrictedIdealEquiv.toLinearMap
      restrictedIdealEquiv.surjective,
    Module.Projective.of_equiv restrictedIdealEquiv⟩

/-- Lifting both scalar and module universes does not make the matrix ideal free. -/
theorem matrixIdealSource_not_free :
    ¬ Module.Free (ULift.{uS} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uS, uM} := by
  intro hfree
  let : Module.Free (ULift.{uS} IntMatrix)ᵐᵒᵖ matrixIdealSource.{uS, uM} := hfree
  exact FiniteProjectiveRestrictionModelClient.matrixRightIdeal_not_free
    (Module.Free.of_equiv matrixIdealSourceEquiv.symm)

/-- The independently transported restricted ideal is not free. -/
theorem restrictedIdeal_not_free :
    ¬ Module.Free (ULift.{uR} IntMatrix)ᵐᵒᵖ restrictedIdeal.{uR, uS, uM} := by
  intro hfree
  let : Module.Free (ULift.{uR} IntMatrix)ᵐᵒᵖ restrictedIdeal.{uR, uS, uM} := hfree
  exact FiniteProjectiveRestrictionModelClient.matrixRightIdeal_not_free
    (Module.Free.of_equiv restrictedIdealEquiv.symm)

/-- The lifted principal generator in the finite-projective source ideal. -/
def sourceGenerator : matrixIdeal.{uS, uM} :=
  ULift.up matrixGenerator

/-- The source principal generator remains nonzero. -/
theorem sourceGenerator_ne_zero : sourceGenerator.{uS, uM} ≠ 0 := by
  intro h
  exact matrixGenerator_ne_zero (congrArg ULift.down h)

/-- The lifted nonzero principal generator in the restricted ideal. -/
def restrictedGenerator : restrictedIdeal.{uR, uS, uM} :=
  ULift.up matrixGenerator

/-- The lifted upper-right member in the restricted ideal. -/
def restrictedUpperRightMember : restrictedIdeal.{uR, uS, uM} :=
  ULift.up matrixUpperRightMember

/-- The restricted principal generator remains nonzero. -/
theorem restrictedGenerator_ne_zero : restrictedGenerator.{uR, uS, uM} ≠ 0 := by
  intro h
  exact matrixGenerator_ne_zero (congrArg ULift.down h)

/-- The restricted upper-right member remains nonzero. -/
theorem restrictedUpperRightMember_ne_zero :
    restrictedUpperRightMember.{uR, uS, uM} ≠ 0 := by
  intro h
  exact matrixUpperRightMember_ne_zero (congrArg ULift.down h)

/-- The stored restricted action kills the nonzero upper-right member. -/
theorem restrictedIdeal_action_boundary :
    MulOpposite.op (ULift.up intE11) •
        restrictedUpperRightMember.{uR, uS, uM} = 0 ∧
      restrictedUpperRightMember.{uR, uS, uM} ≠ 0 := by
  refine ⟨?_, restrictedUpperRightMember_ne_zero⟩
  let r : (ULift.{uR} IntMatrix)ᵐᵒᵖ := MulOpposite.op (ULift.up intE11)
  let s : (ULift.{uS} IntMatrix)ᵐᵒᵖ := MulOpposite.op (ULift.up intE11)
  let x : matrixIdealSource.{uS, uM} := ULift.up matrixUpperRightMember
  let y : restrictedIdeal.{uR, uS, uM} := restrictedUpperRightMember
  have hsource : s • x = 0 :=
    (matrixIdealSource_smul s matrixUpperRightMember).trans
      (congrArg (fun m : matrixRightIdeal ↦
        (show matrixIdealSource.{uS, uM} from ULift.up m)) matrix_right_action_boundary.1)
  change r • y = 0
  exact (ModuleCat.restrictScalars.smul_def matrixIdentityEquiv.{uR, uS}.toRingHom.op
    (M := matrixIdeal.{uS, uM}.obj) r y).trans hsource

/-- The additive doubling endomorphism of the source matrix ideal. -/
def matrixIdealDouble : matrixIdeal.{uS, uM}.obj ⟶ matrixIdeal.{uS, uM}.obj :=
  ModuleCat.ofHom (X := matrixIdealSource.{uS, uM}) (Y := matrixIdealSource.{uS, uM})
    ((LinearMap.id : matrixIdealSource.{uS, uM} →ₗ[(ULift.{uS} IntMatrix)ᵐᵒᵖ]
      matrixIdealSource.{uS, uM}) + LinearMap.id)

/-- The source doubling endomorphism evaluates by adding an element to itself. -/
@[simp]
theorem matrixIdealDouble_apply (x : matrixIdeal.{uS, uM}.obj) :
    matrixIdealDouble.{uS, uM} x = x + x :=
  rfl

/-- The canonical restriction of the source doubling endomorphism. -/
def restrictedDouble : restrictedIdeal.{uR, uS, uM} ⟶ restrictedIdeal.{uR, uS, uM} :=
  (ModuleCat.restrictScalars matrixIdentityEquiv.{uR, uS}.toRingHom.op).map
    matrixIdealDouble.{uS, uM}

/-- The existing restriction functor keeps the doubling map's pointwise values. -/
@[simp]
theorem restrictedDouble_apply (x : restrictedIdeal.{uR, uS, uM}) :
    restrictedDouble.{uR, uS, uM} x = x + x := by
  let xSource : matrixIdealSource.{uS, uM} := x
  let y : restrictedIdeal.{uR, uS, uM} := x + x
  change (ModuleCat.restrictScalars matrixIdentityEquiv.{uR, uS}.toRingHom.op).map
    matrixIdealDouble.{uS, uM} x = y
  exact (ModuleCat.restrictScalars.map_apply matrixIdentityEquiv.{uR, uS}.toRingHom.op
    matrixIdealDouble.{uS, uM} x).trans (matrixIdealDouble_apply xSource)

/-- Doubling moves the specified nonzero principal generator. -/
theorem restrictedDouble_generator_ne :
    restrictedDouble.{uR, uS, uM} restrictedGenerator ≠ restrictedGenerator := by
  rw [restrictedDouble_apply]
  intro h
  apply restrictedGenerator_ne_zero
  exact add_left_cancel (by simpa only [add_zero] using h)

/-- Doubling the specified principal generator has a nonzero matrix entry. -/
theorem restrictedDouble_generator_ne_zero :
    restrictedDouble.{uR, uS, uM} restrictedGenerator ≠ 0 := by
  rw [restrictedDouble_apply]
  intro h
  have hbase : matrixGenerator + matrixGenerator = 0 := congrArg ULift.down h
  let E : matrixRightIdeal ≃ₗ[IntMatrixᵐᵒᵖ] Ideal.span {MulOpposite.op intE11} :=
    IsIdempotentElem.rightSpanFiniteProjectiveLinearEquiv intE11_isIdempotent
  have hgen : (Ideal.span {MulOpposite.op intE11}).subtype (E matrixGenerator) =
      MulOpposite.op intE11 := matrixGenerator_coe
  have hscalar : MulOpposite.op intE11 + MulOpposite.op intE11 = 0 := by
    simpa only [map_add, map_zero, hgen] using
      congrArg (fun m : matrixRightIdeal ↦
        (Ideal.span {MulOpposite.op intE11}).subtype (E m)) hbase
  have hentry := congrArg (fun A : IntMatrixᵐᵒᵖ ↦ MulOpposite.unop A 0 0) hscalar
  simp [intE11] at hentry

/-- A target scalar ring in universe one with a universe-zero ideal carrier. -/
def higherCoefficientSource : FiniteProjective.{1, 0} (ULift.{1} IntMatrix)ᵐᵒᵖ :=
  matrixIdeal.{1, 0}

/-- Restriction to universe-zero scalars keeps the universe-zero ideal carrier. -/
def higherCoefficientObject : ModuleCat.{0} (ULift.{0} IntMatrix)ᵐᵒᵖ :=
  restrictedIdeal.{0, 1, 0}

/-- The displayed universe-zero object is the canonical restriction of the
universe-zero source carrier over universe-one target scalars. -/
theorem higherCoefficientObject_eq :
    higherCoefficientObject =
      (ModuleCat.restrictScalars matrixIdentityEquiv.{0, 1}.toRingHom.op).obj
        higherCoefficientSource.obj :=
  rfl

/-- The source and restricted ideal are nonfree at levels `(0, 1, 0)`. -/
theorem higherCoefficient_nonfree_control :
    ¬ Module.Free (ULift.{1} IntMatrix)ᵐᵒᵖ higherCoefficientSource ∧
      ¬ Module.Free (ULift.{0} IntMatrix)ᵐᵒᵖ higherCoefficientObject :=
  ⟨matrixIdealSource_not_free, restrictedIdeal_not_free⟩

/-- The source, coefficient and restricted object are finite projective for
scalar and carrier levels `(0, 1, 0)`, with a nonzero moving-map witness. -/
theorem higherCoefficient_control :
    isFiniteProjective (ULift.{1} IntMatrix)ᵐᵒᵖ higherCoefficientSource.obj ∧
      isFiniteProjective (ULift.{0} IntMatrix)ᵐᵒᵖ matrixCoefficient.{0, 1} ∧
      isFiniteProjective (ULift.{0} IntMatrix)ᵐᵒᵖ higherCoefficientObject ∧
      (matrixCoefficient.{0, 1} : Type 1) = (ULift.{1} IntMatrix)ᵐᵒᵖ ∧
      (higherCoefficientObject : Type 0) = ULift.{0} matrixRightIdeal ∧
      sourceGenerator.{1, 0} ≠ 0 ∧
      restrictedGenerator.{0, 1, 0} ≠ 0 ∧
      restrictedDouble.{0, 1, 0} restrictedGenerator ≠ 0 ∧
      restrictedDouble.{0, 1, 0} restrictedGenerator ≠ restrictedGenerator ∧
      (MulOpposite.op (ULift.up intE11) • restrictedUpperRightMember.{0, 1, 0} = 0 ∧
        restrictedUpperRightMember.{0, 1, 0} ≠ 0) :=
  ⟨higherCoefficientSource.property, matrixCoefficient_finite_projective,
    restrictedIdeal_finite_projective, matrixCoefficient_carrier, restrictedIdeal_carrier,
    sourceGenerator_ne_zero, restrictedGenerator_ne_zero, restrictedDouble_generator_ne_zero,
    restrictedDouble_generator_ne, restrictedIdeal_action_boundary⟩

/-- A universe-zero target scalar ring and a universe-zero ideal carrier. -/
def higherSourceScalarSource : FiniteProjective.{0, 0} (ULift.{0} IntMatrix)ᵐᵒᵖ :=
  matrixIdeal.{0, 0}

/-- Restriction to universe-one scalars keeps the universe-zero ideal carrier. -/
def higherSourceScalarObject : ModuleCat.{0} (ULift.{1} IntMatrix)ᵐᵒᵖ :=
  restrictedIdeal.{1, 0, 0}

/-- The displayed universe-zero object is the canonical restriction to
universe-one source scalars. -/
theorem higherSourceScalarObject_eq :
    higherSourceScalarObject =
      (ModuleCat.restrictScalars matrixIdentityEquiv.{1, 0}.toRingHom.op).obj
        higherSourceScalarSource.obj :=
  rfl

/-- The source and restricted ideal are nonfree at levels `(1, 0, 0)`. -/
theorem higherSourceScalar_nonfree_control :
    ¬ Module.Free (ULift.{0} IntMatrix)ᵐᵒᵖ higherSourceScalarSource ∧
      ¬ Module.Free (ULift.{1} IntMatrix)ᵐᵒᵖ higherSourceScalarObject :=
  ⟨matrixIdealSource_not_free, restrictedIdeal_not_free⟩

/-- The source, coefficient and restricted object are finite projective for
scalar and carrier levels `(1, 0, 0)`, with a nonzero moving-map witness. -/
theorem higherSourceScalar_control :
    isFiniteProjective (ULift.{0} IntMatrix)ᵐᵒᵖ higherSourceScalarSource.obj ∧
      isFiniteProjective (ULift.{1} IntMatrix)ᵐᵒᵖ matrixCoefficient.{1, 0} ∧
      isFiniteProjective (ULift.{1} IntMatrix)ᵐᵒᵖ higherSourceScalarObject ∧
      (matrixCoefficient.{1, 0} : Type 0) = (ULift.{0} IntMatrix)ᵐᵒᵖ ∧
      (higherSourceScalarObject : Type 0) = ULift.{0} matrixRightIdeal ∧
      sourceGenerator.{0, 0} ≠ 0 ∧
      restrictedGenerator.{1, 0, 0} ≠ 0 ∧
      restrictedDouble.{1, 0, 0} restrictedGenerator ≠ 0 ∧
      restrictedDouble.{1, 0, 0} restrictedGenerator ≠ restrictedGenerator ∧
      (MulOpposite.op (ULift.up intE11) • restrictedUpperRightMember.{1, 0, 0} = 0 ∧
        restrictedUpperRightMember.{1, 0, 0} ≠ 0) :=
  ⟨higherSourceScalarSource.property, matrixCoefficient_finite_projective,
    restrictedIdeal_finite_projective, matrixCoefficient_carrier, restrictedIdeal_carrier,
    sourceGenerator_ne_zero, restrictedGenerator_ne_zero, restrictedDouble_generator_ne_zero,
    restrictedDouble_generator_ne, restrictedIdeal_action_boundary⟩

/-- A universe-one ideal carrier over a universe-zero target scalar ring. -/
def higherCarrierSource : FiniteProjective.{0, 1} (ULift.{0} IntMatrix)ᵐᵒᵖ :=
  matrixIdeal.{0, 1}

/-- Restriction between universe-zero scalars keeps the universe-one carrier. -/
def higherCarrierObject : ModuleCat.{1} (ULift.{0} IntMatrix)ᵐᵒᵖ :=
  restrictedIdeal.{0, 0, 1}

/-- The displayed universe-one object is the canonical restriction of the
universe-one source carrier between universe-zero scalar rings. -/
theorem higherCarrierObject_eq :
    higherCarrierObject =
      (ModuleCat.restrictScalars matrixIdentityEquiv.{0, 0}.toRingHom.op).obj
        higherCarrierSource.obj :=
  rfl

/-- The source and restricted ideal are nonfree at levels `(0, 0, 1)`. -/
theorem higherCarrier_nonfree_control :
    ¬ Module.Free (ULift.{0} IntMatrix)ᵐᵒᵖ higherCarrierSource ∧
      ¬ Module.Free (ULift.{0} IntMatrix)ᵐᵒᵖ higherCarrierObject :=
  ⟨matrixIdealSource_not_free, restrictedIdeal_not_free⟩

/-- The source, coefficient and restricted object are finite projective for
scalar and carrier levels `(0, 0, 1)`, with a nonzero moving-map witness. -/
theorem higherCarrier_control :
    isFiniteProjective (ULift.{0} IntMatrix)ᵐᵒᵖ higherCarrierSource.obj ∧
      isFiniteProjective (ULift.{0} IntMatrix)ᵐᵒᵖ matrixCoefficient.{0, 0} ∧
      isFiniteProjective (ULift.{0} IntMatrix)ᵐᵒᵖ higherCarrierObject ∧
      (matrixCoefficient.{0, 0} : Type 0) = (ULift.{0} IntMatrix)ᵐᵒᵖ ∧
      (higherCarrierObject : Type 1) = ULift.{1} matrixRightIdeal ∧
      sourceGenerator.{0, 1} ≠ 0 ∧
      restrictedGenerator.{0, 0, 1} ≠ 0 ∧
      restrictedDouble.{0, 0, 1} restrictedGenerator ≠ 0 ∧
      restrictedDouble.{0, 0, 1} restrictedGenerator ≠ restrictedGenerator ∧
      (MulOpposite.op (ULift.up intE11) • restrictedUpperRightMember.{0, 0, 1} = 0 ∧
        restrictedUpperRightMember.{0, 0, 1} ≠ 0) :=
  ⟨higherCarrierSource.property, matrixCoefficient_finite_projective,
    restrictedIdeal_finite_projective, matrixCoefficient_carrier, restrictedIdeal_carrier,
    sourceGenerator_ne_zero, restrictedGenerator_ne_zero, restrictedDouble_generator_ne_zero,
    restrictedDouble_generator_ne, restrictedIdeal_action_boundary⟩

end ProjectiveModulesTests.FiniteProjectiveRestrictionUniverseClient
