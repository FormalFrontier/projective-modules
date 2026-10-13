/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Dual.ModuleCat
public import ProjectiveModulesTests.RightDualFunctorClient
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Ring.ULift

/-!
# The right-module dual with independently lifted carrier and coefficients

The right regular module of `M₂(ℤ)` gives two mixed-universe clients of
`ModuleCat.rightDual`: coefficient/source levels `(0, 1)` and `(1, 0)`.
Both dual objects have their natural Hom carrier in `Type 1`. The second
source carrier remains the original matrix ring in `Type 0`, with its
stored opposite-ring action obtained by canonical restriction of scalars.

The maps are compositions of the `LinearMap.mulLeft` provider with
`ULift.moduleEquiv` and its inverse. No new lifted action or equivalence
body is constructed. The public functor interface computes precomposition
and the left coefficient action. Matrix units detect nonzero moving maps,
nonzero moving scalars, and the contravariant order of composition in both
models. A raw right-coefficient function fails right linearity in each.

## References

* Mathlib's `ULift.moduleEquiv`, `ULift.ringEquiv`, `Module.compHom`,
  `ModuleCat.restrictScalars`, and `LinearMap.mulLeft`.
* `ProjectiveModules.Module.RightRegular` for the ordinary right regular
  scalar convention, and `ProjectiveModules.Dual.ModuleCat` for the functor.
* The matrix-unit identities in
  `ProjectiveModulesTests.RightDualFunctorClient`.
-/

@[expose] public section

namespace ProjectiveModulesTests.RightDualUniverseClient

open CategoryTheory Opposite
open RightDualFunctorClient

namespace CarrierLift

/-- A genuinely universe-one source over the universe-zero matrix ring. -/
abbrev modelModule : ModuleCat.{1} MatrixRingᵐᵒᵖ :=
  ModuleCat.of MatrixRingᵐᵒᵖ (ULift.{1} MatrixRing)

/-- The down linear equivalence, specialized to the right regular action. -/
def down : modelModule ≃ₗ[MatrixRingᵐᵒᵖ] MatrixRing :=
  ULift.moduleEquiv (R := MatrixRingᵐᵒᵖ) (M := MatrixRing)

/-- The source carrier is lifted, without changing coefficient universes. -/
theorem source_carrier : (modelModule : Type 1) = ULift.{1} MatrixRing :=
  rfl

/-- The mixed-universe functor object has the ordinary Hom carrier. -/
theorem object_eq :
    (ModuleCat.rightDual.{0, 1} MatrixRing).obj (op modelModule) =
      ModuleCat.of MatrixRing (modelModule →ₗ[MatrixRingᵐᵒᵖ] MatrixRing) :=
  ModuleCat.rightDual_obj MatrixRing (op modelModule)

/-- In particular, the dual carrier is in `Type 1`. -/
theorem object_carrier :
    ((ModuleCat.rightDual.{0, 1} MatrixRing).obj (op modelModule) : Type 1) =
      (modelModule →ₗ[MatrixRingᵐᵒᵖ] MatrixRing) :=
  congrArg (fun N : ModuleCat.{1} MatrixRing => (N : Type 1)) object_eq

/-- The inherited source actor is right multiplication, not left multiplication. -/
theorem source_smul (b x : MatrixRing) :
    MulOpposite.op b • (show modelModule from ULift.up x) = ULift.up (x * b) :=
  rfl

/-- The noncommuting source action retains a nonzero result in one order. -/
theorem source_actor_boundary :
    MulOpposite.op p • (show modelModule from ULift.up q) = 0 ∧
      MulOpposite.op q • (show modelModule from ULift.up p) = ULift.up q ∧
      (ULift.up q : modelModule) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [source_smul, q_mul_p]
    rfl
  · rw [source_smul, p_mul_q]
  · intro h
    exact q_ne_zero (congrArg ULift.down h)

/-- Left multiplication transported through the down equivalence. -/
def leftMul (b : MatrixRing) : modelModule ⟶ modelModule :=
  ModuleCat.ofHom (X := modelModule) (Y := modelModule)
    (down.symm.toLinearMap.comp
      ((LinearMap.mulLeft MatrixRingᵐᵒᵖ b).comp down.toLinearMap))

/-- A right-linear function in the universe-one functor object. -/
def dualMap (a : MatrixRing) :
    (ModuleCat.rightDual.{0, 1} MatrixRing).obj (op modelModule) :=
  (LinearMap.mulLeft MatrixRingᵐᵒᵖ a).comp down.toLinearMap

@[simp]
theorem leftMul_apply (b : MatrixRing) (x : modelModule) :
    leftMul b x = ULift.up (b * x.down) :=
  rfl

@[simp]
theorem dualMap_apply (a : MatrixRing) (x : modelModule) :
    dualMap a x = a * x.down :=
  rfl

/-- Right linearity belongs to the inherited ordinary codomain right action. -/
theorem dualMap_right_linear (a b : MatrixRing) (x : modelModule) :
    dualMap a (MulOpposite.op b • x) = dualMap a x * b :=
  (dualMap a).map_smul (MulOpposite.op b) x

/-- The public Hom characterization specializes to the transported source arrow. -/
theorem map_hom (b : MatrixRing) :
    ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul b).op).hom =
      LinearMap.lcomp MatrixRing MatrixRing (leftMul b).hom :=
  ModuleCat.rightDual_map_hom MatrixRing (leftMul b).op

/-- Public precomposition computes the ordinary product in the correct order. -/
theorem precompose_apply (a b : MatrixRing) (x : modelModule) :
    ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul b).op (dualMap a)) x =
      (a * b) * x.down := by
  rw [ModuleCat.rightDual_map_apply, Quiver.Hom.unop_op, leftMul_apply,
    dualMap_apply, mul_assoc]

/-- The precomposed vector is a vector in the functor object. -/
theorem precompose (a b : MatrixRing) :
    (ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul b).op (dualMap a) =
      dualMap (a * b) := by
  apply LinearMap.ext
  intro x
  rw [precompose_apply, dualMap_apply]

/-- The public scalar law uses ordinary left multiplication on the coefficient. -/
theorem scalar_apply (r a : MatrixRing) (x : modelModule) :
    (r • dualMap a) x = r * (a * x.down) := by
  rw [ModuleCat.rightDual_smul_apply MatrixRing (X := op modelModule), dualMap_apply]

/-- A fixed precomposition arrow is left-linear on the dual object. -/
theorem precompose_smul (r a b : MatrixRing) :
    (ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul b).op (r • dualMap a) =
      r • (ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul b).op (dualMap a) :=
  ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul b).op).hom.map_smul r _

/-- Evaluation after public precomposition preserves the left coefficient actor. -/
theorem precompose_scalar_apply (r a b : MatrixRing) (x : modelModule) :
    ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul b).op (r • dualMap a)) x =
      r * ((a * b) * x.down) := by
  rw [precompose_smul,
    ModuleCat.rightDual_smul_apply MatrixRing (X := op modelModule), precompose_apply]

/-- Identity precomposition fixes the chosen nonzero dual vector. -/
theorem identity_on_q :
    (ModuleCat.rightDual.{0, 1} MatrixRing).map (𝟙 (op modelModule)) (dualMap q) =
      dualMap q := by
  rw [CategoryTheory.Functor.map_id]
  exact ModuleCat.id_apply _ _

/-- The identity control is evaluated on a nonzero, rather than a killed, vector. -/
theorem identity_nonzero :
    ((ModuleCat.rightDual.{0, 1} MatrixRing).map (𝟙 (op modelModule))
        (dualMap q)) (ULift.up 1) = q ∧ q ≠ 0 := by
  refine ⟨?_, q_ne_zero⟩
  rw [identity_on_q, dualMap_apply, mul_one]

/-- Changing the source morphism produces two distinct nonzero values. -/
theorem moving_morphism_values :
    ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul p).op
        (dualMap 1)) (ULift.up 1) = p ∧
      ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul q).op
        (dualMap 1)) (ULift.up 1) = q := by
  constructor <;> rw [precompose_apply, one_mul, mul_one]

/-- The two precomposition maps move the same vector differently and nontrivially. -/
theorem moving_morphisms :
    ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul p).op
        (dualMap 1)) (ULift.up 1) ≠ 0 ∧
      ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul q).op
        (dualMap 1)) (ULift.up 1) ≠ 0 ∧
      (ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul p).op (dualMap 1) ≠
        (ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul q).op (dualMap 1) := by
  rcases moving_morphism_values with ⟨hp, hq⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hp]
    exact p_ne_zero
  · rw [hq]
    exact q_ne_zero
  · intro h
    have he := congrArg (fun f :
      (ModuleCat.rightDual.{0, 1} MatrixRing).obj (op modelModule) => f (ULift.up 1)) h
    rw [hp, hq] at he
    exact p_ne_q he

/-- Thus the functor maps, not merely their input source arrows, are distinct. -/
theorem moving_functor_maps :
    (ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul p).op ≠
      (ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul q).op := by
  intro h
  apply moving_morphisms.2.2
  exact congrArg (fun k :
    (ModuleCat.rightDual.{0, 1} MatrixRing).obj (op modelModule) ⟶
      (ModuleCat.rightDual.{0, 1} MatrixRing).obj (op modelModule) => k (dualMap 1)) h

/-- The left scalar actor also moves one vector to two distinct nonzero values. -/
theorem moving_scalars :
    (p • dualMap 1) (ULift.up 1) = p ∧
      (q • dualMap 1) (ULift.up 1) = q ∧
      (p • dualMap 1) (ULift.up 1) ≠ 0 ∧
      (q • dualMap 1) (ULift.up 1) ≠ 0 ∧
      p • dualMap 1 ≠ q • dualMap 1 := by
  have hp : (p • dualMap 1) (ULift.up 1) = p := by
    rw [scalar_apply, one_mul, mul_one]
  have hq : (q • dualMap 1) (ULift.up 1) = q := by
    rw [scalar_apply, one_mul, mul_one]
  refine ⟨hp, hq, ?_, ?_, ?_⟩
  · rw [hp]
    exact p_ne_zero
  · rw [hq]
    exact q_ne_zero
  · intro h
    have he := congrArg (fun f :
      (ModuleCat.rightDual.{0, 1} MatrixRing).obj (op modelModule) => f (ULift.up 1)) h
    rw [hp, hq] at he
    exact p_ne_q he

/-- Scalar/evaluation/precomposition has a nonzero value on both sides of left linearity. -/
theorem scalar_precomposition :
    ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul q).op
        (p • dualMap 1)) (ULift.up 1) = q ∧
      (p • (ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul q).op
        (dualMap 1)) (ULift.up 1) = q ∧ q ≠ 0 := by
  have h : ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul q).op
      (p • dualMap 1)) (ULift.up 1) = q := by
    rw [precompose_scalar_apply, one_mul, mul_one, p_mul_q]
  refine ⟨h, ?_, q_ne_zero⟩
  rw [← precompose_smul]
  exact h

/-- Ordered products distinguish the two genuine right-linear vectors. -/
theorem ordered_precomposition :
    ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul q).op
        (dualMap p)) (ULift.up 1) = q ∧
      ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul p).op
        (dualMap q)) (ULift.up 1) = 0 ∧ q ≠ 0 := by
  refine ⟨?_, ?_, q_ne_zero⟩
  · rw [precompose_apply, p_mul_q, mul_one]
  · rw [precompose_apply, q_mul_p, zero_mul]

/-- Source composition multiplies the matrix coefficients in categorical order. -/
theorem leftMul_comp (b c : MatrixRing) :
    leftMul b ≫ leftMul c = leftMul (c * b) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [ModuleCat.comp_apply, leftMul_apply c (leftMul b x), leftMul_apply b x,
    leftMul_apply (c * b) x, mul_assoc]

/-- The selected source composite has the nonzero order prescribed by the matrix units. -/
theorem source_composition_order :
    leftMul q ≫ leftMul p = leftMul q ∧
      leftMul p ≫ leftMul q = leftMul 0 := by
  constructor
  · rw [leftMul_comp, p_mul_q]
  · rw [leftMul_comp, q_mul_p]

/-- The functor reverses ordinary source composition. -/
theorem contravariant_composition (b c : MatrixRing) :
    (ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul b ≫ leftMul c).op =
      (ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul c).op ≫
        (ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul b).op := by
  rw [CategoryTheory.op_comp, Functor.map_comp]

/-- The correct reversed composite is nonzero; the false covariant order is zero. -/
theorem composition_order :
    ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul q ≫ leftMul p).op
        (dualMap 1)) (ULift.up 1) = q ∧
      ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul q).op
        ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul p).op
          (dualMap 1))) (ULift.up 1) = q ∧
      ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul p).op
        ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul q).op
          (dualMap 1))) (ULift.up 1) = 0 ∧ q ≠ 0 := by
  have h : ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul q).op
      ((ModuleCat.rightDual.{0, 1} MatrixRing).map (leftMul p).op
        (dualMap 1))) (ULift.up 1) = q := by
    rw [precompose 1 p, one_mul, precompose_apply, p_mul_q, mul_one]
  refine ⟨?_, h, ?_, q_ne_zero⟩
  · rw [contravariant_composition, ModuleCat.comp_apply]
    exact h
  · rw [precompose 1 q, one_mul, precompose_apply, q_mul_p, zero_mul]

/-- The tempting right-coefficient operation is only a raw function. -/
def wrongRight (x : modelModule) : MatrixRing :=
  x.down * p

/-- This raw function fails the source and codomain right-action law. -/
theorem wrongRight_not_right_linear :
    wrongRight (MulOpposite.op q • (show modelModule from ULift.up 1)) ≠
      MulOpposite.op q • wrongRight (ULift.up 1) := by
  rw [source_smul]
  change (1 * q) * p ≠ (1 * p) * q
  rw [one_mul, one_mul, q_mul_p, p_mul_q]
  exact Ne.symm q_ne_zero

/-- In particular, the wrong raw operation cannot be packaged as a right-linear map. -/
theorem wrongRight_no_linearMap :
    ¬ ∃ f : modelModule →ₗ[MatrixRingᵐᵒᵖ] MatrixRing,
      ∀ x, f x = wrongRight x := by
  rintro ⟨f, hf⟩
  apply wrongRight_not_right_linear
  calc
    wrongRight (MulOpposite.op q • (show modelModule from ULift.up 1)) =
        f (MulOpposite.op q • (show modelModule from ULift.up 1)) := (hf _).symm
    _ = MulOpposite.op q • f (ULift.up 1) := f.map_smul _ _
    _ = MulOpposite.op q • wrongRight (ULift.up 1) :=
      congrArg (fun y : MatrixRing => MulOpposite.op q • y) (hf _)

end CarrierLift

namespace CoefficientLift

/-- A genuinely universe-one coefficient ring. -/
abbrev CoefficientRing : Type 1 := ULift.{1} MatrixRing

/-- The down ring equivalence, with no new equivalence body. -/
def downRing : CoefficientRing ≃+* MatrixRing :=
  ULift.ringEquiv

/-- The source remains in `Type 0`, with the `Module.compHom` storing its actor. -/
abbrev modelModule : ModuleCat.{0} CoefficientRingᵐᵒᵖ :=
  letI := Module.compHom MatrixRing downRing.toRingHom.op
  ModuleCat.of CoefficientRingᵐᵒᵖ MatrixRing

-- Retain the bundled restriction action when its carrier reduces to `MatrixRing`.
local instance : Module CoefficientRingᵐᵒᵖ modelModule :=
  modelModule.isModule

-- Keep the coefficient codomain's ordinary right regular action, rather than
-- synthesizing a lifted action from the restricted source carrier.
local instance : Module CoefficientRingᵐᵒᵖ CoefficientRing :=
  Semiring.toOppositeModule

/-- This is precisely the canonical restriction bundle. -/
theorem source_eq_restrictScalars :
    modelModule = (ModuleCat.restrictScalars downRing.toRingHom.op).obj matrixModule :=
  rfl

/-- The module down equivalence for this restricted target action.
Its lifted-domain action is definitionally the ordinary coefficient right action. -/
def down : CoefficientRing ≃ₗ[CoefficientRingᵐᵒᵖ] modelModule :=
  ULift.moduleEquiv (R := CoefficientRingᵐᵒᵖ) (M := modelModule)

/-- Coefficient restriction does not lift the source carrier. -/
theorem source_carrier : (modelModule : Type 0) = MatrixRing :=
  rfl

/-- The independently lifted coefficient produces the natural universe-one Hom object. -/
theorem object_eq :
    (ModuleCat.rightDual.{1, 0} CoefficientRing).obj (op modelModule) =
      ModuleCat.of CoefficientRing (modelModule →ₗ[CoefficientRingᵐᵒᵖ] CoefficientRing) :=
  ModuleCat.rightDual_obj CoefficientRing (op modelModule)

/-- The Hom carrier is universe one although the source carrier is universe zero. -/
theorem object_carrier :
    ((ModuleCat.rightDual.{1, 0} CoefficientRing).obj (op modelModule) : Type 1) =
      (modelModule →ₗ[CoefficientRingᵐᵒᵖ] CoefficientRing) :=
  congrArg (fun N : ModuleCat.{1} CoefficientRing => (N : Type 1)) object_eq

/-- The stored source actor is the restriction of right multiplication. -/
theorem source_smul (b : MatrixRing) (x : modelModule) :
    MulOpposite.op (ULift.up b : CoefficientRing) • x = x * b :=
  ModuleCat.restrictScalars.smul_def downRing.toRingHom.op
    (M := matrixModule) (MulOpposite.op (ULift.up b)) x

/-- The ordinary coefficient's canonical right actor agrees with the lifted old actor. -/
theorem coefficient_right_smul (b x : MatrixRing) :
    MulOpposite.op (ULift.up b : CoefficientRing) •
      (ULift.up x : CoefficientRing) = ULift.up (x * b) :=
  rfl

/-- The ordinary coefficient's canonical left actor is left multiplication. -/
theorem coefficient_left_smul (r x : MatrixRing) :
    (ULift.up r : CoefficientRing) • (ULift.up x : CoefficientRing) =
      ULift.up (r * x) :=
  rfl

/-- The restricted source actor still detects the noncommuting matrix units. -/
theorem source_actor_boundary :
    MulOpposite.op (ULift.up p : CoefficientRing) • (show modelModule from q) = 0 ∧
      MulOpposite.op (ULift.up q : CoefficientRing) • (show modelModule from p) = q ∧
      (q : modelModule) ≠ 0 := by
  refine ⟨?_, ?_, q_ne_zero⟩
  · rw [source_smul, q_mul_p]
  · rw [source_smul, p_mul_q]

/-- Left multiplication transported using only the down module equivalence. -/
def leftMul (b : MatrixRing) : modelModule ⟶ modelModule :=
  ModuleCat.ofHom (X := modelModule) (Y := modelModule)
    (down.toLinearMap.comp
      ((LinearMap.mulLeft CoefficientRingᵐᵒᵖ (ULift.up b : CoefficientRing)).comp
        down.symm.toLinearMap))

/-- A right-linear function with ordinary lifted coefficient codomain, in the dual. -/
def dualMap (a : MatrixRing) :
    (ModuleCat.rightDual.{1, 0} CoefficientRing).obj (op modelModule) :=
  (LinearMap.mulLeft CoefficientRingᵐᵒᵖ (ULift.up a : CoefficientRing)).comp
    down.symm.toLinearMap

@[simp]
theorem leftMul_apply (b : MatrixRing) (x : modelModule) :
    leftMul b x = b * x :=
  rfl

@[simp]
theorem dualMap_apply (a : MatrixRing) (x : modelModule) :
    dualMap a x = (ULift.up (a * x) : CoefficientRing) :=
  rfl

/-- This is right linearity over the lifted opposite ring, not a left-source hypothesis. -/
theorem dualMap_right_linear (a b : MatrixRing) (x : modelModule) :
    dualMap a (MulOpposite.op (ULift.up b : CoefficientRing) • x) =
      dualMap a x * ULift.up b :=
  (dualMap a).map_smul (MulOpposite.op (ULift.up b)) x

/-- The same public Hom characterization works with independent coefficient universes. -/
theorem map_hom (b : MatrixRing) :
    ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul b).op).hom =
      LinearMap.lcomp CoefficientRing CoefficientRing (leftMul b).hom :=
  ModuleCat.rightDual_map_hom CoefficientRing (leftMul b).op

/-- Public precomposition preserves the ordered product with lifted coefficients. -/
theorem precompose_apply (a b : MatrixRing) (x : modelModule) :
    ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul b).op (dualMap a)) x =
      (ULift.up ((a * b) * x) : CoefficientRing) := by
  rw [ModuleCat.rightDual_map_apply CoefficientRing, Quiver.Hom.unop_op,
    leftMul_apply, dualMap_apply, mul_assoc]

/-- Equality of the precomposed vectors is in the mixed-universe functor object. -/
theorem precompose (a b : MatrixRing) :
    (ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul b).op (dualMap a) =
      dualMap (a * b) := by
  apply LinearMap.ext
  intro x
  rw [precompose_apply, dualMap_apply]

/-- Public scalar evaluation uses the coefficient's left, not right, actor. -/
theorem scalar_apply (r a : MatrixRing) (x : modelModule) :
    ((ULift.up r : CoefficientRing) • dualMap a) x =
      (ULift.up (r * (a * x)) : CoefficientRing) := by
  rw [ModuleCat.rightDual_smul_apply CoefficientRing (X := op modelModule), dualMap_apply]
  rfl

/-- For a fixed right-module arrow, the functor map is left coefficient-linear. -/
theorem precompose_smul (r : CoefficientRing) (a b : MatrixRing) :
    (ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul b).op (r • dualMap a) =
      r • (ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul b).op (dualMap a) :=
  ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul b).op).hom.map_smul r _

/-- Evaluation after precomposition retains the ordinary left coefficient action. -/
theorem precompose_scalar_apply (r a b : MatrixRing) (x : modelModule) :
    ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul b).op
        ((ULift.up r : CoefficientRing) • dualMap a)) x =
      (ULift.up (r * ((a * b) * x)) : CoefficientRing) := by
  rw [ModuleCat.rightDual_map_apply CoefficientRing, Quiver.Hom.unop_op,
    leftMul_apply, scalar_apply, mul_assoc]

/-- Identity precomposition retains the nonzero lifted upper-right matrix vector. -/
theorem identity_on_q :
    (ModuleCat.rightDual.{1, 0} CoefficientRing).map (𝟙 (op modelModule)) (dualMap q) =
      dualMap q := by
  rw [CategoryTheory.Functor.map_id]
  exact ModuleCat.id_apply _ _

/-- The identity control evaluates to a nonzero lifted matrix. -/
theorem identity_nonzero :
    ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (𝟙 (op modelModule))
        (dualMap q)) 1 = (ULift.up q : CoefficientRing) ∧
      (ULift.up q : CoefficientRing) ≠ 0 := by
  constructor
  · rw [identity_on_q, dualMap_apply, mul_one]
  · intro h
    exact q_ne_zero (congrArg ULift.down h)

/-- The map interface has two distinct nonzero moving-morphism values. -/
theorem moving_morphism_values :
    ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul p).op
        (dualMap 1)) 1 = (ULift.up p : CoefficientRing) ∧
      ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul q).op
        (dualMap 1)) 1 = (ULift.up q : CoefficientRing) := by
  constructor
  · rw [precompose_apply, one_mul, mul_one]
  · rw [precompose_apply, one_mul, mul_one]

/-- Both changed morphisms have nonzero values. -/
theorem moving_morphisms :
    ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul p).op
        (dualMap 1)) 1 ≠ 0 ∧
      ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul q).op
        (dualMap 1)) 1 ≠ 0 ∧
      (ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul p).op (dualMap 1) ≠
        (ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul q).op (dualMap 1) := by
  rcases moving_morphism_values with ⟨hp, hq⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hp]
    intro h
    exact p_ne_zero (congrArg ULift.down h)
  · rw [hq]
    intro h
    exact q_ne_zero (congrArg ULift.down h)
  · intro h
    have he := congrArg (fun f :
      (ModuleCat.rightDual.{1, 0} CoefficientRing).obj (op modelModule) => (f 1).down) h
    rw [hp, hq] at he
    exact p_ne_q he

/-- Consequently the coefficient-lift functor maps are distinct. -/
theorem moving_functor_maps :
    (ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul p).op ≠
      (ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul q).op := by
  intro h
  apply moving_morphisms.2.2
  exact congrArg (fun k :
    (ModuleCat.rightDual.{1, 0} CoefficientRing).obj (op modelModule) ⟶
      (ModuleCat.rightDual.{1, 0} CoefficientRing).obj (op modelModule) => k (dualMap 1)) h

/-- Two lifted left scalars give distinct nonzero values on the same dual vector. -/
theorem moving_scalars :
    ((ULift.up p : CoefficientRing) • dualMap 1) 1 = ULift.up p ∧
      ((ULift.up q : CoefficientRing) • dualMap 1) 1 = ULift.up q ∧
      ((ULift.up p : CoefficientRing) • dualMap 1) 1 ≠ 0 ∧
      ((ULift.up q : CoefficientRing) • dualMap 1) 1 ≠ 0 ∧
      (ULift.up p : CoefficientRing) • dualMap 1 ≠
        (ULift.up q : CoefficientRing) • dualMap 1 := by
  have hp : ((ULift.up p : CoefficientRing) • dualMap 1) 1 = ULift.up p := by
    rw [scalar_apply, one_mul, mul_one]
  have hq : ((ULift.up q : CoefficientRing) • dualMap 1) 1 = ULift.up q := by
    rw [scalar_apply, one_mul, mul_one]
  refine ⟨hp, hq, ?_, ?_, ?_⟩
  · rw [hp]
    intro h
    exact p_ne_zero (congrArg ULift.down h)
  · rw [hq]
    intro h
    exact q_ne_zero (congrArg ULift.down h)
  · intro h
    have he := congrArg (fun f :
      (ModuleCat.rightDual.{1, 0} CoefficientRing).obj (op modelModule) => (f 1).down) h
    rw [hp, hq] at he
    exact p_ne_q he

/-- Both sides of fixed-map left linearity evaluate to the same nonzero lifted matrix. -/
theorem scalar_precomposition :
    ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul q).op
        ((ULift.up p : CoefficientRing) • dualMap 1)) 1 = ULift.up q ∧
      ((ULift.up p : CoefficientRing) •
        (ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul q).op
          (dualMap 1)) 1 = ULift.up q ∧
      (ULift.up q : CoefficientRing) ≠ 0 := by
  have h : ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul q).op
      ((ULift.up p : CoefficientRing) • dualMap 1)) 1 = ULift.up q := by
    rw [precompose_scalar_apply, one_mul, mul_one, p_mul_q]
  refine ⟨h, ?_, ?_⟩
  · rw [← precompose_smul]
    exact h
  · intro hz
    exact q_ne_zero (congrArg ULift.down hz)

/-- Reversing the ordinary product changes a nonzero functor value to zero. -/
theorem ordered_precomposition :
    ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul q).op
        (dualMap p)) 1 = ULift.up q ∧
      ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul p).op
        (dualMap q)) 1 = 0 ∧ (ULift.up q : CoefficientRing) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [precompose_apply, p_mul_q, mul_one]
  · rw [precompose_apply, q_mul_p, zero_mul]
    rfl
  · intro h
    exact q_ne_zero (congrArg ULift.down h)

/-- The transported source maps compose in ordinary matrix multiplication order. -/
theorem leftMul_comp (b c : MatrixRing) :
    leftMul b ≫ leftMul c = leftMul (c * b) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change leftMul c (leftMul b x) = leftMul (c * b) x
  rw [leftMul_apply, leftMul_apply, leftMul_apply, mul_assoc]

/-- The two selected ordinary source composites retain their noncommutative order. -/
theorem source_composition_order :
    leftMul q ≫ leftMul p = leftMul q ∧
      leftMul p ≫ leftMul q = leftMul 0 := by
  constructor
  · rw [leftMul_comp, p_mul_q]
  · rw [leftMul_comp, q_mul_p]

/-- The functor, not just the lower Hom construction, reverses composition. -/
theorem contravariant_composition (b c : MatrixRing) :
    (ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul b ≫ leftMul c).op =
      (ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul c).op ≫
        (ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul b).op := by
  rw [CategoryTheory.op_comp, Functor.map_comp]

/-- The correctly reversed composite is nonzero, and false covariance gives zero. -/
theorem composition_order :
    ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul q ≫ leftMul p).op
        (dualMap 1)) 1 = ULift.up q ∧
      ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul q).op
        ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul p).op
          (dualMap 1))) 1 = ULift.up q ∧
      ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul p).op
        ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul q).op
          (dualMap 1))) 1 = 0 ∧ (ULift.up q : CoefficientRing) ≠ 0 := by
  have h : ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul q).op
      ((ModuleCat.rightDual.{1, 0} CoefficientRing).map (leftMul p).op
        (dualMap 1))) 1 = ULift.up q := by
    rw [precompose 1 p, precompose (1 * p) q, dualMap_apply, one_mul, p_mul_q, mul_one]
  refine ⟨?_, h, ?_, ?_⟩
  · rw [contravariant_composition, ModuleCat.comp_apply]
    exact h
  · rw [precompose 1 q, precompose (1 * q) p, dualMap_apply, one_mul, q_mul_p, zero_mul]
    rfl
  · intro hz
    exact q_ne_zero (congrArg ULift.down hz)

/-- Right-coefficient multiplication as a raw function. -/
def wrongRight (x : modelModule) : CoefficientRing :=
  ULift.up (x * p)

/-- The raw operation fails the canonical restricted source right-action law. -/
theorem wrongRight_not_right_linear :
    wrongRight (MulOpposite.op (ULift.up q : CoefficientRing) •
        (show modelModule from 1)) ≠
      MulOpposite.op (ULift.up q : CoefficientRing) • wrongRight 1 := by
  rw [source_smul]
  intro h
  have he : (1 * q) * p = (1 * p) * q := congrArg ULift.down h
  rw [one_mul, one_mul, q_mul_p, p_mul_q] at he
  exact q_ne_zero he.symm

/-- There is no right-linear packaging of the raw right-coefficient function. -/
theorem wrongRight_no_linearMap :
    ¬ ∃ f : modelModule →ₗ[CoefficientRingᵐᵒᵖ] CoefficientRing,
      ∀ x, f x = wrongRight x := by
  rintro ⟨f, hf⟩
  apply wrongRight_not_right_linear
  calc
    wrongRight (MulOpposite.op (ULift.up q : CoefficientRing) •
        (show modelModule from 1)) =
      f (MulOpposite.op (ULift.up q : CoefficientRing) •
        (show modelModule from 1)) := (hf _).symm
    _ = MulOpposite.op (ULift.up q : CoefficientRing) • f 1 := f.map_smul _ _
    _ = MulOpposite.op (ULift.up q : CoefficientRing) • wrongRight 1 :=
      congrArg (fun y : CoefficientRing =>
        MulOpposite.op (ULift.up q : CoefficientRing) • y) (hf _)

end CoefficientLift

end ProjectiveModulesTests.RightDualUniverseClient
