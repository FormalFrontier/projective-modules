/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.RightExtension
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Right scalar extension and commutative-base tensor products

Let `R` be a commutative ring, `S` an arbitrary ring and `φ : R →+* S`
a ring homomorphism whose image need not be central. A right `R`-module is
viewed as a left module by restriction along `RingEquiv.toOpposite R`.
The coefficient module is restriction of the regular left `S`-module along `φ`.
Both views are bundled: this also specifies the intended actions when `R = S`
and `φ` is not the identity.

`tensorProductObj` has the module-first Mathlib tensor carrier. Its right
`S`-action is transported through `TensorProduct.comm` from right
multiplication on the coefficient factor. Thus `op t • (m ⊗ s) = m ⊗ (s * t)`.
`tensorProductTmul` specifies these pure tensors using the two bundled module
structures. `tensorFunctor` maps morphisms by Mathlib's tensor map on the
source factor and the identity on the coefficient factor, bundled as a
right-linear map using this action. No right action on `M` by `S`, finite
generation or projectivity is required. The coefficient actions commute by associativity, using
`ModuleCat.RightExtension.smulCommClass`; no additional commuting-action
hypothesis or `Algebra R S` structure is imposed.

The comparison with `Obj φ M` retains module-first order.
For commutative `S`, a separate comparison lands in the right-module view of
Mathlib's scalar-first `ModuleCat.extendScalars` object. Its characterization
identifies the switch of factors with `TensorProduct.comm`.

For commutative `R` and `S`, `oppositeScalarEquiv` instead compares directly
with scalar extension along `RingHom.op φ`, retaining the given right-module
actions. `tensorBaseChangeEquiv` distributes right extension over
`M ⊗[Rᵐᵒᵖ] N`; its inverse combines the coefficients by ordinary multiplication
in `S`. Both equivalences have forward and inverse pure-tensor formulas.

## Universes and scope

The scalar universes `uR`, `uS` and source carrier universe `uM` are independent.
Both one-step extension carriers live in `max uM uS`, independently of `uR`;
these pointwise linear equivalences require no `ULift`. For source modules
in independent universes `uM` and `uN`, the tensor base-change carriers live in
`max uS uM uN`, with no contribution from `uR`. Morphism naturality
uses the common carrier universe of `ModuleCat` morphisms. Packaging at a
separately prescribed larger universe requires carrier lifts, for example
`ModuleCat.uliftFunctor`. The tensor functor satisfies the categorical
identity and composition laws. No natural isomorphism, ring-homomorphism
coherence or statement about
algebraic K-theory is supplied here.

## Formalization references

This AI-assisted adaptation uses the right-extension and balanced-tensor
universal properties originally formalized by Prism in this library and
Lens's subsequent scalar-extension interfaces. The opposite scalar conversion,
pure-tensor relations, tensor commutation, tensor maps, target-linear tensor
base change, tensor congruence and transport of module structures use Mathlib.
The scalar-first categorical object and morphisms use Jujian Zhang's Mathlib
change-of-rings formalization. No alternative tensor quotient is constructed.
-/

@[expose] public section

universe uR uS uM uN

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat.RightExtension

section RingTarget

variable {R : Type uR} {S : Type uS} [CommRing R] [Ring S]
variable (φ : R →+* S)

/-- The module-first Mathlib tensor product, with the right `S`-action on the
coefficient factor. The left action on the coefficient is specified by `φ`,
even for a nonidentity endomorphism of `R` itself. -/
noncomputable def tensorProductObj (M : ModuleCat.{uM} Rᵐᵒᵖ) :
    ModuleCat.{max uM uS} Sᵐᵒᵖ := by
  letI : Module Sᵐᵒᵖ ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) :=
    inferInstanceAs (Module Sᵐᵒᵖ S)
  letI : SMulCommClass R Sᵐᵒᵖ
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) := smulCommClass φ
  letI : Module Sᵐᵒᵖ
      (TensorProduct R
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M)
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))) :=
    (TensorProduct.comm R
      ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M)
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))).toAddEquiv.module Sᵐᵒᵖ
  exact ModuleCat.of Sᵐᵒᵖ
    (TensorProduct R
      ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M)
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)))

/-- The tensor object has precisely the module-first Mathlib tensor carrier. -/
@[simp]
theorem tensorProductObj_coe (M : ModuleCat.{uM} Rᵐᵒᵖ) :
    (tensorProductObj φ M : Type (max uM uS)) =
      TensorProduct R
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M)
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) := rfl

/-- The module-first pure tensor with the source action obtained from the
opposite scalar view and the coefficient action specified by `φ`. -/
noncomputable def tensorProductTmul (M : ModuleCat.{uM} Rᵐᵒᵖ) (m : M) (s : S) :
    tensorProductObj φ M :=
  @TensorProduct.tmul R _
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M)
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) _ _
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M).isModule
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule m s

/-- The pure-tensor constructor is Mathlib's pure tensor for the specified
bundled source and coefficient modules. -/
theorem tensorProductTmul_eq_tmul (M : ModuleCat.{uM} Rᵐᵒᵖ) (m : M) (s : S) :
    tensorProductTmul φ M m s =
      @TensorProduct.tmul R _
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M)
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) _ _
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M).isModule
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule m s := rfl

/-- A pure tensor with zero source factor is zero. -/
@[simp]
theorem tensorProductTmul_zero_left (M : ModuleCat.{uM} Rᵐᵒᵖ) (s : S) :
    tensorProductTmul φ M 0 s = 0 := by
  let sourceModule : Module R M :=
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M).isModule
  let coefficientModule : Module R S :=
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
  exact @TensorProduct.zero_tmul R _ M S _ _ sourceModule coefficientModule s

/-- A pure tensor is additive in its source factor. -/
theorem tensorProductTmul_add_left (M : ModuleCat.{uM} Rᵐᵒᵖ) (m n : M) (s : S) :
    tensorProductTmul φ M (m + n) s =
      tensorProductTmul φ M m s + tensorProductTmul φ M n s := by
  let sourceModule : Module R M :=
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M).isModule
  let coefficientModule : Module R S :=
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
  exact @TensorProduct.add_tmul R _ M S _ _ sourceModule coefficientModule m n s

/-- A pure tensor with zero coefficient is zero. -/
@[simp]
theorem tensorProductTmul_zero_right (M : ModuleCat.{uM} Rᵐᵒᵖ) (m : M) :
    tensorProductTmul φ M m 0 = 0 := by
  let sourceModule : Module R M :=
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M).isModule
  let coefficientModule : Module R S :=
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
  exact @TensorProduct.tmul_zero R _ M S _ _ sourceModule coefficientModule m

/-- A pure tensor is additive in its coefficient factor. -/
theorem tensorProductTmul_add_right (M : ModuleCat.{uM} Rᵐᵒᵖ) (m : M) (s t : S) :
    tensorProductTmul φ M m (s + t) =
      tensorProductTmul φ M m s + tensorProductTmul φ M m t := by
  let sourceModule : Module R M :=
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M).isModule
  let coefficientModule : Module R S :=
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
  exact @TensorProduct.tmul_add R _ M S _ _ sourceModule coefficientModule m s t

/-- Moving a source scalar to the coefficient uses the specified homomorphism,
with left multiplication on the coefficient. -/
theorem tensorProductTmul_balance (M : ModuleCat.{uM} Rᵐᵒᵖ)
    (r : R) (m : M) (s : S) :
    tensorProductTmul φ M (@SMul.smul Rᵐᵒᵖ M M.isModule.toSMul (MulOpposite.op r) m) s =
      tensorProductTmul φ M m (φ r * s) := by
  let sourceModule : Module R M :=
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M).isModule
  let coefficientModule : Module R S :=
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
  change
    @TensorProduct.tmul R _ M S _ _ sourceModule coefficientModule
        (@SMul.smul R M sourceModule.toSMul r m) s =
      @TensorProduct.tmul R _ M S _ _ sourceModule coefficientModule m
        (@SMul.smul R S coefficientModule.toSMul r s)
  exact TensorProduct.smul_tmul (R := R) (R' := R) (M := M) (N := S) r m s

/-- Right multiplication on the coefficient is the transferred action; the
multiplication order is in `S`, not in its opposite. -/
@[simp]
theorem tensorProductObj_smul_tmul (M : ModuleCat.{uM} Rᵐᵒᵖ)
    (m : M) (s t : S) :
    @SMul.smul Sᵐᵒᵖ (tensorProductObj φ M) (tensorProductObj φ M).isModule.toSMul
        (MulOpposite.op t) (tensorProductTmul φ M m s) =
      tensorProductTmul φ M m (s * t) := by
  let sourceModule : Module R M :=
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M).isModule
  let coefficientModule : Module R S :=
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
  let : Module R M := sourceModule
  let : Module R S := coefficientModule
  let : SMul R M := sourceModule.toSMul
  let : SMul R S := coefficientModule.toSMul
  let : SMulCommClass R Sᵐᵒᵖ S := smulCommClass φ
  let : Module R (TensorProduct R M S) := TensorProduct.instModule
  let : Module R (TensorProduct R S M) := TensorProduct.instModule
  let commute := @TensorProduct.comm R _ M S _ _ sourceModule coefficientModule
  calc
    _ = commute.symm (MulOpposite.op t • commute
        (@TensorProduct.tmul R _ M S _ _ sourceModule coefficientModule m s)) :=
      commute.toEquiv.smul_def (MulOpposite.op t) _
    _ = @TensorProduct.tmul R _ M S _ _ sourceModule coefficientModule m (s * t) := by
      rw [TensorProduct.comm_tmul, TensorProduct.smul_tmul', TensorProduct.comm_symm_tmul]
      rfl

/-- Right-linear maps out of the tensor object are determined by pure tensors.
The target need not carry an action of the base ring. -/
theorem tensorProduct_hom_ext (M : ModuleCat.{uM} Rᵐᵒᵖ)
    {P : Type*} [AddCommMonoid P] [Module Sᵐᵒᵖ P]
    {f g : tensorProductObj φ M →ₗ[Sᵐᵒᵖ] P}
    (h : ∀ m s, f (tensorProductTmul φ M m s) = g (tensorProductTmul φ M m s)) :
    f = g := by
  let sourceRCat :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M
  let coefficientRCat := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)
  apply LinearMap.ext
  intro x
  refine @TensorProduct.inductionOn R _ sourceRCat coefficientRCat
    sourceRCat.isAddCommGroup.toAddCommMonoid
    coefficientRCat.isAddCommGroup.toAddCommMonoid
    sourceRCat.isModule coefficientRCat.isModule (fun y ↦ f y = g y) x ?_ ?_
  · exact h
  · intro y z hy hz
    exact (f.map_add y z).trans
      ((congrArg₂ (fun a b : P ↦ a + b) hy hz).trans (g.map_add y z).symm)

/-- Tensor extension of a source morphism, linear for the right action on the
coefficient factor. Its underlying function is Mathlib's tensor map, with the
identity on the coefficient module restricted along `φ`. -/
noncomputable def tensorProductMap {M N : ModuleCat.{uM} Rᵐᵒᵖ} (g : M ⟶ N) :
    tensorProductObj φ M →ₗ[Sᵐᵒᵖ] tensorProductObj φ N := by
  let sourceRCat :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M
  let targetRCat :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj N
  let coefficientRCat := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)
  let sourceMap : sourceRCat →ₗ[R] targetRCat :=
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).map g).hom
  let coefficientId := @LinearMap.id R coefficientRCat _ _ coefficientRCat.isModule
  let tensorMap := @TensorProduct.map R R _ _ (RingHom.id R)
    sourceRCat coefficientRCat targetRCat coefficientRCat
    sourceRCat.isAddCommGroup.toAddCommMonoid
    coefficientRCat.isAddCommGroup.toAddCommMonoid
    targetRCat.isAddCommGroup.toAddCommMonoid
    coefficientRCat.isAddCommGroup.toAddCommMonoid
    sourceRCat.isModule coefficientRCat.isModule
    targetRCat.isModule coefficientRCat.isModule sourceMap coefficientId
  have pure (m : M) (s : S) :
      tensorMap (tensorProductTmul φ M m s) = tensorProductTmul φ N (g m) s :=
    @TensorProduct.map_tmul R R _ _ (RingHom.id R)
      sourceRCat coefficientRCat targetRCat coefficientRCat
      sourceRCat.isAddCommGroup.toAddCommMonoid
      coefficientRCat.isAddCommGroup.toAddCommMonoid
      targetRCat.isAddCommGroup.toAddCommMonoid
      coefficientRCat.isAddCommGroup.toAddCommMonoid
      sourceRCat.isModule coefficientRCat.isModule
      targetRCat.isModule coefficientRCat.isModule sourceMap coefficientId m s
  refine { toFun := tensorMap, map_add' := tensorMap.map_add, map_smul' := ?_ }
  intro t x
  refine @TensorProduct.inductionOn R _ M S
    sourceRCat.isAddCommGroup.toAddCommMonoid
    coefficientRCat.isAddCommGroup.toAddCommMonoid
    sourceRCat.isModule coefficientRCat.isModule
    (fun y ↦ tensorMap
        (@SMul.smul Sᵐᵒᵖ (tensorProductObj φ M)
          (tensorProductObj φ M).isModule.toSMul t y) =
      @SMul.smul Sᵐᵒᵖ (tensorProductObj φ N)
        (tensorProductObj φ N).isModule.toSMul t (tensorMap y)) x ?_ ?_
  · intro m s
    have sourceAction :
        @SMul.smul Sᵐᵒᵖ (tensorProductObj φ M)
          (tensorProductObj φ M).isModule.toSMul t (tensorProductTmul φ M m s) =
        tensorProductTmul φ M m (s * MulOpposite.unop t) := by
      simpa only [MulOpposite.op_unop] using
        tensorProductObj_smul_tmul φ M m s (MulOpposite.unop t)
    have targetAction :
        @SMul.smul Sᵐᵒᵖ (tensorProductObj φ N)
          (tensorProductObj φ N).isModule.toSMul t (tensorProductTmul φ N (g m) s) =
        tensorProductTmul φ N (g m) (s * MulOpposite.unop t) := by
      simpa only [MulOpposite.op_unop] using
        tensorProductObj_smul_tmul φ N (g m) s (MulOpposite.unop t)
    exact (congrArg tensorMap sourceAction).trans
      ((pure m (s * MulOpposite.unop t)).trans
        (targetAction.symm.trans
          (congrArg (@SMul.smul Sᵐᵒᵖ (tensorProductObj φ N)
            (tensorProductObj φ N).isModule.toSMul t) (pure m s).symm)))
  · intro y z hy hz
    exact (congrArg tensorMap
      (@DistribMulAction.smul_add Sᵐᵒᵖ (tensorProductObj φ M) _
        (tensorProductObj φ M).isAddCommGroup.toAddCommMonoid.toAddMonoid
        (tensorProductObj φ M).isModule.toDistribMulAction t y z)).trans
      ((tensorMap.map_add _ _).trans
        ((congrArg₂ (fun a b : tensorProductObj φ N ↦ a + b) hy hz).trans
          ((@DistribMulAction.smul_add Sᵐᵒᵖ (tensorProductObj φ N) _
            (tensorProductObj φ N).isAddCommGroup.toAddCommMonoid.toAddMonoid
            (tensorProductObj φ N).isModule.toDistribMulAction t
            (tensorMap y) (tensorMap z)).symm.trans
            (congrArg (@SMul.smul Sᵐᵒᵖ (tensorProductObj φ N)
              (tensorProductObj φ N).isModule.toSMul t) (tensorMap.map_add y z).symm))))

/-- Tensor extension of a morphism is Mathlib's tensor map for the specified
source and coefficient actors. -/
theorem tensorProductMap_apply {M N : ModuleCat.{uM} Rᵐᵒᵖ} (g : M ⟶ N)
    (x : tensorProductObj φ M) :
    tensorProductMap φ g x =
      @TensorProduct.map R R _ _ (RingHom.id R)
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M)
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj N)
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) _ _ _ _
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M).isModule
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj N).isModule
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).map g).hom
        (@LinearMap.id R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) _ _
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule) x := rfl

/-- Tensor extension applies the source morphism to the first factor. -/
@[simp]
theorem tensorProductMap_tmul {M N : ModuleCat.{uM} Rᵐᵒᵖ}
    (g : M ⟶ N) (m : M) (s : S) :
    tensorProductMap φ g (tensorProductTmul φ M m s) =
      tensorProductTmul φ N (g m) s := by
  let sourceRCat :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M
  let targetRCat :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj N
  let coefficientRCat := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)
  rw [tensorProductMap_apply]
  exact @TensorProduct.map_tmul R R _ _ (RingHom.id R)
    sourceRCat coefficientRCat targetRCat coefficientRCat
    sourceRCat.isAddCommGroup.toAddCommMonoid
    coefficientRCat.isAddCommGroup.toAddCommMonoid
    targetRCat.isAddCommGroup.toAddCommMonoid
    coefficientRCat.isAddCommGroup.toAddCommMonoid
    sourceRCat.isModule coefficientRCat.isModule
    targetRCat.isModule coefficientRCat.isModule
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).map g).hom
    (@LinearMap.id R coefficientRCat _ _ coefficientRCat.isModule) m s

/-- Tensor extension of the identity is the identity right-linear map. -/
@[simp]
theorem tensorProductMap_id (M : ModuleCat.{uM} Rᵐᵒᵖ) :
    tensorProductMap φ (𝟙 M) = LinearMap.id := by
  apply tensorProduct_hom_ext φ M
  intro m s
  simp only [tensorProductMap_tmul, ModuleCat.id_apply, LinearMap.id_apply]

/-- Tensor extension respects composition of source morphisms. -/
theorem tensorProductMap_comp {M N P : ModuleCat.{uM} Rᵐᵒᵖ}
    (g : M ⟶ N) (h : N ⟶ P) :
    tensorProductMap φ (g ≫ h) = (tensorProductMap φ h).comp (tensorProductMap φ g) := by
  apply tensorProduct_hom_ext φ M
  intro m s
  simp only [tensorProductMap_tmul, LinearMap.comp_apply, ModuleCat.comp_apply]

/-- Tensor extension of right modules over a commutative base ring.
The morphism map is the tensor product of the opposite-restricted source map
and the identity of the coefficient module restricted along `φ`. -/
noncomputable def tensorFunctor : ModuleCat.{uM} Rᵐᵒᵖ ⥤
    ModuleCat.{max uM uS} Sᵐᵒᵖ where
  obj := tensorProductObj φ
  map {M N} g := ModuleCat.ofHom
    (X := tensorProductObj φ M) (Y := tensorProductObj φ N) (tensorProductMap φ g)
  map_id M := by
    apply ModuleCat.hom_ext
    change tensorProductMap φ (𝟙 M) = LinearMap.id
    apply tensorProduct_hom_ext φ M
    intro m s
    simp only [tensorProductMap_tmul, ModuleCat.id_apply, LinearMap.id_apply]
  map_comp {M N P} g h := by
    apply ModuleCat.hom_ext
    change tensorProductMap φ (g ≫ h) =
      (tensorProductMap φ h).comp (tensorProductMap φ g)
    apply tensorProduct_hom_ext φ M
    intro m s
    simp only [tensorProductMap_tmul, LinearMap.comp_apply, ModuleCat.comp_apply]

/-- Tensor extension uses the module-first tensor object. -/
@[simp]
theorem tensorFunctor_obj (M : ModuleCat.{uM} Rᵐᵒᵖ) :
    (tensorFunctor φ).obj M = tensorProductObj φ M := rfl

/-- The right-linear map underlying a tensor-functor morphism is tensor
extension of the source morphism. -/
@[simp]
theorem tensorFunctor_map_hom {M N : ModuleCat.{uM} Rᵐᵒᵖ} (g : M ⟶ N) :
    ((tensorFunctor φ).map g).hom = tensorProductMap φ g := rfl

/-- Tensor extension of a morphism is Mathlib's tensor map for the specified
source and coefficient actors. -/
theorem tensorFunctor_map_apply {M N : ModuleCat.{uM} Rᵐᵒᵖ} (g : M ⟶ N)
    (x : (tensorFunctor φ).obj M) :
    (tensorFunctor φ).map g x =
      @TensorProduct.map R R _ _ (RingHom.id R)
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M)
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj N)
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) _ _ _ _
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M).isModule
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj N).isModule
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).map g).hom
        (@LinearMap.id R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) _ _
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule) x := by
  change ((tensorFunctor φ).map g).hom x = _
  rw [tensorFunctor_map_hom]
  exact tensorProductMap_apply φ g x

/-- Tensor extension applies the source morphism to the first factor. -/
@[simp]
theorem tensorFunctor_map_tmul {M N : ModuleCat.{uM} Rᵐᵒᵖ}
    (g : M ⟶ N) (m : M) (s : S) :
    (tensorFunctor φ).map g (tensorProductTmul φ M m s) =
      tensorProductTmul φ N (g m) s := by
  change ((tensorFunctor φ).map g).hom (tensorProductTmul φ M m s) = _
  rw [tensorFunctor_map_hom]
  exact tensorProductMap_tmul φ g m s

/-- Tensor extension of the identity fixes every element of the tensor object. -/
@[simp]
theorem tensorFunctor_map_id_apply (M : ModuleCat.{uM} Rᵐᵒᵖ)
    (x : tensorProductObj φ M) :
    (tensorFunctor φ).map (𝟙 M) x = x := by
  exact (congrArg (fun f : (tensorFunctor φ).obj M ⟶ (tensorFunctor φ).obj M ↦ f x)
    ((tensorFunctor φ).map_id M)).trans
      (ModuleCat.id_apply ((tensorFunctor φ).obj M) x)

/-- Composition of tensor-functor morphisms acts by successive application
on the module-first tensor carrier. -/
theorem tensorFunctor_map_comp_apply {M N P : ModuleCat.{uM} Rᵐᵒᵖ}
    (g : M ⟶ N) (h : N ⟶ P) (x : tensorProductObj φ M) :
    (tensorFunctor φ).map (g ≫ h) x =
      (tensorFunctor φ).map h ((tensorFunctor φ).map g x) := by
  exact (congrArg (fun f : (tensorFunctor φ).obj M ⟶ (tensorFunctor φ).obj P ↦ f x)
    ((tensorFunctor φ).map_comp g h)).trans
      (ModuleCat.comp_apply ((tensorFunctor φ).map g) ((tensorFunctor φ).map h) x)

/-- Right scalar extension agrees with the module-first Mathlib tensor product
over a commutative base, with the canonical right action on the coefficient. -/
noncomputable def tensorProductLinearEquiv (M : ModuleCat.{uM} Rᵐᵒᵖ) :
    Obj φ M ≃ₗ[Sᵐᵒᵖ] tensorProductObj φ M := by
  let extensionAdd : AddCommGroup (Obj φ M) := inferInstance
  let extensionModule : @Module Sᵐᵒᵖ (Obj φ M) _ extensionAdd.toAddCommMonoid :=
    inferInstance
  let tensorAdd : AddCommGroup (tensorProductObj φ M) := inferInstance
  let tensorModule : @Module Sᵐᵒᵖ (tensorProductObj φ M) _ tensorAdd.toAddCommMonoid :=
    inferInstance
  letI : AddCommGroup (Obj φ M) := extensionAdd
  letI : Module Sᵐᵒᵖ (Obj φ M) := extensionModule
  letI : SMul Sᵐᵒᵖ (Obj φ M) := extensionModule.toSMul
  letI : AddCommGroup (tensorProductObj φ M) := tensorAdd
  letI : Module Sᵐᵒᵖ (tensorProductObj φ M) := tensorModule
  letI : SMul Sᵐᵒᵖ (tensorProductObj φ M) := tensorModule.toSMul
  let sourceAdd : AddCommGroup M := M.isAddCommGroup
  let coefficientAdd : AddCommGroup S := (ModuleCat.of S S).isAddCommGroup
  let sourceRightModule : @Module Rᵐᵒᵖ M _ sourceAdd.toAddCommMonoid := M.isModule
  let sourceModule : @Module R M _ sourceAdd.toAddCommMonoid :=
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M).isModule
  let coefficientModule : @Module R S _ coefficientAdd.toAddCommMonoid :=
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
  let toTensor :
      @BalancedTensorProduct.BalancedMap R M S _ sourceAdd coefficientAdd
        sourceRightModule φ.toModule (tensorProductObj φ M)
        (tensorProductObj φ M).isAddCommGroup :=
    { toFun := tensorProductTmul φ M
      map_zero_left := tensorProductTmul_zero_left φ M
      map_add_left := tensorProductTmul_add_left φ M
      map_zero_right := tensorProductTmul_zero_right φ M
      map_add_right := tensorProductTmul_add_right φ M
      balance := tensorProductTmul_balance φ M }
  let forward : Obj φ M →+ tensorProductObj φ M :=
    @BalancedTensorProduct.lift R M S _ sourceAdd coefficientAdd
      sourceRightModule φ.toModule (tensorProductObj φ M)
      (tensorProductObj φ M).isAddCommGroup toTensor
  have forward_tmul (m : M) (s : S) :
      forward (tmul φ m s) = tensorProductTmul φ M m s :=
    @BalancedTensorProduct.lift_tmul R M S _ sourceAdd coefficientAdd
      sourceRightModule φ.toModule (tensorProductObj φ M)
      (tensorProductObj φ M).isAddCommGroup toTensor m s
  let toOld : M →+ S →+ Obj φ M :=
    { toFun := fun m ↦
        { toFun := tmul φ m
          map_zero' := @BalancedTensorProduct.tmul_zero R M S _ sourceAdd coefficientAdd
            sourceRightModule φ.toModule m
          map_add' := @BalancedTensorProduct.tmul_add R M S _ sourceAdd coefficientAdd
            sourceRightModule φ.toModule m }
      map_zero' := by
        apply AddMonoidHom.ext
        intro s
        exact @BalancedTensorProduct.zero_tmul R M S _ sourceAdd coefficientAdd
          sourceRightModule φ.toModule s
      map_add' := by
        intro m n
        apply AddMonoidHom.ext
        intro s
        exact @BalancedTensorProduct.add_tmul R M S _ sourceAdd coefficientAdd
          sourceRightModule φ.toModule m n s }
  have balanced (r : R) (m : M) (s : S) :
      toOld (@SMul.smul R M sourceModule.toSMul r m) s =
        toOld m (@SMul.smul R S coefficientModule.toSMul r s) := by
    have sourceAction :
        @SMul.smul R M sourceModule.toSMul r m =
          @SMul.smul Rᵐᵒᵖ M sourceRightModule.toSMul (MulOpposite.op r) m :=
      ModuleCat.restrictScalars.smul_def'
        (RingEquiv.toOpposite R).toRingHom (M := M) r m
    have coefficientAction :
        @SMul.smul R S coefficientModule.toSMul r s = φ r * s := by
      have h := ModuleCat.restrictScalars.smul_def' φ (M := ModuleCat.of S S) r s
      exact h.trans (show
        @SMul.smul S S (ModuleCat.of S S).isModule.toSMul (φ r) s = φ r * s from rfl)
    change tmul φ (@SMul.smul R M sourceModule.toSMul r m) s =
      tmul φ m (@SMul.smul R S coefficientModule.toSMul r s)
    rw [sourceAction, coefficientAction]
    exact @smul_tmul R S _ _ φ M sourceAdd sourceRightModule r m s
  let inverse : tensorProductObj φ M →+ Obj φ M :=
    @TensorProduct.liftAddHom R _ M S (Obj φ M)
      sourceAdd.toAddCommMonoid coefficientAdd.toAddCommMonoid _
      sourceModule coefficientModule toOld balanced
  have inverse_tmul (m : M) (s : S) :
      inverse (tensorProductTmul φ M m s) = tmul φ m s := by
    rw [tensorProductTmul_eq_tmul]
    exact @TensorProduct.liftAddHom_tmul R _ M S (Obj φ M)
      sourceAdd.toAddCommMonoid coefficientAdd.toAddCommMonoid _
      sourceModule coefficientModule toOld balanced m s
  have leftHom : inverse.comp forward = AddMonoidHom.id (Obj φ M) := by
    apply @BalancedTensorProduct.hom_ext R M S _ sourceAdd coefficientAdd
      sourceRightModule φ.toModule (Obj φ M) _
    intro m s
    change inverse (forward (tmul φ m s)) = tmul φ m s
    rw [forward_tmul, inverse_tmul]
  refine
    { toFun := forward
      invFun := inverse
      left_inv := fun x ↦ DFunLike.congr_fun leftHom x
      right_inv := by
        intro x
        refine @TensorProduct.inductionOn R _ M S
          sourceAdd.toAddCommMonoid coefficientAdd.toAddCommMonoid
          sourceModule coefficientModule (fun x ↦ forward (inverse x) = x) x ?_ ?_
        · intro m s
          change forward (inverse (tensorProductTmul φ M m s)) = tensorProductTmul φ M m s
          rw [inverse_tmul, forward_tmul]
        · intro x y hx hy
          exact (congrArg forward (inverse.map_add
            (show tensorProductObj φ M from x) (show tensorProductObj φ M from y))).trans
            ((forward.map_add (inverse x) (inverse y)).trans
              (congrArg₂ (fun a b : tensorProductObj φ M ↦ a + b) hx hy))
      map_add' := forward.map_add
      map_smul' := by
        intro t x
        induction x using @BalancedTensorProduct.induction_on R M S _ sourceAdd coefficientAdd
          sourceRightModule φ.toModule with
        | zero => rw [smul_zero, forward.map_zero, smul_zero]
        | pure m s =>
            have oldAction :
                @SMul.smul Sᵐᵒᵖ (Obj φ M) extensionModule.toSMul t (tmul φ m s) =
                  tmul φ m (s * MulOpposite.unop t) :=
              tmul_smul φ m s t
            have tensorAction :
                @SMul.smul Sᵐᵒᵖ (tensorProductObj φ M) tensorModule.toSMul t
                    (tensorProductTmul φ M m s) =
                  tensorProductTmul φ M m (s * MulOpposite.unop t) := by
              simpa only [MulOpposite.op_unop] using
                tensorProductObj_smul_tmul φ M m s (MulOpposite.unop t)
            calc
              _ = forward (tmul φ m (s * MulOpposite.unop t)) :=
                congrArg forward oldAction
              _ = tensorProductTmul φ M m (s * MulOpposite.unop t) :=
                forward_tmul m (s * MulOpposite.unop t)
              _ = @SMul.smul Sᵐᵒᵖ (tensorProductObj φ M) tensorModule.toSMul t
                  (tensorProductTmul φ M m s) := tensorAction.symm
              _ = @SMul.smul Sᵐᵒᵖ (tensorProductObj φ M) tensorModule.toSMul t
                  (forward (tmul φ m s)) :=
                congrArg
                  (@SMul.smul Sᵐᵒᵖ (tensorProductObj φ M) tensorModule.toSMul t)
                  (forward_tmul m s).symm
        | neg x hx => rw [smul_neg, forward.map_neg, forward.map_neg, hx, smul_neg]
        | add x y hx hy => rw [smul_add, forward.map_add, forward.map_add, hx, hy, smul_add] }

/-- The comparison retains the module-first pure tensor and its coefficient. -/
@[simp]
theorem tensorProductLinearEquiv_tmul (M : ModuleCat.{uM} Rᵐᵒᵖ) (m : M) (s : S) :
    tensorProductLinearEquiv φ M (tmul φ m s) =
      tensorProductTmul φ M m s := by
  let e : Obj φ M ≃ₗ[Sᵐᵒᵖ] tensorProductObj φ M := tensorProductLinearEquiv φ M
  change e (tmul φ m s) = tensorProductTmul φ M m s
  apply e.symm.injective
  rw [e.symm_apply_apply, tensorProductTmul_eq_tmul]
  rfl

/-- The inverse comparison sends a Mathlib pure tensor to the corresponding
balanced pure tensor. -/
@[simp]
theorem tensorProductLinearEquiv_symm_tmul (M : ModuleCat.{uM} Rᵐᵒᵖ)
    (m : M) (s : S) :
    (tensorProductLinearEquiv φ M).symm
        (tensorProductTmul φ M m s) =
      tmul φ m s := by
  let e : Obj φ M ≃ₗ[Sᵐᵒᵖ] tensorProductObj φ M := tensorProductLinearEquiv φ M
  exact e.symm_apply_eq.mpr (tensorProductLinearEquiv_tmul φ M m s).symm

/-- The comparison intertwines right extension of a module map with
Mathlib's tensor map on the module factor. -/
theorem tensorProductLinearEquiv_naturality {M N : ModuleCat.{uM} Rᵐᵒᵖ}
    (g : M ⟶ N) (x : Obj φ M) :
    tensorProductLinearEquiv φ N (map φ g.hom x) =
      TensorProduct.map
        (M := (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M)
        (N := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))
        (M₂ := (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj N)
        (N₂ := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).map g).hom
        (@LinearMap.id R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) _ _
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule)
        (tensorProductLinearEquiv φ M x) := by
  let sourceRCat :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M
  let targetRCat :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj N
  let coefficientRCat := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)
  let sourceMap : sourceRCat →ₗ[R] targetRCat :=
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).map g).hom
  let coefficientId := @LinearMap.id R coefficientRCat _ _ coefficientRCat.isModule
  let tensorMap := TensorProduct.map
    (M := sourceRCat) (N := coefficientRCat)
    (M₂ := targetRCat) (N₂ := coefficientRCat) sourceMap coefficientId
  have tensorMap_tmul (m : M) (s : S) :
      tensorMap (tensorProductTmul φ M m s) =
        tensorProductTmul φ N (g.hom m) s := by
    have pure : tensorMap (tensorProductTmul φ M m s) =
        tensorProductTmul φ N (sourceMap m) (coefficientId s) :=
      (congrArg tensorMap (tensorProductTmul_eq_tmul φ M m s)).trans
        ((@TensorProduct.map_tmul R R _ _ (RingHom.id R)
          sourceRCat coefficientRCat targetRCat coefficientRCat
          sourceRCat.isAddCommGroup.toAddCommMonoid
          coefficientRCat.isAddCommGroup.toAddCommMonoid
          targetRCat.isAddCommGroup.toAddCommMonoid
          coefficientRCat.isAddCommGroup.toAddCommMonoid
          sourceRCat.isModule coefficientRCat.isModule
          targetRCat.isModule coefficientRCat.isModule sourceMap coefficientId
          (show sourceRCat from m) (show coefficientRCat from s)).trans
            (tensorProductTmul_eq_tmul φ N (sourceMap m) (coefficientId s)).symm)
    have sourceMap_apply : sourceMap m = g.hom m :=
      ModuleCat.restrictScalars.map_apply (RingEquiv.toOpposite R).toRingHom g m
    have coefficientId_apply : coefficientId s = s := rfl
    exact pure.trans
      (congrArg₂ (tensorProductTmul φ N) sourceMap_apply coefficientId_apply)
  have h :
      (tensorProductLinearEquiv φ N).toLinearMap.toAddMonoidHom.comp
          (map φ g.hom).toAddMonoidHom =
        tensorMap.toAddMonoidHom.comp
          (tensorProductLinearEquiv φ M).toLinearMap.toAddMonoidHom := by
    apply @BalancedTensorProduct.hom_ext R M S _ M.isAddCommGroup
      (ModuleCat.of S S).isAddCommGroup M.isModule φ.toModule
      (tensorProductObj φ N) (tensorProductObj φ N).isAddCommGroup.toAddMonoid
    intro m s
    change tensorProductLinearEquiv φ N (map φ g.hom (tmul φ m s)) =
      tensorMap (tensorProductLinearEquiv φ M (tmul φ m s))
    rw [map_tmul, tensorProductLinearEquiv_tmul, tensorProductLinearEquiv_tmul]
    exact (tensorMap_tmul m s).symm
  exact DFunLike.congr_fun h x

/-- The same intertwining law uses the morphism of the right-extension functor
with its independent source and output carrier universes. -/
theorem tensorProductLinearEquiv_functor'_map {M N : ModuleCat.{uM} Rᵐᵒᵖ}
    (g : M ⟶ N) (x : (functor' φ).obj M) :
    tensorProductLinearEquiv φ N ((functor' φ).map g x) =
      TensorProduct.map
        (M := (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M)
        (N := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))
        (M₂ := (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj N)
        (N₂ := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).map g).hom
        (@LinearMap.id R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) _ _
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule)
        (tensorProductLinearEquiv φ M x) := by
  change tensorProductLinearEquiv φ N (((functor' φ).map g).hom x) = _
  rw [functor'_map_hom φ (M := M) (N := N) g]
  exact tensorProductLinearEquiv_naturality φ (M := M) (N := N) g x

end RingTarget

section CommutativeTarget

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
variable (φ : R →+* S)

/-- For commutative target scalars, right extension agrees pointwise with the
right-module view of Mathlib's scalar-first categorical extension along `φ`.
Its coefficient action is the specified restriction along `φ`, independent of
any separately supplied algebra structure. The input and output carrier
universes are `uM` and `max uM uS`, respectively. -/
noncomputable def extendScalarsLinearEquiv (M : ModuleCat.{uM} Rᵐᵒᵖ) :
    Obj φ M ≃ₗ[Sᵐᵒᵖ]
      (ModuleCat.restrictScalars (RingEquiv.toOpposite S).symm.toRingHom).obj
        ((ModuleCat.extendScalars φ).obj
          ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M)) := by
  let sourceRCat :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M
  let coefficientRCat := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)
  let sourceAdd : AddCommMonoid sourceRCat := sourceRCat.isAddCommGroup.toAddCommMonoid
  let coefficientAdd : AddCommMonoid coefficientRCat :=
    coefficientRCat.isAddCommGroup.toAddCommMonoid
  let sourceModule : @Module R sourceRCat _ sourceAdd := sourceRCat.isModule
  let coefficientModule : @Module R coefficientRCat _ coefficientAdd := coefficientRCat.isModule
  let scalarFirst := (ModuleCat.extendScalars φ).obj sourceRCat
  let rightScalarFirst :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite S).symm.toRingHom).obj scalarFirst
  let commute := @TensorProduct.comm R _ sourceRCat coefficientRCat
    sourceAdd coefficientAdd sourceModule coefficientModule
  have rightAction (t : Sᵐᵒᵖ) (s : S) (m : sourceRCat) :
      @SMul.smul Sᵐᵒᵖ rightScalarFirst rightScalarFirst.isModule.toSMul t
        (@TensorProduct.tmul R _ coefficientRCat sourceRCat
          coefficientAdd sourceAdd coefficientModule sourceModule s m) =
      @TensorProduct.tmul R _ coefficientRCat sourceRCat
        coefficientAdd sourceAdd coefficientModule sourceModule (MulOpposite.unop t * s) m := by
    exact (ModuleCat.restrictScalars.smul_def'
      (RingEquiv.toOpposite S).symm.toRingHom (M := scalarFirst) t
      (@TensorProduct.tmul R _ coefficientRCat sourceRCat
        coefficientAdd sourceAdd coefficientModule sourceModule s m)).trans
          (ModuleCat.ExtendScalars.smul_tmul φ (MulOpposite.unop t) s m)
  have commute_smul (t : Sᵐᵒᵖ) (x : tensorProductObj φ M) :
      commute (@SMul.smul Sᵐᵒᵖ (tensorProductObj φ M)
        (tensorProductObj φ M).isModule.toSMul t x) =
      @SMul.smul Sᵐᵒᵖ rightScalarFirst rightScalarFirst.isModule.toSMul t (commute x) := by
    refine @TensorProduct.inductionOn R _ sourceRCat coefficientRCat
      sourceAdd coefficientAdd sourceModule coefficientModule
      (fun y ↦ commute (@SMul.smul Sᵐᵒᵖ (tensorProductObj φ M)
        (tensorProductObj φ M).isModule.toSMul t y) =
        @SMul.smul Sᵐᵒᵖ rightScalarFirst rightScalarFirst.isModule.toSMul t (commute y))
      x ?_ ?_
    · intro m s
      -- Only the carrier is reduced: the coefficient R-action remains the bundled one.
      change S at s
      have sourceAction :
          @SMul.smul Sᵐᵒᵖ (tensorProductObj φ M)
            (tensorProductObj φ M).isModule.toSMul t
            (@TensorProduct.tmul R _ sourceRCat coefficientRCat
              sourceAdd coefficientAdd sourceModule coefficientModule m s) =
          @TensorProduct.tmul R _ sourceRCat coefficientRCat
            sourceAdd coefficientAdd sourceModule coefficientModule m (s * MulOpposite.unop t) := by
        exact (congrArg (fun a : Sᵐᵒᵖ ↦
          @SMul.smul Sᵐᵒᵖ (tensorProductObj φ M)
            (tensorProductObj φ M).isModule.toSMul a (tensorProductTmul φ M m s))
          (MulOpposite.op_unop t)).symm.trans
            (tensorProductObj_smul_tmul φ M m s (MulOpposite.unop t))
      exact (congrArg commute sourceAction).trans
        ((@TensorProduct.comm_tmul R _ sourceRCat coefficientRCat
          sourceAdd coefficientAdd sourceModule coefficientModule m (s * MulOpposite.unop t)).trans
          ((congrArg (fun a : S ↦ @TensorProduct.tmul R _ coefficientRCat sourceRCat
            coefficientAdd sourceAdd coefficientModule sourceModule a m)
            (mul_comm s (MulOpposite.unop t))).trans
            ((rightAction t s m).symm.trans
              (congrArg (fun z : rightScalarFirst ↦
                @SMul.smul Sᵐᵒᵖ rightScalarFirst rightScalarFirst.isModule.toSMul t z)
                (@TensorProduct.comm_tmul R _ sourceRCat coefficientRCat
                  sourceAdd coefficientAdd sourceModule coefficientModule m s).symm))))
    · intro y z hy hz
      -- Use the stored actions and their additive laws, rather than rewriting across carriers.
      exact (congrArg commute
        (@DistribMulAction.smul_add Sᵐᵒᵖ (tensorProductObj φ M) _
          (tensorProductObj φ M).isAddCommGroup.toAddCommMonoid.toAddMonoid
          (tensorProductObj φ M).isModule.toDistribMulAction t y z)).trans
        ((commute.map_add _ _).trans
          ((congrArg₂ (fun a b : rightScalarFirst ↦ a + b) hy hz).trans
            ((@DistribMulAction.smul_add Sᵐᵒᵖ rightScalarFirst _
                rightScalarFirst.isAddCommGroup.toAddCommMonoid.toAddMonoid
                rightScalarFirst.isModule.toDistribMulAction t (commute y) (commute z)).symm.trans
              (congrArg (fun w : rightScalarFirst ↦
                @SMul.smul Sᵐᵒᵖ rightScalarFirst rightScalarFirst.isModule.toSMul t w)
                (commute.map_add y z).symm))))
  let categoricalComm : tensorProductObj φ M ≃ₗ[Sᵐᵒᵖ] rightScalarFirst :=
    { __ := commute.toAddEquiv
      map_smul' := fun t x ↦ commute_smul t x }
  exact (tensorProductLinearEquiv φ M).trans categoricalComm

/-- The categorical comparison switches the factors, using Mathlib's
specified homomorphism-induced coefficient action. -/
@[simp]
theorem extendScalarsLinearEquiv_tmul (M : ModuleCat.{uM} Rᵐᵒᵖ) (m : M) (s : S) :
    extendScalarsLinearEquiv φ M (tmul φ m s) =
      @TensorProduct.tmul R _
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M) _ _
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M).isModule
        s m := by
  let sourceRCat :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M
  let coefficientRCat := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)
  change @TensorProduct.comm R _ sourceRCat coefficientRCat _ _
    sourceRCat.isModule coefficientRCat.isModule
    (tensorProductLinearEquiv φ M (tmul φ m s)) = _
  rw [tensorProductLinearEquiv_tmul, tensorProductTmul_eq_tmul]
  exact @TensorProduct.comm_tmul R _ sourceRCat coefficientRCat _ _
    sourceRCat.isModule coefficientRCat.isModule m s

/-- The inverse categorical comparison restores module-first order. -/
@[simp]
theorem extendScalarsLinearEquiv_symm_tmul (M : ModuleCat.{uM} Rᵐᵒᵖ)
    (m : M) (s : S) :
    (extendScalarsLinearEquiv φ M).symm
        (@TensorProduct.tmul R _
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))
          ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M) _ _
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
          ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M).isModule
          s m) =
      tmul φ m s := by
  let sourceRCat :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M
  let coefficientRCat := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)
  change (tensorProductLinearEquiv φ M).symm
    ((@TensorProduct.comm R _ sourceRCat coefficientRCat _ _
      sourceRCat.isModule coefficientRCat.isModule).symm
      (@TensorProduct.tmul R _ coefficientRCat sourceRCat _ _
        coefficientRCat.isModule sourceRCat.isModule s m)) = _
  rw [@TensorProduct.comm_symm_tmul R _ sourceRCat coefficientRCat _ _
    sourceRCat.isModule coefficientRCat.isModule m s]
  exact tensorProductLinearEquiv_symm_tmul φ M m s

/-- The scalar-first comparison is obtained on carriers by tensor commutation
from the module-first comparison. The bundled coefficient agrees with the
coefficient used by Mathlib's categorical extension. -/
theorem extendScalarsLinearEquiv_eq_comm (M : ModuleCat.{uM} Rᵐᵒᵖ)
    (x : Obj φ M) :
    extendScalarsLinearEquiv φ M x =
      @TensorProduct.comm R _
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M)
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) _ _
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M).isModule
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule
        (tensorProductLinearEquiv φ M x) := by
  rfl

/-- Pointwise naturality of the scalar-first comparison uses the maps of
Mathlib's change-of-rings functors, including both opposite scalar views. -/
theorem extendScalarsLinearEquiv_naturality {M N : ModuleCat.{uM} Rᵐᵒᵖ}
    (g : M ⟶ N) (x : Obj φ M) :
    extendScalarsLinearEquiv φ N (map φ g.hom x) =
      (ModuleCat.restrictScalars (RingEquiv.toOpposite S).symm.toRingHom).map
        ((ModuleCat.extendScalars φ).map
          ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).map g))
        (extendScalarsLinearEquiv φ M x) := by
  let sourceRCat :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M
  let targetRCat :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj N
  let coefficientRCat := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)
  let sourceAdd : AddCommMonoid sourceRCat := sourceRCat.isAddCommGroup.toAddCommMonoid
  let targetAdd : AddCommMonoid targetRCat := targetRCat.isAddCommGroup.toAddCommMonoid
  let coefficientAdd : AddCommMonoid coefficientRCat :=
    coefficientRCat.isAddCommGroup.toAddCommMonoid
  let sourceModule : @Module R sourceRCat _ sourceAdd := sourceRCat.isModule
  let targetModule : @Module R targetRCat _ targetAdd := targetRCat.isModule
  let coefficientModule : @Module R coefficientRCat _ coefficientAdd := coefficientRCat.isModule
  let sourceMap : sourceRCat →ₗ[R] targetRCat :=
    ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).map g).hom
  let coefficientId := @LinearMap.id R coefficientRCat _ coefficientAdd coefficientModule
  let moduleFirstMap := @TensorProduct.map R R _ _ (RingHom.id R)
    sourceRCat coefficientRCat targetRCat coefficientRCat
    sourceAdd coefficientAdd targetAdd coefficientAdd
    sourceModule coefficientModule targetModule coefficientModule sourceMap coefficientId
  let scalarFirstMap := @TensorProduct.map R R _ _ (RingHom.id R)
    coefficientRCat sourceRCat coefficientRCat targetRCat
    coefficientAdd sourceAdd coefficientAdd targetAdd
    coefficientModule sourceModule coefficientModule targetModule coefficientId sourceMap
  let commuteM := @TensorProduct.comm R _ sourceRCat coefficientRCat
    sourceAdd coefficientAdd sourceModule coefficientModule
  let commuteN := @TensorProduct.comm R _ targetRCat coefficientRCat
    targetAdd coefficientAdd targetModule coefficientModule
  let rightScalarFirstM :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite S).symm.toRingHom).obj
      ((ModuleCat.extendScalars φ).obj sourceRCat)
  let rightScalarFirstN :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite S).symm.toRingHom).obj
      ((ModuleCat.extendScalars φ).obj targetRCat)
  let categoricalMap : rightScalarFirstM ⟶ rightScalarFirstN :=
    (ModuleCat.restrictScalars (RingEquiv.toOpposite S).symm.toRingHom).map
      ((ModuleCat.extendScalars φ).map
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).map g))
  have categoricalMap_eq (z : rightScalarFirstM) :
      categoricalMap z = scalarFirstMap z := by
    refine @TensorProduct.inductionOn R _ coefficientRCat sourceRCat
      coefficientAdd sourceAdd coefficientModule sourceModule
      (fun y ↦ categoricalMap y = scalarFirstMap y) z ?_ ?_
    · intro s m
      have categoricalPure : categoricalMap
          (@TensorProduct.tmul R _ coefficientRCat sourceRCat
            coefficientAdd sourceAdd coefficientModule sourceModule s m) =
          @TensorProduct.tmul R _ coefficientRCat targetRCat
            coefficientAdd targetAdd coefficientModule targetModule s (sourceMap m) := by
        exact (ModuleCat.restrictScalars.map_apply
          (RingEquiv.toOpposite S).symm.toRingHom
          ((ModuleCat.extendScalars φ).map
            ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).map g))
          (@TensorProduct.tmul R _ coefficientRCat sourceRCat
            coefficientAdd sourceAdd coefficientModule sourceModule s m)).trans
              (ModuleCat.ExtendScalars.map_tmul φ
                ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).map g) s m)
      have tensorPure : scalarFirstMap
          (@TensorProduct.tmul R _ coefficientRCat sourceRCat
            coefficientAdd sourceAdd coefficientModule sourceModule s m) =
          @TensorProduct.tmul R _ coefficientRCat targetRCat
            coefficientAdd targetAdd coefficientModule targetModule s (sourceMap m) :=
        @TensorProduct.map_tmul R R _ _ (RingHom.id R)
          coefficientRCat sourceRCat coefficientRCat targetRCat
          coefficientAdd sourceAdd coefficientAdd targetAdd
          coefficientModule sourceModule coefficientModule targetModule coefficientId sourceMap s m
      exact categoricalPure.trans tensorPure.symm
    · intro y z hy hz
      -- The hom projection fixes both categorical additive structures as data.
      exact (categoricalMap.hom.map_add y z).trans
        ((congrArg₂ (fun a b : rightScalarFirstN ↦ a + b) hy hz).trans
          (scalarFirstMap.map_add y z).symm)
  have moduleFirstNaturality :
      tensorProductLinearEquiv φ N (map φ g.hom x) =
        moduleFirstMap (tensorProductLinearEquiv φ M x) :=
    tensorProductLinearEquiv_naturality φ g x
  have commute_map (y : tensorProductObj φ M) :
      commuteN (moduleFirstMap y) = scalarFirstMap (commuteM y) :=
    (@TensorProduct.map_comm R R _ _ (RingHom.id R)
      coefficientRCat sourceRCat coefficientRCat targetRCat
      coefficientAdd sourceAdd coefficientAdd targetAdd
      coefficientModule sourceModule coefficientModule targetModule coefficientId sourceMap y).symm
  exact (extendScalarsLinearEquiv_eq_comm φ N (map φ g.hom x)).trans
    ((congrArg commuteN moduleFirstNaturality).trans
      ((commute_map (tensorProductLinearEquiv φ M x)).trans
        ((categoricalMap_eq (commuteM (tensorProductLinearEquiv φ M x))).symm.trans
          (congrArg (fun z : rightScalarFirstM ↦ categoricalMap z)
            (extendScalarsLinearEquiv_eq_comm φ M x).symm))))

end CommutativeTarget

section OppositeBaseChange

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

open scoped ChangeOfRings

/-- Right scalar extension agrees with scalar-first extension along the opposite
ring homomorphism. The coefficient module is restriction along `RingHom.op φ`,
and the equivalence is linear over `Sᵐᵒᵖ`. No nontriviality or finiteness
assumption is required. -/
noncomputable def oppositeScalarEquiv (φ : R →+* S)
    (M : ModuleCat.{uM} Rᵐᵒᵖ) :
    Obj φ M ≃ₗ[Sᵐᵒᵖ] (ModuleCat.extendScalars (RingHom.op φ)).obj M := by
  letI : Algebra Rᵐᵒᵖ Sᵐᵒᵖ := (RingHom.op φ).toAlgebra
  -- Normalize the whole stored coefficient Module and tensor actions, not just SMul.
  -- This is the original extendScalars carrier: both coefficient Modules reduce
  -- to Module.compHom Sᵐᵒᵖ (RingHom.op φ).
  change Obj φ M ≃ₗ[Sᵐᵒᵖ] Sᵐᵒᵖ ⊗[Rᵐᵒᵖ] M
  let inclusion : M →ₛₗ[RingHom.op φ] Sᵐᵒᵖ ⊗[Rᵐᵒᵖ] M :=
    { toFun := fun m ↦ (1 : Sᵐᵒᵖ) ⊗ₜ[Rᵐᵒᵖ] m
      map_add' := fun m n ↦ TensorProduct.tmul_add _ m n
      map_smul' := by
        intro r m
        change (1 : Sᵐᵒᵖ) ⊗ₜ[Rᵐᵒᵖ] (r • m) =
          (RingHom.op φ r) • ((1 : Sᵐᵒᵖ) ⊗ₜ[Rᵐᵒᵖ] m)
        calc
          (1 : Sᵐᵒᵖ) ⊗ₜ[Rᵐᵒᵖ] (r • m) = (r • (1 : Sᵐᵒᵖ)) ⊗ₜ[Rᵐᵒᵖ] m :=
            (TensorProduct.smul_tmul r (1 : Sᵐᵒᵖ) m).symm
          _ = ((RingHom.op φ r) • (1 : Sᵐᵒᵖ)) ⊗ₜ[Rᵐᵒᵖ] m := rfl
          _ = (RingHom.op φ r) • ((1 : Sᵐᵒᵖ) ⊗ₜ[Rᵐᵒᵖ] m) :=
            (TensorProduct.smul_tmul' (RingHom.op φ r) (1 : Sᵐᵒᵖ) m).symm }
  let forward : Obj φ M →ₗ[Sᵐᵒᵖ] Sᵐᵒᵖ ⊗[Rᵐᵒᵖ] M :=
    fromSemilinear φ inclusion
  have forward_tmul (m : M) (s : S) :
      forward (tmul φ m s) = MulOpposite.op s ⊗ₜ[Rᵐᵒᵖ] m := by
    rw [fromSemilinear_tmul]
    change MulOpposite.op s • ((1 : Sᵐᵒᵖ) ⊗ₜ[Rᵐᵒᵖ] m) =
      MulOpposite.op s ⊗ₜ[Rᵐᵒᵖ] m
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  let pureInverse : Sᵐᵒᵖ →+ M →+ Obj φ M :=
    { toFun := fun s ↦
        { toFun := fun m ↦ tmul φ m (MulOpposite.unop s)
          map_zero' := by
            letI : Module R S := φ.toModule
            exact BalancedTensorProduct.zero_tmul (MulOpposite.unop s)
          map_add' := fun m n ↦ by
            letI : Module R S := φ.toModule
            exact BalancedTensorProduct.add_tmul m n (MulOpposite.unop s) }
      map_zero' := by
        apply AddMonoidHom.ext
        intro m
        letI : Module R S := φ.toModule
        exact BalancedTensorProduct.tmul_zero m
      map_add' := by
        intro s t
        apply AddMonoidHom.ext
        intro m
        letI : Module R S := φ.toModule
        exact BalancedTensorProduct.tmul_add m (MulOpposite.unop s) (MulOpposite.unop t) }
  have balanced (r : Rᵐᵒᵖ) (s : Sᵐᵒᵖ) (m : M) :
      pureInverse (r • s) m = pureInverse s (r • m) := by
    change tmul φ m (MulOpposite.unop s * φ (MulOpposite.unop r)) =
      tmul φ (MulOpposite.op (MulOpposite.unop r) • m) (MulOpposite.unop s)
    rw [smul_tmul, mul_comm]
  let inverse : Sᵐᵒᵖ ⊗[Rᵐᵒᵖ] M →+ Obj φ M :=
    TensorProduct.liftAddHom pureInverse balanced
  have inverse_tmul (s : Sᵐᵒᵖ) (m : M) :
      inverse (s ⊗ₜ[Rᵐᵒᵖ] m) = tmul φ m (MulOpposite.unop s) := rfl
  have leftHom : inverse.comp forward.toAddMonoidHom = AddMonoidHom.id (Obj φ M) := by
    letI : Module R S := φ.toModule
    apply BalancedTensorProduct.hom_ext (R := R) (M := M) (N := S)
    intro m s
    change inverse (forward (tmul φ m s)) = tmul φ m s
    exact (congrArg inverse (forward_tmul m s)).trans
      (inverse_tmul (MulOpposite.op s) m)
  exact
    { toFun := forward
      invFun := inverse
      left_inv := fun x ↦ DFunLike.congr_fun leftHom x
      right_inv := by
        intro x
        induction x using TensorProduct.inductionOn with
        | tmul s m =>
            change forward (inverse (s ⊗ₜ[Rᵐᵒᵖ] m)) = s ⊗ₜ[Rᵐᵒᵖ] m
            exact (congrArg forward (inverse_tmul s m)).trans
              (forward_tmul m (MulOpposite.unop s))
        | add x y hx hy =>
            change forward (inverse (x + y)) = x + y
            exact (congrArg forward (inverse.map_add x y)).trans
              ((forward.map_add (inverse x) (inverse y)).trans
                (congrArg₂ (fun a b ↦ a + b) hx hy))
      map_add' := forward.map_add
      map_smul' := forward.map_smul' }

/-- The inverse comparison restores the coefficient as an ordinary ring element. -/
@[simp]
theorem oppositeScalarEquiv_symm_tmul (φ : R →+* S)
    (M : ModuleCat.{uM} Rᵐᵒᵖ) (m : M) (s : S) :
    (oppositeScalarEquiv φ M).symm
        (MulOpposite.op s ⊗ₜ[Rᵐᵒᵖ, RingHom.op φ] m) = tmul φ m s :=
  rfl

/-- The comparison puts the opposite coefficient first. -/
@[simp]
theorem oppositeScalarEquiv_tmul (φ : R →+* S)
    (M : ModuleCat.{uM} Rᵐᵒᵖ) (m : M) (s : S) :
    oppositeScalarEquiv φ M (tmul φ m s) =
      MulOpposite.op s ⊗ₜ[Rᵐᵒᵖ, RingHom.op φ] m := by
  apply (oppositeScalarEquiv φ M).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (oppositeScalarEquiv_symm_tmul φ M m s).symm

/-- Right scalar extension distributes over the tensor product of the original
right `R`-modules. This equivalence is linear over `Sᵐᵒᵖ`; the source modules
may have independent carrier universes, and either scalar ring may be zero. -/
noncomputable def tensorBaseChangeEquiv (φ : R →+* S)
    (M : ModuleCat.{uM} Rᵐᵒᵖ) (N : ModuleCat.{uN} Rᵐᵒᵖ) :
    Obj φ (M ⊗[Rᵐᵒᵖ] N) ≃ₗ[Sᵐᵒᵖ] Obj φ M ⊗[Sᵐᵒᵖ] Obj φ N := by
  letI : Algebra Rᵐᵒᵖ Sᵐᵒᵖ := (RingHom.op φ).toAlgebra
  exact (oppositeScalarEquiv φ (ModuleCat.of Rᵐᵒᵖ (M ⊗[Rᵐᵒᵖ] N))).trans
    ((TensorProduct.AlgebraTensorModule.distribBaseChange Rᵐᵒᵖ Sᵐᵒᵖ M N).trans
      (TensorProduct.congr (oppositeScalarEquiv φ M).symm
        (oppositeScalarEquiv φ N).symm))

/-- The coefficient can be placed in the first extended tensor factor. -/
@[simp]
theorem tensorBaseChangeEquiv_tmul (φ : R →+* S)
    (M : ModuleCat.{uM} Rᵐᵒᵖ) (N : ModuleCat.{uN} Rᵐᵒᵖ)
    (m : M) (n : N) (s : S) :
    tensorBaseChangeEquiv φ M N (tmul φ (m ⊗ₜ[Rᵐᵒᵖ] n) s) =
      tmul φ m s ⊗ₜ[Sᵐᵒᵖ] tmul φ n 1 := by
  letI : Algebra Rᵐᵒᵖ Sᵐᵒᵖ := (RingHom.op φ).toAlgebra
  -- Fix the scalar bridges and distribution map on the canonical tensor modules.
  let eM : Obj φ M ≃ₗ[Sᵐᵒᵖ] Sᵐᵒᵖ ⊗[Rᵐᵒᵖ] M := oppositeScalarEquiv φ M
  let eN : Obj φ N ≃ₗ[Sᵐᵒᵖ] Sᵐᵒᵖ ⊗[Rᵐᵒᵖ] N := oppositeScalarEquiv φ N
  let eMN : Obj φ (M ⊗[Rᵐᵒᵖ] N) ≃ₗ[Sᵐᵒᵖ]
      Sᵐᵒᵖ ⊗[Rᵐᵒᵖ] (M ⊗[Rᵐᵒᵖ] N) :=
    oppositeScalarEquiv φ (ModuleCat.of Rᵐᵒᵖ (M ⊗[Rᵐᵒᵖ] N))
  let d := TensorProduct.AlgebraTensorModule.distribBaseChange Rᵐᵒᵖ Sᵐᵒᵖ M N
  let c := TensorProduct.congr eM.symm eN.symm
  have hMN : eMN (tmul φ (m ⊗ₜ[Rᵐᵒᵖ] n) s) =
      MulOpposite.op s ⊗ₜ[Rᵐᵒᵖ] (m ⊗ₜ[Rᵐᵒᵖ] n) :=
    oppositeScalarEquiv_tmul φ (ModuleCat.of Rᵐᵒᵖ (M ⊗[Rᵐᵒᵖ] N)) (m ⊗ₜ n) s
  have hM : eM.symm (MulOpposite.op s ⊗ₜ[Rᵐᵒᵖ] m) = tmul φ m s :=
    oppositeScalarEquiv_symm_tmul φ M m s
  have hN : eN.symm ((1 : Sᵐᵒᵖ) ⊗ₜ[Rᵐᵒᵖ] n) = tmul φ n 1 :=
    oppositeScalarEquiv_symm_tmul φ N n 1
  change c (d (eMN (tmul φ (m ⊗ₜ[Rᵐᵒᵖ] n) s))) = _
  calc
    c (d (eMN (tmul φ (m ⊗ₜ[Rᵐᵒᵖ] n) s))) =
        c (d (MulOpposite.op s ⊗ₜ[Rᵐᵒᵖ] (m ⊗ₜ[Rᵐᵒᵖ] n))) :=
      congrArg (fun x ↦ c (d x)) hMN
    _ = c ((MulOpposite.op s ⊗ₜ[Rᵐᵒᵖ] m) ⊗ₜ[Sᵐᵒᵖ]
        ((1 : Sᵐᵒᵖ) ⊗ₜ[Rᵐᵒᵖ] n)) :=
      congrArg c (TensorProduct.AlgebraTensorModule.distribBaseChange_tmul
        (R := Rᵐᵒᵖ) (A := Sᵐᵒᵖ) m n (MulOpposite.op s))
    _ = eM.symm (MulOpposite.op s ⊗ₜ[Rᵐᵒᵖ] m) ⊗ₜ[Sᵐᵒᵖ]
        eN.symm ((1 : Sᵐᵒᵖ) ⊗ₜ[Rᵐᵒᵖ] n) :=
      TensorProduct.congr_tmul eM.symm eN.symm _ _
    _ = tmul φ m s ⊗ₜ[Sᵐᵒᵖ] tmul φ n 1 :=
      congrArg₂ (fun x y ↦ x ⊗ₜ[Sᵐᵒᵖ] y) hM hN

/-- The inverse multiplies the two ordinary coefficients. -/
@[simp]
theorem tensorBaseChangeEquiv_symm_tmul (φ : R →+* S)
    (M : ModuleCat.{uM} Rᵐᵒᵖ) (N : ModuleCat.{uN} Rᵐᵒᵖ)
    (m : M) (n : N) (s t : S) :
    (tensorBaseChangeEquiv φ M N).symm
        (tmul φ m s ⊗ₜ[Sᵐᵒᵖ] tmul φ n t) =
      tmul φ (m ⊗ₜ[Rᵐᵒᵖ] n) (s * t) := by
  letI : Algebra Rᵐᵒᵖ Sᵐᵒᵖ := (RingHom.op φ).toAlgebra
  let eM : Obj φ M ≃ₗ[Sᵐᵒᵖ] Sᵐᵒᵖ ⊗[Rᵐᵒᵖ] M := oppositeScalarEquiv φ M
  let eN : Obj φ N ≃ₗ[Sᵐᵒᵖ] Sᵐᵒᵖ ⊗[Rᵐᵒᵖ] N := oppositeScalarEquiv φ N
  let eMN : Obj φ (M ⊗[Rᵐᵒᵖ] N) ≃ₗ[Sᵐᵒᵖ]
      Sᵐᵒᵖ ⊗[Rᵐᵒᵖ] (M ⊗[Rᵐᵒᵖ] N) :=
    oppositeScalarEquiv φ (ModuleCat.of Rᵐᵒᵖ (M ⊗[Rᵐᵒᵖ] N))
  let d := TensorProduct.AlgebraTensorModule.distribBaseChange Rᵐᵒᵖ Sᵐᵒᵖ M N
  let c := TensorProduct.congr eM.symm eN.symm
  have hM : eM (tmul φ m s) = MulOpposite.op s ⊗ₜ[Rᵐᵒᵖ] m :=
    oppositeScalarEquiv_tmul φ M m s
  have hN : eN (tmul φ n t) = MulOpposite.op t ⊗ₜ[Rᵐᵒᵖ] n :=
    oppositeScalarEquiv_tmul φ N n t
  have hop : MulOpposite.op s * MulOpposite.op t = MulOpposite.op (s * t) := by
    change MulOpposite.op (t * s) = MulOpposite.op (s * t)
    exact congrArg MulOpposite.op (mul_comm t s)
  change eMN.symm (d.symm (c.symm (tmul φ m s ⊗ₜ[Sᵐᵒᵖ] tmul φ n t))) = _
  calc
    eMN.symm (d.symm (c.symm (tmul φ m s ⊗ₜ[Sᵐᵒᵖ] tmul φ n t))) =
        eMN.symm (d.symm (eM (tmul φ m s) ⊗ₜ[Sᵐᵒᵖ] eN (tmul φ n t))) :=
      congrArg (fun x ↦ eMN.symm (d.symm x))
        (TensorProduct.congr_symm_tmul eM.symm eN.symm _ _)
    _ = eMN.symm (d.symm ((MulOpposite.op s ⊗ₜ[Rᵐᵒᵖ] m) ⊗ₜ[Sᵐᵒᵖ]
        (MulOpposite.op t ⊗ₜ[Rᵐᵒᵖ] n))) :=
      congrArg (fun x ↦ eMN.symm (d.symm x))
        (congrArg₂ (fun x y ↦ x ⊗ₜ[Sᵐᵒᵖ] y) hM hN)
    _ = eMN.symm ((MulOpposite.op s * MulOpposite.op t) ⊗ₜ[Rᵐᵒᵖ]
        (m ⊗ₜ[Rᵐᵒᵖ] n)) :=
      congrArg eMN.symm (TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul
        (R := Rᵐᵒᵖ) (A := Sᵐᵒᵖ) m n (MulOpposite.op s) (MulOpposite.op t))
    _ = eMN.symm (MulOpposite.op (s * t) ⊗ₜ[Rᵐᵒᵖ] (m ⊗ₜ[Rᵐᵒᵖ] n)) :=
      congrArg (fun a ↦ eMN.symm (a ⊗ₜ[Rᵐᵒᵖ] (m ⊗ₜ[Rᵐᵒᵖ] n))) hop
    _ = tmul φ (m ⊗ₜ[Rᵐᵒᵖ] n) (s * t) :=
      oppositeScalarEquiv_symm_tmul φ (ModuleCat.of Rᵐᵒᵖ (M ⊗[Rᵐᵒᵖ] N))
        (m ⊗ₜ[Rᵐᵒᵖ] n) (s * t)

end OppositeBaseChange

end ModuleCat.RightExtension
