/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import ProjectiveModules.Module.BalancedTensorProduct
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Extension of scalars for right modules over arbitrary rings

For a homomorphism of possibly noncommutative rings `f : R →+* S`, this file
constructs extension of scalars from right `R`-modules to right `S`-modules.
The canonical semilinear map into the extension is surjective whenever `f` is
surjective.
-/

@[expose] public section

universe uR uS uM uN

open CategoryTheory

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The left `R`-action and right `S`-action on `S` induced by a ring
homomorphism commute. -/
theorem smulCommClass (f : R →+* S) :
    let _ : Module R S := f.toModule
    SMulCommClass R Sᵐᵒᵖ S := by
  let _ : Module R S := f.toModule
  exact
    { smul_comm := fun r s x => by
        change f r * (x * MulOpposite.unop s) = (f r * x) * MulOpposite.unop s
        rw [mul_assoc] }

/-- Extension of a right module along a homomorphism of arbitrary rings. -/
abbrev Obj (f : R →+* S) (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    Type (max uM uS) :=
  @BalancedTensorProduct R M S _ _ _ _ f.toModule

variable (f : R →+* S)

variable {M : Type uM} {N : Type uN}
variable [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable [AddCommGroup N] [Module Rᵐᵒᵖ N]

instance : AddCommGroup (Obj f M) := by
  letI : Module R S := f.toModule
  infer_instance

instance : Module Sᵐᵒᵖ (Obj f M) := by
  letI : Module R S := f.toModule
  let _ : SMulCommClass R Sᵐᵒᵖ S := smulCommClass f
  infer_instance

/-- The canonical pure tensor in a right-module extension of scalars. -/
def tmul (m : M) (s : S) : Obj f M := by
  letI : Module R S := f.toModule
  exact BalancedTensorProduct.tmul m s

@[simp]
theorem tmul_smul (m : M) (s : S) (t : Sᵐᵒᵖ) :
    t • tmul f m s = tmul f m (t • s) := by
  let _ : Module R S := f.toModule
  let _ : SMulCommClass R Sᵐᵒᵖ S := smulCommClass f
  exact BalancedTensorProduct.smul_tmul_right t m s

@[simp]
theorem smul_tmul (r : R) (m : M) (s : S) :
    tmul f (MulOpposite.op r • m) s = tmul f m (f r * s) := by
  let _ : Module R S := f.toModule
  exact BalancedTensorProduct.smul_tmul r m s

/-- The additive homomorphism underlying scalar extension of a morphism. This
is an implementation detail of `ModuleCat.RightExtension.map`. -/
def mapAddHom (g : M →ₗ[Rᵐᵒᵖ] N) : Obj f M →+ Obj f N := by
  letI : Module R S := f.toModule
  apply BalancedTensorProduct.lift
  exact
    { toFun := fun m s => tmul f (g m) s
      map_zero_left := fun s => by simp [tmul]
      map_add_left := fun m₁ m₂ s => by simp [tmul, map_add, BalancedTensorProduct.add_tmul]
      map_zero_right := fun m => by simp [tmul]
      map_add_right := fun m s₁ s₂ => by simp [tmul, BalancedTensorProduct.tmul_add]
      balance := fun r m s => by
        rw [g.map_smul]
        exact BalancedTensorProduct.smul_tmul r (g m) s }

/-- Extension of scalars on a morphism of right modules. -/
def map (g : M →ₗ[Rᵐᵒᵖ] N) : Obj f M →ₗ[Sᵐᵒᵖ] Obj f N where
  __ := mapAddHom (f := f) g
  map_smul' t x := by
    let _ : Module R S := f.toModule
    let _ : SMulCommClass R Sᵐᵒᵖ S := smulCommClass f
    exact DFunLike.congr_fun
      (BalancedTensorProduct.hom_ext (R := R) (M := M) (N := S)
        (g := (mapAddHom (f := f) g).comp (BalancedTensorProduct.smulAddHom t))
        (h := (BalancedTensorProduct.smulAddHom t).comp (mapAddHom (f := f) g))
        fun m s => by
          simp [mapAddHom, tmul, BalancedTensorProduct.smulAddHom,
            BalancedTensorProduct.smulBalancedMap]) x

@[simp]
theorem map_tmul (g : M →ₗ[Rᵐᵒᵖ] N) (m : M) (s : S) :
    map f g (tmul f m s) = tmul f (g m) s := by
  let _ : Module R S := f.toModule
  simp [map, mapAddHom, tmul]

/-- Two right-linear maps from an extension of scalars are equal if they agree
on pure tensors. -/
theorem linearMap_ext {X : Type*} [AddCommGroup X] [Module Sᵐᵒᵖ X]
    {g h : Obj f M →ₗ[Sᵐᵒᵖ] X}
    (H : ∀ m s, g (tmul f m s) = h (tmul f m s)) : g = h := by
  apply LinearMap.ext
  intro x
  let _ : Module R S := f.toModule
  exact DFunLike.congr_fun
    (BalancedTensorProduct.hom_ext (R := R) (M := M) (N := S)
      (g := g.toAddMonoidHom) (h := h.toAddMonoidHom) H) x

@[simp]
theorem map_id : map f (LinearMap.id (R := Rᵐᵒᵖ) (M := M)) = LinearMap.id := by
  apply linearMap_ext f
  intro m s
  simp

@[simp]
theorem map_comp {P : Type*} [AddCommGroup P] [Module Rᵐᵒᵖ P]
    (g : M →ₗ[Rᵐᵒᵖ] N) (h : N →ₗ[Rᵐᵒᵖ] P) :
    map f (h.comp g) = (map f h).comp (map f g) := by
  apply linearMap_ext f
  intro m s
  simp

@[simp]
theorem map_add (g h : M →ₗ[Rᵐᵒᵖ] N) : map f (g + h) = map f g + map f h := by
  apply linearMap_ext f
  intro m s
  simp only [LinearMap.add_apply, map_tmul]
  let _ : Module R S := f.toModule
  exact BalancedTensorProduct.add_tmul (g m) (h m) s

/-- Extension of scalars along a homomorphism of arbitrary rings, as a functor
between categories of right modules. -/
abbrev functor : ModuleCat.{max uM uS} (MulOpposite R) ⥤
    ModuleCat.{max uM uS} (MulOpposite S) where
  obj M := ModuleCat.of Sᵐᵒᵖ (Obj f M)
  map g := ModuleCat.ofHom (map f g.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    exact map_id (f := f) (M := M)
  map_comp g h := by
    apply ModuleCat.hom_ext
    exact map_comp f g.hom h.hom

instance functorAdditive : (functor f).Additive where
  map_add {X Y} g h := by
    apply ModuleCat.hom_ext
    exact map_add f g.hom h.hom

section SemilinearHomEquiv

universe uX

variable {X : Type uX} [AddCommGroup X] [Module Sᵐᵒᵖ X]

/-- Restrict a right-linear map out of an extension of scalars to tensors with
second factor `1`. -/
def toSemilinear (g : Obj f M →ₗ[Sᵐᵒᵖ] X) : M →ₛₗ[RingHom.op f] X where
  toFun m := g (tmul f m 1)
  map_add' m n := by
    let _ : Module R S := f.toModule
    have h : tmul f (m + n) 1 = tmul f m 1 + tmul f n 1 := by
      change BalancedTensorProduct.tmul (m + n) 1 =
        BalancedTensorProduct.tmul m 1 + BalancedTensorProduct.tmul n 1
      exact BalancedTensorProduct.add_tmul m n 1
    rw [h, g.map_add]
  map_smul' r m := by
    change g (tmul f (r • m) 1) = (RingHom.op f r) • g (tmul f m 1)
    rw [← g.map_smul]
    congr 1
    rw [tmul_smul]
    simpa using smul_tmul f (MulOpposite.unop r) m 1

@[simp]
theorem toSemilinear_apply (g : Obj f M →ₗ[Sᵐᵒᵖ] X) (m : M) :
    toSemilinear f g m = g (tmul f m 1) :=
  rfl

/-- The canonical semilinear map from a right module to its extension of
scalars, sending `m` to `m ⊗ 1`. -/
def tmulOne : M →ₛₗ[RingHom.op f] Obj f M :=
  toSemilinear f LinearMap.id

@[simp]
theorem tmulOne_apply (m : M) : tmulOne f m = tmul f m 1 :=
  rfl

/-- The canonical map to a right-module extension of scalars is surjective
when the ring homomorphism is surjective. -/
theorem tmulOne_surjective (hf : Function.Surjective f) :
    Function.Surjective (tmulOne f : M → Obj f M) := by
  intro x
  induction x using BalancedTensorProduct.induction_on with
  | zero => exact ⟨0, (tmulOne f).map_zero⟩
  | pure m s =>
      obtain ⟨r, rfl⟩ := hf s
      refine ⟨MulOpposite.op r • m, ?_⟩
      rw [tmulOne_apply, smul_tmul, mul_one]
      rfl
  | neg x hx =>
      obtain ⟨m, rfl⟩ := hx
      exact ⟨-m, (tmulOne f).map_neg m⟩
  | add x y hx hy =>
      obtain ⟨m, rfl⟩ := hx
      obtain ⟨n, rfl⟩ := hy
      exact ⟨m + n, (tmulOne f).map_add m n⟩

/-- The additive homomorphism induced by a semilinear map from the original
right module. This is an implementation detail of `fromSemilinear`. -/
def fromSemilinearAddHom (h : M →ₛₗ[RingHom.op f] X) : Obj f M →+ X := by
  letI : Module R S := f.toModule
  apply BalancedTensorProduct.lift
  exact
    { toFun := fun m s => MulOpposite.op s • h m
      map_zero_left := fun s => by rw [h.map_zero, smul_zero]
      map_add_left := fun m n s => by rw [h.map_add, smul_add]
      map_zero_right := fun m => by
        change (0 : Sᵐᵒᵖ) • h m = 0
        exact zero_smul Sᵐᵒᵖ (h m)
      map_add_right := fun m s t => by rw [MulOpposite.op_add, add_smul]
      balance := fun r m s => by
        rw [h.map_smulₛₗ]
        change MulOpposite.op s • (MulOpposite.op (f r) • h m) =
          MulOpposite.op (f r * s) • h m
        rw [← mul_smul]
        rfl }

/-- Extend a semilinear map from the original right module to a right-linear
map from its extension of scalars. -/
def fromSemilinear (h : M →ₛₗ[RingHom.op f] X) : Obj f M →ₗ[Sᵐᵒᵖ] X where
  __ := fromSemilinearAddHom f h
  map_smul' t x := by
    let _ : Module R S := f.toModule
    let _ : SMulCommClass R Sᵐᵒᵖ S := smulCommClass f
    let lhs : Obj f M →+ X :=
      (fromSemilinearAddHom f h).comp (BalancedTensorProduct.smulAddHom t)
    let rhs : Obj f M →+ X :=
      { toFun := fun z => t • fromSemilinearAddHom f h z
        map_zero' := by rw [(fromSemilinearAddHom f h).map_zero, smul_zero]
        map_add' := fun a b => by rw [(fromSemilinearAddHom f h).map_add, smul_add] }
    exact DFunLike.congr_fun
      (BalancedTensorProduct.hom_ext (R := R) (M := M) (N := S)
        (g := lhs) (h := rhs) fun m s => by
          change fromSemilinearAddHom f h
              (BalancedTensorProduct.smulAddHom t (BalancedTensorProduct.tmul m s)) =
            t • fromSemilinearAddHom f h (BalancedTensorProduct.tmul m s)
          simp only [fromSemilinearAddHom, BalancedTensorProduct.smulAddHom,
            BalancedTensorProduct.lift_tmul, BalancedTensorProduct.smulBalancedMap]
          exact mul_smul t (MulOpposite.op s) (h m)) x

@[simp]
theorem fromSemilinear_tmul (h : M →ₛₗ[RingHom.op f] X) (m : M) (s : S) :
    fromSemilinear f h (tmul f m s) = MulOpposite.op s • h m := by
  let _ : Module R S := f.toModule
  change BalancedTensorProduct.lift _ (BalancedTensorProduct.tmul (R := R) m s) = _
  rw [BalancedTensorProduct.lift_tmul]

/-- The extension/restriction correspondence for linear and semilinear maps
over arbitrary, possibly noncommutative rings. -/
def linearMapEquiv : (Obj f M →ₗ[Sᵐᵒᵖ] X) ≃ (M →ₛₗ[RingHom.op f] X) where
  toFun := toSemilinear f
  invFun := fromSemilinear f
  left_inv g := by
    apply linearMap_ext f
    intro m s
    rw [fromSemilinear_tmul]
    change MulOpposite.op s • g (tmul f m 1) = g (tmul f m s)
    rw [← g.map_smul, tmul_smul]
    simp
  right_inv h := by
    apply LinearMap.ext
    intro m
    change fromSemilinear f h (tmul f m 1) = h m
    rw [fromSemilinear_tmul]
    change (1 : Sᵐᵒᵖ) • h m = h m
    exact one_smul Sᵐᵒᵖ (h m)

/-- The additive extension/restriction correspondence for right modules over
arbitrary, possibly noncommutative rings. -/
def linearMapAddEquiv : (Obj f M →ₗ[Sᵐᵒᵖ] X) ≃+ (M →ₛₗ[RingHom.op f] X) where
  __ := linearMapEquiv f
  map_add' g h := by
    apply LinearMap.ext
    intro m
    rfl

end SemilinearHomEquiv

namespace HomEquiv

variable (M' : ModuleCat.{max uM uS} (MulOpposite R))
variable (X : ModuleCat.{max uM uS} (MulOpposite S))

set_option backward.isDefEq.respectTransparency false in
/-- Send a map out of an extension of scalars to its value on tensors with
second factor `1`. -/
noncomputable def toRestriction (g : (functor f).obj M' ⟶ X) :
    M' ⟶ (ModuleCat.restrictScalars.{max uM uS} (RingHom.op f)).obj X :=
  ModuleCat.ofHom
    (X := M')
    (Y := (ModuleCat.restrictScalars.{max uM uS} (RingHom.op f)).obj X)
    { toFun := fun m => g (tmul f m 1)
      map_add' := fun m n => by
        change g.hom (tmul f (m + n) 1) = g.hom (tmul f m 1) + g.hom (tmul f n 1)
        let _ : Module R S := f.toModule
        have h : tmul f (m + n) 1 = tmul f m 1 + tmul f n 1 := by
          change BalancedTensorProduct.tmul (m + n) 1 =
            BalancedTensorProduct.tmul m 1 + BalancedTensorProduct.tmul n 1
          exact BalancedTensorProduct.add_tmul m n 1
        rw [h, g.hom.map_add]
      map_smul' := fun r m => by
        change g.hom (tmul f (r • m) 1) = (RingHom.op f r) • g.hom (tmul f m 1)
        rw [← g.hom.map_smul]
        congr 1
        rw [tmul_smul]
        simpa using smul_tmul f (MulOpposite.unop r) m 1 }

@[simp]
theorem toRestriction_apply (g : (functor f).obj M' ⟶ X) (m : M') :
    toRestriction f M' X g m = g (tmul f m 1) :=
  rfl

/-- The additive homomorphism induced by a map to a restricted right module.
This is an implementation detail of `ModuleCat.RightExtension.HomEquiv.fromRestriction`. -/
noncomputable def fromRestrictionAddHom
    (h : M' ⟶ (ModuleCat.restrictScalars.{max uM uS} (RingHom.op f)).obj X) :
    Obj f M' →+ X := by
  letI : Module R S := f.toModule
  apply BalancedTensorProduct.lift
  exact
    { toFun := fun m s => MulOpposite.op s • h m
      map_zero_left := fun s => by
        rw [h.hom.map_zero, smul_zero]
        rfl
      map_add_left := fun m n s => by
        rw [h.hom.map_add, smul_add]
        rfl
      map_zero_right := fun m => by
        change (0 : Sᵐᵒᵖ) • h m = 0
        exact zero_smul Sᵐᵒᵖ (h m)
      map_add_right := fun m s t => by
        rw [MulOpposite.op_add, add_smul]
        rfl
      balance := fun r m s => by
        rw [h.hom.map_smul]
        change MulOpposite.op s • (MulOpposite.op (f r) • h m) =
          MulOpposite.op (f r * s) • h m
        rw [← mul_smul]
        rfl }

/-- Send a map to a restricted right module to the corresponding map from the
extension of scalars. -/
noncomputable def fromRestriction
    (h : M' ⟶ (ModuleCat.restrictScalars.{max uM uS} (RingHom.op f)).obj X) :
    (functor f).obj M' ⟶ X :=
  ModuleCat.ofHom
    { __ := fromRestrictionAddHom f M' X h
      map_smul' := fun t x => by
        let _ : Module R S := f.toModule
        let _ : SMulCommClass R Sᵐᵒᵖ S := smulCommClass f
        let lhs : Obj f M' →+ X :=
          (fromRestrictionAddHom f M' X h).comp
            (BalancedTensorProduct.smulAddHom t)
        let rhs : Obj f M' →+ X :=
          { toFun := fun z => t • fromRestrictionAddHom f M' X h z
            map_zero' := by
              rw [(fromRestrictionAddHom f M' X h).map_zero, smul_zero]
            map_add' := fun a b => by
              rw [(fromRestrictionAddHom f M' X h).map_add, smul_add] }
        exact DFunLike.congr_fun
          (BalancedTensorProduct.hom_ext (R := R) (M := M') (N := S)
            (g := lhs) (h := rhs) fun m s => by
              simp [lhs, rhs, fromRestrictionAddHom, BalancedTensorProduct.smulAddHom,
                BalancedTensorProduct.smulBalancedMap, mul_smul]
              rfl) x }

@[simp]
theorem fromRestriction_tmul
    (h : M' ⟶ (ModuleCat.restrictScalars.{max uM uS} (RingHom.op f)).obj X)
    (m : M') (s : S) :
    fromRestriction f M' X h (tmul f m s) = MulOpposite.op s • h m := by
  let _ : Module R S := f.toModule
  change BalancedTensorProduct.lift _ (BalancedTensorProduct.tmul m s) = _
  rw [BalancedTensorProduct.lift_tmul]

/-- The extension/restriction adjunction for right modules over arbitrary
possibly noncommutative rings. -/
noncomputable def homEquiv :
    ((functor f).obj M' ⟶ X) ≃
      (M' ⟶ (ModuleCat.restrictScalars.{max uM uS} (RingHom.op f)).obj X) where
  toFun := toRestriction f M' X
  invFun := fromRestriction f M' X
  left_inv g := by
    apply ModuleCat.hom_ext
    apply linearMap_ext f
    intro m s
    rw [fromRestriction_tmul]
    change MulOpposite.op s • g.hom (tmul f m 1) = g.hom (tmul f m s)
    rw [← g.hom.map_smul, tmul_smul]
    simp
  right_inv h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change fromRestriction f M' X h (tmul f m 1) = h m
    rw [fromRestriction_tmul]
    change (1 : Sᵐᵒᵖ) • h m = h m
    exact one_smul Sᵐᵒᵖ (h m)

end HomEquiv

/-- Extension of scalars for right modules over arbitrary rings is left
adjoint to restriction of scalars. -/
noncomputable def adjunction :
    functor f ⊣ ModuleCat.restrictScalars.{max uM uS} (RingHom.op f) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M' X => HomEquiv.homEquiv f M' X
      homEquiv_naturality_left_symm := fun {M₁ M₂ X} g h => by
        apply ModuleCat.hom_ext
        apply linearMap_ext f
        intro m s
        change HomEquiv.fromRestriction f M₁ X (g ≫ h) (tmul f m s) =
          HomEquiv.fromRestriction f M₂ X h (tmul f (g m) s)
        rw [HomEquiv.fromRestriction_tmul, HomEquiv.fromRestriction_tmul]
        rfl
      homEquiv_naturality_right := fun {M' X Y} g h => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        rfl }

/-- Extension of scalars along a homomorphism of arbitrary rings preserves
projective right modules. -/
instance instProjective [Module.Projective Rᵐᵒᵖ M] :
    Module.Projective Sᵐᵒᵖ (Obj f M) := by
  apply Module.Projective.of_lifting_property
  intro A B _ _ _ _ q g hq
  let _ : Module Rᵐᵒᵖ A := Module.compHom A (RingHom.op f)
  let _ : Module Rᵐᵒᵖ B := Module.compHom B (RingHom.op f)
  let qR : A →ₗ[Rᵐᵒᵖ] B :=
    { toFun := q
      map_add' := q.map_add
      map_smul' := fun r a => q.map_smul (RingHom.op f r) a }
  let gR : M →ₗ[Rᵐᵒᵖ] B :=
    { toFun := toSemilinear f g
      map_add' := (toSemilinear f g).map_add
      map_smul' := (toSemilinear f g).map_smulₛₗ }
  obtain ⟨hR, hh⟩ := Module.projective_lifting_property qR gR hq
  let hSemi : M →ₛₗ[RingHom.op f] A :=
    { toFun := hR
      map_add' := hR.map_add
      map_smul' := hR.map_smul }
  let hS := fromSemilinear f hSemi
  refine ⟨hS, ?_⟩
  apply linearMap_ext f
  intro m s
  rw [LinearMap.comp_apply, fromSemilinear_tmul, q.map_smul]
  have hm := DFunLike.congr_fun hh m
  change q (hR m) = g (tmul f m 1) at hm
  change MulOpposite.op s • q (hR m) = g (tmul f m s)
  rw [hm, ← g.map_smul, tmul_smul]
  simp

/-- Extension of scalars along a homomorphism of arbitrary rings preserves
finite generation of right modules. -/
instance instFinite [Module.Finite Rᵐᵒᵖ M] : Module.Finite Sᵐᵒᵖ (Obj f M) := by
  obtain ⟨n, generators, hgenerators⟩ := Module.Finite.exists_fin (R := Rᵐᵒᵖ) (M := M)
  let Q : Submodule Sᵐᵒᵖ (Obj f M) :=
    Submodule.span Sᵐᵒᵖ (Set.range fun i => tmul f (generators i) 1)
  let P : Submodule Rᵐᵒᵖ M :=
    { carrier := {m | tmul f m 1 ∈ Q}
      zero_mem' := by
        change tmul f (0 : M) 1 ∈ Q
        let _ : Module R S := f.toModule
        rw [show tmul f (0 : M) 1 = 0 by
          change BalancedTensorProduct.tmul (0 : M) 1 = 0
          exact BalancedTensorProduct.zero_tmul 1]
        exact Q.zero_mem
      add_mem' := fun {m n} hm hn => by
        change tmul f (m + n) 1 ∈ Q
        let _ : Module R S := f.toModule
        rw [show tmul f (m + n) 1 = tmul f m 1 + tmul f n 1 by
          change BalancedTensorProduct.tmul (m + n) 1 =
            BalancedTensorProduct.tmul m 1 + BalancedTensorProduct.tmul n 1
          exact BalancedTensorProduct.add_tmul m n 1]
        exact Q.add_mem hm hn
      smul_mem' := fun r m hm => by
        change tmul f (MulOpposite.op (MulOpposite.unop r) • m) 1 ∈ Q
        change tmul f m 1 ∈ Q at hm
        rw [smul_tmul]
        have hs := Q.smul_mem (MulOpposite.op (f (MulOpposite.unop r))) hm
        simpa [tmul_smul] using hs }
  have hgen_mem : Set.range generators ⊆ P := by
    rintro m ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  have hP : P = ⊤ := by
    apply top_unique
    rw [← hgenerators]
    exact Submodule.span_le.2 hgen_mem
  have hpure (m : M) (s : S) : tmul f m s ∈ Q := by
    have hm : tmul f m 1 ∈ Q := by
      change m ∈ P
      rw [hP]
      trivial
    have hs := Q.smul_mem (MulOpposite.op s) hm
    simpa [tmul_smul] using hs
  have hmkQ : Q.mkQ = 0 := by
    apply linearMap_ext f
    intro m s
    change Q.mkQ (tmul f m s) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 (hpure m s)
  have hQ : Q = ⊤ := by
    rw [← Q.ker_mkQ, hmkQ, LinearMap.ker_zero]
  apply Module.Finite.of_fg_top
  have hfinite : (Set.range fun i => tmul f (generators i) 1).Finite := Set.finite_range _
  have hfg :
      (Submodule.span Sᵐᵒᵖ (Set.range fun i => tmul f (generators i) 1)).FG :=
    Submodule.fg_span hfinite
  change Q.FG at hfg
  rw [hQ] at hfg
  exact hfg

end ModuleCat.RightExtension
