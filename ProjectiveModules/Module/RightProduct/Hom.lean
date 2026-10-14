/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.RightProduct
public import Mathlib.Algebra.Module.LinearMap.End

/-!
# Linear maps between right modules over coefficient products

For families of right modules over semirings, `Module.piRightHomAddEquiv`
identifies maps linear for the canonical coefficient-product action with
families of factor-linear maps. The forward map evaluates on an input supported
at one coordinate; its inverse applies the factor maps coordinatewise.

`Module.piRightEndEquiv` uses the same additive equivalence on endomorphisms
and the ordinary Pi semiring structure on factor endomorphisms. Multiplication
is composition, in the convention `f * g = f.comp g`.

## Implementation notes

The index can be arbitrary. Coefficients, source fibers, target fibers and
composition's third family have independent universes. The source and target
use the existing `Module.piRightModule` explicitly, not a global instance or
a replacement scalar action. Classical decidable equality is confined to
supported-function expressions and definition bodies.

## References

These constructions use Projective Modules' coefficient-product module data
and Mathlib's supported functions, linear maps, additive equivalences and
endomorphism semirings.
-/

@[expose] public section

universe uι uR uM uN uP

namespace Module

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) (Mi : ι → Type uM)
variable [∀ i, Semiring (Ri i)] [∀ i, AddCommMonoid (Mi i)]
variable [∀ i, Module (Ri i)ᵐᵒᵖ (Mi i)]
variable (Ni : ι → Type uN) [∀ i, AddCommMonoid (Ni i)]
variable [∀ i, Module (Ri i)ᵐᵒᵖ (Ni i)]

private theorem piRightModule_smul_apply_unop
    (a : (∀ i, Ri i)ᵐᵒᵖ) (x : ∀ i, Mi i) (i : ι) :
    (@SMul.smul _ _ (piRightModule Ri Mi).toSMul a x) i =
      MulOpposite.op (a.unop i) • x i := by
  exact piRightModule_smul_apply Ri Mi a.unop x i

private theorem piRightModule_single_smul (a : ∀ i, Ri i) (i : ι) (m : Mi i) :
    (by
      classical
      exact Pi.single i (MulOpposite.op (a i) • m)) =
        @SMul.smul _ _ (piRightModule Ri Mi).toSMul (MulOpposite.op a)
          (by
            classical
            exact Pi.single i m) := by
  classical
  let : ∀ j, Module (∀ k, Ri k)ᵐᵒᵖ (Mi j) := fun j =>
    Module.compHom (Mi j) (RingHom.op (Pi.evalRingHom Ri j))
  exact Pi.single_smul (f := Mi) i (MulOpposite.op a) m

private theorem piRightModule_single_one_smul (i : ι) (x : ∀ i, Mi i) :
    @SMul.smul _ _ (piRightModule Ri Mi).toSMul
      (MulOpposite.op (by
        classical
        exact Pi.single i (1 : Ri i))) x =
          (by
            classical
            exact Pi.single i (x i)) := by
  classical
  funext j
  rw [piRightModule_smul_apply]
  simpa only [MulOpposite.op_one, one_smul] using
    (Pi.apply_single (fun j (r : Ri j) => MulOpposite.op r • x j)
      (fun j => by simp only [MulOpposite.op_zero, zero_smul]) i (1 : Ri i) j)

/-- Maps linear for the canonical right coefficient-product action correspond
additively to families of factor-linear maps. -/
noncomputable def piRightHomAddEquiv :
    (@LinearMap (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ri i)ᵐᵒᵖ _ _ (RingHom.id _)
      (∀ i, Mi i) (∀ i, Ni i) _ _ (piRightModule Ri Mi) (piRightModule Ri Ni)) ≃+
        (∀ i, Mi i →ₗ[(Ri i)ᵐᵒᵖ] Ni i) := by
  classical
  letI : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) := piRightModule Ri Mi
  letI : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ni i) := piRightModule Ri Ni
  exact
    { toFun := fun f i =>
        { toFun := fun m => f (Pi.single i m) i
          map_add' := by
            intro m n
            rw [Pi.single_add]
            exact congrArg (fun y : ∀ i, Ni i => y i)
              (f.map_add (Pi.single i m) (Pi.single i n))
          map_smul' := by
            intro r m
            have hs : Pi.single i (r • m) =
                @SMul.smul _ _ (piRightModule Ri Mi).toSMul
                  (MulOpposite.op (Pi.single i r.unop)) (Pi.single i m) := by
              simpa only [Pi.single_eq_same, MulOpposite.op_unop] using
                piRightModule_single_smul Ri Mi (Pi.single i r.unop) i m
            calc
              f (Pi.single i (r • m)) i =
                  f (@SMul.smul _ _ (piRightModule Ri Mi).toSMul
                    (MulOpposite.op (Pi.single i r.unop)) (Pi.single i m)) i :=
                congrArg (fun y : ∀ i, Mi i => f y i) hs
              _ = (@SMul.smul _ _ (piRightModule Ri Ni).toSMul
                  (MulOpposite.op (Pi.single i r.unop)) (f (Pi.single i m))) i :=
                congrArg (fun y : ∀ i, Ni i => y i)
                  (f.map_smul (MulOpposite.op (Pi.single i r.unop)) (Pi.single i m))
              _ = r • f (Pi.single i m) i := by
                rw [piRightModule_smul_apply, Pi.single_eq_same, MulOpposite.op_unop] }
      invFun := fun φ =>
        { toFun := fun x i => φ i (x i)
          map_add' := by
            intro x y
            funext i
            exact (φ i).map_add (x i) (y i)
          map_smul' := by
            intro a x
            funext i
            calc
              φ i ((@SMul.smul _ _ (piRightModule Ri Mi).toSMul a x) i) =
                  φ i (MulOpposite.op (a.unop i) • x i) :=
                congrArg (φ i) (piRightModule_smul_apply_unop Ri Mi a x i)
              _ = MulOpposite.op (a.unop i) • φ i (x i) := (φ i).map_smul _ _
              _ = (@SMul.smul _ _ (piRightModule Ri Ni).toSMul a
                  (fun j => φ j (x j))) i :=
                (piRightModule_smul_apply_unop Ri Ni a (fun j => φ j (x j)) i).symm }
      left_inv := by
        intro f
        apply LinearMap.ext
        intro x
        funext i
        change f (Pi.single i (x i)) i = f x i
        calc
          f (Pi.single i (x i)) i =
              f (@SMul.smul _ _ (piRightModule Ri Mi).toSMul
                (MulOpposite.op (Pi.single i (1 : Ri i))) x) i :=
            congrArg (fun y : ∀ i, Mi i => f y i)
              (piRightModule_single_one_smul Ri Mi i x).symm
          _ = (@SMul.smul _ _ (piRightModule Ri Ni).toSMul
              (MulOpposite.op (Pi.single i (1 : Ri i))) (f x)) i :=
            congrArg (fun y : ∀ i, Ni i => y i)
              (f.map_smul (MulOpposite.op (Pi.single i (1 : Ri i))) x)
          _ = f x i := by
            rw [piRightModule_smul_apply, Pi.single_eq_same, MulOpposite.op_one, one_smul]
      right_inv := by
        intro φ
        funext i
        apply LinearMap.ext
        intro m
        change φ i ((Pi.single i m) i) = φ i m
        rw [Pi.single_eq_same]
      map_add' := by
        intro f g
        funext i
        apply LinearMap.ext
        intro m
        rfl }

/-- The component map is evaluation on an input supported at its coordinate. -/
@[simp] theorem piRightHomAddEquiv_apply
    (f : @LinearMap (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ri i)ᵐᵒᵖ _ _ (RingHom.id _)
      (∀ i, Mi i) (∀ i, Ni i) _ _ (piRightModule Ri Mi) (piRightModule Ri Ni))
    (i : ι) (m : Mi i) :
    piRightHomAddEquiv Ri Mi Ni f i m =
      f (by
        classical
        exact Pi.single i m) i := by
  rfl

/-- The inverse correspondence applies each factor map at its coordinate. -/
@[simp] theorem piRightHomAddEquiv_symm_apply
    (φ : ∀ i, Mi i →ₗ[(Ri i)ᵐᵒᵖ] Ni i) (x : ∀ i, Mi i) (i : ι) :
    (piRightHomAddEquiv Ri Mi Ni).symm φ x i = φ i (x i) := by
  rfl

/-- Every output coordinate depends only on the corresponding input coordinate. -/
theorem piRightHomAddEquiv_eval
    (f : @LinearMap (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ri i)ᵐᵒᵖ _ _ (RingHom.id _)
      (∀ i, Mi i) (∀ i, Ni i) _ _ (piRightModule Ri Mi) (piRightModule Ri Ni))
    (x : ∀ i, Mi i) (i : ι) :
    f x i = piRightHomAddEquiv Ri Mi Ni f i (x i) := by
  let : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) := piRightModule Ri Mi
  let : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ni i) := piRightModule Ri Ni
  calc
    f x i = (piRightHomAddEquiv Ri Mi Ni).symm
        (piRightHomAddEquiv Ri Mi Ni f) x i :=
      congrFun (LinearMap.congr_fun
        ((piRightHomAddEquiv Ri Mi Ni).symm_apply_apply f).symm x) i
    _ = piRightHomAddEquiv Ri Mi Ni f i (x i) :=
      piRightHomAddEquiv_symm_apply Ri Mi Ni _ x i

/-- A supported input is sent to the same support, with its value given by the
corresponding component map. -/
theorem piRightHomAddEquiv_single
    (f : @LinearMap (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ri i)ᵐᵒᵖ _ _ (RingHom.id _)
      (∀ i, Mi i) (∀ i, Ni i) _ _ (piRightModule Ri Mi) (piRightModule Ri Ni))
    (i : ι) (m : Mi i) :
    f (by
      classical
      exact Pi.single i m) =
        (by
          classical
          exact Pi.single i (piRightHomAddEquiv Ri Mi Ni f i m)) := by
  classical
  funext j
  rw [piRightHomAddEquiv_eval Ri Mi Ni f (Pi.single i m) j]
  by_cases h : j = i
  · subst j
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h, map_zero]

/-- A supported input has zero image at every distinct output coordinate. -/
theorem piRightHomAddEquiv_single_apply_of_ne
    (f : @LinearMap (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ri i)ᵐᵒᵖ _ _ (RingHom.id _)
      (∀ i, Mi i) (∀ i, Ni i) _ _ (piRightModule Ri Mi) (piRightModule Ri Ni))
    (i j : ι) (h : j ≠ i) (m : Mi i) :
    f (by
      classical
      exact Pi.single i m) j = 0 := by
  classical
  rw [piRightHomAddEquiv_single Ri Mi Ni f i m, Pi.single_eq_of_ne h]

/-- Equality of coefficient-product-linear maps is detected by all their factor
components, without identifying the universes of different fibers. -/
theorem piRightHomAddEquiv_ext_iff
    (f g : @LinearMap (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ri i)ᵐᵒᵖ _ _ (RingHom.id _)
      (∀ i, Mi i) (∀ i, Ni i) _ _ (piRightModule Ri Mi) (piRightModule Ri Ni)) :
    f = g ↔ ∀ i (m : Mi i),
      piRightHomAddEquiv Ri Mi Ni f i m = piRightHomAddEquiv Ri Mi Ni g i m := by
  constructor
  · rintro rfl i m
    rfl
  · intro h
    apply (piRightHomAddEquiv Ri Mi Ni).injective
    funext i
    exact LinearMap.ext (h i)

/-- The components of the identity map are the factor identity maps. -/
theorem piRightHomAddEquiv_id (i : ι) :
    piRightHomAddEquiv Ri Mi Mi
      (@LinearMap.id (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) _ _ (piRightModule Ri Mi)) i =
        LinearMap.id := by
  classical
  apply LinearMap.ext
  intro m
  simp only [piRightHomAddEquiv_apply, LinearMap.id_apply, Pi.single_eq_same]

variable (Pi' : ι → Type uP) [∀ i, AddCommMonoid (Pi' i)]
variable [∀ i, Module (Ri i)ᵐᵒᵖ (Pi' i)]

/-- Components preserve composition, allowing the third family its own universe. -/
theorem piRightHomAddEquiv_comp
    (f : @LinearMap (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ri i)ᵐᵒᵖ _ _ (RingHom.id _)
      (∀ i, Mi i) (∀ i, Ni i) _ _ (piRightModule Ri Mi) (piRightModule Ri Ni))
    (g : @LinearMap (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ri i)ᵐᵒᵖ _ _ (RingHom.id _)
      (∀ i, Ni i) (∀ i, Pi' i) _ _ (piRightModule Ri Ni) (piRightModule Ri Pi'))
    (i : ι) :
    piRightHomAddEquiv Ri Mi Pi' (g.comp f) i =
      (piRightHomAddEquiv Ri Ni Pi' g i).comp (piRightHomAddEquiv Ri Mi Ni f i) := by
  classical
  apply LinearMap.ext
  intro m
  calc
    piRightHomAddEquiv Ri Mi Pi' (g.comp f) i m =
        g (f (Pi.single i m)) i :=
      piRightHomAddEquiv_apply Ri Mi Pi' (g.comp f) i m
    _ = piRightHomAddEquiv Ri Ni Pi' g i (f (Pi.single i m) i) :=
      piRightHomAddEquiv_eval Ri Ni Pi' g (f (Pi.single i m)) i
    _ = ((piRightHomAddEquiv Ri Ni Pi' g i).comp
        (piRightHomAddEquiv Ri Mi Ni f i)) m := by
      simp only [LinearMap.comp_apply, piRightHomAddEquiv_apply]

/-- The endomorphism semiring of an assembled right module is the product of
its factor endomorphism semirings, using the additive component correspondence. -/
noncomputable def piRightEndEquiv :
    (@Module.End (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) _ _ (piRightModule Ri Mi)) ≃+*
      (∀ i, Module.End (Ri i)ᵐᵒᵖ (Mi i)) := by
  letI : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) := piRightModule Ri Mi
  exact
    { __ := piRightHomAddEquiv Ri Mi Mi
      map_mul' := by
        intro f g
        funext i
        change piRightHomAddEquiv Ri Mi Mi (f.comp g) i =
          (piRightHomAddEquiv Ri Mi Mi f i).comp (piRightHomAddEquiv Ri Mi Mi g i)
        exact piRightHomAddEquiv_comp Ri Mi Mi Mi g f i }

/-- The endomorphism correspondence has the same additive data as the Hom
correspondence. -/
theorem piRightEndEquiv_toAddEquiv :
    (piRightEndEquiv Ri Mi).toAddEquiv = piRightHomAddEquiv Ri Mi Mi := by
  rfl

/-- The endomorphism component evaluates on an input supported at its coordinate. -/
@[simp] theorem piRightEndEquiv_apply
    (f : @Module.End (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) _ _ (piRightModule Ri Mi))
    (i : ι) (m : Mi i) :
    piRightEndEquiv Ri Mi f i m =
      f (by
        classical
        exact Pi.single i m) i := by
  exact piRightHomAddEquiv_apply Ri Mi Mi f i m

/-- The inverse endomorphism correspondence acts coordinatewise. -/
@[simp] theorem piRightEndEquiv_symm_apply
    (φ : ∀ i, Module.End (Ri i)ᵐᵒᵖ (Mi i)) (x : ∀ i, Mi i) (i : ι) :
    (piRightEndEquiv Ri Mi).symm φ x i = φ i (x i) := by
  exact piRightHomAddEquiv_symm_apply Ri Mi Mi φ x i

/-- The multiplicative identity corresponds to the family of factor identities. -/
theorem piRightEndEquiv_one (i : ι) :
    piRightEndEquiv Ri Mi
      (1 : @Module.End (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) _ _ (piRightModule Ri Mi)) i = 1 := by
  classical
  let : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) := piRightModule Ri Mi
  apply LinearMap.ext
  intro m
  simp only [piRightEndEquiv_apply, Module.End.one_eq_id, LinearMap.id_apply,
    Pi.single_eq_same]

/-- Multiplication is preserved in the order `f * g = f.comp g`. -/
theorem piRightEndEquiv_mul
    (f g : @Module.End (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) _ _ (piRightModule Ri Mi))
    (i : ι) :
    piRightEndEquiv Ri Mi (f * g) i =
      piRightEndEquiv Ri Mi f i * piRightEndEquiv Ri Mi g i := by
  let : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) := piRightModule Ri Mi
  exact congrFun (map_mul (piRightEndEquiv Ri Mi) f g) i

end Pi

end Module
