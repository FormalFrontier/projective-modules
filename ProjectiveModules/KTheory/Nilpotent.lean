/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.ScalarExtension
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.RingTheory.Ideal.Maps
import ProjectiveModules.Module.RightEndomorphismMatrix
import ProjectiveModules.Module.RightRegular
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Nilpotent.Basic
import GeneralLinearGroups.MatrixNilpotentIdeal

/-!
# Nilpotent change of rings on finite-projective classes and K₀

A surjective homomorphism of rings with nilpotent kernel induces additive
bijections on finite-projective right-module classes and on K₀. The associated
additive equivalences have precisely the scalar-extension maps as their forward
homomorphisms. Here nilpotence means that one power of the kernel ideal is zero;
it is not merely the assertion that each kernel element is nilpotent.

The rings need not be commutative or nontrivial. Their universes, and the carrier
universe of a finite projective module used in a generator formula, are independent.

## References and credits

The constructions use Mathlib's `AddEquiv.ofBijective` and ideal powers, and the
finite-projective class and scalar-extension APIs of Projective Modules,
including contributions by Prism and Lens. These interfaces use Mathlib's
finite-projective representatives and additive Grothendieck group.

Charles A. Weibel's *The K-book* provides mathematical motivation. Iris
contributed the scalar-extension kernel API; Loupe contributed the matrix-ideal
nilpotence API in General Linear Groups. Original formalization by Formal
Frontier Agents, with AI assistance by Lens.
-/

@[expose] public section

universe uR uS uT v

namespace KTheory

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [Ring R] [Ring S] [Ring T]
variable (f : R →+* S) (hf : Function.Surjective f)
variable (hker : IsNilpotent (RingHom.ker f))

namespace ProjectiveClass

/-- Surjective change of rings with uniformly nilpotent kernel induces a
bijection on finite-projective right-module isomorphism classes. -/
theorem map_bijective_of_surjective_of_isNilpotent_ker
    (hf : Function.Surjective f) (hker : IsNilpotent (RingHom.ker f)) :
    Function.Bijective (map f) := by
  constructor
  · exact (by
      classical
      intro a b hab
      obtain ⟨P, rfl⟩ := KTheory.ProjectiveClass.of_surjective R a
      obtain ⟨Q, rfl⟩ := KTheory.ProjectiveClass.of_surjective R b
      simp only [KTheory.ProjectiveClass.map_of] at hab
      obtain ⟨e⟩ :=
        (KTheory.ProjectiveClass.of_eq_iff S
          (ModuleCat.RightExtension.Obj f P)
          (ModuleCat.RightExtension.Obj f Q)).mp hab
      obtain ⟨n, hn⟩ := hker
      let J : Ideal Rᵐᵒᵖ :=
        ModuleCat.RightExtension.oppositeIdeal (RingHom.ker f)
      have hJpow : J ^ n = 0 := by
        change (ModuleCat.RightExtension.oppositeIdeal (RingHom.ker f)) ^ n = 0
        have hmem (k : ℕ) :
            ∀ x ∈ (ModuleCat.RightExtension.oppositeIdeal (RingHom.ker f)) ^ k,
              x.unop ∈ (RingHom.ker f) ^ k := by
          induction k with
          | zero =>
              intro x _
              simp only [Submodule.pow_zero, Ideal.one_eq_top, Submodule.mem_top]
          | succ k ih =>
              intro x hx
              rw [Submodule.pow_succ] at hx
              exact Submodule.mul_induction_on hx
                (fun a ha b hb => by
                  have hb' : b.unop ∈ RingHom.ker f := by
                    apply (ModuleCat.RightExtension.mem_oppositeIdeal_iff
                      (RingHom.ker f) b.unop).mp
                    simpa only [MulOpposite.op_unop] using hb
                  rw [MulOpposite.unop_mul, Ideal.IsTwoSided.pow_succ]
                  exact Ideal.mul_mem_mul hb' (ih a ha))
                (fun a b ha hb => by
                  rw [MulOpposite.unop_add]
                  exact add_mem ha hb)
        apply le_antisymm
        · intro x hx
          have hx' := hmem n x hx
          rw [hn] at hx'
          simpa only [Ideal.zero_eq_bot, Submodule.mem_bot,
            MulOpposite.unop_eq_zero_iff] using hx'
        · rw [Ideal.zero_eq_bot]
          exact bot_le
      have uniformEndPower :
          ∀ {X : Type uR} [AddCommGroup X] [Module Rᵐᵒᵖ X]
            (d : Module.End Rᵐᵒᵖ X),
            LinearMap.range d ≤ J • (⊤ : Submodule Rᵐᵒᵖ X) → d ^ n = 0 := by
        intro X _ _ d hd
        have hpow : ∀ k : ℕ,
            LinearMap.range (d ^ k) ≤ J ^ k • (⊤ : Submodule Rᵐᵒᵖ X) := by
          intro k
          induction k with
          | zero =>
              rw [Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul]
              exact le_top
          | succ k ih =>
              calc
                LinearMap.range (d ^ (k + 1)) =
                    (LinearMap.range (d ^ k)).map d := by
                  rw [Module.End.iterate_succ', LinearMap.range_comp]
                _ ≤ (J ^ k • (⊤ : Submodule Rᵐᵒᵖ X)).map d :=
                  Submodule.map_mono ih
                _ = J ^ k • LinearMap.range d := by
                  rw [Submodule.map_smul'', Submodule.map_top]
                _ ≤ J ^ k • (J • (⊤ : Submodule Rᵐᵒᵖ X)) :=
                  Submodule.smul_mono le_rfl hd
                _ = J ^ (k + 1) • (⊤ : Submodule Rᵐᵒᵖ X) := by
                  rw [Submodule.pow_succ, Submodule.mul_smul]
        apply (LinearMap.range_le_bot_iff (d ^ n)).mp
        simpa only [hJpow, Ideal.zero_eq_bot, Submodule.bot_smul] using hpow n
      let : Module Rᵐᵒᵖ (ModuleCat.RightExtension.Obj f P) :=
        Module.compHom (ModuleCat.RightExtension.Obj f P) (RingHom.op f)
      let : Module Rᵐᵒᵖ (ModuleCat.RightExtension.Obj f Q) :=
        Module.compHom (ModuleCat.RightExtension.Obj f Q) (RingHom.op f)
      let tauP : P →ₗ[Rᵐᵒᵖ] ModuleCat.RightExtension.Obj f P :=
        { toFun := ModuleCat.RightExtension.tmulOne f
          map_add' := (ModuleCat.RightExtension.tmulOne f).map_add
          map_smul' := (ModuleCat.RightExtension.tmulOne f).map_smulₛₗ }
      let tauQ : Q →ₗ[Rᵐᵒᵖ] ModuleCat.RightExtension.Obj f Q :=
        { toFun := ModuleCat.RightExtension.tmulOne f
          map_add' := (ModuleCat.RightExtension.tmulOne f).map_add
          map_smul' := (ModuleCat.RightExtension.tmulOne f).map_smulₛₗ }
      let eR : ModuleCat.RightExtension.Obj f P →ₗ[Rᵐᵒᵖ]
          ModuleCat.RightExtension.Obj f Q :=
        { toFun := e
          map_add' := e.map_add
          map_smul' := fun r x => e.map_smul (RingHom.op f r) x }
      let eiR : ModuleCat.RightExtension.Obj f Q →ₗ[Rᵐᵒᵖ]
          ModuleCat.RightExtension.Obj f P :=
        { toFun := e.symm
          map_add' := e.symm.map_add
          map_smul' := fun r x => e.symm.map_smul (RingHom.op f r) x }
      obtain ⟨u, hu⟩ := Module.projective_lifting_property tauQ (eR.comp tauP)
        (ModuleCat.RightExtension.tmulOne_surjective (M := Q) f hf)
      obtain ⟨v, hv⟩ := Module.projective_lifting_property tauP (eiR.comp tauQ)
        (ModuleCat.RightExtension.tmulOne_surjective (M := P) f hf)
      have hu' (p : P) : ModuleCat.RightExtension.tmulOne f (u p) =
          e (ModuleCat.RightExtension.tmulOne f p) := by
        exact congrArg
          (fun g : P →ₗ[Rᵐᵒᵖ] ModuleCat.RightExtension.Obj f Q => g p) hu
      have hv' (q : Q) : ModuleCat.RightExtension.tmulOne f (v q) =
          e.symm (ModuleCat.RightExtension.tmulOne f q) := by
        exact congrArg
          (fun g : Q →ₗ[Rᵐᵒᵖ] ModuleCat.RightExtension.Obj f P => g q) hv
      let dP : Module.End Rᵐᵒᵖ P := v.comp u - LinearMap.id
      let dQ : Module.End Rᵐᵒᵖ Q := u.comp v - LinearMap.id
      have hdPzero (p : P) : ModuleCat.RightExtension.tmulOne f (dP p) = 0 := by
        change ModuleCat.RightExtension.tmulOne f (v (u p) - p) = 0
        rw [map_sub, hv', hu', e.symm_apply_apply, sub_self]
      have hdQzero (q : Q) : ModuleCat.RightExtension.tmulOne f (dQ q) = 0 := by
        change ModuleCat.RightExtension.tmulOne f (u (v q) - q) = 0
        rw [map_sub, hu', hv', e.apply_symm_apply, sub_self]
      have hdP : LinearMap.range dP ≤ J • (⊤ : Submodule Rᵐᵒᵖ P) := by
        rintro x ⟨p, rfl⟩
        change dP p ∈ ModuleCat.RightExtension.idealSubmodule (M := P) (RingHom.ker f)
        rw [← ModuleCat.RightExtension.tmulOne_ker_of_surjective (M := P) f hf]
        exact hdPzero p
      have hdQ : LinearMap.range dQ ≤ J • (⊤ : Submodule Rᵐᵒᵖ Q) := by
        rintro x ⟨q, rfl⟩
        change dQ q ∈ ModuleCat.RightExtension.idealSubmodule (M := Q) (RingHom.ker f)
        rw [← ModuleCat.RightExtension.tmulOne_ker_of_surjective (M := Q) f hf]
        exact hdQzero q
      have hdPnil : IsNilpotent dP := ⟨n, uniformEndPower dP hdP⟩
      have hdQnil : IsNilpotent dQ := ⟨n, uniformEndPower dQ hdQ⟩
      have hPunit : IsUnit (v.comp u : Module.End Rᵐᵒᵖ P) := by
        have h := hdPnil.isUnit_one_add
        change IsUnit ((1 : Module.End Rᵐᵒᵖ P) + (v.comp u - 1)) at h
        rw [sub_eq_add_neg, add_left_comm, add_neg_cancel, add_zero] at h
        exact h
      have hQunit : IsUnit (u.comp v : Module.End Rᵐᵒᵖ Q) := by
        have h := hdQnil.isUnit_one_add
        change IsUnit ((1 : Module.End Rᵐᵒᵖ Q) + (u.comp v - 1)) at h
        rw [sub_eq_add_neg, add_left_comm, add_neg_cancel, add_zero] at h
        exact h
      have hPbij : Function.Bijective (v.comp u) :=
        (Module.End.isUnit_iff (v.comp u)).mp hPunit
      have hQbij : Function.Bijective (u.comp v) :=
        (Module.End.isUnit_iff (u.comp v)).mp hQunit
      have huinj : Function.Injective u := by
        intro p p' h
        exact hPbij.1 (congrArg v h)
      have husurj : Function.Surjective u := by
        intro q
        obtain ⟨q', hq'⟩ := hQbij.2 q
        exact ⟨v q', hq'⟩
      exact KTheory.ProjectiveClass.of_eq_of_equiv R P
        (LinearEquiv.ofBijective u ⟨huinj, husurj⟩)
    )
  · apply map_surjective_of_lift_idempotents f
    intro n E hE
    let F : Matrix (Fin n) (Fin n) R →+* Matrix (Fin n) (Fin n) S :=
      RingHom.mapMatrix f
    have hFsurj : Function.Surjective F := by
      intro B
      refine ⟨fun a b ↦ (hf (B a b)).choose, ?_⟩
      ext a b
      exact (hf (B a b)).choose_spec
    have hFnil : ∀ B ∈ RingHom.ker F, IsNilpotent B := by
      intro B hB
      apply Matrix.isNilpotent_of_isNilpotent_ideal (RingHom.ker f) B ?_ hker
      intro a b
      apply RingHom.mem_ker.mpr
      exact congrArg (fun C : Matrix (Fin n) (Fin n) S ↦ C a b)
        (RingHom.mem_ker.mp hB)
    exact exists_isIdempotentElem_eq_of_ker_isNilpotent F hFnil E (hFsurj E) hE

/-- The additive equivalence on finite-projective right-module classes induced
by a surjective ring homomorphism with nilpotent kernel. Its forward map is
scalar extension along that homomorphism. -/
noncomputable def equivOfSurjectiveOfIsNilpotentKer :
    ProjectiveClass R ≃+ ProjectiveClass S :=
  AddEquiv.ofBijective (map f)
    (map_bijective_of_surjective_of_isNilpotent_ker f hf hker)

/-- The whole forward additive homomorphism is the scalar-extension map. -/
theorem equivOfSurjectiveOfIsNilpotentKer_toAddMonoidHom :
    (equivOfSurjectiveOfIsNilpotentKer f hf hker).toAddMonoidHom = map f := by
  rfl

/-- The equivalence acts by scalar extension on every projective class. -/
@[simp]
theorem equivOfSurjectiveOfIsNilpotentKer_apply (x : ProjectiveClass R) :
    equivOfSurjectiveOfIsNilpotentKer f hf hker x = map f x := by
  rfl

/-- On a finite projective module in any carrier universe, the equivalence
returns the class of its right scalar extension. -/
theorem equivOfSurjectiveOfIsNilpotentKer_of (M : Type v)
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    equivOfSurjectiveOfIsNilpotentKer f hf hker (of R M) =
      of S (ModuleCat.RightExtension.Obj f M) := by
  simpa only [equivOfSurjectiveOfIsNilpotentKer_apply] using map_of f M

/-- The inverse recovers a projective class from its scalar extension. -/
@[simp]
theorem equivOfSurjectiveOfIsNilpotentKer_symm_map (x : ProjectiveClass R) :
    (equivOfSurjectiveOfIsNilpotentKer f hf hker).symm (map f x) = x := by
  simpa only [equivOfSurjectiveOfIsNilpotentKer_apply] using
    (equivOfSurjectiveOfIsNilpotentKer f hf hker).symm_apply_apply x

variable (R) in
/-- For the identity ring homomorphism, the change-of-rings equivalence is the
identity, independently of the witnesses of its hypotheses. -/
@[simp]
theorem equivOfSurjectiveOfIsNilpotentKer_id
    (hid : Function.Surjective (RingHom.id R))
    (hker_id : IsNilpotent (RingHom.ker (RingHom.id R))) :
    equivOfSurjectiveOfIsNilpotentKer (RingHom.id R) hid hker_id =
      AddEquiv.refl (ProjectiveClass R) := by
  apply AddEquiv.ext
  intro x
  simp only [equivOfSurjectiveOfIsNilpotentKer_apply, map_id,
    AddMonoidHom.id_apply, AddEquiv.refl_apply]

/-- Iterated nilpotent change of rings acts by the scalar-extension map of the
composite. The formula does not require a separate nilpotence witness for the
composite kernel. -/
theorem equivOfSurjectiveOfIsNilpotentKer_comp_apply
    (g : S →+* T) (hg : Function.Surjective g)
    (hker_g : IsNilpotent (RingHom.ker g)) (x : ProjectiveClass R) :
    equivOfSurjectiveOfIsNilpotentKer g hg hker_g
        (equivOfSurjectiveOfIsNilpotentKer f hf hker x) =
      map (g.comp f) x := by
  simp only [equivOfSurjectiveOfIsNilpotentKer_apply, map_comp,
    AddMonoidHom.comp_apply]

end ProjectiveClass

namespace K0

/-- Surjective change of rings with uniformly nilpotent kernel induces a
bijection on K₀. -/
theorem map_bijective_of_surjective_of_isNilpotent_ker
    (hf : Function.Surjective f) (hker : IsNilpotent (RingHom.ker f)) :
    Function.Bijective (map f) := by
  exact KTheory.K0.map_bijective_of_projectiveClass_map_bijective f
    (KTheory.ProjectiveClass.map_bijective_of_surjective_of_isNilpotent_ker f hf hker)

/-- The additive equivalence on K₀ induced by a surjective ring homomorphism
with nilpotent kernel. Its forward homomorphism is the existing scalar-extension
map on K₀. -/
noncomputable def equivOfSurjectiveOfIsNilpotentKer : K0 R ≃+ K0 S :=
  AddEquiv.ofBijective (map f)
    (map_bijective_of_surjective_of_isNilpotent_ker f hf hker)

/-- The whole forward additive homomorphism is the K₀ scalar-extension map. -/
theorem equivOfSurjectiveOfIsNilpotentKer_toAddMonoidHom :
    (equivOfSurjectiveOfIsNilpotentKer f hf hker).toAddMonoidHom = map f := by
  rfl

/-- The equivalence acts by scalar extension on every K₀ element. -/
@[simp]
theorem equivOfSurjectiveOfIsNilpotentKer_apply (x : K0 R) :
    equivOfSurjectiveOfIsNilpotentKer f hf hker x = map f x := by
  rfl

/-- On a class generator, the K₀ equivalence is induced by the equivalence on
finite-projective classes. -/
theorem equivOfSurjectiveOfIsNilpotentKer_ofClass (x : ProjectiveClass R) :
    equivOfSurjectiveOfIsNilpotentKer f hf hker (ofClass R x) =
      ofClass S (ProjectiveClass.equivOfSurjectiveOfIsNilpotentKer f hf hker x) := by
  change map f (ofClass R x) = ofClass S (ProjectiveClass.map f x)
  exact map_ofClass f x

/-- On a finite projective module in any carrier universe, the equivalence
returns the K₀ generator of its right scalar extension. -/
theorem equivOfSurjectiveOfIsNilpotentKer_of (M : Type v)
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    equivOfSurjectiveOfIsNilpotentKer f hf hker (of R M) =
      of S (ModuleCat.RightExtension.Obj f M) := by
  simpa only [equivOfSurjectiveOfIsNilpotentKer_apply] using map_of f M

/-- The inverse recovers a K₀ element from its scalar extension. -/
@[simp]
theorem equivOfSurjectiveOfIsNilpotentKer_symm_map (x : K0 R) :
    (equivOfSurjectiveOfIsNilpotentKer f hf hker).symm (map f x) = x := by
  simpa only [equivOfSurjectiveOfIsNilpotentKer_apply] using
    (equivOfSurjectiveOfIsNilpotentKer f hf hker).symm_apply_apply x

variable (R) in
/-- For the identity ring homomorphism, the K₀ change-of-rings equivalence is
the identity, independently of the witnesses of its hypotheses. -/
@[simp]
theorem equivOfSurjectiveOfIsNilpotentKer_id
    (hid : Function.Surjective (RingHom.id R))
    (hker_id : IsNilpotent (RingHom.ker (RingHom.id R))) :
    equivOfSurjectiveOfIsNilpotentKer (RingHom.id R) hid hker_id =
      AddEquiv.refl (K0 R) := by
  apply AddEquiv.ext
  intro x
  change map (RingHom.id R) x = x
  exact DFunLike.congr_fun (map_id R) x

/-- Iterated nilpotent change of rings acts by the K₀ scalar-extension map of
the composite, without a separate witness for the composite kernel. -/
theorem equivOfSurjectiveOfIsNilpotentKer_comp_apply
    (g : S →+* T) (hg : Function.Surjective g)
    (hker_g : IsNilpotent (RingHom.ker g)) (x : K0 R) :
    equivOfSurjectiveOfIsNilpotentKer g hg hker_g
        (equivOfSurjectiveOfIsNilpotentKer f hf hker x) =
      map (g.comp f) x := by
  change map g (map f x) = map (g.comp f) x
  exact (DFunLike.congr_fun (map_comp f g) x).symm

end K0

end KTheory
