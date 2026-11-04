/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Jacobson
public import ProjectiveModules.KTheory.ScalarExtension
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.RingTheory.Ideal.Maps
import ProjectiveModules.Module.RightEndomorphismMatrix
import ProjectiveModules.Module.RightRegular
import ProjectiveModules.Module.RightExtensionReflection
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Nilpotent.Basic
import GeneralLinearGroups.MatrixNilpotentIdeal

/-!
# Nilpotent change of rings on finite-projective classes and K₀

A surjective homomorphism whose kernel elements are nilpotent induces an
injective map on finite-projective right-module classes. No common exponent of
nilpotence is required for this injectivity statement.

If one power of the kernel ideal is zero, scalar extension induces additive
bijections on finite-projective right-module classes and on K₀. The associated
additive equivalences have precisely the scalar-extension maps as their forward
homomorphisms. These bijectivity and equivalence statements retain the stronger
ideal-nilpotence hypothesis.

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

namespace ProjectiveClass

/-- A surjective homomorphism whose kernel elements are nilpotent induces an
injective scalar-extension map on finite-projective right-module classes.
No common nilpotence exponent is required. This gives the injectivity part of
nil-ideal invariance from Weibel's *The K-book*, Chapter II, §2, for arbitrary,
possibly noncommutative rings. -/
theorem map_injective_of_surjective_of_isNilpotent_mem_ker
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hnil : ∀ r ∈ RingHom.ker f, IsNilpotent r) :
    Function.Injective (map f) := by
  exact map_injective_of_surjective_of_ker_le_jacobson f hf
    (Ideal.le_jacobson_bot_of_isNilpotent_mem (RingHom.ker f) hnil)

end ProjectiveClass

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
  · apply map_injective_of_surjective_of_isNilpotent_mem_ker f hf
    obtain ⟨n, hn⟩ := hker
    intro r hr
    refine ⟨n, ?_⟩
    have hrn : r ^ n ∈ (RingHom.ker f) ^ n :=
      Ideal.pow_mem_pow hr n
    rw [hn] at hrn
    simpa only [Ideal.zero_eq_bot, Submodule.mem_bot] using hrn
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
