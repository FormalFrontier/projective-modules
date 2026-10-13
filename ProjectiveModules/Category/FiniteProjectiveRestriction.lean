/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.FiniteProjective
public import ProjectiveModules.Module.ScalarRestriction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Equiv.Opposite

/-!
# Restriction of scalars for finite projective modules

For a homomorphism of arbitrary rings `φ : R →+* S`, restriction of scalars
preserves finite projective modules provided the canonical restricted regular
`S`-module is finite projective over `R`. Its `R`-action is `r • s = φ r * s`.
The functor is the full-subcategory lift of `ModuleCat.restrictScalars`, so its
objects retain their carriers and its morphisms retain their functions. The
scalar and carrier universes are independent; restriction leaves the carrier
universe unchanged.

Right modules use this same functor at `φ.op`, with the finite-projectivity
hypothesis on the restricted regular `Sᵐᵒᵖ`-module. On ordinary elements its
coefficient action is `s * φ r`. The left coefficient hypothesis alone does not
supply the right coefficient hypothesis for a noncommutative ring homomorphism.

## References

This construction uses Jujian Zhang's Mathlib change-of-rings formalization,
Mathlib's finite-module transitivity, and its full-subcategory lift and opposite
module interfaces, together with the finite-projective category of this library.
-/

@[expose] public section

universe uR uS uM

open CategoryTheory

namespace ModuleCat

variable {R : Type uR} {S : Type uS}

section RingHom

variable [Ring R] [Ring S] (φ : R →+* S)

/-- Restriction preserves finite projectivity if the canonical restricted
regular scalar module is finite projective. -/
theorem finiteProjective_restrictScalars
    (hC : isFiniteProjective R
      ((ModuleCat.restrictScalars.{uS} φ).obj (ModuleCat.of S S)))
    (M : ModuleCat.{uM} S) (hM : isFiniteProjective S M) :
    isFiniteProjective R ((ModuleCat.restrictScalars φ).obj M) := by
  let : Module R S := Module.compHom S φ
  let : Module R M := Module.compHom M φ
  let : IsScalarTower R S S := SMul.comp.isScalarTower φ
  let : IsScalarTower R S M := SMul.comp.isScalarTower φ
  let : Module.Finite R S := hC.1
  let : Module.Projective R S := hC.2
  let : Module.Finite S M := hM.1
  let : Module.Projective S M := hM.2
  change Module.Finite R M ∧ Module.Projective R M
  exact ⟨Module.Finite.trans S M, Module.Projective.trans (R := R) (S := S) (M := M)⟩

/-- The canonical restricted regular module uses left multiplication by `φ r`. -/
@[simp]
theorem restrictScalars.smul_regular (r : R) (s : S) :
    @SMul.smul R ((ModuleCat.restrictScalars.{uS} φ).obj (ModuleCat.of S S))
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)).isModule.toSMul r s =
    φ r * s := rfl

/-- Restriction along the opposite homomorphism uses right multiplication on
ordinary scalar elements. -/
@[simp]
theorem restrictScalars.unop_smul_op (r : R) (s : S) :
    MulOpposite.unop
      (@SMul.smul Rᵐᵒᵖ
        ((ModuleCat.restrictScalars.{uS} (RingHom.op φ)).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ))
        ((ModuleCat.restrictScalars (RingHom.op φ)).obj
          (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)).isModule.toSMul
        (MulOpposite.op r) (MulOpposite.op s)) = s * φ r := rfl

namespace FiniteProjective

variable (hC : isFiniteProjective R
  ((ModuleCat.restrictScalars.{uS} φ).obj (ModuleCat.of S S)))

/-- Restrict finite projective modules along a ring homomorphism whose
canonical restricted regular scalar module is finite projective. -/
noncomputable def restrictScalars :
    FiniteProjective.{uS, uM} S ⥤ FiniteProjective.{uR, uM} R :=
  (isFiniteProjective R).lift
    ((isFiniteProjective S).ι ⋙ ModuleCat.restrictScalars.{uM} φ)
    (fun M ↦ finiteProjective_restrictScalars φ hC M.obj M.property)

/-- The underlying object is exactly Mathlib's restriction of scalars. -/
@[simp]
theorem restrictScalars_obj (M : FiniteProjective.{uS, uM} S) :
    ((restrictScalars φ hC).obj M).obj =
      (ModuleCat.restrictScalars φ).obj M.obj := rfl

/-- Restriction of scalars leaves the carrier unchanged. -/
@[simp]
theorem restrictScalars_carrier (M : FiniteProjective.{uS, uM} S) :
    ((restrictScalars φ hC).obj M : Type uM) = M := rfl

/-- A restricted morphism has the same underlying function as its source. -/
@[simp]
theorem restrictScalars_map_apply {M N : FiniteProjective.{uS, uM} S}
    (f : M ⟶ N) (x : M) :
    ((restrictScalars φ hC).map f).hom x = f.hom x :=
  ModuleCat.restrictScalars.map_apply φ f.hom x

/-- The destination action is the source action pulled back along `φ`. Both
module structures are specified by their bundled objects. -/
@[simp]
theorem restrictScalars_smul (M : FiniteProjective.{uS, uM} S) (r : R) (x : M) :
    @SMul.smul R ((restrictScalars φ hC).obj M)
      ((restrictScalars φ hC).obj M).obj.isModule.toSMul r
      (show (restrictScalars φ hC).obj M from x) =
    @SMul.smul S M M.obj.isModule.toSMul (φ r) x :=
  ModuleCat.restrictScalars.smul_def' φ (M := M.obj) r x

/-- Forgetting finite projectivity recovers the canonical restriction functor. -/
noncomputable def restrictScalarsCompιIso :
    restrictScalars φ hC ⋙ (isFiniteProjective R).ι ≅
      (isFiniteProjective S).ι ⋙ ModuleCat.restrictScalars.{uM} φ :=
  (isFiniteProjective R).liftCompιIso
    ((isFiniteProjective S).ι ⋙ ModuleCat.restrictScalars.{uM} φ)
    (fun M ↦ finiteProjective_restrictScalars φ hC M.obj M.property)

/-- The forward underlying-functor comparison acts identically on elements. -/
@[simp]
theorem restrictScalarsCompιIso_hom_app_apply
    (M : FiniteProjective.{uS, uM} S) (x : M) :
    ((restrictScalarsCompιIso φ hC).hom.app M).hom x = x := rfl

/-- The inverse underlying-functor comparison acts identically on elements. -/
@[simp]
theorem restrictScalarsCompιIso_inv_app_apply
    (M : FiniteProjective.{uS, uM} S) (x : M) :
    ((restrictScalarsCompιIso φ hC).inv.app M).hom x = x := rfl

end FiniteProjective

end RingHom

section Algebra

variable [CommRing R] [Ring S] [Algebra R S]

/-- Along `algebraMap`, the bundled action is Mathlib's
`Module.restrictScalars`, hence `Module.compHom` along that map. -/
theorem restrictScalars.algebraMap_isModule (M : ModuleCat.{uM} S) :
    ((ModuleCat.restrictScalars (algebraMap R S)).obj M).isModule =
      Module.restrictScalars R S M := rfl

/-- The canonical coefficient condition at `algebraMap` agrees with finite
projectivity for the existing algebra action on the scalar ring. -/
theorem isFiniteProjective_restrictScalars_algebraMap_iff :
    isFiniteProjective R
      ((ModuleCat.restrictScalars.{uS} (algebraMap R S)).obj (ModuleCat.of S S)) ↔
    Module.Finite R S ∧ Module.Projective R S := by
  have hmodule : Module.compHom S (algebraMap R S) = (inferInstance : Module R S) :=
    Module.ext' _ _ (fun r s ↦ (Algebra.smul_def r s).symm)
  change
    (@Module.Finite R S _ _ (Module.compHom S (algebraMap R S)) ∧
      @Module.Projective R _ S _ (Module.compHom S (algebraMap R S))) ↔ _
  rw [hmodule]

end Algebra

end ModuleCat
