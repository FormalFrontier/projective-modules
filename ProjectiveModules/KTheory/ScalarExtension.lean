/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
public import ProjectiveModules.Module.RightExtensionComparison
public import ProjectiveModules.Module.RightExtension

import ProjectiveModules.Module.RightExtensionFree
import ProjectiveModules.Module.RightEndomorphismMatrix
import ProjectiveModules.Module.RightRegular
import Mathlib.Algebra.Field.Opposite
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Scalar extension on finite-projective classes and K₀

A unital homomorphism `φ : R →+* S` of arbitrary rings induces additive maps
`KTheory.ProjectiveClass.map φ` and `KTheory.K0.map φ`. On a finite projective
right `R`-module, they give the class and K₀ generator of its right scalar
extension. Both maps respect identity homomorphisms and composition.

If the source is a division ring, both entire additive maps are independent
of the chosen ring homomorphism, even when the target is merely a ring.
A finite source basis identifies both extensions with the same finite free
target module. This is a statement about module classes and K₀, not equality
of scalar-extension functors.

The class map uses `ProjectiveClass.lift`: scalar extension preserves linear
equivalences, zero modules and binary direct sums. Its finite-generation and
projectivity instances are independent preservation results. The K₀ map is
then the universal group-completion extension of the class map. If scalar
extension is bijective on finite-projective classes, it is bijective on K₀:
group completion preserves isomorphisms of commutative monoids.

The scalar and module carrier universes are independent. The existing
finite-projective representatives normalize classes into the scalar universe;
linear equivalences compare scalar extensions before this normalization.
The rings may be noncommutative or subsingleton, and the ring homomorphisms
need not be injective. Addition is direct sum, not tensor multiplication.
No unconditional injectivity of the induced maps or cancellation of projective
modules is asserted.

## References and credits

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter II, change of rings and the group-completion definition of K₀.
* Mathlib's additive-functor zero preservation, finite-module representatives,
  division-ring bases, finite basis indices, linear-equivalence interfaces and
  additive Grothendieck group.
* Projective Modules' finite-projective representatives, class descent and
  group-completion APIs, and its right scalar extension and pointwise
  identity/composition comparisons, contributed by Prism and Lens.
-/

@[expose] public section

universe uR uS uT uM

open CategoryTheory CategoryTheory.Limits
open ModuleCat (FiniteProjective)

namespace KTheory

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [Ring R] [Ring S] [Ring T]

namespace ProjectiveClass

private noncomputable def mapValue (φ : R →+* S)
    (X : FiniteProjective.{uR, uR} Rᵐᵒᵖ) : ProjectiveClass S :=
  of S ((ModuleCat.RightExtension.functor' φ).obj X.obj)

private theorem mapValue_iso (φ : R →+* S)
    {X Y : FiniteProjective.{uR, uR} Rᵐᵒᵖ} (e : X ≅ Y) :
    mapValue φ X = mapValue φ Y :=
  of_eq_of_equiv S _
    (ModuleCat.RightExtension.mapLinearEquiv φ (FiniteProjective.isoToLinearEquiv e))

private theorem mapValue_zero (φ : R →+* S) :
    mapValue φ (FiniteProjective.of Rᵐᵒᵖ PUnit.{uR + 1}) = 0 := by
  have hzero : IsZero (ModuleCat.of Rᵐᵒᵖ PUnit.{uR + 1}) :=
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  have hsub : Subsingleton ((ModuleCat.RightExtension.functor' φ).obj
      (ModuleCat.of Rᵐᵒᵖ PUnit.{uR + 1})) :=
    ModuleCat.isZero_iff_subsingleton.mp
      ((ModuleCat.RightExtension.functor' φ).map_isZero hzero)
  exact @of_zero S _ _ _ _ hsub

private theorem mapValue_prod (φ : R →+* S)
    (X Y : FiniteProjective.{uR, uR} Rᵐᵒᵖ) :
    mapValue φ (FiniteProjective.of Rᵐᵒᵖ (X × Y)) = mapValue φ X + mapValue φ Y :=
  (of_eq_of_equiv S _
    (ModuleCat.RightExtension.prodLinearEquiv (f := φ) (M := X) (N := Y))).trans
      (of_prod S (ModuleCat.RightExtension.Obj φ X) (ModuleCat.RightExtension.Obj φ Y))

/-- The additive map on finite-projective right-module classes induced by
scalar extension along a unital ring homomorphism. It descends scalar
extension using preservation of isomorphisms, zero and direct sum, as in
Weibel's *The K-book*, Chapter II. -/
@[no_expose]
noncomputable def map (φ : R →+* S) : ProjectiveClass R →+ ProjectiveClass S :=
  lift R (mapValue φ) (mapValue_iso φ) (mapValue_zero φ) (mapValue_prod φ)

/-- Scalar extension evaluates on a finite projective module class in any
carrier universe. The source representative is transported by scalar
extension of its linear equivalence to the original module. -/
@[simp]
theorem map_of (φ : R →+* S) (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    map φ (of R M) = of S (ModuleCat.RightExtension.Obj φ M) := by
  calc
    map φ (of R M) = mapValue φ (FiniteProjective.repr Rᵐᵒᵖ M) :=
      lift_of_module (R := R) (M := M) (f := mapValue φ)
        (hiso := mapValue_iso φ) (hzero := mapValue_zero φ) (hadd := mapValue_prod φ)
    _ = of S (ModuleCat.RightExtension.Obj φ M) :=
      of_eq_of_equiv S _
        (ModuleCat.RightExtension.mapLinearEquiv φ (FiniteProjective.reprEquiv Rᵐᵒᵖ M))

/-- If every finite idempotent matrix lifts along a ring homomorphism, scalar
extension is surjective on finite-projective right-module classes. A finite
projective module is a retract of a finite free module; extending the split
maps compares it with the range of the lifted idempotent. -/
theorem map_surjective_of_lift_idempotents (f : R →+* S)
    (hlift : ∀ (n : ℕ) (E : Matrix (Fin n) (Fin n) S),
      IsIdempotentElem E →
        ∃ A : Matrix (Fin n) (Fin n) R,
          IsIdempotentElem A ∧ (RingHom.mapMatrix f) A = E) :
    Function.Surjective (map f) := by
  classical
  intro y
  obtain ⟨M, rfl⟩ := KTheory.ProjectiveClass.of_surjective S y
  obtain ⟨n, p₀, i₀, _, _, hp₀i₀⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective Sᵐᵒᵖ M
  let coord := Module.rightFreeCoordEquiv S (Fin n)
  let p : (Fin n → S) →ₗ[Sᵐᵒᵖ] M := p₀.comp coord.symm.toLinearMap
  let i : M →ₗ[Sᵐᵒᵖ] (Fin n → S) := coord.toLinearMap.comp i₀
  have hpi : p.comp i = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change p₀ (coord.symm (coord (i₀ x))) = x
    rw [coord.symm_apply_apply]
    exact DFunLike.congr_fun hp₀i₀ x
  let e : Module.End Sᵐᵒᵖ (Fin n → S) := i.comp p
  have he : e.comp e = e := by
    apply LinearMap.ext
    intro x
    change i (p (i (p x))) = i (p x)
    exact congrArg i (DFunLike.congr_fun hpi (p x))
  let ER := Module.rightEndomorphismMatrixEquiv R (Fin n)
  let ES := Module.rightEndomorphismMatrixEquiv S (Fin n)
  let F : Matrix (Fin n) (Fin n) R →+* Matrix (Fin n) (Fin n) S :=
    RingHom.mapMatrix f
  have heMatrix : IsIdempotentElem (ES e) := by
    change ES e * ES e = ES e
    calc
      ES e * ES e = ES (e.comp e) :=
        (Module.rightEndomorphismMatrixEquiv_comp S (Fin n) e e).symm
      _ = ES e := congrArg ES he
  obtain ⟨A, hA, hFA⟩ := hlift n (ES e) heMatrix
  let d : Module.End Rᵐᵒᵖ (Fin n → R) := ER.symm A
  have hERd : ER d = A := ER.apply_symm_apply A
  have hd : d.comp d = d := by
    apply ER.injective
    calc
      ER (d.comp d) = ER d * ER d :=
        Module.rightEndomorphismMatrixEquiv_comp R (Fin n) d d
      _ = A * A := by simp only [hERd]
      _ = A := hA.eq
      _ = ER d := hERd.symm
  have hds : Module.rightEndomorphismScalarExtension R (Fin n) f d = e := by
    apply ES.injective
    calc
      ES (Module.rightEndomorphismScalarExtension R (Fin n) f d) = F (ER d) :=
        (Module.rightEndomorphismMatrixEquiv_scalarExtension R (Fin n) f d).symm
      _ = F A := congrArg F hERd
      _ = ES e := hFA
  let Q := LinearMap.range d
  let j : Q →ₗ[Rᵐᵒᵖ] (Fin n → R) := Q.subtype
  let r : (Fin n → R) →ₗ[Rᵐᵒᵖ] Q := d.rangeRestrict
  have hjr : j.comp r = d := LinearMap.subtype_comp_rangeRestrict d
  have hrj : r.comp j = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    obtain ⟨z, hz⟩ := x.property
    change d x.val = x.val
    calc
      d x.val = d (d z) := congrArg d hz.symm
      _ = d z := DFunLike.congr_fun hd z
      _ = x.val := hz
  letI : Module.Finite Rᵐᵒᵖ Q :=
    Module.Finite.of_surjective r (LinearMap.surjective_rangeRestrict d)
  letI : Module.Projective Rᵐᵒᵖ Q := Module.Projective.of_split j r hrj
  let c := ModuleCat.RightExtension.rightFreeLinearEquiv f (Fin n)
  let J := ModuleCat.RightExtension.map f j
  let B := ModuleCat.RightExtension.map f r
  have hBJ : B.comp J = LinearMap.id := by
    calc
      B.comp J = ModuleCat.RightExtension.map f (r.comp j) :=
        (ModuleCat.RightExtension.map_comp f j r).symm
      _ = ModuleCat.RightExtension.map f LinearMap.id :=
        congrArg (ModuleCat.RightExtension.map f) hrj
      _ = LinearMap.id := ModuleCat.RightExtension.map_id f
  have hJB : J.comp B = ModuleCat.RightExtension.map f d := by
    calc
      J.comp B = ModuleCat.RightExtension.map f (j.comp r) :=
        (ModuleCat.RightExtension.map_comp f r j).symm
      _ = ModuleCat.RightExtension.map f d :=
        congrArg (ModuleCat.RightExtension.map f) hjr
  have hconj :
      c.toLinearMap.comp ((J.comp B).comp c.symm.toLinearMap) = e := by
    rw [hJB]
    exact (Module.rightEndomorphismScalarExtension_eq_tensor R (Fin n) f d).symm.trans hds
  let alpha : ModuleCat.RightExtension.Obj f Q →ₗ[Sᵐᵒᵖ] M :=
    p.comp (c.toLinearMap.comp J)
  let beta : M →ₗ[Sᵐᵒᵖ] ModuleCat.RightExtension.Obj f Q :=
    B.comp (c.symm.toLinearMap.comp i)
  have hab : alpha.comp beta = LinearMap.id := by
    apply LinearMap.ext
    intro x
    have hx : p (i x) = x := DFunLike.congr_fun hpi x
    have hc : c (J (B (c.symm (i x)))) = i (p (i x)) :=
      DFunLike.congr_fun hconj (i x)
    change p (c (J (B (c.symm (i x))))) = x
    exact (congrArg p hc).trans
      ((congrArg (fun z ↦ p (i z)) hx).trans hx)
  have hba : beta.comp alpha = LinearMap.id := by
    apply LinearMap.ext
    intro z
    have hz : B (J z) = z := DFunLike.congr_fun hBJ z
    have hfix : i (p (c (J z))) = c (J z) := by
      have hh := DFunLike.congr_fun hconj (c (J z))
      change c (J (B (c.symm (c (J z))))) = i (p (c (J z))) at hh
      rw [c.symm_apply_apply, hz] at hh
      exact hh.symm
    change B (c.symm (i (p (c (J z))))) = z
    calc
      B (c.symm (i (p (c (J z))))) = B (c.symm (c (J z))) :=
        congrArg (fun w ↦ B (c.symm w)) hfix
      _ = B (J z) := congrArg B (c.symm_apply_apply (J z))
      _ = z := hz
  let equiv : ModuleCat.RightExtension.Obj f Q ≃ₗ[Sᵐᵒᵖ] M :=
    LinearEquiv.ofLinearMap alpha beta hab hba
  refine ⟨KTheory.ProjectiveClass.of R Q, ?_⟩
  exact (KTheory.ProjectiveClass.map_of f Q).trans
    (KTheory.ProjectiveClass.of_eq_of_equiv S _ equiv)

/-- Scalar extension sends the scalar-self regular right-module class to the
scalar-self regular right-module class of the target ring. -/
@[simp]
theorem map_of_self (φ : R →+* S) :
    map φ (of R Rᵐᵒᵖ) = of S Sᵐᵒᵖ := by
  rw [map_of]
  exact of_eq_of_equiv S _
    ((ModuleCat.RightExtension.mapLinearEquiv φ
      ((LinearEquiv.piUnique Rᵐᵒᵖ (fun _ : Fin 1 ↦ Rᵐᵒᵖ)).symm.trans
        (Module.rightFreeCoordEquiv R (Fin 1)))).trans
      ((ModuleCat.RightExtension.rightFreeLinearEquiv φ (Fin 1)).trans
        ((Module.rightFreeCoordEquiv S (Fin 1)).symm.trans
          (LinearEquiv.piUnique Sᵐᵒᵖ (fun _ : Fin 1 ↦ Sᵐᵒᵖ)))))

variable (R) in
/-- Scalar extension along the identity induces the identity additive map
on the entire finite-projective class monoid. -/
theorem map_id : map (RingHom.id R) = AddMonoidHom.id (ProjectiveClass R) := by
  apply addHom_ext R
  intro X
  simpa only [map_of, AddMonoidHom.id_apply] using
    (of_eq_of_equiv R _ (ModuleCat.RightExtension.idLinearEquiv R X))

/-- Scalar extension along a composite induces the composite additive map
on finite-projective classes. The pointwise comparison allows the iterated
and direct extensions to have different carrier universes. -/
theorem map_comp (φ : R →+* S) (ψ : S →+* T) :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  apply addHom_ext R
  intro X
  simp only [AddMonoidHom.comp_apply, map_of]
  exact (of_eq_of_equiv T _ (ModuleCat.RightExtension.compLinearEquiv φ ψ X)).symm

/-- Homomorphisms from a fixed division ring to a fixed ring induce the same
additive map on finite-projective right-module classes. A finite source basis
identifies both scalar extensions with the same target coordinate module. -/
theorem map_eq_map {D : Type uR} [DivisionRing D] (φ ψ : D →+* S) :
    map φ = map ψ := by
  classical
  apply addHom_ext D
  intro X
  let ι := Module.Free.ChooseBasisIndex Dᵐᵒᵖ X
  let : Fintype ι := Module.Free.ChooseBasisIndex.fintype Dᵐᵒᵖ X
  let b : Module.Basis ι Dᵐᵒᵖ X := Module.Free.chooseBasis Dᵐᵒᵖ X
  let e : X ≃ₗ[Dᵐᵒᵖ] (ι → D) :=
    b.equivFun.trans (Module.rightFreeCoordEquiv D ι)
  let eS (χ : D →+* S) : ModuleCat.RightExtension.Obj χ X ≃ₗ[Sᵐᵒᵖ]
      (ι → Sᵐᵒᵖ) :=
    (ModuleCat.RightExtension.mapLinearEquiv χ e).trans
      ((ModuleCat.RightExtension.rightFreeLinearEquiv χ ι).trans
        (Module.rightFreeCoordEquiv S ι).symm)
  simp only [map_of]
  exact of_eq_of_equiv S _ ((eS φ).trans (eS ψ).symm)

end ProjectiveClass

namespace K0

/-- The additive map on K₀ induced by right scalar extension along a unital
ring homomorphism. This is the group-completion extension of the induced
class map, giving the change-of-rings functoriality of Weibel's *The K-book*,
Chapter II. -/
@[no_expose]
noncomputable def map (φ : R →+* S) : K0 R →+ K0 S :=
  lift R ((ofClass S).comp (ProjectiveClass.map φ))

/-- On every class generator, the K₀ scalar-extension map agrees with the
scalar-extension map on finite-projective classes. -/
@[simp]
theorem map_ofClass (φ : R →+* S) (a : ProjectiveClass R) :
    map φ (ofClass R a) = ofClass S (ProjectiveClass.map φ a) :=
  lift_ofClass R ((ofClass S).comp (ProjectiveClass.map φ)) a

/-- Bijectivity of scalar extension on finite-projective right-module classes
implies bijectivity on K₀, for arbitrary rings. Group completion preserves
isomorphisms of commutative monoids. -/
theorem map_bijective_of_projectiveClass_map_bijective (f : R →+* S)
    (hf : Function.Bijective (ProjectiveClass.map f)) :
    Function.Bijective (map f) := by
  let e : ProjectiveClass R ≃+ ProjectiveClass S :=
    AddEquiv.ofBijective (ProjectiveClass.map f) hf
  have he : (⊤ : AddSubmonoid (ProjectiveClass R)).map e.toAddMonoidHom =
      (⊤ : AddSubmonoid (ProjectiveClass S)) := by
    rw [← AddMonoidHom.mrange_eq_map]
    exact AddMonoidHom.mrange_eq_top_of_surjective _ e.surjective
  let E : K0 R ≃+ K0 S :=
    (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass R))).addEquivOfAddEquiv
      (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass S)))
      (j := e) he
  have hE : E.toAddMonoidHom = map f := by
    apply hom_ext_ofClass R
    intro a
    rw [map_ofClass]
    exact AddSubmonoid.LocalizationMap.addEquivOfAddEquiv_eq
      (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass R)))
      (k := AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass S)))
      (j := e) he a
  rw [← hE]
  exact E.bijective

/-- Scalar extension evaluates on a finite projective K₀ generator in any
carrier universe. -/
@[simp]
theorem map_of (φ : R →+* S) (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    map φ (of R M) = of S (ModuleCat.RightExtension.Obj φ M) := by
  simpa only [ProjectiveClass.map_of, ofClass_of] using
    map_ofClass φ (ProjectiveClass.of R M)

/-- Scalar extension sends the scalar-self regular right-module K₀ generator
to the corresponding generator over the target ring. -/
@[simp]
theorem map_of_self (φ : R →+* S) :
    map φ (of R Rᵐᵒᵖ) = of S Sᵐᵒᵖ := by
  simpa only [ProjectiveClass.map_of_self, ofClass_of] using
    map_ofClass φ (ProjectiveClass.of R Rᵐᵒᵖ)

variable (R) in
/-- Scalar extension along the identity induces the identity additive map
on the entire K₀ group. -/
theorem map_id : map (RingHom.id R) = AddMonoidHom.id (K0 R) := by
  apply hom_ext_ofClass R
  intro a
  simp only [map_ofClass, ProjectiveClass.map_id, AddMonoidHom.id_apply]

/-- Scalar extension along a composite induces the composite additive map
on the entire K₀ group. -/
theorem map_comp (φ : R →+* S) (ψ : S →+* T) :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  apply hom_ext_ofClass R
  intro a
  simp only [AddMonoidHom.comp_apply, map_ofClass, ProjectiveClass.map_comp]

/-- The K₀ scalar-extension homomorphism from a fixed division ring to a fixed
ring is independent of the chosen ring homomorphism. -/
theorem map_eq_map {D : Type uR} [DivisionRing D] (φ ψ : D →+* S) :
    map φ = map ψ := by
  apply hom_ext_ofClass D
  intro a
  simp only [map_ofClass, ProjectiveClass.map_eq_map φ ψ]

end K0

end KTheory
