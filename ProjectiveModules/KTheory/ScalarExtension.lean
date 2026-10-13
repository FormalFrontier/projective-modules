/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
public import ProjectiveModules.Module.RightExtensionComparison
public import ProjectiveModules.Module.RightExtension

import ProjectiveModules.Module.RightExtensionFree
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
then the universal group-completion extension of the class map.

The scalar and module carrier universes are independent. The existing
finite-projective representatives normalize classes into the scalar universe;
linear equivalences compare scalar extensions before this normalization.
The rings may be noncommutative or subsingleton, and the ring homomorphisms
need not be injective. Addition is direct sum, not tensor multiplication.
No injectivity of the induced maps or cancellation of projective modules is
asserted.

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

/-- Scalar extension evaluates on a finite projective K₀ generator in any
carrier universe. -/
@[simp]
theorem map_of (φ : R →+* S) (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    map φ (of R M) = of S (ModuleCat.RightExtension.Obj φ M) := by
  simpa only [ProjectiveClass.map_of, ofClass_of] using
    map_ofClass φ (ProjectiveClass.of R M)

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
