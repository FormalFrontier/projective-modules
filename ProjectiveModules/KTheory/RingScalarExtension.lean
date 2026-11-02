/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Ring
public import ProjectiveModules.KTheory.ScalarExtension
public import ProjectiveModules.KTheory.TensorProduct

import ProjectiveModules.Module.RightExtensionTensorProduct

/-!
# Multiplicative scalar extension on projective classes and K₀

For a unital homomorphism `f : R →+* S` of commutative rings,
`KTheory.ProjectiveClass.mapRingHom f` enriches the additive scalar-extension map
`ProjectiveClass.map f` to a semiring homomorphism. Its whole underlying additive
homomorphism is unchanged. It sends a finite projective right-module class to
the class of its right scalar extension, respects identity and composition, and
allows zero rings and independent scalar and module universes.

The induced `KTheory.K0.mapRingHom f` is a ring homomorphism on K₀. Its whole
underlying additive homomorphism is the existing `K0.map f`. It agrees with the
specified right extension on finite projective generators, and its identity and
composition laws are equalities of ring homomorphisms.

Multiplicativity follows by descending the target-opposite-linear tensor
base-change equivalence. The supplied right actions are retained: tensor
products are over `Rᵐᵒᵖ` and `Sᵐᵒᵖ`, and the unit is the class of the regular
right module `Rᵐᵒᵖ`. The arbitrary-ring additive maps on classes and K₀ remain
available without a commutativity hypothesis.

## References and credits

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter II, §2, tensor multiplication and change of rings. The zero-ring case
  extends the standing nonzero-ring convention.
* Projective Modules' finite-projective class, scalar-extension and tensor
  interfaces, including the right-extension comparisons contributed by Prism
  and Lens.
* The Grothendieck-ring universal property `Algebra.GrothendieckAddGroup.liftRingHom`.
* Mathlib's tensor and change-of-rings formalizations, including those of
  Alex J. Best, Yaël Dillies and Jujian Zhang, and its bundled homomorphism API.
-/

@[expose] public section

universe uR uS uT uM

open scoped TensorProduct

namespace KTheory.ProjectiveClass

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [rR : CommRing R] [rS : CommRing S] [rT : CommRing T]

/-- Right scalar extension as a homomorphism of the tensor semirings of finite
projective right-module classes over commutative rings, including zero rings.
Its additive homomorphism is `ProjectiveClass.map f`; tensor base change gives
multiplicativity, as in Weibel's *The K-book*, Chapter II, §2. -/
noncomputable def mapRingHom (f : R →+* S) : ProjectiveClass R →+* ProjectiveClass S where
  __ := @map R S rR.toRing rS.toRing f
  map_one' := by
    change (@map R S rR.toRing rS.toRing f) (1 : ProjectiveClass R) = (1 : ProjectiveClass S)
    rw [one_eq_of, map_of_self, ← one_eq_of]
  map_mul' a b := by
    change (@map R S rR.toRing rS.toRing f) (a * b) =
      (@map R S rR.toRing rS.toRing f) a * (@map R S rR.toRing rS.toRing f) b
    refine induction_on R a fun M ↦ ?_
    refine induction_on R b fun N ↦ ?_
    simpa only [of_mul, map_of] using
      (of_eq_of_equiv S _
        (ModuleCat.RightExtension.tensorBaseChangeEquiv f M.obj N.obj))

/-- The whole underlying additive homomorphism of scalar extension is the
original additive class map, with the additive structures obtained from the
original direct-sum monoid constructors. -/
theorem mapRingHom_toAddMonoidHom (f : R →+* S) :
    ((mapRingHom f).toAddMonoidHom :
      @AddMonoidHom (ProjectiveClass R) (ProjectiveClass S)
        (@KTheory.instAddCommMonoidProjectiveClass R rR.toRing).toAddMonoid.toAddZeroClass.toAddZero
        (@KTheory.instAddCommMonoidProjectiveClass S
          rS.toRing).toAddMonoid.toAddZeroClass.toAddZero) =
      @map R S rR.toRing rS.toRing f := rfl

/-- Evaluation of the scalar-extension semiring homomorphism agrees with the
original additive scalar-extension map. -/
theorem mapRingHom_apply (f : R →+* S) (a : ProjectiveClass R) :
    mapRingHom f a = @map R S rR.toRing rS.toRing f a := rfl

/-- Scalar extension as a semiring homomorphism sends a finite projective
right-module class, in any carrier universe, to its right-extension class. -/
theorem mapRingHom_of (f : R →+* S)
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    mapRingHom f (of R M) = of S (ModuleCat.RightExtension.Obj f M) := by
  rw [mapRingHom_apply, map_of]

variable (R) in
/-- Scalar extension along the identity is the identity on the entire tensor
semiring of finite-projective right-module classes. -/
theorem mapRingHom_id :
    mapRingHom (RingHom.id R) = RingHom.id (ProjectiveClass R) := by
  apply RingHom.ext
  intro a
  simpa only [mapRingHom_apply, RingHom.id_apply, AddMonoidHom.id_apply] using
    congrArg (fun F : ProjectiveClass R →+ ProjectiveClass R ↦ F a) (map_id R)

/-- Scalar extension along a composite is the composite of the scalar-extension
semiring homomorphisms, with independent universes for all three rings. -/
theorem mapRingHom_comp (f : R →+* S) (g : S →+* T) :
    mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom f) := by
  apply RingHom.ext
  intro a
  simpa only [mapRingHom_apply, RingHom.comp_apply, AddMonoidHom.comp_apply] using
    congrArg (fun F : ProjectiveClass R →+ ProjectiveClass T ↦ F a) (map_comp f g)

end KTheory.ProjectiveClass

namespace KTheory.K0

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [rR : CommRing R] [rS : CommRing S] [rT : CommRing T]

/-- Scalar extension on `K₀` as a ring homomorphism.

Its underlying additive homomorphism is the scalar-extension map `K0.map`. -/
noncomputable def mapRingHom (f : R →+* S) : K0 R →+* K0 S :=
  Algebra.GrothendieckAddGroup.liftRingHom
    ((ofClassRingHom S).comp (ProjectiveClass.mapRingHom f))

/-- Scalar extension on a projective class agrees with the canonical map on classes. -/
theorem mapRingHom_ofClass (f : R →+* S) (a : ProjectiveClass R) :
    mapRingHom f (ofClass R a) =
      ofClass S (@ProjectiveClass.map R S rR.toRing rS.toRing f a) := by
  simp only [mapRingHom, Algebra.GrothendieckAddGroup.liftRingHom_apply,
    grothendieckLift_ofClass]
  change ((ofClassRingHom S).comp (ProjectiveClass.mapRingHom f)) a = _
  simp only [RingHom.comp_apply, ofClassRingHom_apply,
    ProjectiveClass.mapRingHom_apply]

/-- The ring homomorphism for scalar extension has exactly the existing additive map
as its underlying additive homomorphism. -/
theorem mapRingHom_toAddMonoidHom (f : R →+* S) :
    (mapRingHom f).toAddMonoidHom = @map R S rR.toRing rS.toRing f := by
  apply hom_ext_ofClass R
  intro a
  exact (mapRingHom_ofClass f a).trans
    (@map_ofClass R S rR.toRing rS.toRing f a).symm

/-- The ring and additive scalar-extension maps agree on every virtual class. -/
@[simp]
theorem mapRingHom_apply (f : R →+* S) (x : K0 R) :
    mapRingHom f x = @map R S rR.toRing rS.toRing f x := by
  exact congrArg (fun h : K0 R →+ K0 S => h x) (mapRingHom_toAddMonoidHom f)

/-- Scalar extension sends a finite projective right module to its extension
of scalars, with its given right-module structure. -/
theorem mapRingHom_of (f : R →+* S)
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    mapRingHom f (of R M) = of S (ModuleCat.RightExtension.Obj f M) := by
  rw [mapRingHom_apply, map_of]

variable (R) in
/-- Scalar extension along the identity is the identity ring homomorphism. -/
@[simp]
theorem mapRingHom_id :
    mapRingHom (RingHom.id R) = RingHom.id (K0 R) := by
  apply RingHom.ext
  intro x
  simp [map_id]

/-- Scalar extension respects composition as an equality of ring homomorphisms. -/
@[simp]
theorem mapRingHom_comp (f : R →+* S) (g : S →+* T) :
    mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom f) := by
  apply RingHom.ext
  intro x
  simp [map_comp]

end KTheory.K0
