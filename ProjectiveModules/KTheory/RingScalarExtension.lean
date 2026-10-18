/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.ScalarExtension
public import ProjectiveModules.KTheory.TensorProduct

import ProjectiveModules.Module.RightExtensionTensorProduct

/-!
# Scalar extension on the tensor semiring of projective classes

For a unital homomorphism `f : R →+* S` of commutative rings,
`KTheory.ProjectiveClass.mapRingHom f` enriches the additive scalar-extension map
`ProjectiveClass.map f` to a semiring homomorphism. Its whole underlying additive
homomorphism is unchanged. It sends a finite projective right-module class to
the class of its right scalar extension, respects identity and composition, and
allows zero rings and independent scalar and module universes.

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
