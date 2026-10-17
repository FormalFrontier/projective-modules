/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.Ring
import ProjectiveModules.KTheory.Rank
import ProjectiveModules.KTheory.ZeroRing
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Ring.PUnit

/-!
# Tensor-induced commutative-ring structure on K₀

The tensor semiring of projective classes induces a commutative-ring structure
on its additive Grothendieck group `KTheory.K0 R`, for every commutative ring
`R`, including the zero ring. The additive group, its stored operations and the
bundled completion map agree with those of the additive construction.

The comparisons fix the direct-sum monoid, additive-completion group and
completion map by their public constants. Thus they compare the additive
structures independently of instance inference after importing the ring
structure. The unit is the class of the regular right module; casts use the
stored natural and integer scaling of this class. Module and additive-target
universes are independent of the scalar universe, and module actions are over
`Rᵐᵒᵖ`.

Integer dimension detects the nonzero unit over the rationals. For the
one-element scalar ring, subsingleton projective-class and K₀ constructions
identify the unit with zero. The zero-module formula holds over every scalar
ring and is distinct from this zero-scalar-ring boundary.

## References and credits

These comparisons use Projective Modules' tensor semiring, K₀, rank and
zero-ring APIs; Mathlib's additive Grothendieck group; and the ring structure
and generator in `GroupTheory.MonoidLocalization.GrothendieckGroup.Ring`.
-/

universe uR uM uG

namespace ProjectiveModulesTests.K0RingInput

open KTheory

variable (R : Type uR) [CommRing R]

/-- The type of commutative-ring structures on the K₀ carrier. -/
private abbrev CommRingStructure := CommRing (K0 R)

/-- The commutative-ring structure induced by tensor products of projective classes. -/
private noncomputable abbrev canonicalRing : CommRingStructure R :=
  inferInstance

/-- The inferred commutative ring is the Grothendieck ring of the tensor semiring. -/
private theorem inferredRing_eq_generic :
    canonicalRing R =
      Algebra.GrothendieckAddGroup.instCommRing (ProjectiveClass R) := rfl

/-- The direct-sum monoid on projective classes. -/
private noncomputable abbrev oldClassMonoid : AddCommMonoid (ProjectiveClass R) :=
  KTheory.instAddCommMonoidProjectiveClass R

/-- The additive-completion group of the direct-sum monoid. -/
private noncomputable abbrev oldCompletionGroup : AddCommGroup (K0 R) :=
  @Algebra.GrothendieckAddGroup.instAddCommGroup
    (ProjectiveClass R) (oldClassMonoid R)

/-- Additive maps from projective classes with the direct-sum and completion structures. -/
private noncomputable abbrev OldClassHom : Type uR :=
  @AddMonoidHom (ProjectiveClass R) (K0 R)
    (oldClassMonoid R).toAddMonoid.toAddZeroClass.toAddZero
    (oldCompletionGroup R).toAddCommMonoid.toAddMonoid.toAddZeroClass.toAddZero

/-- The completion map with the direct-sum and additive-completion structures. -/
private noncomputable abbrev oldOfClass : OldClassHom R :=
  KTheory.K0.ofClass R

/-- The tensor semiring has the direct-sum additive monoid. -/
private theorem classMonoid_preserved :
    (ProjectiveClass.instCommSemiring R).toAddCommMonoid = oldClassMonoid R := rfl

/-- The tensor-induced ring has the additive-completion group. -/
private theorem completionGroup_preserved :
    (canonicalRing R).toAddCommGroup = oldCompletionGroup R := rfl

/-- The inferred additive group agrees with the additive-completion group. -/
private theorem inferredGroup_eq_old :
    (inferInstance : AddCommGroup (K0 R)) = oldCompletionGroup R := rfl

/-- All six stored additive operations agree, as values or whole functions. -/
private theorem additiveOperations_preserved :
    (canonicalRing R).zero = (oldCompletionGroup R).zero ∧
      (canonicalRing R).add = (oldCompletionGroup R).add ∧
      (canonicalRing R).neg = (oldCompletionGroup R).neg ∧
      (canonicalRing R).sub = (oldCompletionGroup R).sub ∧
      (canonicalRing R).nsmul = (oldCompletionGroup R).nsmul ∧
      (canonicalRing R).zsmul = (oldCompletionGroup R).zsmul :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Forgetting commutativity gives the Grothendieck ring structure. -/
private theorem genericRing_projection :
    (canonicalRing R).toRing =
      Algebra.GrothendieckAddGroup.instRing (ProjectiveClass R) := rfl

/-- The ring generator has the same underlying additive map as the completion map. -/
private theorem generator_eq_old :
    ((K0.ofClassRingHom R).toAddMonoidHom :
      OldClassHom R) = oldOfClass R := rfl

/-- Multiplication is the biadditive extension of tensor multiplication. -/
private theorem multiplication_eq_generic :
    (canonicalRing R).mul =
      (fun x y : K0 R ↦ Algebra.GrothendieckAddGroup.mulAddHom x y) := rfl

/-- Bundled multiplication is the biadditive extension of tensor multiplication. -/
private theorem bundledMultiplication_eq_generic :
    (AddMonoidHom.mul : K0 R →+ K0 R →+ K0 R) =
      Algebra.GrothendieckAddGroup.mulAddHom := rfl

/-- The unit is the completion-map image of the regular right-module class. -/
private theorem unit_eq_old_regular :
    (canonicalRing R).one = oldOfClass R (ProjectiveClass.of R Rᵐᵒᵖ) := rfl

/-- Casts use the additive-completion group’s natural and integer scaling of the unit. -/
private theorem casts_eq_old_scaling :
    (canonicalRing R).natCast =
        (fun n ↦ (oldCompletionGroup R).nsmul n
          (oldOfClass R (ProjectiveClass.of R Rᵐᵒᵖ))) ∧
      (canonicalRing R).intCast =
        (fun z ↦ (oldCompletionGroup R).zsmul z
          (oldOfClass R (ProjectiveClass.of R Rᵐᵒᵖ))) :=
  ⟨rfl, rfl⟩

/-- The completion map evaluates on a projective class as the module generator. -/
private theorem oldOfClass_of_module
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    oldOfClass R (ProjectiveClass.of R M) = K0.of R M :=
  K0.ofClass_of R M

/-- Generator compatibility keeps independent module and additive-target universes. -/
private theorem generator_module_to_target
    (G : Type uG) [AddCommGroup G] (f : K0 R →+ G)
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    f (K0.ofClassRingHom R (ProjectiveClass.of R M)) = f (K0.of R M) := by
  rw [K0.ofClassRingHom_of]

/-- A zero module gives zero over every scalar ring, not only a zero scalar ring. -/
private theorem zeroModule_generator
    (Z : Type uM) [AddCommGroup Z] [Module Rᵐᵒᵖ Z] [Subsingleton Z] :
    K0.ofClassRingHom R (ProjectiveClass.of R Z) = (0 : K0 R) := by
  rw [K0.ofClassRingHom_of, K0.of_zero]

/-- Integer dimension sends the rational ring’s unit to one. -/
private theorem rational_unit_dimension :
    K0.finrankHom ℚ (1 : K0 ℚ) = (1 : ℤ) := by
  rw [K0.one_eq_of]
  exact K0.finrankHom_of_self ℚ

/-- Integer dimension sends the rational ring’s zero to zero. -/
private theorem rational_zero_dimension :
    K0.finrankHom ℚ (0 : K0 ℚ) = 0 :=
  (K0.finrankHom ℚ).map_zero

/-- The tensor-induced ring on K₀ of the rationals has nonzero unit. -/
private theorem rational_unit_ne_zero :
    (1 : K0 ℚ) ≠ 0 := by
  intro h
  have hdim : (1 : ℤ) = 0 :=
    rational_unit_dimension.symm.trans
      ((congrArg (K0.finrankHom ℚ) h).trans rational_zero_dimension)
  exact one_ne_zero hdim

/-- The tensor square of the rational regular right module represents the ring unit. -/
private theorem rational_regular_tensor :
    K0.of ℚ (TensorProduct ℚᵐᵒᵖ ℚᵐᵒᵖ ℚᵐᵒᵖ) = (1 : K0 ℚ) := by
  simpa only [K0.of_self, one_mul] using
    (K0.of_mul ℚ ℚᵐᵒᵖ ℚᵐᵒᵖ).symm

/-- Over the one-element scalar ring, the tensor-induced ring’s unit is zero. -/
private theorem punit_unit_eq_zero :
    (1 : K0 PUnit.{uR + 1}) = 0 :=
  Subsingleton.elim _ _

end ProjectiveModulesTests.K0RingInput
