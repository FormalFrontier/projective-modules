/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.Product
import ProjectiveModules.KTheory.ProductRing
import ProjectiveModules.KTheory.Rank
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Ring.ULift
import Mathlib.Algebra.Field.ULift
import Mathlib.Tactic.NormNum

/-!
# Finite-coordinate clients of product decompositions of classes and K₀

Canonical finite-projective coordinate modules over the rationals assemble into
modules over a three-factor ring. The inverse class and K₀ equivalences recover
these module generators, and the factor dimension maps observe ranks `(1, 2, 3)`.
Subtracting the family of ranks `(4, 2, 1)` gives the signed K₀ tuple `(-3, 0, 2)`.
The completion formulas compute the same generators without assuming that the
class-to-K₀ map is injective.

The binary examples use independently lifted rational scalar rings and module
carriers. Their canonical finite-projective products have factor ranks `(1, 3)`
and `(4, 1)`, so their difference has signed dimensions `(-3, 2)`. A further
carrier lift tests the module-generator formulas on the scalar extensions
themselves. The empty-family inverse is the zero class or zero K₀ element.

## References and credits

These examples use Mathlib's finite coordinate modules, opposite rings, carrier
lifts, additive equivalences and module dimension formulas, together with
Projective Modules' finite-projective coefficient products, right scalar
extension, projective-class, group-completion and division-ring dimension APIs.
-/

@[expose] public section

noncomputable section

open KTheory ModuleCat

namespace ProjectiveModulesTests.K0ProductEquivalenceClient

namespace RationalTriple

private abbrev rings := fun _ : Fin 3 => ℚ
private abbrev A := Fin 3 → ℚ

private def coordinates (n : ℕ) : FiniteProjective ℚᵐᵒᵖ :=
  FiniteProjective.of ℚᵐᵒᵖ (Fin n → ℚᵐᵒᵖ)

private def negativeSize (i : Fin 3) : ℕ :=
  if i = 0 then 4 else if i = 1 then 2 else 1

private def positive (i : Fin 3) : FiniteProjective ℚᵐᵒᵖ :=
  coordinates (i.val + 1)

private def negative (i : Fin 3) : FiniteProjective ℚᵐᵒᵖ :=
  coordinates (negativeSize i)

private def P : FiniteProjective Aᵐᵒᵖ := FiniteProjective.pi rings positive
private def N : FiniteProjective Aᵐᵒᵖ := FiniteProjective.pi rings negative
private abbrev cP := ProjectiveClass.of A P
private abbrev cN := ProjectiveClass.of A N
private abbrev kP := K0.of A P
private abbrev kN := K0.of A N
private abbrev positiveClasses := fun i => ProjectiveClass.of ℚ (positive i)
private abbrev negativeClasses := fun i => ProjectiveClass.of ℚ (negative i)

/-- The three-factor comparison sends the tensor unit to the coordinate units. -/
private theorem unit_coordinates :
    K0.piMap rings (1 : K0 A) = 1 :=
  K0.piMap_one rings

/-- Multiplication of the two product module classes is coordinatewise. -/
private theorem multiplication_coordinates :
    K0.piMap rings (kP * kN) = K0.piMap rings kP * K0.piMap rings kN :=
  K0.piMap_mul rings kP kN

/-- The regular opposite-ring module maps to the regular factor modules. -/
private theorem regular_coordinates :
    K0.piMap rings (K0.of A Aᵐᵒᵖ) =
      fun _ : Fin 3 => K0.of ℚ ℚᵐᵒᵖ :=
  K0.piMap_of_regular rings

/-- Finite coordinate modules supply the prescribed natural and integer dimensions. -/
private theorem coordinate_dimensions (n : ℕ) :
    ProjectiveClass.finrankHom ℚ (ProjectiveClass.of ℚ (coordinates n)) = n ∧
      K0.finrankEquiv ℚ (K0.of ℚ (coordinates n)) = (n : ℤ) := by
  constructor
  · rw [ProjectiveClass.finrankHom_of_module]
    exact Module.finrank_fin_fun ℚᵐᵒᵖ
  · rw [K0.finrankEquiv_of_module]
    exact congrArg (fun d : ℕ => (d : ℤ))
      (show Module.finrank ℚᵐᵒᵖ (coordinates n) = n from Module.finrank_fin_fun ℚᵐᵒᵖ)

/-- Both rational families reassemble to their canonical coefficient-product classes. -/
private theorem class_inverse :
    (ProjectiveClass.piEquiv rings).symm positiveClasses = cP ∧
      (ProjectiveClass.piEquiv rings).symm negativeClasses = cN := by
  exact ⟨ProjectiveClass.piEquiv_symm_of_module rings positive,
    ProjectiveClass.piEquiv_symm_of_module rings negative⟩

private theorem class_decomposition :
    ProjectiveClass.piEquiv rings cP = positiveClasses ∧
      ProjectiveClass.piEquiv rings cN = negativeClasses := by
  constructor
  · rw [← class_inverse.1]
    exact (ProjectiveClass.piEquiv rings).apply_symm_apply positiveClasses
  · rw [← class_inverse.2]
    exact (ProjectiveClass.piEquiv rings).apply_symm_apply negativeClasses

/-- The assembled positive class has three nonzero coordinate dimensions. -/
private theorem class_dimensions (i : Fin 3) :
    ProjectiveClass.finrankHom ℚ (ProjectiveClass.piEquiv rings cP i) = i.val + 1 := by
  rw [class_decomposition.1]
  exact (coordinate_dimensions (i.val + 1)).1

/-- The whole forward homomorphism observes the same dimensions by scalar extension. -/
private theorem class_projection_dimensions (i : Fin 3) :
    ProjectiveClass.finrankHom ℚ
      (ProjectiveClass.map (Pi.evalRingHom rings i) cP) = i.val + 1 := by
  have forward := DFunLike.congr_fun
    (ProjectiveClass.piEquiv_toAddMonoidHom rings) cP
  exact (congrArg (ProjectiveClass.finrankHom ℚ) (congrFun forward i)).symm.trans
    (class_dimensions i)

/-- The inverse K₀ equivalence also returns the canonical product module generators. -/
private theorem group_inverse :
    (K0.piEquiv rings).symm (fun i => K0.of ℚ (positive i)) = kP ∧
      (K0.piEquiv rings).symm (fun i => K0.of ℚ (negative i)) = kN := by
  exact ⟨K0.piEquiv_symm_of_module rings positive,
    K0.piEquiv_symm_of_module rings negative⟩

private theorem group_decomposition :
    K0.piEquiv rings kP = (fun i => K0.of ℚ (positive i)) ∧
      K0.piEquiv rings kN = (fun i => K0.of ℚ (negative i)) := by
  constructor
  · rw [← group_inverse.1]
    exact (K0.piEquiv rings).apply_symm_apply _
  · rw [← group_inverse.2]
    exact (K0.piEquiv rings).apply_symm_apply _

/-- Module-generator formulas compute dimensions of the coordinate extensions themselves. -/
private theorem extension_dimensions (i : Fin 3) :
    ProjectiveClass.finrankHom ℚ
        (ProjectiveClass.of ℚ (RightExtension.Obj (Pi.evalRingHom rings i) P)) =
      i.val + 1 ∧
      K0.finrankEquiv ℚ
        (K0.of ℚ (RightExtension.Obj (Pi.evalRingHom rings i) P)) =
      ((i.val + 1 : ℕ) : ℤ) := by
  constructor
  · exact (congrArg (ProjectiveClass.finrankHom ℚ)
      (ProjectiveClass.piEquiv_of_module rings P i)).symm.trans (class_dimensions i)
  · have dimension : K0.finrankEquiv ℚ (K0.piEquiv rings kP i) =
        ((i.val + 1 : ℕ) : ℤ) := by
      rw [group_decomposition.1]
      exact (coordinate_dimensions (i.val + 1)).2
    exact (congrArg (K0.finrankEquiv ℚ)
      (K0.piEquiv_of_module rings P i)).symm.trans dimension

/-- Completion before or after reassembly gives the same positive generator. -/
private theorem completion_inverse :
    (K0.piEquiv rings).symm (fun i => K0.ofClass ℚ (positiveClasses i)) = kP := by
  rw [K0.piEquiv_symm_ofClass, class_inverse.1, K0.ofClass_of]

private theorem completion_dimensions (i : Fin 3) :
    K0.finrankEquiv ℚ (K0.piEquiv rings (K0.ofClass A cP) i) =
      ((i.val + 1 : ℕ) : ℤ) := by
  rw [K0.piEquiv_ofClass, class_decomposition.1, K0.ofClass_of]
  exact (coordinate_dimensions (i.val + 1)).2

/-- The signed inverse is a difference of the two concrete product generators. -/
private theorem signed_inverse :
    (K0.piEquiv rings).symm
        (fun i => K0.of ℚ (positive i) - K0.of ℚ (negative i)) = kP - kN := by
  simpa only [class_inverse.1, class_inverse.2, K0.ofClass_of] using
    K0.piEquiv_symm_sub_ofClass rings positiveClasses negativeClasses

private theorem signed_dimensions (i : Fin 3) :
    K0.finrankEquiv ℚ (K0.piEquiv rings (kP - kN) i) =
      ((i.val + 1 : ℕ) : ℤ) - (negativeSize i : ℤ) := by
  have image : K0.piEquiv rings (kP - kN) i =
      K0.of ℚ (positive i) - K0.of ℚ (negative i) := by
    rw [map_sub, Pi.sub_apply, group_decomposition.1, group_decomposition.2]
  rw [image, map_sub]
  simp only [positive, negative]
  rw [(coordinate_dimensions (i.val + 1)).2, (coordinate_dimensions (negativeSize i)).2]

/-- Subtraction gives a negative, a zero and a positive coordinate in one K₀ element. -/
private theorem signed_example :
    (K0.finrankEquiv ℚ (K0.piEquiv rings (kP - kN) 0),
      K0.finrankEquiv ℚ (K0.piEquiv rings (kP - kN) 1),
      K0.finrankEquiv ℚ (K0.piEquiv rings (kP - kN) 2)) = (-3, 0, 2) := by
  simp only [signed_dimensions]
  norm_num [negativeSize]

/-- The canonical forward K₀ maps recover the signed factor dimensions. -/
private theorem signed_projection_dimensions (i : Fin 3) :
    K0.finrankHom ℚ (K0.map (Pi.evalRingHom rings i) (kP - kN)) =
      ((i.val + 1 : ℕ) : ℤ) - (negativeSize i : ℤ) := by
  have forward := DFunLike.congr_fun (K0.piEquiv_toAddMonoidHom rings) (kP - kN)
  rw [← K0.finrankEquiv_apply]
  exact (congrArg (K0.finrankEquiv ℚ) (congrFun forward i)).symm.trans
    (signed_dimensions i)

private theorem nonzero_class_and_signed_element : cP ≠ 0 ∧ kP - kN ≠ 0 := by
  have positiveDimension :
      ProjectiveClass.finrankHom ℚ (ProjectiveClass.piEquiv rings cP 0) = 1 :=
    class_dimensions 0
  have signedDimension : K0.finrankEquiv ℚ (K0.piEquiv rings (kP - kN) 0) = -3 :=
    congrArg Prod.fst signed_example
  constructor
  · intro equality
    have observation := congrArg
      (fun a => ProjectiveClass.finrankHom ℚ (ProjectiveClass.piEquiv rings a 0)) equality
    have impossible : (1 : ℕ) = 0 := by
      simpa only [positiveDimension, map_zero, Pi.zero_apply] using observation
    exact one_ne_zero impossible
  · intro equality
    have observation := congrArg
      (fun z => K0.finrankEquiv ℚ (K0.piEquiv rings z 0)) equality
    have impossible : (-3 : ℤ) = 0 := by
      simpa only [signedDimension, map_zero, Pi.zero_apply] using observation
    exact (by decide : (-3 : ℤ) ≠ 0) impossible

end RationalTriple

namespace LiftedBinary

private abbrev R : Type 1 := ULift.{1} ℚ
private abbrev S : Type 2 := ULift.{2} ℚ
private abbrev A := R × S

private def LP : FiniteProjective.{1, 3} Rᵐᵒᵖ :=
  FiniteProjective.of Rᵐᵒᵖ (ULift.{3} Rᵐᵒᵖ)

private def RP : FiniteProjective.{2, 4} Sᵐᵒᵖ :=
  FiniteProjective.of Sᵐᵒᵖ (ULift.{4} (Fin 3 → Sᵐᵒᵖ))

private def LN : FiniteProjective.{1, 3} Rᵐᵒᵖ :=
  FiniteProjective.of Rᵐᵒᵖ (ULift.{3} (Fin 4 → Rᵐᵒᵖ))

private def RN : FiniteProjective.{2, 4} Sᵐᵒᵖ :=
  FiniteProjective.of Sᵐᵒᵖ (ULift.{4} Sᵐᵒᵖ)

private def P : FiniteProjective.{2, 4} Aᵐᵒᵖ := FiniteProjective.prodRight R S LP RP
private def N : FiniteProjective.{2, 4} Aᵐᵒᵖ := FiniteProjective.prodRight R S LN RN
private abbrev cP := ProjectiveClass.of A P
private abbrev cN := ProjectiveClass.of A N
private abbrev kP := K0.of A P
private abbrev kN := K0.of A N

/-- Independently sized scalar and carrier inputs reassemble to the product classes. -/
private theorem class_inverse :
    (ProjectiveClass.prodEquiv R S).symm
        (ProjectiveClass.of R LP, ProjectiveClass.of S RP) = cP ∧
      (ProjectiveClass.prodEquiv R S).symm
        (ProjectiveClass.of R LN, ProjectiveClass.of S RN) = cN := by
  exact ⟨ProjectiveClass.prodEquiv_symm_of_module R S LP RP,
    ProjectiveClass.prodEquiv_symm_of_module R S LN RN⟩

private theorem class_decomposition :
    ProjectiveClass.prodEquiv R S cP =
        (ProjectiveClass.of R LP, ProjectiveClass.of S RP) ∧
      ProjectiveClass.prodEquiv R S cN =
        (ProjectiveClass.of R LN, ProjectiveClass.of S RN) := by
  constructor
  · rw [← class_inverse.1]
    exact (ProjectiveClass.prodEquiv R S).apply_symm_apply _
  · rw [← class_inverse.2]
    exact (ProjectiveClass.prodEquiv R S).apply_symm_apply _

/-- Factor dimensions distinguish the two nonzero canonical product classes. -/
private theorem class_dimensions :
    (ProjectiveClass.finrankHom R (ProjectiveClass.prodEquiv R S cP).1,
        ProjectiveClass.finrankEquiv S (ProjectiveClass.prodEquiv R S cP).2) = (1, 3) ∧
      (ProjectiveClass.finrankHom R (ProjectiveClass.prodEquiv R S cN).1,
        ProjectiveClass.finrankEquiv S (ProjectiveClass.prodEquiv R S cN).2) = (4, 1) := by
  have positiveClass : ProjectiveClass.of R LP = ProjectiveClass.of R Rᵐᵒᵖ :=
    @ProjectiveClass.of_eq_of_equiv.{1, 3, 1} R _ (LP : Type 3)
      LP.obj.isAddCommGroup LP.obj.isModule LP.property.1 LP.property.2
      Rᵐᵒᵖ _ _ _ _ (ULift.moduleEquiv : LP ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ)
  have negativeClass : ProjectiveClass.of R LN =
      ProjectiveClass.of R (Fin 4 → Rᵐᵒᵖ) :=
    @ProjectiveClass.of_eq_of_equiv.{1, 3, 1} R _ (LN : Type 3)
      LN.obj.isAddCommGroup LN.obj.isModule LN.property.1 LN.property.2
      (Fin 4 → Rᵐᵒᵖ) _ _ _ _
      (ULift.moduleEquiv : LN ≃ₗ[Rᵐᵒᵖ] (Fin 4 → Rᵐᵒᵖ))
  have positiveSClass : ProjectiveClass.of S RP =
      ProjectiveClass.of S (Fin 3 → Sᵐᵒᵖ) :=
    @ProjectiveClass.of_eq_of_equiv.{2, 4, 2} S _ (RP : Type 4)
      RP.obj.isAddCommGroup RP.obj.isModule RP.property.1 RP.property.2
      (Fin 3 → Sᵐᵒᵖ) _ _ _ _
      (ULift.moduleEquiv : RP ≃ₗ[Sᵐᵒᵖ] (Fin 3 → Sᵐᵒᵖ))
  have negativeSClass : ProjectiveClass.of S RN = ProjectiveClass.of S Sᵐᵒᵖ :=
    @ProjectiveClass.of_eq_of_equiv.{2, 4, 2} S _ (RN : Type 4)
      RN.obj.isAddCommGroup RN.obj.isModule RN.property.1 RN.property.2
      Sᵐᵒᵖ _ _ _ _ (ULift.moduleEquiv : RN ≃ₗ[Sᵐᵒᵖ] Sᵐᵒᵖ)
  constructor
  · rw [class_decomposition.1, positiveClass, positiveSClass,
      ProjectiveClass.finrankHom_of_self, ProjectiveClass.finrankEquiv_of_module,
      Module.finrank_fin_fun]
  · rw [class_decomposition.2, negativeClass, negativeSClass,
      ProjectiveClass.finrankHom_of_module, Module.finrank_fin_fun,
      ProjectiveClass.finrankEquiv_of_self]

private theorem class_projection_dimensions :
    (ProjectiveClass.finrankHom R (ProjectiveClass.map (RingHom.fst R S) cP),
      ProjectiveClass.finrankEquiv S (ProjectiveClass.map (RingHom.snd R S) cP)) =
      (1, 3) := by
  have forward := DFunLike.congr_fun (ProjectiveClass.prodEquiv_toAddMonoidHom R S) cP
  exact (congrArg (fun p : ProjectiveClass R × ProjectiveClass S =>
    (ProjectiveClass.finrankHom R p.1, ProjectiveClass.finrankEquiv S p.2))
      forward).symm.trans class_dimensions.1

/-- Both K₀ inverse module formulas accept the separately lifted factor carriers. -/
private theorem group_inverse :
    (K0.prodEquiv R S).symm (K0.of R LP, K0.of S RP) = kP ∧
      (K0.prodEquiv R S).symm (K0.of R LN, K0.of S RN) = kN := by
  exact ⟨K0.prodEquiv_symm_of_module R S LP RP,
    K0.prodEquiv_symm_of_module R S LN RN⟩

private theorem group_decomposition :
    K0.prodEquiv R S kP = (K0.of R LP, K0.of S RP) ∧
      K0.prodEquiv R S kN = (K0.of R LN, K0.of S RN) := by
  constructor
  · rw [← group_inverse.1]
    exact (K0.prodEquiv R S).apply_symm_apply _
  · rw [← group_inverse.2]
    exact (K0.prodEquiv R S).apply_symm_apply _

private theorem group_dimensions :
    (K0.finrankHom R (K0.prodEquiv R S kP).1,
        K0.finrankEquiv S (K0.prodEquiv R S kP).2) = (1, 3) ∧
      (K0.finrankHom R (K0.prodEquiv R S kN).1,
        K0.finrankEquiv S (K0.prodEquiv R S kN).2) = (4, 1) := by
  have positiveGenerator : K0.of R LP = K0.of R Rᵐᵒᵖ :=
    @K0.of_eq_of_equiv.{1, 3, 1} R _ (LP : Type 3)
      LP.obj.isAddCommGroup LP.obj.isModule LP.property.1 LP.property.2
      Rᵐᵒᵖ _ _ _ _ (ULift.moduleEquiv : LP ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ)
  have negativeGenerator : K0.of R LN = K0.of R (Fin 4 → Rᵐᵒᵖ) :=
    @K0.of_eq_of_equiv.{1, 3, 1} R _ (LN : Type 3)
      LN.obj.isAddCommGroup LN.obj.isModule LN.property.1 LN.property.2
      (Fin 4 → Rᵐᵒᵖ) _ _ _ _
      (ULift.moduleEquiv : LN ≃ₗ[Rᵐᵒᵖ] (Fin 4 → Rᵐᵒᵖ))
  have positiveSGenerator : K0.of S RP = K0.of S (Fin 3 → Sᵐᵒᵖ) :=
    @K0.of_eq_of_equiv.{2, 4, 2} S _ (RP : Type 4)
      RP.obj.isAddCommGroup RP.obj.isModule RP.property.1 RP.property.2
      (Fin 3 → Sᵐᵒᵖ) _ _ _ _
      (ULift.moduleEquiv : RP ≃ₗ[Sᵐᵒᵖ] (Fin 3 → Sᵐᵒᵖ))
  have negativeSGenerator : K0.of S RN = K0.of S Sᵐᵒᵖ :=
    @K0.of_eq_of_equiv.{2, 4, 2} S _ (RN : Type 4)
      RN.obj.isAddCommGroup RN.obj.isModule RN.property.1 RN.property.2
      Sᵐᵒᵖ _ _ _ _ (ULift.moduleEquiv : RN ≃ₗ[Sᵐᵒᵖ] Sᵐᵒᵖ)
  constructor
  · rw [group_decomposition.1, positiveGenerator, positiveSGenerator,
      K0.finrankHom_of_self, K0.finrankEquiv_of_module, Module.finrank_fin_fun]
    norm_num
  · rw [group_decomposition.2, negativeGenerator, negativeSGenerator,
      K0.finrankHom_of_module, Module.finrank_fin_fun, K0.finrankEquiv_of_self]
    norm_num

/-- A further source carrier lift retains the dimensions of both projection extensions. -/
private theorem lifted_extension_class_dimensions :
    (ProjectiveClass.finrankHom R
        (ProjectiveClass.of R (RightExtension.Obj (RingHom.fst R S) (ULift.{5} P))),
      ProjectiveClass.finrankEquiv S
        (ProjectiveClass.of S (RightExtension.Obj (RingHom.snd R S) (ULift.{5} P)))) =
      (1, 3) := by
  have observation := congrArg (fun p : ProjectiveClass R × ProjectiveClass S =>
    (ProjectiveClass.finrankHom R p.1, ProjectiveClass.finrankEquiv S p.2))
      (ProjectiveClass.prodEquiv_of_module R S (ULift.{5} P))
  have source :
      (ProjectiveClass.finrankHom R
          (ProjectiveClass.prodEquiv R S (ProjectiveClass.of A (ULift.{5} P))).1,
        ProjectiveClass.finrankEquiv S
          (ProjectiveClass.prodEquiv R S (ProjectiveClass.of A (ULift.{5} P))).2) =
        (1, 3) := by
    simpa only [ProjectiveClass.of_ulift] using class_dimensions.1
  exact observation.symm.trans source

private theorem lifted_extension_group_dimensions :
    (K0.finrankHom R
        (K0.of R (RightExtension.Obj (RingHom.fst R S) (ULift.{5} P))),
      K0.finrankEquiv S
        (K0.of S (RightExtension.Obj (RingHom.snd R S) (ULift.{5} P)))) = (1, 3) := by
  have observation := congrArg (fun p : K0 R × K0 S =>
    (K0.finrankHom R p.1, K0.finrankEquiv S p.2))
      (K0.prodEquiv_of_module R S (ULift.{5} P))
  have source :
      (K0.finrankHom R (K0.prodEquiv R S (K0.of A (ULift.{5} P))).1,
        K0.finrankEquiv S (K0.prodEquiv R S (K0.of A (ULift.{5} P))).2) = (1, 3) := by
    simpa only [K0.of_ulift] using group_dimensions.1
  exact observation.symm.trans source

/-- Completion and the binary inverse recover the same canonical product generator. -/
private theorem completion_inverse :
    (K0.prodEquiv R S).symm
        (K0.ofClass R (ProjectiveClass.of R LP), K0.ofClass S (ProjectiveClass.of S RP)) =
      kP := by
  rw [K0.prodEquiv_symm_ofClass, class_inverse.1, K0.ofClass_of]

private theorem completion_decomposition :
    K0.prodEquiv R S (K0.ofClass A cP) = (K0.of R LP, K0.of S RP) := by
  rw [K0.prodEquiv_ofClass, class_decomposition.1]
  rfl

/-- The signed inverse uses differences of classes, not cancellation of those classes. -/
private theorem signed_inverse :
    (K0.prodEquiv R S).symm (K0.of R LP - K0.of R LN, K0.of S RP - K0.of S RN) =
      kP - kN := by
  simpa only [class_inverse.1, class_inverse.2, K0.ofClass_of] using
    K0.prodEquiv_symm_sub_ofClass R S
      (ProjectiveClass.of R LP) (ProjectiveClass.of R LN)
      (ProjectiveClass.of S RP) (ProjectiveClass.of S RN)

/-- The binary K₀ equivalence observes both signs in the difference of product modules. -/
private theorem signed_dimensions :
    (K0.finrankHom R (K0.prodEquiv R S (kP - kN)).1,
      K0.finrankEquiv S (K0.prodEquiv R S (kP - kN)).2) = (-3, 2) := by
  have positiveLeft : K0.finrankHom R (K0.prodEquiv R S kP).1 = (1 : ℤ) :=
    congrArg Prod.fst group_dimensions.1
  have positiveRight : K0.finrankEquiv S (K0.prodEquiv R S kP).2 = (3 : ℤ) :=
    congrArg Prod.snd group_dimensions.1
  have negativeLeft : K0.finrankHom R (K0.prodEquiv R S kN).1 = (4 : ℤ) :=
    congrArg Prod.fst group_dimensions.2
  have negativeRight : K0.finrankEquiv S (K0.prodEquiv R S kN).2 = (1 : ℤ) :=
    congrArg Prod.snd group_dimensions.2
  calc
    _ = ((1 : ℤ) - 4, (3 : ℤ) - 1) := by
      simp only [map_sub, Prod.fst_sub, Prod.snd_sub,
        positiveLeft, positiveRight, negativeLeft, negativeRight]
    _ = (-3, 2) := by norm_num

private theorem signed_projection_dimensions :
    (K0.finrankHom R (K0.map (RingHom.fst R S) (kP - kN)),
      K0.finrankEquiv S (K0.map (RingHom.snd R S) (kP - kN))) = (-3, 2) := by
  have forward := DFunLike.congr_fun (K0.prodEquiv_toAddMonoidHom R S) (kP - kN)
  exact (congrArg (fun p : K0 R × K0 S =>
    (K0.finrankHom R p.1, K0.finrankEquiv S p.2)) forward).symm.trans signed_dimensions

private theorem nonzero_and_distinct : cP ≠ 0 ∧ cP ≠ cN ∧ kP - kN ≠ 0 := by
  have positiveDimension :
      ProjectiveClass.finrankHom R (ProjectiveClass.prodEquiv R S cP).1 = 1 :=
    congrArg Prod.fst class_dimensions.1
  have negativeDimension :
      ProjectiveClass.finrankHom R (ProjectiveClass.prodEquiv R S cN).1 = 4 :=
    congrArg Prod.fst class_dimensions.2
  have signedDimension : K0.finrankHom R (K0.prodEquiv R S (kP - kN)).1 = -3 :=
    congrArg Prod.fst signed_dimensions
  refine ⟨?_, ?_, ?_⟩
  · intro equality
    have observation := congrArg
      (fun a => ProjectiveClass.finrankHom R (ProjectiveClass.prodEquiv R S a).1) equality
    have impossible : (1 : ℕ) = 0 := by
      simpa only [positiveDimension, map_zero, Prod.fst_zero] using observation
    exact one_ne_zero impossible
  · intro equality
    have observation := congrArg
      (fun a => ProjectiveClass.finrankHom R (ProjectiveClass.prodEquiv R S a).1) equality
    have impossible : (1 : ℕ) = 4 := by
      simpa only [positiveDimension, negativeDimension] using observation
    exact (by decide : (1 : ℕ) ≠ 4) impossible
  · intro equality
    have observation := congrArg
      (fun z => K0.finrankHom R (K0.prodEquiv R S z).1) equality
    have impossible : (-3 : ℤ) = 0 := by
      simpa only [signedDimension, map_zero, Prod.fst_zero] using observation
    exact (by decide : (-3 : ℤ) ≠ 0) impossible

end LiftedBinary

/-- An empty coordinate family reassembles to zero, even with a regular generator as its body. -/
private theorem empty_family_inverse :
    (ProjectiveClass.piEquiv (fun _ : Fin 0 => ℚ)).symm
        (fun _ => ProjectiveClass.of ℚ ℚᵐᵒᵖ) = 0 ∧
      (K0.piEquiv (fun _ : Fin 0 => ℚ)).symm (fun _ => K0.of ℚ ℚᵐᵒᵖ) = 0 := by
  have classes : (fun _ : Fin 0 => ProjectiveClass.of ℚ ℚᵐᵒᵖ) = 0 := by
    funext i
    exact Fin.elim0 i
  have generators : (fun _ : Fin 0 => K0.of ℚ ℚᵐᵒᵖ) = 0 := by
    funext i
    exact Fin.elim0 i
  constructor
  · rw [classes, map_zero]
  · rw [generators, map_zero]

end ProjectiveModulesTests.K0ProductEquivalenceClient
