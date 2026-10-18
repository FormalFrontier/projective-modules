/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.RingScalarExtension
import ProjectiveModules.KTheory.Rank
import ProjectiveModules.KTheory.ZeroRing
import ProjectiveModules.Module.RightRegular
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Rat

/-!
# Integer, rational and zero-ring scalar extension on projective classes

The additive dimension map detects the nonzero rational regular class
without a scalar-extension semiring homomorphism. Extension along
`Int.castRingHom ℚ` retains this regular-class image and its integer dimension
in the additive Grothendieck completion. It also computes dimension two on an
extended, universe-lifted two-coordinate integer module. The semiring
homomorphism transports tensor multiplication of natural-number classes.
Extension from the rationals to the one-element ring sends the nonzero regular
class to the target unit, which is zero, and annihilates the ordinary rational
right-regular carrier as well.

These clients reuse the class, dimension, right-regular and zero-ring APIs of
Projective Modules and Mathlib's integer cast and one-element algebra.
-/

public section

universe uR uS uM

open KTheory

namespace ProjectiveModulesTests.ProjectiveClassRingScalarExtensionClient

-- This witness uses only the additive dimension invariant and the old module class.
private theorem rational_regular_ne_zero : ProjectiveClass.of ℚ ℚᵐᵒᵖ ≠ 0 := by
  intro h
  have hdim : (1 : ℕ) = 0 := by
    simpa only [ProjectiveClass.finrankHom_of_self, map_zero] using
      congrArg (ProjectiveClass.finrankHom ℚ) h
  exact Nat.one_ne_zero hdim

-- The entire direct-sum monoid is retained, including its stored nsmul field.
example (R : Type uR) [rR : CommRing R] :
    (@ProjectiveClass.instCommSemiring R rR).toAddCommMonoid =
      @KTheory.instAddCommMonoidProjectiveClass R rR.toRing := rfl

private noncomputable def integerExtension : ProjectiveClass ℤ →+* ProjectiveClass ℚ :=
  ProjectiveClass.mapRingHom (Int.castRingHom ℚ)

private noncomputable def zeroExtension :
    ProjectiveClass ℚ →+* ProjectiveClass PUnit.{uS + 1} :=
  ProjectiveClass.mapRingHom (algebraMap ℚ PUnit.{uS + 1})

-- Evaluate the whole old-map bridge at its explicit original AddZero endpoints.
private theorem integerExtension_regular :
    integerExtension (ProjectiveClass.of ℤ ℤᵐᵒᵖ) = ProjectiveClass.of ℚ ℚᵐᵒᵖ := by
  have h := congrArg
    (fun F :
      @AddMonoidHom (ProjectiveClass ℤ) (ProjectiveClass ℚ)
        (@KTheory.instAddCommMonoidProjectiveClass ℤ
          (inferInstance : CommRing ℤ).toRing).toAddMonoid.toAddZeroClass.toAddZero
        (@KTheory.instAddCommMonoidProjectiveClass ℚ
          (inferInstance : CommRing ℚ).toRing).toAddMonoid.toAddZeroClass.toAddZero ↦
      F (ProjectiveClass.of ℤ ℤᵐᵒᵖ))
    (ProjectiveClass.mapRingHom_toAddMonoidHom (Int.castRingHom ℚ))
  exact h.trans (ProjectiveClass.map_of_self (Int.castRingHom ℚ))

example :
    ProjectiveClass.finrankHom ℚ
        (integerExtension (ProjectiveClass.of ℤ ℤᵐᵒᵖ)) = 1 ∧
      integerExtension (ProjectiveClass.of ℤ ℤᵐᵒᵖ) ≠ 0 ∧
      K0.finrankHom ℚ
        (K0.ofClass ℚ (integerExtension (ProjectiveClass.of ℤ ℤᵐᵒᵖ))) = 1 := by
  rw [integerExtension_regular]
  refine ⟨ProjectiveClass.finrankHom_of_self ℚ, rational_regular_ne_zero, ?_⟩
  simp only [K0.finrankHom_ofClass, ProjectiveClass.finrankHom_of_self, Nat.cast_one]

-- The arbitrary-carrier evaluation API computes an extension in a lifted universe.
example :
    ProjectiveClass.finrankHom ℚ
      (ProjectiveClass.of ℚ
        (ModuleCat.RightExtension.Obj (Int.castRingHom ℚ)
          (ULift.{uM} (Fin 2 → ℤᵐᵒᵖ)))) = 2 := by
  rw [← ProjectiveClass.mapRingHom_of, ProjectiveClass.of_ulift,
    ProjectiveClass.of_fin_fun_eq_nsmul, map_nsmul]
  change ProjectiveClass.finrankHom ℚ
    (2 • integerExtension (ProjectiveClass.of ℤ ℤᵐᵒᵖ)) = 2
  rw [integerExtension_regular, map_nsmul, ProjectiveClass.finrankHom_of_self]
  simp

-- Identity and generic multiplicative arithmetic compute a tensor-class image.
example :
    (integerExtension.comp (ProjectiveClass.mapRingHom (RingHom.id ℤ)))
      ((2 : ProjectiveClass ℤ) * 3) = (6 : ProjectiveClass ℚ) := by
  rw [ProjectiveClass.mapRingHom_id]
  change integerExtension ((2 : ProjectiveClass ℤ) * 3) = (6 : ProjectiveClass ℚ)
  calc
    integerExtension ((2 : ProjectiveClass ℤ) * 3) =
        (2 : ProjectiveClass ℚ) * 3 := by
      simpa only [map_ofNat] using
        map_mul integerExtension (2 : ProjectiveClass ℤ) (3 : ProjectiveClass ℤ)
    _ = (6 : ProjectiveClass ℚ) := (Nat.cast_mul 2 3).symm

-- The zero target includes both presentations of the regular right module.
example :
    zeroExtension.{uS} (ProjectiveClass.of ℚ ℚ) = 0 ∧
      zeroExtension.{uS} (ProjectiveClass.of ℚ ℚᵐᵒᵖ) = 1 ∧
      (1 : ProjectiveClass PUnit.{uS + 1}) = 0 ∧
      ProjectiveClass.of ℚ ℚᵐᵒᵖ ≠ 0 := by
  refine ⟨?_, ?_, Subsingleton.elim _ _, rational_regular_ne_zero⟩
  · change ProjectiveClass.mapRingHom (algebraMap ℚ PUnit.{uS + 1})
      (ProjectiveClass.of ℚ ℚ) = 0
    rw [ProjectiveClass.mapRingHom_of]
    exact Subsingleton.elim _ _
  · rw [← ProjectiveClass.one_eq_of]
    exact map_one zeroExtension.{uS}

-- Composition connects integer extension with the zero boundary.
example :
    zeroExtension.{uS} (integerExtension (ProjectiveClass.of ℤ ℤᵐᵒᵖ)) = 0 := by
  change ((ProjectiveClass.mapRingHom (algebraMap ℚ PUnit.{uS + 1})).comp
    (ProjectiveClass.mapRingHom (Int.castRingHom ℚ)))
      (ProjectiveClass.of ℤ ℤᵐᵒᵖ) = 0
  rw [← ProjectiveClass.mapRingHom_comp, ProjectiveClass.mapRingHom_apply,
    ProjectiveClass.map_of_self]
  exact Subsingleton.elim _ _

end ProjectiveModulesTests.ProjectiveClassRingScalarExtensionClient
