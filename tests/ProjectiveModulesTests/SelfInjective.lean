/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Category.ModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Module.PUnit
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Injectivity of matrix modules

The finite-projective injectivity theorem is applied to the column object of the
rational matrix equivalence. Morita invariance of self-injectivity is applied to
the same equivalence. Independent semisimple-ring arguments establish the
injectivity premises and the corresponding concrete conclusions.

The model equivalence is `ModuleCat.matrixEquivalence ℚ (0 : Fin 2)`. Its image
of the regular rational module is the column object with its bundled matrix
action, not the regular matrix module and not a pointwise scalar action.
Finite projectivity follows from the public equivalence theorem and the
algebraic finite-projectivity bridge. Injectivity in the independent models
follows instead from the semisimplicity of the rational matrix ring.

For the inverse-image example, the target is the lifted regular matrix module.
The counit compares the image of its inverse image with that target; no
identification of regular modules under an arbitrary equivalence is used.
Elementary matrices witness noncommutativity. Zero modules, the zero ring and
empty matrices give the remaining boundary examples.

## References

* Mathlib's module injectivity formalization, and Sophie Morel's formalization
  of injectivity over semisimple rings.
* Yunzhou Xie and Jujian Zhang's Mathlib matrix Morita equivalence and bundled
  matrix-module action.
* Mathlib's elementary-matrix and zero-object APIs.
* `ProjectiveModules.Category.FiniteProjective` and
  `ProjectiveModules.Category.ModuleEquivalence` for finite-projective transport.
-/

universe uR uP

open CategoryTheory

section MatrixColumn

-- Independent premises and conclusion for the bundled column object.
private theorem matrixColumn_finite_projective_injective :
    let e : ModuleCat.{0} ℚ ≌ ModuleCat.{0} (Matrix (Fin 2) (Fin 2) ℚ) :=
      ModuleCat.matrixEquivalence ℚ (0 : Fin 2)
    let Pcol := e.functor.obj (ModuleCat.of ℚ ℚ)
    Module.Finite (Matrix (Fin 2) (Fin 2) ℚ) Pcol ∧
      Module.Projective (Matrix (Fin 2) (Fin 2) ℚ) Pcol ∧
      Module.Injective (Matrix (Fin 2) (Fin 2) ℚ) (Matrix (Fin 2) (Fin 2) ℚ) ∧
      Module.Injective (Matrix (Fin 2) (Fin 2) ℚ) Pcol := by
  let e : ModuleCat.{0} ℚ ≌ ModuleCat.{0} (Matrix (Fin 2) (Fin 2) ℚ) :=
    ModuleCat.matrixEquivalence ℚ (0 : Fin 2)
  let X : ModuleCat.{0} ℚ := ModuleCat.of ℚ ℚ
  let Pcol : ModuleCat.{0} (Matrix (Fin 2) (Fin 2) ℚ) := e.functor.obj X
  have hX : ModuleCat.isFiniteProjective ℚ X :=
    (ModuleCat.isFiniteProjective_iff X).mpr ⟨inferInstance, inferInstance⟩
  have hPcol : Module.Finite (Matrix (Fin 2) (Fin 2) ℚ) Pcol ∧
      Module.Projective (Matrix (Fin 2) (Fin 2) ℚ) Pcol :=
    (ModuleCat.isFiniteProjective_iff Pcol).mp
      (ModuleCat.isFiniteProjective_of_equivalence ℚ
        (Matrix (Fin 2) (Fin 2) ℚ) e X hX)
  exact ⟨hPcol.1, hPcol.2,
    Module.injective_of_isSemisimpleRing (Matrix (Fin 2) (Fin 2) ℚ)
      (Matrix (Fin 2) (Fin 2) ℚ),
    Module.injective_of_isSemisimpleRing (Matrix (Fin 2) (Fin 2) ℚ) Pcol⟩

-- Apply finite-projective injectivity to the same bundled column object.
example :
    let e : ModuleCat.{0} ℚ ≌ ModuleCat.{0} (Matrix (Fin 2) (Fin 2) ℚ) :=
      ModuleCat.matrixEquivalence ℚ (0 : Fin 2)
    Module.Injective (Matrix (Fin 2) (Fin 2) ℚ)
      (e.functor.obj (ModuleCat.of ℚ ℚ)) := by
  let e : ModuleCat.{0} ℚ ≌ ModuleCat.{0} (Matrix (Fin 2) (Fin 2) ℚ) :=
    ModuleCat.matrixEquivalence ℚ (0 : Fin 2)
  let X : ModuleCat.{0} ℚ := ModuleCat.of ℚ ℚ
  let Pcol : ModuleCat.{0} (Matrix (Fin 2) (Fin 2) ℚ) := e.functor.obj X
  have hX : ModuleCat.isFiniteProjective ℚ X :=
    (ModuleCat.isFiniteProjective_iff X).mpr ⟨inferInstance, inferInstance⟩
  have hPcol : Module.Finite (Matrix (Fin 2) (Fin 2) ℚ) Pcol ∧
      Module.Projective (Matrix (Fin 2) (Fin 2) ℚ) Pcol :=
    (ModuleCat.isFiniteProjective_iff Pcol).mp
      (ModuleCat.isFiniteProjective_of_equivalence ℚ
        (Matrix (Fin 2) (Fin 2) ℚ) e X hX)
  let : Module.Finite (Matrix (Fin 2) (Fin 2) ℚ) Pcol := hPcol.1
  let : Module.Projective (Matrix (Fin 2) (Fin 2) ℚ) Pcol := hPcol.2
  let : Module.Injective (Matrix (Fin 2) (Fin 2) ℚ) (Matrix (Fin 2) (Fin 2) ℚ) :=
    Module.injective_of_isSemisimpleRing (Matrix (Fin 2) (Fin 2) ℚ)
      (Matrix (Fin 2) (Fin 2) ℚ)
  exact Module.injective_of_finite_projective (Matrix (Fin 2) (Fin 2) ℚ) Pcol

end MatrixColumn

section LiftedRegularMatrixModule

-- Independent inverse-image premises, the counit law, and both regular conclusions.
private theorem matrixEquivalence_inverse_liftedRegular_finite_projective_counit_injective :
    let e : ModuleCat.{0} ℚ ≌ ModuleCat.{0} (Matrix (Fin 2) (Fin 2) ℚ) :=
      ModuleCat.matrixEquivalence ℚ (0 : Fin 2)
    let Y := ModuleCat.of (Matrix (Fin 2) (Fin 2) ℚ)
      (ULift.{0} (Matrix (Fin 2) (Fin 2) ℚ))
    Module.Finite ℚ (e.inverse.obj Y) ∧
      Module.Projective ℚ (e.inverse.obj Y) ∧
      (∀ y : Y, (e.counitIso.app Y).hom ((e.counitIso.app Y).inv y) = y) ∧
      Module.Injective ℚ ℚ ∧
      Module.Injective (Matrix (Fin 2) (Fin 2) ℚ) (Matrix (Fin 2) (Fin 2) ℚ) := by
  let e : ModuleCat.{0} ℚ ≌ ModuleCat.{0} (Matrix (Fin 2) (Fin 2) ℚ) :=
    ModuleCat.matrixEquivalence ℚ (0 : Fin 2)
  let Y : ModuleCat.{0} (Matrix (Fin 2) (Fin 2) ℚ) :=
    ModuleCat.of (Matrix (Fin 2) (Fin 2) ℚ) (ULift.{0} (Matrix (Fin 2) (Fin 2) ℚ))
  have hY : ModuleCat.isFiniteProjective (Matrix (Fin 2) (Fin 2) ℚ) Y :=
    (ModuleCat.isFiniteProjective_iff Y).mpr ⟨inferInstance, inferInstance⟩
  have hXinv : Module.Finite ℚ (e.inverse.obj Y) ∧
      Module.Projective ℚ (e.inverse.obj Y) :=
    (ModuleCat.isFiniteProjective_iff (e.inverse.obj Y)).mp
      (ModuleCat.isFiniteProjective_of_equivalence
        (Matrix (Fin 2) (Fin 2) ℚ) ℚ e.symm Y hY)
  refine ⟨hXinv.1, hXinv.2, ?_,
    Module.injective_of_isSemisimpleRing ℚ ℚ,
    Module.injective_of_isSemisimpleRing (Matrix (Fin 2) (Fin 2) ℚ)
      (Matrix (Fin 2) (Fin 2) ℚ)⟩
  intro y
  exact (e.counitIso.app Y).toLinearEquiv.apply_symm_apply y

-- Use the actual matrix equivalence, not an equality of regular objects.
example : Module.Injective ℚ ℚ ↔
    Module.Injective (Matrix (Fin 2) (Fin 2) ℚ) (Matrix (Fin 2) (Fin 2) ℚ) :=
  ModuleCat.selfInjective_iff_of_equivalence.{0, 0, 0, 0} ℚ (Matrix (Fin 2) (Fin 2) ℚ)
    (ModuleCat.matrixEquivalence.{0, 0, 0} ℚ (0 : Fin 2))

end LiftedRegularMatrixModule

-- E₀₁E₁₀ and E₁₀E₀₁ differ at the (0, 0) entry.
private theorem matrix_single_mul_ne_reverse :
    (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℚ) * Matrix.single 1 0 1 ≠
      Matrix.single 1 0 1 * Matrix.single 0 1 1 := by
  intro h
  have h00 : (1 : ℚ) = 0 := by
    simpa using congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ ↦ A 0 0) h
  exact one_ne_zero h00

section ZeroBoundaries

-- The zero module is injective even without a self-injectivity premise on R.
private theorem punit_finite_projective_injective (R : Type uR) [Ring R] :
    Module.Finite R PUnit.{uP + 1} ∧ Module.Projective R PUnit.{uP + 1} ∧
      Module.Injective R PUnit.{uP + 1} := by
  let : CategoryTheory.Injective (ModuleCat.of R PUnit.{uP + 1}) :=
    ((ModuleCat.isZero_iff_subsingleton (M := ModuleCat.of R PUnit.{uP + 1})).mpr
      inferInstance).injective
  exact ⟨inferInstance, inferInstance,
    Module.injective_module_of_injective_object R PUnit.{uP + 1}⟩

private theorem punit_regular_finite_projective_injective :
    Module.Finite PUnit.{1} PUnit.{1} ∧ Module.Projective PUnit.{1} PUnit.{1} ∧
      Module.Injective PUnit.{1} PUnit.{1} :=
  ⟨inferInstance, inferInstance,
    Module.injective_of_isSemisimpleRing PUnit.{1} PUnit.{1}⟩

-- An empty-index matrix ring is a zero ring; no matrix equivalence is needed.
private theorem emptyMatrix_finite_projective_injective :
    Subsingleton (Matrix (Fin 0) (Fin 0) ℚ) ∧
      Module.Finite (Matrix (Fin 0) (Fin 0) ℚ) (Matrix (Fin 0) (Fin 0) ℚ) ∧
      Module.Projective (Matrix (Fin 0) (Fin 0) ℚ) (Matrix (Fin 0) (Fin 0) ℚ) ∧
      Module.Injective (Matrix (Fin 0) (Fin 0) ℚ) (Matrix (Fin 0) (Fin 0) ℚ) :=
  ⟨inferInstance, inferInstance, inferInstance,
    Module.injective_of_isSemisimpleRing (Matrix (Fin 0) (Fin 0) ℚ)
      (Matrix (Fin 0) (Fin 0) ℚ)⟩

end ZeroBoundaries
