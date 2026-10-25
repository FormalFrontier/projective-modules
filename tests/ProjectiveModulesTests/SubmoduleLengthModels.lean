/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.Length
import Mathlib.Algebra.Field.Rat
import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Morita.Matrix

/-!
# Submodule transport and length for rational matrix modules

The chosen-index matrix equivalence sends the regular rational module to the
simple two-coordinate column module over the noncommutative ring of two-by-two
rational matrices. This column module has length one; it is not the regular
matrix module, which has length two. A coordinate line in the rational plane
transports to a nonzero proper submodule, and the zero module has length zero.

The matrix equivalence is Mathlib's construction by Yunzhou Xie and Jujian Zhang.
The submodule and length APIs use the Mathlib formalizations credited in
`ProjectiveModules.Category.SubmoduleEquivalence` and
`ProjectiveModules.Category.Length`.
-/

@[expose] public section

open CategoryTheory

namespace ProjectiveModulesTests.SubmoduleLengthModels

/-- The noncommutative ring of two-by-two rational matrices. -/
abbrev Mat2Q := Matrix (Fin 2) (Fin 2) ℚ

/-- The chosen-index equivalence from rational modules to rational matrix modules. -/
def matrixEquivalence : ModuleCat.{0} ℚ ≌ ModuleCat.{0} Mat2Q :=
  ModuleCat.matrixEquivalence ℚ (0 : Fin 2)

/-- The image of the regular rational module, with the left matrix-column action. -/
def rationalColumn : ModuleCat.{0} Mat2Q :=
  matrixEquivalence.functor.obj (ModuleCat.of ℚ ℚ)

/-- The image of the regular rational module has two rational coordinates. -/
theorem rationalColumn_carrier : (rationalColumn : Type) = (Fin 2 → ℚ) := by
  rfl

/-- The column module has length one over the matrix ring, not length two. -/
theorem rationalColumn_length : Module.length Mat2Q rationalColumn = 1 := by
  calc
    Module.length Mat2Q rationalColumn = Module.length ℚ (ModuleCat.of ℚ ℚ) :=
      ModuleCat.length_eq_of_equivalence matrixEquivalence (ModuleCat.of ℚ ℚ)
    _ = 1 := Module.length_eq_one ℚ ℚ

/-- The column module has finite length, expressed as a proposition. -/
theorem rationalColumn_isFiniteLength : IsFiniteLength Mat2Q rationalColumn := by
  apply Module.length_ne_top_iff.mp
  rw [rationalColumn_length]
  simp

/-- The first coordinate line in the rational plane is the kernel of the second projection. -/
def firstCoordinateLine : Submodule ℚ (Fin 2 → ℚ) :=
  LinearMap.ker (LinearMap.proj (1 : Fin 2) : (Fin 2 → ℚ) →ₗ[ℚ] ℚ)

/-- The image of the first coordinate line under the submodule order isomorphism. -/
noncomputable def matrixFirstCoordinateLine :
    Submodule Mat2Q
      (matrixEquivalence.functor.obj (ModuleCat.of ℚ (Fin 2 → ℚ))) :=
  ModuleCat.submoduleOrderIsoOfEquivalence matrixEquivalence
    (ModuleCat.of ℚ (Fin 2 → ℚ)) firstCoordinateLine

/-- A coordinate line transports to a nonzero proper submodule of the image plane. -/
theorem matrixFirstCoordinateLine_nonzero_proper :
    ⊥ < matrixFirstCoordinateLine ∧ matrixFirstCoordinateLine < ⊤ := by
  have hbot : (⊥ : Submodule ℚ (Fin 2 → ℚ)) < firstCoordinateLine := by
    apply bot_lt_iff_ne_bot.mpr
    apply firstCoordinateLine.ne_bot_iff.mpr
    refine ⟨![1, 0], ?_, ?_⟩
    · simp [firstCoordinateLine, LinearMap.proj_apply]
    · intro h
      have hzero := congrFun h (0 : Fin 2)
      simp at hzero
  have htop : firstCoordinateLine < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro h
    have hmem : ![0, 1] ∈ firstCoordinateLine := by
      rw [h]
      exact Submodule.mem_top
    simp [firstCoordinateLine, LinearMap.proj_apply] at hmem
  let φ := ModuleCat.submoduleOrderIsoOfEquivalence matrixEquivalence
    (ModuleCat.of ℚ (Fin 2 → ℚ))
  change ⊥ < φ firstCoordinateLine ∧ φ firstCoordinateLine < ⊤
  constructor
  · simpa only [map_bot] using φ.strictMono hbot
  · simpa only [map_top] using φ.strictMono htop

/-- The image of the zero rational module has length zero over the matrix ring. -/
theorem matrixZero_length :
    Module.length Mat2Q
      (matrixEquivalence.functor.obj (ModuleCat.of ℚ (Fin 0 → ℚ))) = 0 := by
  rw [ModuleCat.length_eq_of_equivalence matrixEquivalence]
  exact Module.length_eq_zero

end ProjectiveModulesTests.SubmoduleLengthModels
