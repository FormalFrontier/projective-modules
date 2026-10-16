/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.Matrix
import ProjectiveModules.KTheory.Product
import ProjectiveModules.KTheory.ZeroRing
import Mathlib.Algebra.Ring.Rat
import Mathlib.Tactic.NormNum

/-!
# Integer retractions and scalar-matrix coordinates

The first projection from `ℚ × ℚ` to `ℚ` has an integer retraction on K₀,
but also has a nonzero kernel element obtained from the second factor by the
product equivalence. The factor dimension maps observe its coordinates `(0, 1)`.
The integer-to-rational ring homomorphism supplies a nonsurjective scalar-map
example without a classification of K₀ of the integers.

For two-by-two rational matrices, the regular class has normalized coordinate
two, the scalar map has coordinate minus two on a negative generator, and its
range is a proper cyclic subgroup. The regular-coordinate and nonzero observers
use the Morita regular-module comparison and division-ring dimension laws.
For one-by-one matrices the scalar map splits. Empty matrices instead have
trivial K₀ and cyclic subgroup index one; no integer coordinate is used there.

## References and credits

These examples use Mathlib's finite right-free modules, opposite-module
linear equivalences, integer multiples and subgroup index, together with
Projective Modules' scalar extension, product decomposition, matrix-Morita
comparison, dimension and zero-ring APIs.
-/

@[expose] public section

noncomputable section

open KTheory

namespace ProjectiveModulesTests.K0RetractionMatrixClient

private def secondFactor : K0 (ℚ × ℚ) :=
  (K0.prodEquiv ℚ ℚ).symm (0, K0.of ℚ ℚᵐᵒᵖ)

private theorem secondFactor_coordinates :
    K0.finrankHom ℚ (K0.map (RingHom.fst ℚ ℚ) secondFactor) = 0 ∧
      K0.finrankHom ℚ (K0.map (RingHom.snd ℚ ℚ) secondFactor) = 1 := by
  have h := K0.prod_map_prodEquiv_symm ℚ ℚ (0, K0.of ℚ ℚᵐᵒᵖ)
  constructor
  · simpa only [secondFactor, map_zero] using
      congrArg (K0.finrankHom ℚ) (congrArg Prod.fst h)
  · simpa only [secondFactor, K0.finrankHom_of_self] using
      congrArg (K0.finrankHom ℚ) (congrArg Prod.snd h)

/-- The second factor gives a nonzero kernel element, not an assumed K₀ model. -/
private theorem secondFactor_nonzero : secondFactor ≠ 0 := by
  intro h
  have observed := congrArg
    (fun x : K0 (ℚ × ℚ) ↦ K0.finrankHom ℚ (K0.map (RingHom.snd ℚ ℚ) x)) h
  have impossible : (1 : ℤ) = 0 := by
    simpa only [secondFactor_coordinates.2, map_zero] using observed
  exact one_ne_zero impossible

private theorem product_regular_coordinates :
    (K0.finrankHom ℚ (K0.map (RingHom.fst ℚ ℚ) (K0.of (ℚ × ℚ) (ℚ × ℚ)ᵐᵒᵖ)),
      K0.finrankHom ℚ (K0.map (RingHom.snd ℚ ℚ) (K0.of (ℚ × ℚ) (ℚ × ℚ)ᵐᵒᵖ))) =
        (1, 1) := by
  simp only [K0.map_of_self, K0.finrankHom_of_self]

/-- Retraction does not give the opposite identity on the source K₀ group. -/
private theorem product_section_not_inverse :
    zmultiplesHom (K0 (ℚ × ℚ)) (K0.of (ℚ × ℚ) (ℚ × ℚ)ᵐᵒᵖ)
        (K0.finrankHom ℚ (K0.map (RingHom.fst ℚ ℚ) secondFactor)) ≠
      secondFactor := by
  rw [secondFactor_coordinates.1, zmultiplesHom_apply, zero_zsmul]
  exact Ne.symm secondFactor_nonzero

private theorem product_negative_retraction :
    K0.finrankHom ℚ (K0.map (RingHom.fst ℚ ℚ)
      (zmultiplesHom (K0 (ℚ × ℚ)) (K0.of (ℚ × ℚ) (ℚ × ℚ)ᵐᵒᵖ) (-3))) = -3 := by
  exact DFunLike.congr_fun
    (K0.finrankHom_comp_map_zmultiplesHom (RingHom.fst ℚ ℚ)) (-3)

private theorem integer_cast_retraction :
    K0.finrankHom ℚ (K0.map (Int.castRingHom ℚ)
      (zmultiplesHom (K0 ℤ) (K0.of ℤ ℤᵐᵒᵖ) (-2))) = -2 := by
  exact DFunLike.congr_fun
    (K0.finrankHom_comp_map_zmultiplesHom (Int.castRingHom ℚ)) (-2)

private abbrev A₂ := Matrix (Fin 2) (Fin 2) ℚ

/-- The coordinate two is computed from the regular Morita comparison. -/
private theorem matrix_two_regular_coordinate :
    ((K0.matrixEquiv ℚ (Fin 2)).symm.trans (K0.finrankEquiv ℚ))
        (K0.of A₂ A₂ᵐᵒᵖ) = 2 := by
  have hregular : K0.of A₂ A₂ᵐᵒᵖ = K0.of A₂ A₂ :=
    (K0.of_eq_of_equiv A₂ A₂ (MulOpposite.opLinearEquiv A₂ᵐᵒᵖ)).symm
  rw [hregular, AddEquiv.trans_apply, K0.matrixEquiv_symm_regular,
    K0.finrankEquiv_of_module, (Module.rightFreeCoordEquiv ℚ (Fin 2)).symm.finrank_eq,
    Module.finrank_fin_fun]
  norm_num

private theorem matrix_two_regular_nonzero : K0.of A₂ A₂ᵐᵒᵖ ≠ 0 := by
  intro h
  have observed := congrArg
    ((K0.matrixEquiv ℚ (Fin 2)).symm.trans (K0.finrankEquiv ℚ)) h
  have impossible : (2 : ℤ) = 0 := by
    simpa only [matrix_two_regular_coordinate, map_zero] using observed
  norm_num at impossible

/-- The scalar-coordinate formula has a nonzero right-hand side independently
of the scalar-coordinate identity. -/
private theorem scalar_two_rhs_nonzero :
    zmultiplesHom ℤ (Fintype.card (Fin 2) : ℤ)
      (K0.finrankHom ℚ (-(K0.of ℚ ℚᵐᵒᵖ))) ≠ 0 := by
  norm_num

private theorem scalar_two_negative_coordinate :
    ((K0.matrixEquiv ℚ (Fin 2)).symm.trans (K0.finrankEquiv ℚ))
        (K0.map (Matrix.scalar (Fin 2) : ℚ →+* A₂) (-(K0.of ℚ ℚᵐᵒᵖ))) = -2 := by
  have h := DFunLike.congr_fun
    (K0.finrankEquiv_matrixEquiv_symm_comp_map_scalar ℚ (Fin 2))
      (-(K0.of ℚ ℚᵐᵒᵖ))
  simpa using h

/-- The negative regular matrix class lies in the scalar-map image. -/
private theorem scalar_two_negative_regular_mem :
    -(K0.of A₂ A₂ᵐᵒᵖ) ∈ (K0.map (Matrix.scalar (Fin 2) : ℚ →+* A₂)).range := by
  rw [K0.range_map_matrix_scalar]
  exact (AddSubgroup.zmultiples (K0.of A₂ A₂ᵐᵒᵖ)).neg_mem
    (AddSubgroup.mem_zmultiples _)

private theorem matrix_two_free_class_index_and_proper :
    (AddSubgroup.zmultiples (K0.of A₂ A₂ᵐᵒᵖ)).index = 2 ∧
      AddSubgroup.zmultiples (K0.of A₂ A₂ᵐᵒᵖ) ≠ ⊤ := by
  have hi : (AddSubgroup.zmultiples (K0.of A₂ A₂ᵐᵒᵖ)).index = 2 := by
    simpa using K0.index_zmultiples_matrix_regular ℚ (Fin 2)
  refine ⟨hi, ?_⟩
  intro htop
  rw [htop, AddSubgroup.index_top] at hi
  norm_num at hi

private theorem scalar_two_no_additive_left_inverse :
    ¬ ∃ q : K0 A₂ →+ K0 ℚ,
      Function.LeftInverse q (K0.map (Matrix.scalar (Fin 2) : ℚ →+* A₂)) := by
  rintro ⟨q, hq⟩
  exact K0.not_exists_leftInverse_map_matrix_scalar ℚ (Fin 2) (by decide)
    ⟨q, AddMonoidHom.ext hq⟩

private abbrev A₁ := Matrix (Fin 1) (Fin 1) ℚ

/-- A singleton matrix index admits an additive left inverse to scalar extension. -/
private theorem scalar_one_splits :
    ∃ q : K0 A₁ →+ K0 ℚ,
      q.comp (K0.map (Matrix.scalar (Fin 1) : ℚ →+* A₁)) =
        AddMonoidHom.id (K0 ℚ) := by
  have hcoord : ((K0.matrixEquiv ℚ (Fin 1)).symm.trans (K0.finrankEquiv ℚ))
      (K0.of A₁ A₁ᵐᵒᵖ) = 1 := by
    simpa using K0.finrankEquiv_matrixEquiv_symm_regular ℚ (Fin 1)
  refine ⟨(K0.finrankEquiv ℚ).symm.toAddMonoidHom.comp
    ((K0.matrixEquiv ℚ (Fin 1)).symm.trans (K0.finrankEquiv ℚ)).toAddMonoidHom, ?_⟩
  apply AddMonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := (K0.finrankEquiv ℚ).symm.surjective x
  rw [K0.finrankEquiv_symm_apply]
  simp only [AddMonoidHom.comp_apply, map_zsmul, K0.map_of_self,
    AddEquiv.coe_toAddMonoidHom, AddMonoidHom.id_apply, hcoord,
    K0.finrankEquiv_symm_one]

private abbrev A₀ := Matrix (Fin 0) (Fin 0) ℚ

/-- Empty matrices have no integer coordinate: their entire K₀ group is zero. -/
private theorem empty_matrix_boundary :
    (∀ x : K0 A₀, x = 0) ∧
      (AddSubgroup.zmultiples (0 : K0 A₀)).index = 1 := by
  constructor
  · intro x
    exact Subsingleton.elim _ _
  · have htop : AddSubgroup.zmultiples (0 : K0 A₀) = ⊤ := by
      apply le_antisymm le_top
      intro x _
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx]
      exact AddSubgroup.zero_mem _
    rw [htop, AddSubgroup.index_top]

private theorem empty_scalar_map_zero :
    K0.map (Matrix.scalar (Fin 0) : ℚ →+* A₀) = 0 := by
  apply AddMonoidHom.ext
  intro x
  exact Subsingleton.elim _ _

end ProjectiveModulesTests.K0RetractionMatrixClient
