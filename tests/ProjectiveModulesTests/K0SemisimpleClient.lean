/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.SemisimpleEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Ring.Rat
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.Tactic.NormNum

/-!
# Two rational matrix blocks

The coefficient ring has two factors with block sizes one and two. Its regular
right-module coordinates are `(1, 2)`, and its integer coordinate basis has the
two standard unit vectors. The supported right rows represent the corresponding
coordinate-unit classes. An empty outer family gives the zero class and zero
K₀ generator.
-/

@[expose] public section

noncomputable section

open KTheory

namespace ProjectiveModulesTests.K0SemisimpleClient

private abbrev D : Fin 2 → Type := fun _ ↦ ℚ
private abbrev κ (i : Fin 2) := Fin (i.val + 1)
private abbrev A := ∀ i : Fin 2, Matrix (κ i) (κ i) (D i)

/-- Projection onto the scalar entry of the first, one-by-one block. -/
private def firstBlockScalar : A →+* ℚ :=
  (Matrix.uniqueRingEquiv (m := Fin 1) (A := ℚ)).toRingHom.comp
    (Pi.evalRingHom (fun i : Fin 2 ↦ Matrix (κ i) (κ i) (D i)) 0)

/-- The regular rational opposite module restricted along the first block. -/
private def firstBlockModule : ModuleCat Aᵐᵒᵖ :=
  (ModuleCat.restrictScalars (RingHom.op firstBlockScalar)).obj
    (ModuleCat.of ℚᵐᵒᵖ ℚᵐᵒᵖ)

/-- Surjective scalar restriction preserves simplicity of the rational
regular module, without using any supported-row identification. -/
private theorem firstBlockModule_simple : IsSimpleModule Aᵐᵒᵖ firstBlockModule := by
  have h : Function.Surjective firstBlockScalar :=
    (Matrix.uniqueRingEquiv (m := Fin 1) (A := ℚ)).surjective.comp
      (Pi.evalRingHom (fun i : Fin 2 ↦ Matrix (κ i) (κ i) (D i)) 0).surjective
  let : RingHomSurjective (RingHom.op firstBlockScalar) := ⟨fun q ↦ by
    obtain ⟨a, ha⟩ := h (MulOpposite.unop q)
    exact ⟨MulOpposite.op a,
      (congrArg MulOpposite.op ha).trans (MulOpposite.op_unop q)⟩⟩
  let e : firstBlockModule →ₛₗ[RingHom.op firstBlockScalar] ℚᵐᵒᵖ :=
    (ModuleCat.semilinearMapAddEquiv (RingHom.op firstBlockScalar) firstBlockModule
      (ModuleCat.of ℚᵐᵒᵖ ℚᵐᵒᵖ)).symm
        (ModuleCat.ofHom (X := firstBlockModule) (Y := firstBlockModule) LinearMap.id)
  exact (e.isSimpleModule_iff_of_bijective Function.bijective_id).mpr inferInstance

/-- The regular module has coordinates equal to the sizes of its two
nonempty matrix blocks, in both natural and integer coordinates. -/
private theorem regular_coordinates :
    (ProjectiveClass.matrixFamilyEquiv D κ (ProjectiveClass.of A A) 0,
      ProjectiveClass.matrixFamilyEquiv D κ (ProjectiveClass.of A A) 1) = (1, 2) ∧
      (K0.matrixFamilyEquiv D κ (K0.of A A) 0,
        K0.matrixFamilyEquiv D κ (K0.of A A) 1) = (1, 2) := by
  constructor <;>
    simp only [ProjectiveClass.matrixFamilyEquiv_regular,
      K0.matrixFamilyEquiv_regular, κ, Fintype.card_fin] <;>
    norm_num

/-- The reassembled coordinate basis gives two distinct unit vectors, not
the regular-module coordinates `(1, 2)`. -/
private theorem basis_coordinates :
    (K0.matrixFamilyEquiv D κ (K0.matrixFamilyBasis D κ 0) 0,
      K0.matrixFamilyEquiv D κ (K0.matrixFamilyBasis D κ 0) 1,
      K0.matrixFamilyEquiv D κ (K0.matrixFamilyBasis D κ 1) 0,
      K0.matrixFamilyEquiv D κ (K0.matrixFamilyBasis D κ 1) 1) = (1, 0, 0, 1) := by
  simp only [K0.matrixFamilyEquiv_basis]
  norm_num [Pi.single_apply]

/-- The basis consists of images of the projective coordinate-unit classes,
without using the simple-row identification. -/
private theorem basis_projective_classes (i : Fin 2) :
    K0.matrixFamilyBasis D κ i =
      K0.ofClass A (ProjectiveClass.matrixFamilyRowClass D κ i) :=
  K0.matrixFamilyBasis_eq_ofClass D κ i

/-- The two supported rows specialize the simple-module assertion to the
rational matrix product. -/
private theorem simple_rows (i : Fin 2) :
    IsSimpleModule Aᵐᵒᵖ (matrixBlockModule D κ i) :=
  matrixBlockModule_simple D κ i

/-- The supported rows represent the projective coordinate-unit classes of
the same rational matrix product. -/
private theorem row_classes (i : Fin 2) :
    ProjectiveClass.of A (matrixBlockModule D κ i) =
      ProjectiveClass.matrixFamilyRowClass D κ i :=
  matrixBlockModule_class D κ i

/-- The simple-row basis statement specializes to the same two-block ring. -/
private theorem basis_rows (i : Fin 2) :
    K0.matrixFamilyBasis D κ i = K0.of A (matrixBlockModule D κ i) :=
  K0.matrixFamilyBasis_eq_row D κ i

/-- The first-block rational module is isomorphic to a unique supported row.
Its simplicity follows from surjective scalar restriction of the rational
regular module. -/
private theorem first_block_classification :
    ∃! i : Fin 2, Nonempty
      (firstBlockModule ≃ₗ[Aᵐᵒᵖ] matrixBlockModule D κ i) := by
  let : IsSimpleModule Aᵐᵒᵖ firstBlockModule := firstBlockModule_simple
  exact existsUnique_matrixBlockModule D κ firstBlockModule

/-- Chosen-equivalence transport recovers both the distinct row basis units
and the block-size regular coordinates on the same two-block model. The
identity here checks the composition API, not abstract semisimple classification. -/
private theorem ringEquiv_coordinates :
    (ProjectiveClass.matrixFamilyEquivOfRingEquiv D κ (RingEquiv.refl A)
      (ProjectiveClass.of A A) 0,
      ProjectiveClass.matrixFamilyEquivOfRingEquiv D κ (RingEquiv.refl A)
        (ProjectiveClass.of A A) 1) = (1, 2) ∧
    K0.matrixFamilyEquivOfRingEquiv D κ (RingEquiv.refl A)
      (K0.matrixFamilyBasisOfRingEquiv D κ (RingEquiv.refl A) 1) = Pi.single 1 1 := by
  constructor
  · simpa only [ProjectiveClass.matrixFamilyEquivOfRingEquiv_refl] using
      regular_coordinates.1
  · exact K0.matrixFamilyEquivOfRingEquiv_basis D κ (RingEquiv.refl A) 1

/-- For the same two-block rational product, the transported rows are simple,
have coordinate-unit projective classes and represent the integer basis.
These three identifications use the row simplicity, row-class coordinate and
K₀ basis-generator theorems. -/
private theorem ringEquiv_rows (i : Fin 2) :
    IsSimpleModule Aᵐᵒᵖ (matrixBlockModuleOfRingEquiv D κ (RingEquiv.refl A) i) ∧
      ProjectiveClass.matrixFamilyEquivOfRingEquiv D κ (RingEquiv.refl A)
        (ProjectiveClass.of A (matrixBlockModuleOfRingEquiv D κ (RingEquiv.refl A) i)) =
          Pi.single i 1 ∧
      K0.matrixFamilyBasisOfRingEquiv D κ (RingEquiv.refl A) i =
        K0.of A (matrixBlockModuleOfRingEquiv D κ (RingEquiv.refl A) i) :=
  ⟨matrixBlockModuleOfRingEquiv_simple D κ (RingEquiv.refl A) i,
    matrixBlockModuleOfRingEquiv_class D κ (RingEquiv.refl A) i,
    K0.matrixFamilyBasisOfRingEquiv_eq_row D κ (RingEquiv.refl A) i⟩

/-- The chosen-equivalence classifier applies to the independently simple
first-block rational module, without selecting an equivalence witness. -/
private theorem first_block_ringEquiv_classification :
    ∃! i : Fin 2, Nonempty
      (firstBlockModule ≃ₗ[Aᵐᵒᵖ] matrixBlockModuleOfRingEquiv D κ (RingEquiv.refl A) i) := by
  let : IsSimpleModule Aᵐᵒᵖ firstBlockModule := firstBlockModule_simple
  exact existsUnique_matrixBlockModuleOfRingEquiv D κ (RingEquiv.refl A) firstBlockModule

/-- The regular-coordinate theorems give the distinct block weights `(1, 2)`
in both projective-class and integer coordinates. -/
private theorem ringEquiv_regular_coordinates :
    (ProjectiveClass.matrixFamilyEquivOfRingEquiv D κ (RingEquiv.refl A)
      (ProjectiveClass.of A A) 0,
      ProjectiveClass.matrixFamilyEquivOfRingEquiv D κ (RingEquiv.refl A)
        (ProjectiveClass.of A A) 1) = (1, 2) ∧
      (K0.matrixFamilyEquivOfRingEquiv D κ (RingEquiv.refl A) (K0.of A A) 0,
        K0.matrixFamilyEquivOfRingEquiv D κ (RingEquiv.refl A) (K0.of A A) 1) = (1, 2) := by
  constructor <;>
    simp only [ProjectiveClass.matrixFamilyEquivOfRingEquiv_regular,
      K0.matrixFamilyEquivOfRingEquiv_regular, κ, Fintype.card_fin] <;>
    norm_num

/-- The endomorphism-ring theorem applies to the first right row of the same
two-block model. Only the proposition is used, not an equivalence witness. -/
private theorem ringEquiv_row_end :
    Nonempty (D 0 ≃+* Module.End Aᵐᵒᵖ
      (matrixBlockModuleOfRingEquiv D κ (RingEquiv.refl A) 0)) :=
  matrixBlockModuleOfRingEquiv_end D κ (RingEquiv.refl A) 0

/-- The same independently simple module is classified by the decomposition
chosen from the proved Wedderburn–Artin theorem, not from a classification
proposition or from an identity-only decomposition. -/
private theorem first_block_semisimple_classification :
    ∃! i : Fin (MatrixDivisionDecomposition.ofIsSemisimpleRing A).size, Nonempty
      (firstBlockModule ≃ₗ[Aᵐᵒᵖ] matrixBlockModuleOfRingEquiv
        (MatrixDivisionDecomposition.ofIsSemisimpleRing A).coefficient
        (fun j ↦ Fin ((MatrixDivisionDecomposition.ofIsSemisimpleRing A).blockSize j))
        (MatrixDivisionDecomposition.ofIsSemisimpleRing A).ringEquiv i) := by
  exact (IsSemisimpleRing.matrixDivisionDecomposition_simple_basis A).2.1
    firstBlockModule firstBlockModule_simple

/-- The regular module over an empty coefficient product gives zero in both
class and K₀ calculations; no nontriviality assumption on that ring is needed. -/
private theorem empty_regular :
    ProjectiveClass.of (∀ _ : Fin 0, Matrix (Fin 1) (Fin 1) ℚ)
        (∀ _ : Fin 0, Matrix (Fin 1) (Fin 1) ℚ) = 0 ∧
      K0.of (∀ _ : Fin 0, Matrix (Fin 1) (Fin 1) ℚ)
        (∀ _ : Fin 0, Matrix (Fin 1) (Fin 1) ℚ) = 0 := by
  constructor
  · exact ProjectiveClass.of_zero _ _
  · exact K0.of_zero _ _

end ProjectiveModulesTests.K0SemisimpleClient
