/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Product
public import ProjectiveModules.KTheory.Matrix
public import ProjectiveModules.KTheory.Rank
public import ProjectiveModules.Module.MatrixRow
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Coordinates for finite families of matrix rings over division rings

Let `A = ∀ i, Matrix (κ i) (κ i) (D i)`, where the outer family is finite,
each matrix index is finite and nonempty, and each `D i` is a division ring.
Coordinate scalar extension, inverse matrix Morita equivalence, and dimension
give `ProjectiveClass A ≃+ (ι → ℕ)` and `K0 A ≃+ (ι → ℤ)`. The outer family
may be empty. The ring, outer-index and matrix-index universes are independent.

The regular module has coordinate `Fintype.card (κ i)`, rather than one.
The inverse images of coordinate unit vectors are projective classes; their
images in K₀ form a basis over the integers with its usual scalar action.
Identification of these classes with simple right row modules is a separate
assertion from the coordinate constructions. The supporting row modules and
their coefficient-product assembly are defined over arbitrary coefficient rings.

## References and credits

* Charles A. Weibel, *The K-book*, Chapter II: projective classes and K₀ of
  division rings, matrix rings and finite products.
* Mathlib's matrix Morita equivalence, finite coordinate bases, integer linear
  equivalences, and module dimension.
* Projective Modules' finite-product, right matrix, dimension and
  group-completion equivalences.
-/

@[expose] public section

universe uι uκ uD

namespace KTheory

variable {ι : Type uι} (D : ι → Type uD) (κ : ι → Type uκ)

section RowData

variable [∀ i, Ring (D i)] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- The finite-projective factor family supported at block `i`: its `i`th
factor is the direct right row, and all other factors are zero modules. The
row action is supplied by `ModuleCat.toRightMatrixModCat`. -/
noncomputable def matrixRowFactors (i j : ι) :
    ModuleCat.FiniteProjective.{max uκ uD, max uκ uD}
      (Matrix (κ j) (κ j) (D j))ᵐᵒᵖ := by
  classical
  exact if j = i then
    ⟨(ModuleCat.toRightMatrixModCat.{uD, uκ, uD} (D j) (κ j)).obj
        (ModuleCat.of (D j)ᵐᵒᵖ (D j)),
      ModuleCat.isFiniteProjective_toRightMatrixModCat_obj.{uD, uκ, uD}
        (D j) (κ j) (ModuleCat.of (D j)ᵐᵒᵖ (D j))
        ⟨inferInstance, inferInstance⟩⟩
    else ModuleCat.FiniteProjective.of _ PUnit.{max uκ uD + 1}

/-- The supported factor is the direct right row. -/
@[simp]
theorem matrixRowFactors_same (i : ι) :
    (matrixRowFactors D κ i i).obj =
      (ModuleCat.toRightMatrixModCat.{uD, uκ, uD} (D i) (κ i)).obj
        (ModuleCat.of (D i)ᵐᵒᵖ (D i)) := by
  classical
  simp only [matrixRowFactors, ite_true]

/-- All other factors are the zero module. -/
@[simp]
theorem matrixRowFactors_of_ne (i j : ι) (h : j ≠ i) :
    matrixRowFactors D κ i j =
      ModuleCat.FiniteProjective.of (Matrix (κ j) (κ j) (D j))ᵐᵒᵖ
        PUnit.{max uκ uD + 1} := by
  classical
  simp only [matrixRowFactors, ite_eq_right h]

section

variable [Finite ι]

/-- The supported right row over the whole coefficient product, assembled
using the existing finite-projective coefficient-product construction. -/
noncomputable def matrixBlockModule (i : ι) :
    ModuleCat.FiniteProjective.{max uι (max uκ uD), max uι (max uκ uD)}
      (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ :=
  ModuleCat.FiniteProjective.pi (fun j ↦ Matrix (κ j) (κ j) (D j))
    (matrixRowFactors D κ i)

/-- The underlying module is the canonical coefficient product of the
supported row family. -/
theorem matrixBlockModule_obj (i : ι) :
    (matrixBlockModule D κ i).obj =
      ModuleCat.piRight (fun j ↦ Matrix (κ j) (κ j) (D j))
        (fun j ↦ (matrixRowFactors D κ i j).obj) := rfl

/-- The carrier of the supported module is the family of its factor carriers. -/
theorem matrixBlockModule_carrier (i : ι) :
    (matrixBlockModule D κ i : Type (max uι (max uκ uD))) =
      (∀ j, matrixRowFactors D κ i j) := rfl

/-- Coefficient scalars act on the supported row family coordinatewise. -/
theorem matrixBlockModule_smul_apply (i : ι)
    (a : ∀ j, Matrix (κ j) (κ j) (D j)) (x : matrixBlockModule D κ i) (j : ι) :
    (MulOpposite.op a • x) j = MulOpposite.op (a j) • x j :=
  ModuleCat.FiniteProjective.pi_smul_apply _ _ a x j

/-- The supported coefficient-product row is linearly equivalent to the
canonical row restricted along the opposite coordinate projection. The map
projects to the selected factor and uses the regular-row comparison; the inverse
inserts that row in the selected factor. The selected matrix index may be empty. -/
noncomputable def matrixBlockModuleLinearEquivRow (i : ι) :
    matrixBlockModule D κ i ≃ₗ[(∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ]
      (ModuleCat.restrictScalars
        (RingHom.op (Pi.evalRingHom (fun j ↦ Matrix (κ j) (κ j) (D j)) i))).obj
          (ModuleCat.of (Matrix (κ i) (κ i) (D i))ᵐᵒᵖ (κ i → D i)) := by
  classical
  let A := fun j ↦ Matrix (κ j) (κ j) (D j)
  let Mi := fun j ↦ (matrixRowFactors D κ i j).obj
  let p : (∀ j, A j)ᵐᵒᵖ →+* (A i)ᵐᵒᵖ := RingHom.op (Pi.evalRingHom A i)
  let row := ModuleCat.of (A i)ᵐᵒᵖ (κ i → D i)
  have hzero : ∀ j, j ≠ i → CategoryTheory.Limits.IsZero (Mi j) := by
    intro j hj
    change CategoryTheory.Limits.IsZero ((matrixRowFactors D κ i j).obj)
    rw [matrixRowFactors_of_ne D κ i j hj]
    exact ModuleCat.isZero_of_subsingleton _
  let e := (ModuleCat.FiniteProjective.piLinearEquiv A (matrixRowFactors D κ i)).trans
    (ModuleCat.piRightLinearEquivOfIsZero A Mi i hzero)
  let f : Mi i ≃ₗ[(A i)ᵐᵒᵖ] row :=
    (CategoryTheory.eqToIso (matrixRowFactors_same D κ i)).toLinearEquiv.trans
      (ModuleCat.toRightMatrixModCatRegularLinearEquiv (D i) (κ i))
  let erow : (ModuleCat.restrictScalars p).obj (Mi i) ≃ₗ[(∀ j, A j)ᵐᵒᵖ]
      (ModuleCat.restrictScalars p).obj row :=
    { toFun := f
      invFun := f.symm
      left_inv := f.symm_apply_apply
      right_inv := f.apply_symm_apply
      map_add' := f.map_add
      map_smul' := fun a x ↦ by
        change f (p a • x) = p a • f x
        exact f.map_smul (p a) x }
  exact e.trans erow

/-- The row comparison projects to the selected factor, identifies that factor
with the direct row, and uses the regular-row linear equivalence. -/
@[simp]
theorem matrixBlockModuleLinearEquivRow_apply (i : ι) (x : matrixBlockModule D κ i) :
    matrixBlockModuleLinearEquivRow D κ i x =
      ModuleCat.toRightMatrixModCatRegularLinearEquiv (D i) (κ i)
        ((CategoryTheory.eqToIso (matrixRowFactors_same D κ i)).hom (x i)) := rfl

/-- The inverse row comparison inserts the row in its supported factor, using
the canonical coefficient-product and regular-row comparisons. -/
@[simp]
theorem matrixBlockModuleLinearEquivRow_symm_apply (i : ι)
    (x : (ModuleCat.restrictScalars
      (RingHom.op (Pi.evalRingHom (fun j ↦ Matrix (κ j) (κ j) (D j)) i))).obj
        (ModuleCat.of (Matrix (κ i) (κ i) (D i))ᵐᵒᵖ (κ i → D i))) :
    (matrixBlockModuleLinearEquivRow D κ i).symm x =
      (ModuleCat.FiniteProjective.piLinearEquiv
        (fun j ↦ Matrix (κ j) (κ j) (D j)) (matrixRowFactors D κ i)).symm
          (ModuleCat.piRightSingle (fun j ↦ Matrix (κ j) (κ j) (D j))
            (fun j ↦ (matrixRowFactors D κ i j).obj) i
              ((CategoryTheory.eqToIso (matrixRowFactors_same D κ i)).inv
                ((ModuleCat.toRightMatrixModCatRegularLinearEquiv (D i) (κ i)).symm x))) := rfl

/-- The supported coefficient-product row is linearly equivalent to the
canonical row restricted along the opposite coordinate projection. -/
theorem matrixBlockModule_linearEquiv_row (i : ι) :
    Nonempty (matrixBlockModule D κ i ≃ₗ[(∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ]
      (ModuleCat.restrictScalars
        (RingHom.op (Pi.evalRingHom (fun j ↦ Matrix (κ j) (κ j) (D j)) i))).obj
          (ModuleCat.of (Matrix (κ i) (κ i) (D i))ᵐᵒᵖ (κ i → D i))) :=
  ⟨matrixBlockModuleLinearEquivRow D κ i⟩

end

end RowData

variable [∀ i, DivisionRing (D i)] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  [∀ i, Nonempty (κ i)] [Finite ι]

namespace ProjectiveClass

/-- Natural coordinates of finite-projective right-module classes over a
finite family of nonempty matrix rings over division rings. -/
noncomputable def matrixFamilyEquiv :
    ProjectiveClass (∀ i, Matrix (κ i) (κ i) (D i)) ≃+ (ι → ℕ) :=
  (piEquiv (fun i ↦ Matrix (κ i) (κ i) (D i))).trans
    (AddEquiv.piCongrRight fun i ↦
      (matrixEquiv (D i) (κ i)).symm.trans (finrankEquiv (D i)))

/-- A coordinate is the dimension of the inverse matrix class of the
corresponding scalar extension. -/
@[simp]
theorem matrixFamilyEquiv_apply
    (a : ProjectiveClass (∀ i, Matrix (κ i) (κ i) (D i))) (i : ι) :
    matrixFamilyEquiv D κ a i =
      finrankEquiv (D i) ((matrixEquiv (D i) (κ i)).symm
        (map (Pi.evalRingHom (fun j ↦ Matrix (κ j) (κ j) (D j)) i) a)) := rfl

/-- Reassembly first realizes every natural coordinate over its division ring,
then applies the matrix equivalences and the inverse product equivalence. -/
theorem matrixFamilyEquiv_symm_apply (n : ι → ℕ) :
    (matrixFamilyEquiv D κ).symm n =
      (piEquiv (fun i ↦ Matrix (κ i) (κ i) (D i))).symm
        (fun i ↦ matrixEquiv (D i) (κ i) ((finrankEquiv (D i)).symm (n i))) := rfl

/-- The natural coordinates detect equality of projective classes. -/
theorem eq_iff_matrixFamilyEquiv_eq
    (a b : ProjectiveClass (∀ i, Matrix (κ i) (κ i) (D i))) :
    a = b ↔ ∀ i, matrixFamilyEquiv D κ a i = matrixFamilyEquiv D κ b i := by
  constructor
  · rintro rfl i
    rfl
  · intro h
    exact (matrixFamilyEquiv D κ).injective (funext h)

/-- Every natural coordinate family is realized by exactly one projective class. -/
theorem existsUnique_matrixFamilyEquiv (n : ι → ℕ) :
    ∃! a, matrixFamilyEquiv D κ a = n := by
  refine ⟨(matrixFamilyEquiv D κ).symm n,
    (matrixFamilyEquiv D κ).apply_symm_apply n, ?_⟩
  intro a ha
  exact (matrixFamilyEquiv D κ).injective
    (ha.trans ((matrixFamilyEquiv D κ).apply_symm_apply n).symm)

/-- The regular right module has one coordinate for each row of each block.
-/
@[simp]
theorem matrixFamilyEquiv_regular (i : ι) :
    matrixFamilyEquiv D κ
        (of (∀ j, Matrix (κ j) (κ j) (D j))
          (∀ j, Matrix (κ j) (κ j) (D j))) i = Fintype.card (κ i) := by
  have hregular := of_eq_of_equiv (∀ j, Matrix (κ j) (κ j) (D j))
    (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ
    (MulOpposite.opLinearEquiv (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ).symm
  rw [matrixFamilyEquiv_apply, ← hregular, map_of_self]
  exact finrankEquiv_matrixEquiv_symm_regular (D i) (κ i)

/-- A free right module of rank `n` has coordinate `n * card (κ i)`.
-/
theorem matrixFamilyEquiv_free (n : ℕ) (i : ι) :
    matrixFamilyEquiv D κ
        (of (∀ j, Matrix (κ j) (κ j) (D j))
          (Fin n → (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ)) i =
      n * Fintype.card (κ i) := by
  rw [of_fin_fun_eq_nsmul]
  have hregular := of_eq_of_equiv (∀ j, Matrix (κ j) (κ j) (D j))
    (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ
    (MulOpposite.opLinearEquiv (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ).symm
  rw [hregular, map_nsmul]
  change n • matrixFamilyEquiv D κ
    (of (∀ j, Matrix (κ j) (κ j) (D j))
      (∀ j, Matrix (κ j) (κ j) (D j))) i = _
  rw [matrixFamilyEquiv_regular, Nat.nsmul_eq_mul]

/-- The projective class with one unit in the chosen block coordinate and
zero in all other coordinates. This definition does not itself identify a
simple module or choose a module representative. -/
noncomputable def matrixFamilyRowClass (i : ι) :
    ProjectiveClass (∀ j, Matrix (κ j) (κ j) (D j)) := by
  classical
  exact (matrixFamilyEquiv D κ).symm (Pi.single i 1)

/-- The row class is characterized as the inverse coordinate unit, not the
regular class of the whole matrix block. -/
theorem matrixFamilyRowClass_eq [DecidableEq ι] (i : ι) :
    matrixFamilyRowClass D κ i = (matrixFamilyEquiv D κ).symm (Pi.single i 1) := by
  unfold matrixFamilyRowClass
  apply congrArg (matrixFamilyEquiv D κ).symm
  funext j
  by_cases h : i = j <;> simp [h]

/-- The coordinates of a row class form the corresponding unit vector. -/
@[simp]
theorem matrixFamilyEquiv_matrixFamilyRowClass [DecidableEq ι] (i : ι) :
    matrixFamilyEquiv D κ (matrixFamilyRowClass D κ i) = Pi.single i 1 := by
  rw [matrixFamilyRowClass_eq, AddEquiv.apply_symm_apply]

/-- A row class is nonzero, including when there is only one block. -/
theorem matrixFamilyRowClass_ne_zero (i : ι) : matrixFamilyRowClass D κ i ≠ 0 := by
  classical
  intro h
  have hi := congrFun (congrArg (matrixFamilyEquiv D κ) h) i
  have impossible : (1 : ℕ) = 0 := by
    simpa only [matrixFamilyEquiv_matrixFamilyRowClass, Pi.single_eq_same,
      map_zero, Pi.zero_apply] using hi
  exact one_ne_zero impossible

end ProjectiveClass

namespace K0

/-- Integer coordinates of K₀ of a finite family of nonempty matrix rings
over division rings, using its existing additive group completion. -/
noncomputable def matrixFamilyEquiv :
    K0 (∀ i, Matrix (κ i) (κ i) (D i)) ≃+ (ι → ℤ) :=
  (piEquiv (fun i ↦ Matrix (κ i) (κ i) (D i))).trans
    (AddEquiv.piCongrRight fun i ↦
      (matrixEquiv (D i) (κ i)).symm.trans (finrankEquiv (D i)))

/-- An integer coordinate is the dimension of the inverse matrix image of
coordinate scalar extension. -/
@[simp]
theorem matrixFamilyEquiv_apply
    (z : K0 (∀ i, Matrix (κ i) (κ i) (D i))) (i : ι) :
    matrixFamilyEquiv D κ z i =
      finrankEquiv (D i) ((matrixEquiv (D i) (κ i)).symm
        (map (Pi.evalRingHom (fun j ↦ Matrix (κ j) (κ j) (D j)) i) z)) := rfl

/-- Integer reassembly uses the inverse dimension, matrix and product
coordinate equivalences, in that order. -/
theorem matrixFamilyEquiv_symm_apply (z : ι → ℤ) :
    (matrixFamilyEquiv D κ).symm z =
      (piEquiv (fun i ↦ Matrix (κ i) (κ i) (D i))).symm
        (fun i ↦ matrixEquiv (D i) (κ i) ((finrankEquiv (D i)).symm (z i))) := rfl

/-- The integer coordinates detect equality of arbitrary K₀ elements. -/
theorem eq_iff_matrixFamilyEquiv_eq
    (z w : K0 (∀ i, Matrix (κ i) (κ i) (D i))) :
    z = w ↔ ∀ i, matrixFamilyEquiv D κ z i = matrixFamilyEquiv D κ w i := by
  constructor
  · rintro rfl i
    rfl
  · intro h
    exact (matrixFamilyEquiv D κ).injective (funext h)

/-- Every integer coordinate family is realized by exactly one K₀ element. -/
theorem existsUnique_matrixFamilyEquiv (z : ι → ℤ) :
    ∃! x, matrixFamilyEquiv D κ x = z := by
  refine ⟨(matrixFamilyEquiv D κ).symm z,
    (matrixFamilyEquiv D κ).apply_symm_apply z, ?_⟩
  intro x hx
  exact (matrixFamilyEquiv D κ).injective
    (hx.trans ((matrixFamilyEquiv D κ).apply_symm_apply z).symm)

/-- Group completion sends natural block coordinates to their integer casts. -/
@[simp]
theorem matrixFamilyEquiv_ofClass
    (a : ProjectiveClass (∀ i, Matrix (κ i) (κ i) (D i))) (i : ι) :
    matrixFamilyEquiv D κ
        (ofClass (∀ j, Matrix (κ j) (κ j) (D j)) a) i =
      (ProjectiveClass.matrixFamilyEquiv D κ a i : ℤ) := by
  simp only [matrixFamilyEquiv_apply, ProjectiveClass.matrixFamilyEquiv_apply,
    map_ofClass, matrixEquiv_symm_ofClass (R := D i) (ι := κ i), finrankEquiv_ofClass]

/-- The regular right-module generator has integer coordinates equal to the
sizes of its matrix blocks. -/
@[simp]
theorem matrixFamilyEquiv_regular (i : ι) :
    matrixFamilyEquiv D κ
        (of (∀ j, Matrix (κ j) (κ j) (D j))
          (∀ j, Matrix (κ j) (κ j) (D j))) i = (Fintype.card (κ i) : ℤ) := by
  change matrixFamilyEquiv D κ
    (ofClass _ (ProjectiveClass.of _ _)) i = _
  rw [matrixFamilyEquiv_ofClass, ProjectiveClass.matrixFamilyEquiv_regular]

/-- A free rank-`n` right-module generator has `n` times the regular coordinates.
-/
theorem matrixFamilyEquiv_free (n : ℕ) (i : ι) :
    matrixFamilyEquiv D κ
        (of (∀ j, Matrix (κ j) (κ j) (D j))
          (Fin n → (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ)) i =
      ((n * Fintype.card (κ i) : ℕ) : ℤ) := by
  change matrixFamilyEquiv D κ
    (ofClass _ (ProjectiveClass.of _ _)) i = _
  rw [matrixFamilyEquiv_ofClass, ProjectiveClass.matrixFamilyEquiv_free]

/-- Integer coordinates are a linear equivalence for the usual integer action
on the existing additive K₀ group; no scalar action is transported or replaced. -/
noncomputable def matrixFamilyLinearEquiv :
    K0 (∀ i, Matrix (κ i) (κ i) (D i)) ≃ₗ[ℤ] (ι → ℤ) :=
  (matrixFamilyEquiv D κ).toIntLinearEquiv

/-- The integer linear equivalence has the same coordinate function as the
additive equivalence. -/
@[simp]
theorem matrixFamilyLinearEquiv_apply
    (z : K0 (∀ i, Matrix (κ i) (κ i) (D i))) :
    matrixFamilyLinearEquiv D κ z = matrixFamilyEquiv D κ z := rfl

section Basis

/-- The basis of K₀ over the integers obtained by reassembling the standard
coordinate unit vectors. -/
noncomputable def matrixFamilyBasis :
    Module.Basis ι ℤ (K0 (∀ i, Matrix (κ i) (κ i) (D i))) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  exact (Pi.basisFun ℤ ι).map (matrixFamilyLinearEquiv D κ).symm

/-- A basis vector is the inverse image of its integer coordinate unit. -/
theorem matrixFamilyBasis_apply [DecidableEq ι] (i : ι) :
    matrixFamilyBasis D κ i = (matrixFamilyEquiv D κ).symm (Pi.single i 1) := by
  let : Fintype ι := Fintype.ofFinite ι
  simp only [matrixFamilyBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  rfl

/-- Basis vectors have the corresponding unit coordinates. -/
@[simp]
theorem matrixFamilyEquiv_basis [DecidableEq ι] (i : ι) :
    matrixFamilyEquiv D κ (matrixFamilyBasis D κ i) = Pi.single i 1 := by
  rw [matrixFamilyBasis_apply, AddEquiv.apply_symm_apply]

/-- Basis coordinates are precisely the integer matrix-family coordinates. -/
@[simp]
theorem matrixFamilyBasis_repr
    (z : K0 (∀ i, Matrix (κ i) (κ i) (D i))) (i : ι) :
    (matrixFamilyBasis D κ).repr z i = matrixFamilyEquiv D κ z i := by
  let : Fintype ι := Fintype.ofFinite ι
  change (Pi.basisFun ℤ ι).repr ((matrixFamilyLinearEquiv D κ).symm.symm z) i = _
  rw [LinearEquiv.symm_symm, Pi.basisFun_repr, matrixFamilyLinearEquiv_apply]

/-- The image of the projective coordinate-unit class is the corresponding
integer basis vector. -/
theorem matrixFamilyBasis_eq_ofClass (i : ι) :
    matrixFamilyBasis D κ i =
      ofClass (∀ j, Matrix (κ j) (κ j) (D j))
        (ProjectiveClass.matrixFamilyRowClass D κ i) := by
  classical
  apply (matrixFamilyEquiv D κ).injective
  funext j
  rw [matrixFamilyEquiv_ofClass, ProjectiveClass.matrixFamilyEquiv_matrixFamilyRowClass]
  have h := congrFun (matrixFamilyEquiv_basis D κ i) j
  simpa [Pi.single_apply] using h

end Basis

end K0

/-!
## Simple right rows

The supported right rows represent the coordinate unit classes and exhaust
the simple right modules. Their classes form the integer coordinate basis.
-/

/-- Each supported right row is simple over the whole matrix product.
These are the simple right rows in the semisimple K₀ calculation of Weibel's
*The K-book*, Chapter II. -/
theorem matrixBlockModule_simple (i : ι) :
    IsSimpleModule (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ (matrixBlockModule D κ i) := by
  classical
  let A := fun j ↦ Matrix (κ j) (κ j) (D j)
  let p : (∀ j, A j)ᵐᵒᵖ →+* (A i)ᵐᵒᵖ := RingHom.op (Pi.evalRingHom A i)
  let row := ModuleCat.of (A i)ᵐᵒᵖ (κ i → D i)
  have : RingHomSurjective p := ⟨by
    intro a
    refine ⟨MulOpposite.op (Pi.single i a.unop), ?_⟩
    change MulOpposite.op ((Pi.single i a.unop) i) = a
    simp only [Pi.single_eq_same, MulOpposite.op_unop]⟩
  let f : (ModuleCat.restrictScalars p).obj row →ₛₗ[p] row :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hrestricted :
      IsSimpleModule (∀ j, A j)ᵐᵒᵖ ((ModuleCat.restrictScalars p).obj row) :=
    (LinearMap.isSimpleModule_iff_of_bijective f Function.bijective_id).mpr
      (inferInstance : IsSimpleModule (A i)ᵐᵒᵖ (κ i → D i))
  obtain ⟨e⟩ := matrixBlockModule_linearEquiv_row D κ i
  exact e.isSimpleModule_iff.mpr hrestricted

/-- The supported right row represents the corresponding projective
coordinate-unit class, rather than the regular class of its matrix block. -/
theorem matrixBlockModule_class (i : ι) :
    ProjectiveClass.of (∀ j, Matrix (κ j) (κ j) (D j))
        (matrixBlockModule D κ i) = ProjectiveClass.matrixFamilyRowClass D κ i := by
  classical
  rw [ProjectiveClass.matrixFamilyRowClass_eq,
    ProjectiveClass.matrixFamilyEquiv_symm_apply]
  change ProjectiveClass.of (∀ j, Matrix (κ j) (κ j) (D j))
    (ModuleCat.FiniteProjective.pi (fun j ↦ Matrix (κ j) (κ j) (D j))
      (matrixRowFactors D κ i)) = _
  rw [← ProjectiveClass.piEquiv_symm_of_module]
  apply congrArg
    (ProjectiveClass.piEquiv (fun j ↦ Matrix (κ j) (κ j) (D j))).symm
  funext j
  by_cases h : j = i
  · subst j
    rw [Pi.single_eq_same, ProjectiveClass.finrankEquiv_symm_one]
    have hregular : ProjectiveClass.of (D i) (D i) =
        ProjectiveClass.of (D i) (D i)ᵐᵒᵖ :=
      ProjectiveClass.of_eq_of_equiv (D i) (D i)
        (MulOpposite.opLinearEquiv (D i)ᵐᵒᵖ)
    have hfactor : matrixRowFactors D κ i i =
        ⟨(ModuleCat.toRightMatrixModCat.{uD, uκ, uD} (D i) (κ i)).obj
            (ModuleCat.of (D i)ᵐᵒᵖ (D i)),
          ModuleCat.isFiniteProjective_toRightMatrixModCat_obj.{uD, uκ, uD}
            (D i) (κ i) (ModuleCat.of (D i)ᵐᵒᵖ (D i))
            ⟨inferInstance, inferInstance⟩⟩ := by
      apply CategoryTheory.ObjectProperty.FullSubcategory.ext
      exact matrixRowFactors_same D κ i
    rw [hfactor]
    exact (ProjectiveClass.matrixEquiv_of_module (D i) (κ i) (D i)).symm.trans
      (congrArg (ProjectiveClass.matrixEquiv (D i) (κ i)) hregular)
  · rw [matrixRowFactors_of_ne D κ i j h]
    simp only [ProjectiveClass.of_zero, Pi.single_eq_of_ne h, map_zero]

universe uM

private theorem exists_linearEquiv_matrixRow_restrictScalars (M : Type uM)
    [AddCommGroup M] [Module (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ M]
    [IsSimpleModule (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ M] :
    ∃ i, Nonempty
      (M ≃ₗ[(∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ]
        (ModuleCat.restrictScalars
          (RingHom.op (Pi.evalRingHom (fun j ↦ Matrix (κ j) (κ j) (D j)) i))).obj
            (ModuleCat.of (Matrix (κ i) (κ i) (D i))ᵐᵒᵖ (κ i → D i))) := by
  classical
  let A := fun j ↦ Matrix (κ j) (κ j) (D j)
  let X : ModuleCat.{uM} (∀ j, A j)ᵐᵒᵖ := ModuleCat.of _ M
  have : Nontrivial M := IsSimpleModule.nontrivial (∀ j, A j)ᵐᵒᵖ M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  -- Reconstruction detects a nonzero coordinate, even when the index type might be empty.
  obtain ⟨i, hi⟩ : ∃ i, ModuleCat.RightExtension.tmulOne (Pi.evalRingHom A i) m ≠ 0 := by
    by_contra h
    push Not at h
    apply hm
    apply (ModuleCat.RightExtension.eq_iff_pi_tmulOne_eq A X m 0).2
    intro i
    simpa only [map_zero] using h i
  let p : (∀ j, A j)ᵐᵒᵖ →+* (A i)ᵐᵒᵖ := RingHom.op (Pi.evalRingHom A i)
  let N := ModuleCat.of (A i)ᵐᵒᵖ
    (ModuleCat.RightExtension.Obj (Pi.evalRingHom A i) M)
  let NR := (ModuleCat.restrictScalars p).obj N
  let f : M →ₗ[(∀ j, A j)ᵐᵒᵖ] NR :=
    { toFun := ModuleCat.RightExtension.tmulOne (Pi.evalRingHom A i)
      map_add' := (ModuleCat.RightExtension.tmulOne (Pi.evalRingHom A i)).map_add
      map_smul' := fun a x ↦
        (ModuleCat.RightExtension.tmulOne (Pi.evalRingHom A i)).map_smulₛₗ a x }
  have hf0 : f ≠ 0 := by
    intro hf
    exact hi (DFunLike.congr_fun hf m)
  have hsurj : Function.Surjective (Pi.evalRingHom A i) := by
    intro a
    exact ⟨Pi.single i a, by simp⟩
  have hf : Function.Bijective f :=
    ⟨LinearMap.injective_of_ne_zero hf0,
      ModuleCat.RightExtension.tmulOne_surjective (Pi.evalRingHom A i) hsurj⟩
  let : RingHomSurjective p := ⟨fun a ↦
    ⟨MulOpposite.op (Pi.single i a.unop), by
      change MulOpposite.op ((Pi.single i a.unop) i) = a
      simp⟩⟩
  have : IsSimpleModule (A i)ᵐᵒᵖ N :=
    (LinearMap.isSimpleModule_iff_of_bijective
      (ModuleCat.RightExtension.tmulOne (Pi.evalRingHom A i) : M →ₛₗ[p] N) hf).mp
        inferInstance
  have : IsSemisimpleRing (D i) := inferInstance
  have : IsSemisimpleRing (A i)ᵐᵒᵖ := inferInstance
  have : IsSimpleModule (A i)ᵐᵒᵖ (⊤ : Submodule (A i)ᵐᵒᵖ N) :=
    IsSimpleModule.congr Submodule.topEquiv
  obtain ⟨g⟩ := IsSimpleRing.isIsotypicOfType (A i)ᵐᵒᵖ N (κ i → D i)
    (⊤ : Submodule (A i)ᵐᵒᵖ N)
  let e : N ≃ₗ[(A i)ᵐᵒᵖ] (κ i → D i) := Submodule.topEquiv.symm.trans g
  let S := (ModuleCat.restrictScalars p).obj
    (ModuleCat.of (A i)ᵐᵒᵖ (κ i → D i))
  -- Both actions here are the existing scalar restrictions; only the map is rebundled.
  let eR : NR ≃ₗ[(∀ j, A j)ᵐᵒᵖ] S :=
    { __ := e.toAddEquiv
      map_smul' := fun a x ↦ e.map_smul (p a) x }
  exact ⟨i, ⟨(LinearEquiv.ofBijective f hf).trans eR⟩⟩

private theorem matrixBlockModule_index_eq (M : Type uM) [AddCommGroup M]
    [Module (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ M] [Nontrivial M]
    (i j : ι)
    (ei : M ≃ₗ[(∀ k, Matrix (κ k) (κ k) (D k))ᵐᵒᵖ] matrixBlockModule D κ i)
    (ej : M ≃ₗ[(∀ k, Matrix (κ k) (κ k) (D k))ᵐᵒᵖ] matrixBlockModule D κ j) : i = j := by
  classical
  by_contra hij
  let selector : ∀ k, Matrix (κ k) (κ k) (D k) := Pi.single i 1
  have hi (x : matrixBlockModule D κ i) :
      MulOpposite.op selector • x = x := by
    apply funext
    intro k
    rw [matrixBlockModule_smul_apply]
    by_cases hk : k = i
    · subst k
      simp only [selector, Pi.single_eq_same, MulOpposite.op_one, one_smul]
    · have : Subsingleton (matrixRowFactors D κ i k) := by
        rw [matrixRowFactors_of_ne D κ i k hk]
        infer_instance
      exact Subsingleton.elim _ _
  have hj (x : matrixBlockModule D κ j) :
      MulOpposite.op selector • x = 0 := by
    apply funext
    intro k
    rw [matrixBlockModule_smul_apply]
    by_cases hk : k = j
    · subst k
      simp only [selector, Pi.single_eq_of_ne (Ne.symm hij), MulOpposite.op_zero, zero_smul]
      exact (ModuleCat.piRight_zero_apply (fun k ↦ Matrix (κ k) (κ k) (D k))
        (fun k ↦ (matrixRowFactors D κ j k).obj) j).symm
    · have : Subsingleton (matrixRowFactors D κ j k) := by
        rw [matrixRowFactors_of_ne D κ j k hk]
        infer_instance
      exact Subsingleton.elim _ _
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hm1 : MulOpposite.op selector • m = m := by
    apply ei.injective
    rw [ei.map_smul, hi]
  have hm0 : MulOpposite.op selector • m = 0 := by
    apply ej.injective
    rw [ej.map_smul, hj, ej.map_zero]
  exact hm (hm1.symm.trans hm0)

/-- Every simple right module over the matrix product is isomorphic to
exactly one supported right row, independently of its carrier universe.
For an empty outer family this asserts that there are no simple modules. -/
theorem existsUnique_matrixBlockModule (M : Type uM) [AddCommGroup M]
    [Module (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ M]
    [IsSimpleModule (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ M] :
    ∃! i, Nonempty
      (M ≃ₗ[(∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ] matrixBlockModule D κ i) := by
  have : Nontrivial M :=
    IsSimpleModule.nontrivial (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ M
  obtain ⟨i, ⟨e⟩⟩ := exists_linearEquiv_matrixRow_restrictScalars D κ M
  obtain ⟨erow⟩ := matrixBlockModule_linearEquiv_row D κ i
  let ei := e.trans erow.symm
  refine ⟨i, ⟨ei⟩, ?_⟩
  rintro j ⟨ej⟩
  exact matrixBlockModule_index_eq D κ M j i ej ei

/-- The integer coordinate basis is the family of K₀ generators of the
simple supported right rows. This identifies the basis with module classes,
not merely with an abstract free additive group. -/
theorem K0.matrixFamilyBasis_eq_row (i : ι) :
    K0.matrixFamilyBasis D κ i =
      K0.of (∀ j, Matrix (κ j) (κ j) (D j)) (matrixBlockModule D κ i) := by
  rw [K0.matrixFamilyBasis_eq_ofClass, ← matrixBlockModule_class, K0.ofClass_of]

end KTheory
