/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Semisimple
public import ProjectiveModules.KTheory.ModuleEquivalence
public import ProjectiveModules.RingTheory.Semisimple
import ProjectiveModules.Category.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Simple right-module coordinates along a matrix decomposition

Let `e : R ≃+* ∀ i, Matrix (κ i) (κ i) (D i)` be a chosen ring decomposition,
with finite outer index `ι` and `Fintype` and `DecidableEq` instances on each
matrix index `κ i`. Right `R`-modules are expressed as left `Rᵐᵒᵖ`-modules.
The ring, coefficient, outer-index and matrix-index universes are independent.

## Supported right rows

`KTheory.matrixBlockModuleOfRingEquiv D κ e i` is a finite-projective right
`R`-module, obtained by restricting a lifted supported matrix row along `e.op`.
Its selected factor is the row `κ i → D i`; all other factors are zero.
The selected row is multiplied on the right by the matrix `e r i`, with
coefficients in the order `∑ k, x k * (e r i) k j` at entry `j`.
`KTheory.matrixBlockModuleOfRingEquiv_smul_down` describes this action after
forgetting the carrier lift.

The row construction requires only coefficient rings and allows empty matrix
indices. If the selected `κ i` is nonempty,
`KTheory.matrixBlockModuleOfRingEquiv_end` gives a ring isomorphism between
`D i` and the row's right-linear endomorphism ring, as a `Nonempty` assertion.
The coefficient ring is not replaced by its opposite; the other matrix indices
need not be nonempty for this assertion.

## Coordinates and simple modules

For division-ring coefficients and nonempty matrix indices,
`KTheory.ProjectiveClass.matrixFamilyEquivOfRingEquiv` and
`KTheory.K0.matrixFamilyEquivOfRingEquiv` give additive equivalences with
`ι → ℕ` and `ι → ℤ`, respectively. They use the module-category equivalence
from restriction of scalars along `e.op.symm`. The completion map casts each
natural coordinate to an integer.

The supported right rows are simple, and
`KTheory.existsUnique_matrixBlockModuleOfRingEquiv` classifies every simple
right module by a unique block index. Its carrier universe is arbitrary and
independent of all decomposition universes; no finite-generation or projectivity
hypothesis on that simple module is required. The row classes are the natural
coordinate units, and `KTheory.K0.matrixFamilyBasisOfRingEquiv` is a basis whose
vectors are their K₀ generators, using the usual integer action on K₀.
The regular right module has coordinate `Fintype.card (κ i)` in each block,
not the square of that cardinal.

For example, in `ℚ × Matrix (Fin 2) (Fin 2) ℚ`, the supported rows have
coordinates `(1, 0)` and `(0, 1)`, while the regular class has coordinates
`(1, 2)`. The same unit vectors form the integer K₀ basis, and the regular K₀
generator is the first basis vector plus twice the second.

## Semisimple rings and scope

`IsSemisimpleRing.matrixDivisionDecomposition_simple_basis` assembles the
simple-row, endomorphism-ring, row-class, basis and regular-coordinate statements
for `MatrixDivisionDecomposition.ofIsSemisimpleRing R`. This decomposition is
chosen from Mathlib's Wedderburn–Artin theorem, with coefficient rings in the
universe of `R`; it is not an additional hypothesis on a semisimple ring.

The outer family may be empty. Its coefficient product, and hence `R`, is then
a zero ring: there are no simple right modules, both coordinate types are
singletons, and the integer basis is empty. No commutativity or `Small`
hypothesis is imposed. The integer basis is a basis of K₀, not an assertion
that all projective right `R`-modules are free.

## References and credits

* Charles A. Weibel, *The K-book*, Chapter II: semisimple projective classes and
  the basis of K₀ given by simple right modules.
* Mathlib's Wedderburn–Artin theorem, restriction of scalars and integer bases.
* Projective Modules' finite-projective preservation, module-equivalence
  transport, finite-product, right matrix and division-ring coordinate APIs.
-/

@[expose] public section

universe uR uι uκ uD uM uN

namespace KTheory

variable {R : Type uR} [Ring R] {ι : Type uι}
variable (D : ι → Type uD) (κ : ι → Type uκ)

section RowData

variable [∀ i, Ring (D i)] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  [Finite ι]
variable (e : R ≃+* ∀ i, Matrix (κ i) (κ i) (D i))

/-- The supported right row over `R`, obtained by restriction of scalars along
the chosen matrix decomposition. The carrier lift puts both scalar rings and
this module in one supported module-category universe. -/
noncomputable def matrixBlockModuleOfRingEquiv (i : ι) :
    ModuleCat.FiniteProjective.{uR, max uR (max uι (max uκ uD))} Rᵐᵒᵖ :=
  ⟨(ModuleCat.restrictScalars.{max uR (max uι (max uκ uD))} e.op.toRingHom).obj
      (ModuleCat.of.{max uR (max uι (max uκ uD))}
        (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ
        (ULift.{uR} (matrixBlockModule D κ i))),
    ModuleCat.isFiniteProjective_of_equivalence.{max uι (max uκ uD), uR,
      max uR (max uι (max uκ uD)), max uι (max uκ uD)}
      (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ Rᵐᵒᵖ
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.op)
      (ModuleCat.of.{max uR (max uι (max uκ uD))}
        (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ
        (ULift.{uR} (matrixBlockModule D κ i)))
      ⟨inferInstance, inferInstance⟩⟩

/-- The underlying object is Mathlib's restriction of the lifted supported row. -/
@[simp]
theorem matrixBlockModuleOfRingEquiv_obj (i : ι) :
    (matrixBlockModuleOfRingEquiv D κ e i).obj =
      (ModuleCat.restrictScalars.{max uR (max uι (max uκ uD))} e.op.toRingHom).obj
        (ModuleCat.of.{max uR (max uι (max uκ uD))}
          (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ
          (ULift.{uR} (matrixBlockModule D κ i))) := rfl

/-- Restriction leaves the lifted row carrier unchanged. -/
@[simp]
theorem matrixBlockModuleOfRingEquiv_carrier (i : ι) :
    (matrixBlockModuleOfRingEquiv D κ e i : Type (max uR (max uι (max uκ uD)))) =
      ULift.{uR} (matrixBlockModule D κ i) := rfl

/-- The right action is the supported row action evaluated at the chosen
ring equivalence. No new action on the row carrier is installed. -/
@[simp]
theorem matrixBlockModuleOfRingEquiv_smul_down (i : ι) (r : R)
    (x : matrixBlockModuleOfRingEquiv D κ e i) :
    (MulOpposite.op r • x).down = MulOpposite.op (e r) • x.down := rfl

/-- The transported supported row is semilinearly equivalent along `e.op` to
its coefficient-product row. The maps are `ULift.down` and `ULift.up`, using
Mathlib's `ULift.moduleEquiv` for the underlying additive equivalence.
The maps are available through `LinearEquiv.toFun` and
`LinearEquiv.toAddEquiv` followed by `AddEquiv.invFun`. -/
noncomputable def matrixBlockModuleOfRingEquivLinearEquivRow
    (e : R ≃+* ∀ i, Matrix (κ i) (κ i) (D i)) (i : ι) :
    @LinearEquiv Rᵐᵒᵖ (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ _ _
      e.op.toRingHom e.op.symm.toRingHom
      (RingHomInvPair.of_ringEquiv e.op) (RingHomInvPair.of_ringEquiv_symm e.op)
      (matrixBlockModuleOfRingEquiv D κ e i) (matrixBlockModule D κ i) _ _ _ _ := by
  let : RingHomInvPair e.op.toRingHom e.op.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e.op
  let : RingHomInvPair e.op.symm.toRingHom e.op.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm e.op
  exact
    { __ := (ULift.moduleEquiv :
        ULift.{uR} (matrixBlockModule D κ i) ≃ₗ[(∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ]
          matrixBlockModule D κ i).toAddEquiv
      map_smul' := fun r x ↦ by
        change (r • x).down = e.op r • x.down
        simpa only [RingEquiv.op_apply_apply, MulOpposite.op_unop] using
          matrixBlockModuleOfRingEquiv_smul_down D κ e i r.unop x }

/-- The forward row comparison removes the carrier lift. -/
@[simp]
theorem matrixBlockModuleOfRingEquivLinearEquivRow_apply (i : ι)
    (x : matrixBlockModuleOfRingEquiv D κ e i) :
    (matrixBlockModuleOfRingEquivLinearEquivRow D κ (e := e) i).toFun x = x.down := rfl

/-- The inverse row comparison restores the carrier lift. -/
@[simp]
theorem matrixBlockModuleOfRingEquivLinearEquivRow_symm_apply (i : ι)
    (x : matrixBlockModule D κ i) :
    (@LinearEquiv.toAddEquiv Rᵐᵒᵖ (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ _ _
      e.op.toRingHom e.op.symm.toRingHom
      (RingHomInvPair.of_ringEquiv e.op) (RingHomInvPair.of_ringEquiv_symm e.op)
      (matrixBlockModuleOfRingEquiv D κ e i) (matrixBlockModule D κ i) _ _ _ _
      (matrixBlockModuleOfRingEquivLinearEquivRow D κ (e := e) i)).invFun x =
      ULift.up x := rfl

/-- The endomorphism ring of a transported supported right matrix row is
isomorphic to its coefficient ring, not the opposite coefficient ring.
Only the selected matrix index must be nonempty: an empty row is zero, so
its endomorphism ring cannot recover a nonzero coefficient ring.

The matrix-row/Morita approach adapts Projective Modules' finite matrix-family
construction and Mathlib's restriction-of-scalars transport. Weibel,
*The K-book*, II.2.1.4 provides the division-coefficient matrix-block context;
the statement here extends that context to coefficient rings. -/
theorem matrixBlockModuleOfRingEquiv_end (i : ι) [Nonempty (κ i)] :
    Nonempty (D i ≃+* Module.End Rᵐᵒᵖ (matrixBlockModuleOfRingEquiv D κ e i)) := by
  classical
  let A := fun j ↦ Matrix (κ j) (κ j) (D j)
  let row := ModuleCat.of (A i)ᵐᵒᵖ (κ i → D i)
  let p : (∀ j, A j)ᵐᵒᵖ →+* (A i)ᵐᵒᵖ := RingHom.op (Pi.evalRingHom A i)
  have hp : Function.Surjective p := by
    intro a
    refine ⟨MulOpposite.op (Pi.single i a.unop), ?_⟩
    change MulOpposite.op ((Pi.single i a.unop) i) = a
    simp only [Pi.single_eq_same, MulOpposite.op_unop]
  let f : D i ≃+* Module.End (A i)ᵐᵒᵖ row :=
    (RingEquiv.moduleEndSelfOp (R := D i)).trans
      ((ModuleCat.toRightMatrixModCatEndEquiv.{uD, uκ, uD}
        (D i) (κ i) (Classical.arbitrary (κ i)) (ModuleCat.of (D i)ᵐᵒᵖ (D i))).trans
        (ModuleCat.toRightMatrixModCatRegularLinearEquiv (D i) (κ i)).conjRingEquiv)
  let g := matrixBlockModuleLinearEquivRow D κ i
  let h : D i ≃+* Module.End (∀ j, A j)ᵐᵒᵖ (matrixBlockModule D κ i) :=
    f.trans ((ModuleCat.restrictScalarsEndEquiv p hp row).trans g.symm.conjRingEquiv)
  let l : ULift.{uR} (matrixBlockModule D κ i) ≃ₗ[(∀ j, A j)ᵐᵒᵖ]
      matrixBlockModule D κ i := ULift.moduleEquiv
  exact ⟨(h.trans l.symm.conjRingEquiv).trans
    (ModuleCat.restrictScalarsEndEquiv e.op.toRingHom e.op.surjective
      (ModuleCat.of.{max uR (max uι (max uκ uD))} (∀ j, A j)ᵐᵒᵖ
        (ULift.{uR} (matrixBlockModule D κ i))))⟩

end RowData

variable [∀ i, DivisionRing (D i)] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  [∀ i, Nonempty (κ i)] [Finite ι]
variable (e : R ≃+* ∀ i, Matrix (κ i) (κ i) (D i))

namespace ProjectiveClass

/-- Natural projective-class coordinates along a chosen finite matrix-ring
decomposition. The forward transport restricts scalars along `e.op.symm`. -/
noncomputable def matrixFamilyEquivOfRingEquiv : ProjectiveClass R ≃+ (ι → ℕ) :=
  (equivOfModuleEquivalence.{uR, max uι (max uκ uD), max uι (max uκ uD), uR}
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.op.symm)).trans
    (matrixFamilyEquiv D κ)

/-- Coordinates are those of the existing module-equivalence transport. -/
@[simp]
theorem matrixFamilyEquivOfRingEquiv_apply (a : ProjectiveClass R) :
    matrixFamilyEquivOfRingEquiv D κ e a =
      matrixFamilyEquiv D κ
        (equivOfModuleEquivalence.{uR, max uι (max uκ uD), max uι (max uκ uD), uR}
          (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.op.symm) a) := rfl

/-- Inverse coordinates first reassemble the matrix-family class, then use
inverse module-equivalence transport. -/
theorem matrixFamilyEquivOfRingEquiv_symm_apply (n : ι → ℕ) :
    (matrixFamilyEquivOfRingEquiv D κ e).symm n =
      (equivOfModuleEquivalence.{uR, max uι (max uκ uD), max uι (max uκ uD), uR}
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.op.symm)).symm
        ((matrixFamilyEquiv D κ).symm n) := rfl

/-- The coordinates detect equality of projective classes. -/
theorem eq_iff_matrixFamilyEquivOfRingEquiv_eq (a b : ProjectiveClass R) :
    a = b ↔ ∀ i, matrixFamilyEquivOfRingEquiv D κ e a i =
      matrixFamilyEquivOfRingEquiv D κ e b i := by
  constructor
  · rintro rfl i
    rfl
  · intro h
    exact (matrixFamilyEquivOfRingEquiv D κ e).injective (funext h)

/-- Each natural coordinate tuple has exactly one projective class. -/
theorem existsUnique_matrixFamilyEquivOfRingEquiv (n : ι → ℕ) :
    ∃! a, matrixFamilyEquivOfRingEquiv D κ e a = n := by
  refine ⟨(matrixFamilyEquivOfRingEquiv D κ e).symm n,
    (matrixFamilyEquivOfRingEquiv D κ e).apply_symm_apply n, ?_⟩
  intro a ha
  exact (matrixFamilyEquivOfRingEquiv D κ e).injective
    (ha.trans ((matrixFamilyEquivOfRingEquiv D κ e).apply_symm_apply n).symm)

/-- Finite-projective right modules in independent carrier universes are
isomorphic exactly when all their chosen natural coordinates agree. -/
theorem nonempty_linearEquiv_iff_matrixFamilyEquivOfRingEquiv_eq
    (M : Type uM) (N : Type uN) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    Nonempty (M ≃ₗ[Rᵐᵒᵖ] N) ↔
      ∀ i, matrixFamilyEquivOfRingEquiv D κ e (of R M) i =
        matrixFamilyEquivOfRingEquiv D κ e (of R N) i := by
  rw [← of_eq_iff R M N, eq_iff_matrixFamilyEquivOfRingEquiv_eq D κ e]

/-- The identity ring decomposition recovers the original finite-family
coordinates. This is only an identity boundary, not a simple-module assertion. -/
@[simp]
theorem matrixFamilyEquivOfRingEquiv_refl :
    matrixFamilyEquivOfRingEquiv D κ
        (RingEquiv.refl (∀ i, Matrix (κ i) (κ i) (D i))) = matrixFamilyEquiv D κ := by
  have h := equivOfModuleEquivalence_congr
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (RingEquiv.refl (∀ i, Matrix (κ i) (κ i) (D i))).op.symm)
    (CategoryTheory.Equivalence.refl
      (C := ModuleCat.{max uι (max uκ uD)} (∀ i, Matrix (κ i) (κ i) (D i))ᵐᵒᵖ))
    (ModuleCat.restrictScalarsId (∀ i, Matrix (κ i) (κ i) (D i))ᵐᵒᵖ)
  rw [equivOfModuleEquivalence_refl] at h
  apply AddEquiv.ext
  intro a
  rw [matrixFamilyEquivOfRingEquiv_apply, h, AddEquiv.refl_apply]

end ProjectiveClass

namespace K0

/-- Integer K₀ coordinates along a chosen finite matrix-ring decomposition,
using the existing module-equivalence map and group completion. -/
noncomputable def matrixFamilyEquivOfRingEquiv : K0 R ≃+ (ι → ℤ) :=
  (equivOfModuleEquivalence.{uR, max uι (max uκ uD), max uι (max uκ uD), uR}
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.op.symm)).trans
    (matrixFamilyEquiv D κ)

/-- The whole forward coordinate function uses the existing transport. -/
@[simp]
theorem matrixFamilyEquivOfRingEquiv_apply (z : K0 R) :
    matrixFamilyEquivOfRingEquiv D κ e z =
      matrixFamilyEquiv D κ
        (equivOfModuleEquivalence.{uR, max uι (max uκ uD), max uι (max uκ uD), uR}
          (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.op.symm) z) := rfl

/-- Inverse integer coordinates reassemble and transport back to `R`. -/
theorem matrixFamilyEquivOfRingEquiv_symm_apply (z : ι → ℤ) :
    (matrixFamilyEquivOfRingEquiv D κ e).symm z =
      (equivOfModuleEquivalence.{uR, max uι (max uκ uD), max uι (max uκ uD), uR}
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.op.symm)).symm
        ((matrixFamilyEquiv D κ).symm z) := rfl

/-- The integer coordinates detect equality of K₀ elements. -/
theorem eq_iff_matrixFamilyEquivOfRingEquiv_eq (z w : K0 R) :
    z = w ↔ ∀ i, matrixFamilyEquivOfRingEquiv D κ e z i =
      matrixFamilyEquivOfRingEquiv D κ e w i := by
  constructor
  · rintro rfl i
    rfl
  · intro h
    exact (matrixFamilyEquivOfRingEquiv D κ e).injective (funext h)

/-- Each integer coordinate tuple has exactly one K₀ element. -/
theorem existsUnique_matrixFamilyEquivOfRingEquiv (z : ι → ℤ) :
    ∃! x, matrixFamilyEquivOfRingEquiv D κ e x = z := by
  refine ⟨(matrixFamilyEquivOfRingEquiv D κ e).symm z,
    (matrixFamilyEquivOfRingEquiv D κ e).apply_symm_apply z, ?_⟩
  intro x hx
  exact (matrixFamilyEquivOfRingEquiv D κ e).injective
    (hx.trans ((matrixFamilyEquivOfRingEquiv D κ e).apply_symm_apply z).symm)

/-- The completion square commutes in every chosen block coordinate. -/
@[simp]
theorem matrixFamilyEquivOfRingEquiv_ofClass (a : ProjectiveClass R) (i : ι) :
    matrixFamilyEquivOfRingEquiv D κ e (ofClass R a) i =
      (ProjectiveClass.matrixFamilyEquivOfRingEquiv D κ e a i : ℤ) := by
  rw [matrixFamilyEquivOfRingEquiv_apply, equivOfModuleEquivalence_ofClass,
    matrixFamilyEquiv_ofClass, ProjectiveClass.matrixFamilyEquivOfRingEquiv_apply]

/-- The integer basis transported from the finite matrix family. The linear
equivalence is the inverse additive transport with the usual integer action. -/
noncomputable def matrixFamilyBasisOfRingEquiv : Module.Basis ι ℤ (K0 R) :=
  (matrixFamilyBasis D κ).map
    (equivOfModuleEquivalence.{uR, max uι (max uκ uD), max uι (max uκ uD), uR}
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.op.symm)).symm.toIntLinearEquiv

/-- Each basis vector is the inverse image of its integer coordinate unit. -/
theorem matrixFamilyBasisOfRingEquiv_apply [DecidableEq ι] (i : ι) :
    matrixFamilyBasisOfRingEquiv D κ e i =
      (matrixFamilyEquivOfRingEquiv D κ e).symm (Pi.single i 1) := by
  rw [matrixFamilyBasisOfRingEquiv, Module.Basis.map_apply, matrixFamilyBasis_apply,
    matrixFamilyEquivOfRingEquiv_symm_apply]
  rfl

/-- The transported basis vectors have the standard unit coordinates. -/
@[simp]
theorem matrixFamilyEquivOfRingEquiv_basis [DecidableEq ι] (i : ι) :
    matrixFamilyEquivOfRingEquiv D κ e (matrixFamilyBasisOfRingEquiv D κ e i) =
      Pi.single i 1 := by
  rw [matrixFamilyBasisOfRingEquiv_apply, AddEquiv.apply_symm_apply]

/-- Basis representation is precisely the chosen integer coordinate function. -/
@[simp]
theorem matrixFamilyBasisOfRingEquiv_repr (z : K0 R) (i : ι) :
    (matrixFamilyBasisOfRingEquiv D κ e).repr z i =
      matrixFamilyEquivOfRingEquiv D κ e z i := by
  change (matrixFamilyBasis D κ).repr
    ((equivOfModuleEquivalence.{uR, max uι (max uκ uD), max uι (max uκ uD), uR}
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.op.symm)).symm.toIntLinearEquiv.symm
      z) i = _
  rw [matrixFamilyBasis_repr]
  rfl

/-- The identity ring decomposition recovers the original integer coordinates. -/
@[simp]
theorem matrixFamilyEquivOfRingEquiv_refl :
    matrixFamilyEquivOfRingEquiv D κ
        (RingEquiv.refl (∀ i, Matrix (κ i) (κ i) (D i))) = matrixFamilyEquiv D κ := by
  have h := equivOfModuleEquivalence_congr
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (RingEquiv.refl (∀ i, Matrix (κ i) (κ i) (D i))).op.symm)
    (CategoryTheory.Equivalence.refl
      (C := ModuleCat.{max uι (max uκ uD)} (∀ i, Matrix (κ i) (κ i) (D i))ᵐᵒᵖ))
    (ModuleCat.restrictScalarsId (∀ i, Matrix (κ i) (κ i) (D i))ᵐᵒᵖ)
  rw [equivOfModuleEquivalence_refl] at h
  apply AddEquiv.ext
  intro z
  rw [matrixFamilyEquivOfRingEquiv_apply, h, AddEquiv.refl_apply]

end K0

/-!
## Simple right rows and regular classes

The supported right rows classify simple modules. Their projective classes
are the coordinate units, and their K₀ generators give the integer basis.
The regular module has the size of each matrix block as its coordinate.
-/

/-- Each transported supported right row over division-ring coefficients is simple.

This formulation adapts Projective Modules' finite matrix-family row construction
with Mathlib's restriction-of-scalars transport, following the matrix-block
description of Weibel, *The K-book*, II.2.1.4. -/
theorem matrixBlockModuleOfRingEquiv_simple (i : ι) :
    IsSimpleModule Rᵐᵒᵖ (matrixBlockModuleOfRingEquiv D κ e i) := by
  let A := ∀ j, Matrix (κ j) (κ j) (D j)
  let X : ModuleCat.{max uR (max uι (max uκ uD))} Aᵐᵒᵖ :=
    ModuleCat.of _ (ULift.{uR} (matrixBlockModule D κ i))
  have hX : IsSimpleModule Aᵐᵒᵖ X :=
    (ULift.moduleEquiv :
      ULift.{uR} (matrixBlockModule D κ i) ≃ₗ[Aᵐᵒᵖ]
        matrixBlockModule D κ i).isSimpleModule_iff.mpr (matrixBlockModule_simple D κ i)
  let : RingHomSurjective e.op.toRingHom := ⟨e.op.surjective⟩
  -- The identity map compares the restricted and original lifted actions.
  let f : matrixBlockModuleOfRingEquiv D κ e i →ₛₗ[e.op.toRingHom] X :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact (LinearMap.isSimpleModule_iff_of_bijective f Function.bijective_id).mpr hX

/-- A transported right row has the natural coordinate unit as its projective class.

The simple-class description is Weibel, *The K-book*, II.2.1.4; this formulation
adapts Projective Modules' `ProjectiveClass.matrixFamilyEquiv` coordinates via
`ProjectiveClass.equivOfModuleEquivalence`. -/
theorem matrixBlockModuleOfRingEquiv_class [DecidableEq ι] (i : ι) :
    ProjectiveClass.matrixFamilyEquivOfRingEquiv D κ e
      (ProjectiveClass.of R (matrixBlockModuleOfRingEquiv D κ e i)) = Pi.single i 1 := by
  let A := ∀ j, Matrix (κ j) (κ j) (D j)
  let E : CategoryTheory.Equivalence
      (ModuleCat.{max uR (max uι (max uκ uD))} Rᵐᵒᵖ)
      (ModuleCat.{max uR (max uι (max uκ uD))} Aᵐᵒᵖ) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.op.symm
  let Y : ModuleCat.FiniteProjective.{max uι (max uκ uD),
      max uR (max uι (max uκ uD))} Aᵐᵒᵖ :=
    ModuleCat.FiniteProjective.of _ (ULift.{uR} (matrixBlockModule D κ i))
  -- Inverse transport is the defining restriction of the lifted row.
  have htransport :
      (ProjectiveClass.equivOfModuleEquivalence.{uR, max uι (max uκ uD),
        max uι (max uκ uD), uR} E).symm
          (ProjectiveClass.of A (matrixBlockModule D κ i)) =
        ProjectiveClass.of R (matrixBlockModuleOfRingEquiv D κ e i) := by
    have hY : ProjectiveClass.of A Y =
        ProjectiveClass.of A (matrixBlockModule D κ i) :=
      ProjectiveClass.of_ulift A (matrixBlockModule D κ i)
    have hEY : ModuleCat.isFiniteProjective Rᵐᵒᵖ (E.symm.functor.obj Y.obj) :=
      ModuleCat.isFiniteProjective_of_equivalence.{max uι (max uκ uD), uR,
        max uR (max uι (max uκ uD)), max uι (max uκ uD)}
        Aᵐᵒᵖ Rᵐᵒᵖ E.symm Y.obj Y.property
    let : Module.Finite Rᵐᵒᵖ (E.symm.functor.obj Y.obj) := hEY.1
    let : Module.Projective Rᵐᵒᵖ (E.symm.functor.obj Y.obj) := hEY.2
    have h := ProjectiveClass.equivOfModuleEquivalence_symm_of.{uR,
      max uι (max uκ uD), max uι (max uκ uD), uR} E Y
    rw [hY] at h
    exact h.trans (ProjectiveClass.of_eq_of_equiv R _
      (LinearEquiv.refl Rᵐᵒᵖ (matrixBlockModuleOfRingEquiv D κ e i)))
  rw [ProjectiveClass.matrixFamilyEquivOfRingEquiv_apply, ← htransport,
    AddEquiv.apply_symm_apply, matrixBlockModule_class,
    ProjectiveClass.matrixFamilyEquiv_matrixFamilyRowClass]

/-- Every simple right module, in any carrier universe, is isomorphic to
exactly one transported supported row. The unique datum is the block index,
not the linear equivalence; no finite-generation hypothesis on `M` is needed.
An empty outer family has no simple right modules.

The semisimple classification is described in Weibel, *The K-book*, II.2.1.4.
This formulation adapts Projective Modules' finite matrix-family rows with
Mathlib's restriction-of-scalars transport, extending that description to
independent carrier universes and the empty outer family. -/
theorem existsUnique_matrixBlockModuleOfRingEquiv (M : Type uM) [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [IsSimpleModule Rᵐᵒᵖ M] :
    ∃! i, Nonempty (M ≃ₗ[Rᵐᵒᵖ] matrixBlockModuleOfRingEquiv D κ e i) := by
  let A := ∀ j, Matrix (κ j) (κ j) (D j)
  let X : ModuleCat.{uM} Aᵐᵒᵖ :=
    (ModuleCat.restrictScalars e.op.symm.toRingHom).obj (ModuleCat.of Rᵐᵒᵖ M)
  let : RingHomInvPair e.op.toRingHom e.op.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e.op
  let : RingHomInvPair e.op.symm.toRingHom e.op.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm e.op
  -- The inverse scalar restriction has the same carrier, with the canonical action.
  let mEquiv : M ≃ₛₗ[e.op.toRingHom] X :=
    { __ := AddEquiv.refl M
      map_smul' := fun r x ↦ by
        exact ((ModuleCat.restrictScalars.smul_def e.op.symm.toRingHom
          (M := ModuleCat.of Rᵐᵒᵖ M) (e.op r) x).trans
          (congrArg (fun s : Rᵐᵒᵖ ↦ s • x) (e.op.symm_apply_apply r))).symm }
  let : IsSimpleModule Aᵐᵒᵖ X :=
    (LinearMap.isSimpleModule_iff_of_bijective mEquiv.toLinearMap
      mEquiv.bijective).mp inferInstance
  obtain ⟨i, ⟨g⟩, huni⟩ := existsUnique_matrixBlockModule D κ X
  refine ⟨i, ⟨?_⟩, ?_⟩
  · exact (mEquiv.trans g : M ≃ₛₗ[e.op.toRingHom] matrixBlockModule D κ i).trans
      (matrixBlockModuleOfRingEquivLinearEquivRow D κ (e := e) i).symm
  · rintro j ⟨h⟩
    apply huni j
    exact ⟨mEquiv.symm.trans
      (h.trans (matrixBlockModuleOfRingEquivLinearEquivRow D κ (e := e) j) :
        M ≃ₛₗ[e.op.toRingHom] matrixBlockModule D κ j)⟩

/-- The integer K₀ basis consists of the generators of the transported
simple right rows, with the usual integer action on K₀.

This formulation adapts Projective Modules' `K0.matrixFamilyBasis` and
`K0.equivOfModuleEquivalence` for the simple-right-module ℤ-basis described in
Weibel, *The K-book*, II.2.1.4. -/
theorem K0.matrixFamilyBasisOfRingEquiv_eq_row (i : ι) :
    K0.matrixFamilyBasisOfRingEquiv D κ e i =
      K0.of R (matrixBlockModuleOfRingEquiv D κ e i) := by
  classical
  apply (K0.matrixFamilyEquivOfRingEquiv D κ e).injective
  funext j
  rw [K0.matrixFamilyEquivOfRingEquiv_basis, ← K0.ofClass_of,
    K0.matrixFamilyEquivOfRingEquiv_ofClass, matrixBlockModuleOfRingEquiv_class]
  simp [Pi.single_apply]

/-- The regular right module has coordinate `Fintype.card (κ i)` in block
`i`, not the square of that cardinal. No nontriviality hypothesis on `R` or
nonempty-outer-family hypothesis is required.

The block-size reading is Weibel, *The K-book*, II.2.1.2, applied factorwise to
the finite-product picture of II.2.1.4. This formulation adapts Projective
Modules' finite matrix-family coordinates via
`ProjectiveClass.equivOfModuleEquivalence`. -/
theorem ProjectiveClass.matrixFamilyEquivOfRingEquiv_regular (i : ι) :
    ProjectiveClass.matrixFamilyEquivOfRingEquiv D κ e (ProjectiveClass.of R R) i =
      Fintype.card (κ i) := by
  let A := ∀ j, Matrix (κ j) (κ j) (D j)
  have hR : ProjectiveClass.of R R = ProjectiveClass.of R Rᵐᵒᵖ :=
    ProjectiveClass.of_eq_of_equiv R R (MulOpposite.opLinearEquiv Rᵐᵒᵖ)
  have hA : ProjectiveClass.of A Aᵐᵒᵖ = ProjectiveClass.of A A :=
    ProjectiveClass.of_eq_of_equiv A Aᵐᵒᵖ (MulOpposite.opLinearEquiv Aᵐᵒᵖ).symm
  have hop : e.op.symm = e.symm.op := by
    ext r
    simp only [RingEquiv.op_apply_symm_apply, RingEquiv.op_apply_apply]
  rw [ProjectiveClass.matrixFamilyEquivOfRingEquiv_apply, hR, hop,
    ProjectiveClass.equivOfModuleEquivalence_restrictScalars_regular e.symm,
    hA, ProjectiveClass.matrixFamilyEquiv_regular]

/-- The regular K₀ generator has integer block-size coordinates, the casts
of the natural coordinates of the projective regular class. -/
theorem K0.matrixFamilyEquivOfRingEquiv_regular (i : ι) :
    K0.matrixFamilyEquivOfRingEquiv D κ e (K0.of R R) i =
      (Fintype.card (κ i) : ℤ) := by
  change K0.matrixFamilyEquivOfRingEquiv D κ e
    (K0.ofClass R (ProjectiveClass.of R R)) i = _
  rw [K0.matrixFamilyEquivOfRingEquiv_ofClass,
    ProjectiveClass.matrixFamilyEquivOfRingEquiv_regular]

end KTheory

namespace IsSemisimpleRing

variable (R : Type uR) [Ring R] [IsSemisimpleRing R]

/-- The simple right-module classification and integer K₀ basis for the
decomposition `MatrixDivisionDecomposition.ofIsSemisimpleRing` of a semisimple
ring. The outer family may be empty.

The supported right rows are simple and classify simple right modules in any
carrier universe by a unique block index. Their endomorphism rings are
isomorphic to the coefficient division rings. Their projective classes are
the natural coordinate units, and their K₀ generators form the integer basis.
The regular class has block-size coordinates in both calculations.

Weibel, *The K-book*, II.2.1.4 describes the semisimple classification and
simple-right-module ℤ-basis, with regular weights read factorwise from II.2.1.2.
This formulation adapts Projective Modules' finite matrix-family and
module-equivalence constructions. The decomposition uses Mathlib's proved
Wedderburn–Artin input `IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing`.
Independent carrier universes and the empty outer family extend the published
description. -/
theorem matrixDivisionDecomposition_simple_basis :
    let p : MatrixDivisionDecomposition.{uR, uR} R :=
      MatrixDivisionDecomposition.ofIsSemisimpleRing R
    (∀ i, IsSimpleModule Rᵐᵒᵖ
        (KTheory.matrixBlockModuleOfRingEquiv p.coefficient
          (fun j ↦ Fin (p.blockSize j)) p.ringEquiv i)) ∧
      (∀ M : ModuleCat.{uM} Rᵐᵒᵖ, IsSimpleModule Rᵐᵒᵖ M →
        ∃! i, Nonempty (M ≃ₗ[Rᵐᵒᵖ]
          KTheory.matrixBlockModuleOfRingEquiv p.coefficient
            (fun j ↦ Fin (p.blockSize j)) p.ringEquiv i)) ∧
      (∀ i, Nonempty (p.coefficient i ≃+* Module.End Rᵐᵒᵖ
        (KTheory.matrixBlockModuleOfRingEquiv p.coefficient
          (fun j ↦ Fin (p.blockSize j)) p.ringEquiv i))) ∧
      (∀ i, KTheory.ProjectiveClass.matrixFamilyEquivOfRingEquiv p.coefficient
        (fun j ↦ Fin (p.blockSize j)) p.ringEquiv
        (KTheory.ProjectiveClass.of R (KTheory.matrixBlockModuleOfRingEquiv p.coefficient
          (fun j ↦ Fin (p.blockSize j)) p.ringEquiv i)) = Pi.single i 1) ∧
      (∀ i, KTheory.K0.matrixFamilyBasisOfRingEquiv p.coefficient
        (fun j ↦ Fin (p.blockSize j)) p.ringEquiv i =
        KTheory.K0.of R (KTheory.matrixBlockModuleOfRingEquiv p.coefficient
          (fun j ↦ Fin (p.blockSize j)) p.ringEquiv i)) ∧
      (∀ i, KTheory.ProjectiveClass.matrixFamilyEquivOfRingEquiv p.coefficient
        (fun j ↦ Fin (p.blockSize j)) p.ringEquiv
        (KTheory.ProjectiveClass.of R R) i = p.blockSize i) ∧
      (∀ i, KTheory.K0.matrixFamilyEquivOfRingEquiv p.coefficient
        (fun j ↦ Fin (p.blockSize j)) p.ringEquiv
        (KTheory.K0.of R R) i = (p.blockSize i : ℤ)) := by
  classical
  let p : MatrixDivisionDecomposition.{uR, uR} R :=
    MatrixDivisionDecomposition.ofIsSemisimpleRing R
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact KTheory.matrixBlockModuleOfRingEquiv_simple p.coefficient
      (fun j ↦ Fin (p.blockSize j)) p.ringEquiv i
  · intro M hM
    have : IsSimpleModule Rᵐᵒᵖ M := hM
    exact KTheory.existsUnique_matrixBlockModuleOfRingEquiv p.coefficient
      (fun j ↦ Fin (p.blockSize j)) p.ringEquiv M
  · intro i
    exact KTheory.matrixBlockModuleOfRingEquiv_end p.coefficient
      (fun j ↦ Fin (p.blockSize j)) p.ringEquiv i
  · intro i
    exact KTheory.matrixBlockModuleOfRingEquiv_class p.coefficient
      (fun j ↦ Fin (p.blockSize j)) p.ringEquiv i
  · intro i
    exact KTheory.K0.matrixFamilyBasisOfRingEquiv_eq_row p.coefficient
      (fun j ↦ Fin (p.blockSize j)) p.ringEquiv i
  · intro i
    simpa only [Fintype.card_fin] using
      KTheory.ProjectiveClass.matrixFamilyEquivOfRingEquiv_regular p.coefficient
        (fun j ↦ Fin (p.blockSize j)) p.ringEquiv i
  · intro i
    simpa only [Fintype.card_fin] using
      KTheory.K0.matrixFamilyEquivOfRingEquiv_regular p.coefficient
        (fun j ↦ Fin (p.blockSize j)) p.ringEquiv i

end IsSemisimpleRing
