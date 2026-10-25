/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Morita.Matrix
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Noetherian module examples

The chosen-index matrix equivalences send the regular modules over `ℤ` and
`ZMod 2` to two-coordinate column modules. Integer columns are Noetherian by
restriction along a scalar tower from `ℤ`; the regular matrix module instead
has four integer coordinates. Elementary matrices exhibit noncommutativity
and a nonzero column action. Over `ZMod 2`, the scalar, column, and regular
matrix carriers have respectively two, four, and sixteen elements. The integer
example separates Noetherianity from finiteness of the underlying type.

Identity, zero objects, and universe lifts give boundary examples. Universe
lifting is used as a functor and as a linear equivalence of individual modules,
not as an equivalence of entire module categories at different universes.
The countably generated free integer module is not Noetherian.

## References

These examples use Mathlib's matrix equivalence and column action formalized
by Yunzhou Xie and Jujian Zhang; its Noetherian module interfaces by Mario
Carneiro, Kevin Buzzard, and María Inés de Frutos-Fernández; and its principal
ideal ring interfaces by Chris Hughes and Morenikeji Neri. The universe-lifting
constructions are due to Nailin Guan and Kim Morrison. The finitely supported
basis and finite-basis obstruction follow the formalizations by Johannes Hölzl
and Johan Commelin. The modular integer interfaces are due to Eric Rodriguez
and Chris Hughes. All arguments here use these algebraic interfaces directly.
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators

universe u v w

section Integers

local notation "MatZ" => Matrix (Fin 2) (Fin 2) ℤ
local notation "eZ" => (ModuleCat.matrixEquivalence ℤ (0 : Fin 2))
local notation "intColumn" =>
  (Functor.obj (CategoryTheory.Equivalence.functor eZ) (ModuleCat.of ℤ ℤ) : ModuleCat MatZ)

open scoped Matrix.Module

private theorem intColumn_coe_eq : (intColumn : Type) = (Fin 2 → ℤ) := rfl

private theorem intColumn_smul_apply (A : MatZ) (x : intColumn) (i : Fin 2) :
    (A • x) i = ∑ j, A i j * x j := by
  calc
    (A • x) i = ∑ j : Fin 2, A i j • (show ModuleCat.of ℤ ℤ from x j) :=
      Matrix.Module.smul_apply (M := ModuleCat.of ℤ ℤ) A x i
    _ = ∑ j, A i j * x j := rfl

-- The scalar-tower argument for columns uses two coordinates; the regular
-- matrix module uses the iterated function space, with four coordinates.
private theorem isNoetherian_int_and_intColumn_and_isNoetherianRing_intMatrix :
    IsNoetherian ℤ (ModuleCat.of ℤ ℤ) ∧
      IsNoetherian MatZ intColumn ∧ IsNoetherianRing MatZ := by
  refine ⟨inferInstance, ?_, ?_⟩
  · have hTower : IsScalarTower ℤ MatZ intColumn :=
      @AddCommGroup.intIsScalarTower MatZ intColumn _
        (ModuleCat.isAddCommGroup intColumn) (ModuleCat.isModule intColumn)
    exact @isNoetherian_of_tower ℤ MatZ intColumn
      Int.instSemiring
      (Matrix.instRing (n := Fin 2) (α := ℤ)).toSemiring
      (ModuleCat.isAddCommGroup intColumn).toAddCommMonoid
      ((@AddCommGroup.toIntModule MatZ
        (Matrix.instRing (n := Fin 2) (α := ℤ)).toAddCommGroup
      ).toDistribMulAction.toMulAction.toSemigroupAction.toSMul)
      (ModuleCat.isModule intColumn)
      (@AddCommGroup.toIntModule intColumn (ModuleCat.isAddCommGroup intColumn))
      hTower
      (inferInstance : IsNoetherian ℤ (Fin 2 → ModuleCat.of ℤ ℤ))
  · letI : Module MatZ MatZ := Semiring.toModule
    have hTower : IsScalarTower ℤ MatZ MatZ := AddCommGroup.intIsScalarTower
    exact @isNoetherian_of_tower ℤ MatZ MatZ _ _ _ _
      Semiring.toModule _ hTower
      (inferInstance : IsNoetherian ℤ (Fin 2 → Fin 2 → ℤ))

private theorem isNoetherianRing_int_and_infinite :
    IsNoetherianRing ℤ ∧ Infinite (ModuleCat.of ℤ ℤ) :=
  ⟨inferInstance, inferInstance⟩

local notation "E" => (fun a b : Fin 2 => Matrix.single a b (1 : ℤ))

private theorem intMatrix_single_mul_noncommute_and_smul :
    E 0 0 * E 0 1 = E 0 1 ∧ E 0 1 * E 0 0 = 0 ∧
      E 0 1 ≠ 0 ∧ E 0 0 * E 0 1 ≠ E 0 1 * E 0 0 ∧
      ((E 0 1) • (Pi.single 1 (1 : ℤ) : intColumn)) 0 = 1 := by
  have hleft : E 0 0 * E 0 1 = E 0 1 := by
    simpa only [one_mul] using
      Matrix.single_mul_single_same (c := (1 : ℤ)) (0 : Fin 2) 0 1 1
  have hright : E 0 1 * E 0 0 = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : ℤ)) (0 : Fin 2) 1 0 (by decide) 1
  have hne : E 0 1 ≠ (0 : MatZ) := by
    intro h
    simpa using congrArg (fun A : MatZ => A 0 1) h
  refine ⟨hleft, hright, hne, ?_, ?_⟩
  · intro h
    exact hne (hleft.symm.trans (h.trans hright))
  · simp only [Matrix.Module.single_smul, Pi.single_eq_same, one_smul]

end Integers

section BinaryField

local notation "MatF" => Matrix (Fin 2) (Fin 2) (ZMod 2)
local notation "eF" => (ModuleCat.matrixEquivalence (ZMod 2) (0 : Fin 2))
local notation "binaryColumn" =>
  (Functor.obj (CategoryTheory.Equivalence.functor eF) (ModuleCat.of (ZMod 2) (ZMod 2)) :
    ModuleCat MatF)

local instance : Fintype binaryColumn :=
  (inferInstance : Fintype (Fin 2 → ZMod 2))

open scoped Matrix.Module

private theorem nontrivial_zmod_two : Nontrivial (ZMod 2) := by
  have : Fact (1 < (2 : ℕ)) := ⟨by decide⟩
  infer_instance

private theorem binaryColumn_coe_eq : (binaryColumn : Type) = (Fin 2 → ZMod 2) := rfl

private theorem finite_zmod_two_and_binaryColumn_and_binaryMatrix :
    Finite (ModuleCat.of (ZMod 2) (ZMod 2)) ∧ Finite binaryColumn ∧ Finite MatF :=
  ⟨inferInstance, inferInstance, inferInstance⟩

private theorem isNoetherian_zmod_two_and_binaryColumn_and_isNoetherianRing_binaryMatrix :
    IsNoetherian (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) ∧
      IsNoetherian MatF binaryColumn ∧ IsNoetherianRing MatF := by
  exact ⟨isNoetherian_of_finite (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)),
    isNoetherian_of_finite MatF binaryColumn, isNoetherian_of_finite MatF MatF⟩

private theorem card_zmod_two_module : Fintype.card (ModuleCat.of (ZMod 2) (ZMod 2)) = 2 :=
  ZMod.card 2

private theorem card_binaryColumn : Fintype.card binaryColumn = 4 := by
  change Fintype.card (Fin 2 → ZMod 2) = 4
  simpa only [Fintype.card_pi_const, ZMod.card] using (show 2 ^ 2 = 4 from rfl)

private theorem card_binaryMatrix : Fintype.card MatF = 16 := by
  change Fintype.card (Fin 2 → Fin 2 → ZMod 2) = 16
  simpa only [Fintype.card_pi_const, ZMod.card] using
    (show (2 ^ 2) ^ 2 = 16 from rfl)

local notation "E" => (fun a b : Fin 2 => Matrix.single a b (1 : ZMod 2))

private theorem binaryMatrix_single_mul_noncommute_and_smul :
    E 0 0 * E 0 1 = E 0 1 ∧ E 0 1 * E 0 0 = 0 ∧
      E 0 1 ≠ 0 ∧ E 0 0 * E 0 1 ≠ E 0 1 * E 0 0 ∧
      ((E 0 1) • (Pi.single 1 (1 : ZMod 2) : binaryColumn)) 0 = 1 := by
  have : Fact (1 < (2 : ℕ)) := ⟨by decide⟩
  have hleft : E 0 0 * E 0 1 = E 0 1 := by
    simpa only [one_mul] using
      Matrix.single_mul_single_same (c := (1 : ZMod 2)) (0 : Fin 2) 0 1 1
  have hright : E 0 1 * E 0 0 = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : ZMod 2)) (0 : Fin 2) 1 0 (by decide) 1
  have hne : E 0 1 ≠ (0 : MatF) := by
    intro h
    simpa using congrArg (fun A : MatF => A 0 1) h
  refine ⟨hleft, hright, hne, ?_, ?_⟩
  · intro h
    exact hne (hleft.symm.trans (h.trans hright))
  · simp only [Matrix.Module.single_smul, Pi.single_eq_same, one_smul]

end BinaryField

section Boundaries

private theorem isNoetherian_refl_obj_iff (R : Type u) [Ring R] (X : ModuleCat.{v} R) :
    IsNoetherian R
      ((CategoryTheory.Equivalence.refl : ModuleCat.{v} R ≌ ModuleCat.{v} R).functor.obj X) ↔
      IsNoetherian R X := Iff.rfl

private theorem isNoetherian_int_refl_obj_of_iso :
    IsNoetherian ℤ
      ((CategoryTheory.Equivalence.refl : ModuleCat.{0} ℤ ≌ ModuleCat.{0} ℤ).functor.obj
        (ModuleCat.of ℤ ℤ)) := by
  let i :
      (CategoryTheory.Equivalence.refl : ModuleCat.{0} ℤ ≌ ModuleCat.{0} ℤ).functor.obj
          (ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℤ ℤ :=
    CategoryTheory.Iso.refl (ModuleCat.of ℤ ℤ)
  exact i.toLinearEquiv.isNoetherian_iff.mpr
    (inferInstance : IsNoetherian ℤ (ModuleCat.of ℤ ℤ))

private theorem isNoetherianRing_punit : IsNoetherianRing PUnit :=
  isNoetherian_of_subsingleton PUnit PUnit

private theorem isZero_punit_and_isNoetherian (R : Type u) [Ring R] :
    CategoryTheory.Limits.IsZero (ModuleCat.of R PUnit.{v + 1}) ∧
      IsNoetherian R (ModuleCat.of R PUnit.{v + 1}) :=
  ⟨ModuleCat.isZero_of_subsingleton _, inferInstance⟩

private theorem uliftFunctor_obj_coe_eq (R : Type u) [Ring R] (X : ModuleCat.{v} R) :
    ((ModuleCat.uliftFunctor.{w, v} R).obj X : Type (max v w)) = ULift.{w} X := rfl

private theorem isNoetherian_uliftFunctor_obj_iff (R : Type u) [Ring R] (X : ModuleCat.{v} R) :
    IsNoetherian R ((ModuleCat.uliftFunctor.{w, v} R).obj X) ↔ IsNoetherian R X :=
  (ULift.moduleEquiv : ULift.{w} X ≃ₗ[R] X).isNoetherian_iff

end Boundaries

-- A free module over a Noetherian ring need not be Noetherian.
private theorem isNoetherianRing_int_and_free_finsupp_not_isNoetherian :
    IsNoetherianRing ℤ ∧ Module.Free ℤ (ℕ →₀ ℤ) ∧ ¬ IsNoetherian ℤ (ℕ →₀ ℤ) := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro h
  have : IsNoetherian ℤ (ℕ →₀ ℤ) := h
  exact Module.not_finite_of_infinite_basis
    (Finsupp.basisSingleOne : Module.Basis ℕ ℤ (ℕ →₀ ℤ))
    (inferInstance : Module.Finite ℤ (ℕ →₀ ℤ))
