/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Category.Noetherian
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Module.PUnit
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Morita.Matrix
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Noetherian transport along matrix equivalences

The chosen-index equivalences for `Fin 2`, at index zero, send the regular
modules over `ℤ` and `ZMod 2` to the canonical two-coordinate matrix column
modules. The examples use both the Noetherian-object bridge and module
transport. Ring transport concerns the left regular matrix module, whose
carrier has four scalar coordinates, not the column module.

The source premises come from the integer principal ideal domain and the
finite binary field. Reflection and counit comparisons also use independent
column premises: integer scalar restriction along a tower, or finiteness over
`ZMod 2`. The counit is a linear equivalence between the composite and the
column, rather than a definitional identification. A zero-module example
allows independent scalar and carrier universes. No claim concerns all
modules over a Noetherian ring.

## References

The transport interfaces are from `ProjectiveModules.Category.Noetherian`,
by Formal Frontier Agents. The examples follow Mathlib's matrix equivalence
and column action by Yunzhou Xie and Jujian Zhang, its Noetherian interfaces
by Mario Carneiro, Kevin Buzzard and María Inés de Frutos-Fernández, its
principal ideal ring interfaces by Chris Hughes and Morenikeji Neri, and
its modular integer interfaces by Eric Rodriguez and Chris Hughes. The
module-category isomorphism interface is due to Markus Himmel and Kim Morrison,
and the one-element module instances are due to Kenny Lau.
-/

@[expose] public section

open CategoryTheory

universe uR uS vR vS

section Integers

local notation "MatZ" => Matrix (Fin 2) (Fin 2) ℤ
local notation "eZ" => (ModuleCat.matrixEquivalence ℤ (0 : Fin 2))
local notation "intColumn" =>
  (Functor.obj (CategoryTheory.Equivalence.functor eZ) (ModuleCat.of ℤ ℤ) : ModuleCat MatZ)

open scoped Matrix.Module

-- Object transport starts with the regular scalar module, not with an
-- assumption about preservation or the target column.
private theorem isNoetherianObject_intColumn_and_isNoetherian : IsNoetherianObject intColumn ∧ IsNoetherian MatZ intColumn := by
  have hZ : IsNoetherian ℤ (ModuleCat.of ℤ ℤ) := inferInstance
  have hX : IsNoetherianObject (ModuleCat.of ℤ ℤ) :=
    (ModuleCat.isNoetherianObject_iff _).mpr hZ
  have hColumn : IsNoetherianObject intColumn :=
    (CategoryTheory.isNoetherianObject_iff_of_equivalence eZ _).mp hX
  exact ⟨hColumn, (ModuleCat.isNoetherianObject_iff intColumn).mp hColumn⟩

private theorem isNoetherian_intColumn : IsNoetherian MatZ intColumn :=
  (ModuleCat.isNoetherian_iff_of_equivalence ℤ MatZ eZ
    (ModuleCat.of ℤ ℤ)).mp (inferInstance : IsNoetherian ℤ (ModuleCat.of ℤ ℤ))

-- Reflection uses the two-coordinate integer premise directly.
private theorem isNoetherian_int_of_intColumn : IsNoetherian ℤ (ModuleCat.of ℤ ℤ) := by
  have hColumn : IsNoetherian MatZ intColumn := by
    letI hTower : IsScalarTower ℤ MatZ intColumn :=
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
  exact (ModuleCat.isNoetherian_iff_of_equivalence ℤ MatZ eZ
    (ModuleCat.of ℤ ℤ)).mpr hColumn

-- These two ring conclusions concern left multiplication on MatZ itself.
private theorem isNoetherianRing_intMatrix_of_equivalence : IsNoetherianRing MatZ :=
  ModuleCat.isNoetherianRing_of_equivalence.{0, 0, 0, 0} ℤ MatZ eZ
    (inferInstance : IsNoetherianRing ℤ)

private theorem isNoetherianRing_intMatrix : IsNoetherianRing MatZ :=
  (ModuleCat.isNoetherianRing_iff_of_equivalence.{0, 0, 0, 0} ℤ MatZ eZ).mp
    (inferInstance : IsNoetherianRing ℤ)

-- The reflected ring premise has four integer coordinates, not two.
private theorem isNoetherianRing_int_of_intMatrix : IsNoetherianRing ℤ := by
  have hMat : IsNoetherianRing MatZ := by
    letI : Module MatZ MatZ := Semiring.toModule
    have hTower : IsScalarTower ℤ MatZ MatZ := AddCommGroup.intIsScalarTower
    exact @isNoetherian_of_tower ℤ MatZ MatZ _ _ _ _
      Semiring.toModule _ hTower
      (inferInstance : IsNoetherian ℤ (Fin 2 → Fin 2 → ℤ))
  exact (ModuleCat.isNoetherianRing_iff_of_equivalence.{0, 0, 0, 0}
    ℤ MatZ eZ).mpr hMat

-- The counit comparison uses only the linear-equivalence Noetherian API
-- and the integer-column premise, independently of categorical transport.
private theorem isNoetherian_intColumn_counit : IsNoetherian MatZ ((eZ).functor.obj ((eZ).inverse.obj intColumn)) := by
  have hColumn : IsNoetherian MatZ intColumn := by
    letI hTower : IsScalarTower ℤ MatZ intColumn :=
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
  let ε : (eZ).functor.obj ((eZ).inverse.obj intColumn) ≃ₗ[MatZ] intColumn :=
    ((eZ).counitIso.app intColumn).toLinearEquiv
  exact ε.isNoetherian_iff.mpr hColumn

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

private theorem isNoetherianObject_binaryColumn_and_isNoetherian : IsNoetherianObject binaryColumn ∧ IsNoetherian MatF binaryColumn := by
  have hF : IsNoetherian (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) :=
    isNoetherian_of_finite (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2))
  have hX : IsNoetherianObject (ModuleCat.of (ZMod 2) (ZMod 2)) :=
    (ModuleCat.isNoetherianObject_iff _).mpr hF
  have hColumn : IsNoetherianObject binaryColumn :=
    (CategoryTheory.isNoetherianObject_iff_of_equivalence eF _).mp hX
  exact ⟨hColumn, (ModuleCat.isNoetherianObject_iff binaryColumn).mp hColumn⟩

private theorem isNoetherian_binaryColumn : IsNoetherian MatF binaryColumn :=
  (ModuleCat.isNoetherian_iff_of_equivalence (ZMod 2) MatF eF
    (ModuleCat.of (ZMod 2) (ZMod 2))).mp
      (isNoetherian_of_finite (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)))

private theorem isNoetherian_zmod_two_of_binaryColumn : IsNoetherian (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) :=
  (ModuleCat.isNoetherian_iff_of_equivalence (ZMod 2) MatF eF
    (ModuleCat.of (ZMod 2) (ZMod 2))).mpr
      (isNoetherian_of_finite MatF binaryColumn)

private theorem isNoetherianRing_binaryMatrix_of_equivalence : IsNoetherianRing MatF :=
  ModuleCat.isNoetherianRing_of_equivalence.{0, 0, 0, 0} (ZMod 2) MatF eF
    (isNoetherian_of_finite (ZMod 2) (ZMod 2))

private theorem isNoetherianRing_binaryMatrix : IsNoetherianRing MatF :=
  (ModuleCat.isNoetherianRing_iff_of_equivalence.{0, 0, 0, 0}
    (ZMod 2) MatF eF).mp (isNoetherian_of_finite (ZMod 2) (ZMod 2))

private theorem isNoetherianRing_zmod_two_of_binaryMatrix : IsNoetherianRing (ZMod 2) :=
  (ModuleCat.isNoetherianRing_iff_of_equivalence.{0, 0, 0, 0}
    (ZMod 2) MatF eF).mpr (isNoetherian_of_finite MatF MatF)

private theorem isNoetherian_binaryColumn_counit : IsNoetherian MatF ((eF).functor.obj ((eF).inverse.obj binaryColumn)) := by
  have hColumn : IsNoetherian MatF binaryColumn :=
    isNoetherian_of_finite MatF binaryColumn
  let ε : (eF).functor.obj ((eF).inverse.obj binaryColumn) ≃ₗ[MatF] binaryColumn :=
    ((eF).counitIso.app binaryColumn).toLinearEquiv
  exact ε.isNoetherian_iff.mpr hColumn

end BinaryField

private theorem isNoetherian_int_refl_obj : IsNoetherian ℤ
    ((CategoryTheory.Equivalence.refl : ModuleCat.{0} ℤ ≌ ModuleCat.{0} ℤ).functor.obj
        (ModuleCat.of ℤ ℤ)) :=
  (ModuleCat.isNoetherian_iff_of_equivalence ℤ ℤ
    (CategoryTheory.Equivalence.refl : ModuleCat.{0} ℤ ≌ ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ)).mp
      (inferInstance : IsNoetherian ℤ (ModuleCat.of ℤ ℤ))

-- The zero module exercises independent scalar and carrier universes. The
-- given equivalence is not replaced by an equivalence of lifted categories.
private theorem isNoetherian_punit_obj_and_isNoetherianObject (R : Type uR) (S : Type uS) [Ring R] [Ring S]
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S) :
    IsNoetherian S (e.functor.obj (ModuleCat.of R PUnit.{vR + 1})) ∧
      IsNoetherianObject (e.functor.obj (ModuleCat.of R PUnit.{vR + 1})) := by
  have hZero : IsNoetherian R (ModuleCat.of R PUnit.{vR + 1}) := inferInstance
  have hImage : IsNoetherian S (e.functor.obj (ModuleCat.of R PUnit.{vR + 1})) :=
    (ModuleCat.isNoetherian_iff_of_equivalence R S e
      (ModuleCat.of R PUnit.{vR + 1})).mp hZero
  exact ⟨hImage, (ModuleCat.isNoetherianObject_iff _).mpr hImage⟩
