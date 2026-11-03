/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension and coefficient tensor products

Scalar extension along an algebra map is B-linearly equivalent to the ordinary
coefficient tensor product, with elementary tensors preserved. The construction
uses Mathlib's tensor congruence and scalar-tower criterion. In particular, the
given coefficient action is not identified definitionally with the action induced
by its algebra map.
-/

@[expose] public section

universe uA uB uM

open scoped TensorProduct ChangeOfRings

namespace ModuleCat

private theorem coefficientScalarTower
    {A : Type uA} {B : Type uB} {C : Type uB}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup C]
    [coefficientModule : Module A C] [Module B C]
    (h : ∀ (a : A) (c : C), algebraMap A B a • c = a • c) :
    IsScalarTower A B C :=
  IsScalarTower.of_algebraMap_smul h

private theorem coefficientTensorCongr_tmul
    {A : Type uA} {B : Type uB} {C : Type uB}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup C]
    [coefficientModule : Module A C] [Module B C]
    [coefficientTower : IsScalarTower A B C]
    (M : ModuleCat.{uM} A) (e : C ≃ₗ[B] B) (c : C) (m : M) :
    TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl A M)
        (c ⊗ₜ[A] m) = e c ⊗ₜ[A] m :=
  TensorProduct.AlgebraTensorModule.congr_tmul e (LinearEquiv.refl A M) c m

/-- Scalar extension along the algebra map is the ordinary coefficient tensor product. -/
noncomputable def extendScalarsTensorEquiv
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] [Algebra A B]
    (M : ModuleCat.{uM} A) :
    (ModuleCat.extendScalars (algebraMap A B)).obj M ≃ₗ[B] (B ⊗[A] M) := by
  let scalarTowerCompatibility
      {C : Type uB} [AddCommGroup C]
      [coefficientModule : Module A C] [Module B C]
      (h : ∀ (a : A) (c : C), algebraMap A B a • c = a • c) :
      IsScalarTower A B C :=
    IsScalarTower.of_algebraMap_smul h
  let coefficientTensorCongr
      {C : Type uB} [AddCommGroup C]
      [coefficientModule : Module A C] [Module B C]
      [coefficientTower : IsScalarTower A B C]
      (e : C ≃ₗ[B] B) : C ⊗[A] M ≃ₗ[B] B ⊗[A] M :=
    TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl A M)
  -- The scalar tower is available before the tensor module in the helper's result.
  refine coefficientTensorCongr
    (coefficientModule :=
      @Algebra.toModule A B _ _ (algebraMap A B).toAlgebra)
    (coefficientTower := scalarTowerCompatibility
      (coefficientModule :=
        @Algebra.toModule A B _ _ (algebraMap A B).toAlgebra) ?_)
    (LinearEquiv.refl B B)
  intro a b
  change algebraMap A B a * b = _
  simpa only [RingHom.algebraMap_toAlgebra] using
    (@Algebra.smul_def A B _ _ (algebraMap A B).toAlgebra a b).symm

/-- The coefficient tensor comparison preserves elementary tensors. -/
theorem extendScalarsTensorEquiv_tmul
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] [Algebra A B]
    (M : ModuleCat.{uM} A) (b : B) (m : M) :
    extendScalarsTensorEquiv (A := A) (B := B) M
        (b ⊗ₜ[A, algebraMap A B] m) = b ⊗ₜ[A] m := by
  dsimp only [extendScalarsTensorEquiv]
  exact coefficientTensorCongr_tmul
    (coefficientModule :=
      @Algebra.toModule A B _ _ (algebraMap A B).toAlgebra)
    (coefficientTower := coefficientScalarTower
      (coefficientModule :=
        @Algebra.toModule A B _ _ (algebraMap A B).toAlgebra)
      (by
        intro a b
        change algebraMap A B a * b = _
        simpa only [RingHom.algebraMap_toAlgebra] using
          (@Algebra.smul_def A B _ _ (algebraMap A B).toAlgebra a b).symm))
    M (LinearEquiv.refl B B) b m

end ModuleCat

universe uAInv uBInv uMInv

open scoped TensorProduct ChangeOfRings

namespace ModuleCat

/-- The inverse coefficient tensor comparison preserves elementary tensors. -/
@[simp] public theorem extendScalarsTensorEquiv_symm_tmul
    {A : Type uAInv} {B : Type uBInv} [CommRing A] [CommRing B] [Algebra A B]
    (M : ModuleCat.{uMInv} A) (b : B) (m : M) :
    (extendScalarsTensorEquiv (A := A) (B := B) M).symm
        (b ⊗ₜ[A] m) = b ⊗ₜ[A, algebraMap A B] m := by
  exact (congrArg (extendScalarsTensorEquiv (A := A) (B := B) M).symm
    (extendScalarsTensorEquiv_tmul (A := A) (B := B) M b m)).symm.trans
      ((extendScalarsTensorEquiv (A := A) (B := B) M).symm_apply_apply
        (b ⊗ₜ[A, algebraMap A B] m))

end ModuleCat
