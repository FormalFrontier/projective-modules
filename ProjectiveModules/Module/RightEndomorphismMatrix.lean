/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import GeneralLinearGroups.QuasiregularQuotient
public import ProjectiveModules.Module.RightExtensionFree
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrices of finite free right-module endomorphisms

This file identifies endomorphisms of the finite free right `R`-module
`n → R` with matrices over a possibly noncommutative ring `R`.  The matrix
uses the column-vector convention: its `j`th column is the image of the `j`th
standard basis vector, and composition is represented by matrix multiplication
in the same order.

As an application, invertibility of the coefficient matrix modulo a
quasi-regular two-sided ideal reflects to bijectivity of the specified
right-linear endomorphism.  The matrix equivalence also commutes with scalar
extension along an arbitrary ring homomorphism.
-/

@[expose] public section

universe uR uι

open Function
open scoped Matrix

namespace Module

variable (R : Type uR) [Ring R]
variable (ι : Type uι) [Fintype ι] [DecidableEq ι]

/-- The ring equivalence from endomorphisms of the finite free right
`R`-module to matrices over `R`.

The first equivalence makes a matrix of endomorphisms of one copy of `R`; the
second evaluates each such right-linear endomorphism at `1`. -/
noncomputable def rightEndomorphismMatrixEquiv :
    Module.End Rᵐᵒᵖ (ι → R) ≃+* Matrix ι ι R :=
  (endVecRingEquivMatrixEnd ι Rᵐᵒᵖ R).trans
    (RingEquiv.mapMatrix (RingEquiv.moduleEndSelfOp (R := R)).symm)

/-- The `j`th column of the right-endomorphism matrix is the image of the
`j`th standard basis vector. -/
@[simp]
theorem rightEndomorphismMatrixEquiv_apply
    (f : Module.End Rᵐᵒᵖ (ι → R)) (i j : ι) :
    rightEndomorphismMatrixEquiv R ι f i j = f (Pi.single j 1) i :=
  rfl

/-- The right-endomorphism matrix acts on column vectors exactly as the
endomorphism does. -/
theorem rightEndomorphismMatrixEquiv_mulVec
    (f : Module.End Rᵐᵒᵖ (ι → R)) (x : ι → R) :
    rightEndomorphismMatrixEquiv R ι f *ᵥ x = f x := by
  ext i
  simp only [Matrix.mulVec, dotProduct, rightEndomorphismMatrixEquiv_apply]
  conv_rhs => rw [← Finset.univ_sum_single x, map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hsingle : Pi.single j (x j) =
      MulOpposite.op (x j) • (Pi.single j (1 : R) : ι → R) := by
    simpa using
      (Pi.single_smul' (I := ι) (α := Rᵐᵒᵖ) (β := R)
        j (MulOpposite.op (x j)) (1 : R))
  rw [hsingle, map_smul]
  rfl

/-- Composition of right-linear endomorphisms is represented by matrix
multiplication in the same order. -/
theorem rightEndomorphismMatrixEquiv_comp
    (f g : Module.End Rᵐᵒᵖ (ι → R)) :
    rightEndomorphismMatrixEquiv R ι (f.comp g) =
      rightEndomorphismMatrixEquiv R ι f *
        rightEndomorphismMatrixEquiv R ι g := by
  simpa only [Module.End.mul_eq_comp] using
    (rightEndomorphismMatrixEquiv R ι).map_mul f g

/-- A finite free right-module endomorphism is bijective exactly when its
coefficient matrix is a unit. -/
theorem isUnit_rightEndomorphismMatrixEquiv_iff
    (f : Module.End Rᵐᵒᵖ (ι → R)) :
    IsUnit (rightEndomorphismMatrixEquiv R ι f) ↔ Bijective f := by
  rw [← Module.End.isUnit_iff]
  constructor
  · intro h
    simpa using
      (rightEndomorphismMatrixEquiv R ι).symm.toRingHom.isUnit_map h
  · exact (rightEndomorphismMatrixEquiv R ι).toRingHom.isUnit_map

/-- If the coefficient matrix of a specified finite free right-module
endomorphism is invertible modulo a quasi-regular two-sided ideal, then the
endomorphism is bijective. -/
theorem rightEndomorphism_bijective_of_mapMatrix_quotient_isUnit
    (I : TwoSidedIdeal R) (hI : I.IsQuasiregular)
    (f : Module.End Rᵐᵒᵖ (ι → R))
    (hf : IsUnit ((Ideal.Quotient.mk I.asIdeal).mapMatrix
      (rightEndomorphismMatrixEquiv R ι f))) : Bijective f := by
  rw [← isUnit_rightEndomorphismMatrixEquiv_iff R ι f]
  exact Matrix.GeneralLinearGroup.isUnit_of_mapMatrix_quotient_isUnit
    I hI (rightEndomorphismMatrixEquiv R ι f) hf

/-- Scalar extension of an endomorphism of a finite free right module,
transported across the canonical coordinate equivalences. -/
noncomputable def rightEndomorphismScalarExtension
    {S : Type*} [Ring S] (f : R →+* S)
    (g : Module.End Rᵐᵒᵖ (ι → R)) :
    Module.End Sᵐᵒᵖ (ι → S) :=
  (ModuleCat.RightExtension.rightFreeLinearEquiv f ι).toLinearMap.comp <|
    (ModuleCat.RightExtension.map f g).comp <|
      (ModuleCat.RightExtension.rightFreeLinearEquiv f ι).symm.toLinearMap

/-- Scalar extension of a finite free right-module endomorphism acts on a
standard basis vector by applying the coefficient homomorphism coordinatewise. -/
@[simp]
theorem rightEndomorphismScalarExtension_single
    {S : Type*} [Ring S] (f : R →+* S)
    (g : Module.End Rᵐᵒᵖ (ι → R)) (j : ι) :
    rightEndomorphismScalarExtension R ι f g (Pi.single j 1) =
      fun i ↦ f (g (Pi.single j 1) i) := by
  classical
  ext i
  simp [rightEndomorphismScalarExtension,
    ModuleCat.RightExtension.rightFreeLinearEquiv,
    ModuleCat.RightExtension.rightFreeFrom_apply, Pi.single_apply]

/-- The matrix of a scalar-extended finite free right-module endomorphism is
obtained by applying the coefficient homomorphism entrywise. -/
theorem rightEndomorphismMatrixEquiv_scalarExtension
    {S : Type*} [Ring S] (f : R →+* S)
    (g : Module.End Rᵐᵒᵖ (ι → R)) :
    f.mapMatrix (rightEndomorphismMatrixEquiv R ι g) =
      rightEndomorphismMatrixEquiv S ι
        (rightEndomorphismScalarExtension R ι f g) := by
  ext i j
  simp

/-- Bijectivity of a finite free right-module endomorphism is reflected from
its scalar extension to a quasi-regular quotient. -/
theorem rightEndomorphism_bijective_of_quotientScalarExtension_bijective
    (I : TwoSidedIdeal R) (hI : I.IsQuasiregular)
    (g : Module.End Rᵐᵒᵖ (ι → R))
    (hg : Bijective (rightEndomorphismScalarExtension R ι
      (Ideal.Quotient.mk I.asIdeal) g)) :
    Bijective g := by
  apply rightEndomorphism_bijective_of_mapMatrix_quotient_isUnit
    R ι I hI g
  rw [rightEndomorphismMatrixEquiv_scalarExtension]
  exact (isUnit_rightEndomorphismMatrixEquiv_iff _ _ _).mpr hg

/-- The linear self-equivalence induced by reflection of a specified finite
free right-module endomorphism through a quasi-regular quotient. -/
noncomputable def rightEndomorphismLinearEquivOfMapMatrixQuotientIsUnit
    (I : TwoSidedIdeal R) (hI : I.IsQuasiregular)
    (f : Module.End Rᵐᵒᵖ (ι → R))
    (hf : IsUnit ((Ideal.Quotient.mk I.asIdeal).mapMatrix
      (rightEndomorphismMatrixEquiv R ι f))) :
    (ι → R) ≃ₗ[Rᵐᵒᵖ] (ι → R) :=
  LinearEquiv.ofBijective f
    (rightEndomorphism_bijective_of_mapMatrix_quotient_isUnit R ι I hI f hf)

@[simp]
theorem rightEndomorphismLinearEquivOfMapMatrixQuotientIsUnit_apply
    (I : TwoSidedIdeal R) (hI : I.IsQuasiregular)
    (f : Module.End Rᵐᵒᵖ (ι → R))
    (hf : IsUnit ((Ideal.Quotient.mk I.asIdeal).mapMatrix
      (rightEndomorphismMatrixEquiv R ι f))) (x : ι → R) :
    rightEndomorphismLinearEquivOfMapMatrixQuotientIsUnit R ι I hI f hf x =
      f x :=
  rfl

end Module
