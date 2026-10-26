/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism, Lens
module

public import GeneralLinearGroups.QuasiregularQuotient
public import ProjectiveModules.Module.RightExtensionFree
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrices and scalar extension of finite free right modules

This file identifies endomorphisms of the finite free right `R`-module
`n → R` with matrices over a possibly noncommutative semiring `R`.  The matrix
uses the column-vector convention: its `j`th column is the image of the `j`th
standard basis vector, and composition is represented by matrix multiplication
in the same order.

As an application, invertibility of the coefficient matrix modulo a
quasi-regular two-sided ideal reflects to bijectivity of the specified
right-linear endomorphism. The square scalar-extension operation specializes rectangular
transport of specified maps and equivalences along a semiring homomorphism.
Only the source of a map must be finite; equivalences require finite coordinates
on both sides to transport the specified inverse. The Ring tensor construction
remains the compatibility reference.

The constructions reuse Mathlib's opposite-semiring matrix conversions and
rectangular inverse constructor. The motivating application is Charles A.
Weibel, *The K-book*, Exercise I.1.7; no source excerpt is reproduced here.
-/

@[expose] public section

universe uR uS uT uι uκ uν

open Function
open scoped Matrix

namespace Module

section SquareCore

variable (R : Type uR)
variable (ι : Type uι) [Fintype ι] [DecidableEq ι]

section MatrixCore

variable [Semiring R]

/-- The semiring equivalence from endomorphisms of the finite free right
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

end MatrixCore

section Quasiregular

variable [Ring R]

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

end Quasiregular

end SquareCore

section Rectangular

variable (R : Type uR) [Semiring R]
variable (ι : Type uι) [Fintype ι] (κ : Type uκ)
variable {S : Type uS} [Semiring S]

/-- Transport a specified right-linear map with finite source along a coefficient
homomorphism. The target coordinates need not be finite. The row-matrix
conversions over the opposite semirings are Mathlib's existing conversions. -/
noncomputable def rightFreeLinearMapScalarExtension
    (f : R →+* S) (g : (ι → R) →ₗ[Rᵐᵒᵖ] (κ → R)) :
    (ι → S) →ₗ[Sᵐᵒᵖ] (κ → S) := by
  classical
  exact LinearEquiv.arrowCongrAddEquiv
    (rightFreeCoordEquiv S ι) (rightFreeCoordEquiv S κ)
    (Matrix.toLinearMapRight'
      ((LinearMap.toMatrixRight'
        (LinearEquiv.arrowCongrAddEquiv
          (rightFreeCoordEquiv R ι).symm (rightFreeCoordEquiv R κ).symm g)).map
            (RingHom.op f)))

/-- Transport a specified equivalence and its specified inverse. Both coordinate
sets are finite, but their cardinalities need not agree. Inverse identities are
mapped entrywise, then Mathlib's rectangular inverse constructor is reused. -/
noncomputable def rightFreeScalarExtensionEquiv [Fintype κ]
    (f : R →+* S) (e : (ι → R) ≃ₗ[Rᵐᵒᵖ] (κ → R)) :
    (ι → S) ≃ₗ[Sᵐᵒᵖ] (κ → S) := by
  classical
  let e' := (rightFreeCoordEquiv R ι).trans (e.trans (rightFreeCoordEquiv R κ).symm)
  let A := LinearMap.toMatrixRight' e'.toLinearMap
  let B := LinearMap.toMatrixRight' e'.symm.toLinearMap
  have hAB : A * B = 1 := by
    dsimp [A, B]
    rw [← LinearMap.toMatrixRight'_comp, e'.symm_comp, LinearMap.toMatrixRight'_id]
  have hBA : B * A = 1 := by
    dsimp [A, B]
    rw [← LinearMap.toMatrixRight'_comp, e'.comp_symm, LinearMap.toMatrixRight'_id]
  have hAB' : A.map (RingHom.op f) * B.map (RingHom.op f) = 1 := by
    rw [← Matrix.map_mul, hAB]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hBA' : B.map (RingHom.op f) * A.map (RingHom.op f) = 1 := by
    rw [← Matrix.map_mul, hBA]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  exact (rightFreeCoordEquiv S ι).symm.trans
    ((Matrix.toLinearEquivRight'OfInv hBA' hAB').trans (rightFreeCoordEquiv S κ))

end Rectangular

section CharacteristicLaws

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [Semiring R] [Semiring S] [Semiring T]
variable {ι : Type uι} {κ : Type uκ} {ν : Type uν} [Fintype ι]
variable (f : R →+* S) (g : (ι → R) →ₗ[Rᵐᵒᵖ] (κ → R))

open Classical in
/-- Coefficients act on the left; opposite scalars act on the right. -/
theorem rightFreeLinearMapScalarExtension_apply (y : ι → S) (i : κ) :
    rightFreeLinearMapScalarExtension R ι κ f g y i =
      ∑ j, f (g (Pi.single j 1) i) * y j := by
  have hsingle (j : ι) :
      rightFreeCoordEquiv R ι (Pi.single j (1 : Rᵐᵒᵖ)) =
        Pi.single j (1 : R) := by
    ext k
    by_cases h : k = j <;> simp [h]
  suffices (∑ j, f (MulOpposite.unop
      (LinearMap.toMatrixRight'
        (LinearEquiv.arrowCongrAddEquiv (rightFreeCoordEquiv R ι).symm
          (rightFreeCoordEquiv R κ).symm g) j i)) * y j) =
      ∑ j, f (g (Pi.single j 1) i) * y j by
    simpa [rightFreeLinearMapScalarExtension, LinearEquiv.arrowCongrAddEquiv,
      LinearMap.toMatrixRight', Matrix.vecMul, dotProduct, MulOpposite.unop_mul] using this
  apply Finset.sum_congr rfl
  intro j _
  change f (g (rightFreeCoordEquiv R ι (Pi.single j (1 : Rᵐᵒᵖ))) i) * y j =
    f (g (Pi.single j 1) i) * y j
  rw [hsingle]

open Classical in
/-- A characteristic formula for an arbitrary target basis coefficient. -/
@[simp]
theorem rightFreeLinearMapScalarExtension_single (j : ι) (s : S) :
    rightFreeLinearMapScalarExtension R ι κ f g (Pi.single j s) =
      fun i ↦ f (g (Pi.single j 1) i) * s := by
  funext i
  rw [rightFreeLinearMapScalarExtension_apply]
  exact dotProduct_single (fun k ↦ f (g (Pi.single k 1) i)) s j

open Classical in
/-- The opposite-coordinate row matrix is mapped entrywise, also rectangularly. -/
theorem rightFreeLinearMapScalarExtension_toMatrixRight :
    LinearMap.toMatrixRight' (LinearEquiv.arrowCongrAddEquiv
      (rightFreeCoordEquiv S ι).symm (rightFreeCoordEquiv S κ).symm
        (rightFreeLinearMapScalarExtension R ι κ f g)) =
      (LinearMap.toMatrixRight' (LinearEquiv.arrowCongrAddEquiv
        (rightFreeCoordEquiv R ι).symm (rightFreeCoordEquiv R κ).symm g)).map
          (RingHom.op f) := by
  let C : ((ι → Sᵐᵒᵖ) →ₗ[Sᵐᵒᵖ] (κ → Sᵐᵒᵖ)) ≃+
      ((ι → S) →ₗ[Sᵐᵒᵖ] (κ → S)) :=
    LinearEquiv.arrowCongrAddEquiv
      (rightFreeCoordEquiv S ι) (rightFreeCoordEquiv S κ)
  change LinearMap.toMatrixRight'
    (C.symm (C (Matrix.toLinearMapRight' _))) = _
  rw [AddEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

open Classical in
/-- Naturality on vectors whose entries lie in the coefficient image. -/
theorem rightFreeLinearMapScalarExtension_coefficients (x : ι → R) :
    rightFreeLinearMapScalarExtension R ι κ f g (fun j ↦ f (x j)) =
      fun i ↦ f (g x i) := by
  funext i
  rw [rightFreeLinearMapScalarExtension_apply]
  calc
    (∑ j, f (g (Pi.single j 1) i) * f (x j)) =
        f (∑ j, g (Pi.single j 1) i * x j) := by
      simp only [map_sum, map_mul]
    _ = f (g x i) := by
      congr 1
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

open Classical in
@[simp]
theorem rightFreeLinearMapScalarExtension_zero :
    rightFreeLinearMapScalarExtension R ι κ f 0 = 0 := by
  apply LinearMap.pi_ext
  intro j s
  funext i
  simp [rightFreeLinearMapScalarExtension_single]

open Classical in
theorem rightFreeLinearMapScalarExtension_add (h : (ι → R) →ₗ[Rᵐᵒᵖ] (κ → R)) :
    rightFreeLinearMapScalarExtension R ι κ f (g + h) =
      rightFreeLinearMapScalarExtension R ι κ f g +
        rightFreeLinearMapScalarExtension R ι κ f h := by
  apply LinearMap.pi_ext
  intro j s
  funext i
  simp [rightFreeLinearMapScalarExtension_single, map_add, add_mul]

open Classical in
@[simp]
theorem rightFreeLinearMapScalarExtension_id :
    rightFreeLinearMapScalarExtension R ι ι f LinearMap.id = LinearMap.id := by
  apply LinearMap.pi_ext
  intro j s
  funext i
  by_cases h : i = j <;>
    simp [rightFreeLinearMapScalarExtension_single, h]

open Classical in
/-- Only the intermediate coordinate type must additionally be finite. -/
theorem rightFreeLinearMapScalarExtension_map_comp [Fintype κ]
    (h : (κ → R) →ₗ[Rᵐᵒᵖ] (ν → R)) :
    rightFreeLinearMapScalarExtension R ι ν f (h.comp g) =
      (rightFreeLinearMapScalarExtension R κ ν f h).comp
        (rightFreeLinearMapScalarExtension R ι κ f g) := by
  apply LinearMap.pi_ext
  intro j s
  simp only [LinearMap.comp_apply, rightFreeLinearMapScalarExtension_single]
  change MulOpposite.op s • (fun i ↦ f (h (g (Pi.single j 1)) i)) =
    rightFreeLinearMapScalarExtension R κ ν f h
      (MulOpposite.op s • (fun k ↦ f (g (Pi.single j 1) k)))
  rw [map_smul, rightFreeLinearMapScalarExtension_coefficients]

open Classical in
theorem rightFreeLinearMapScalarExtension_ringHom_comp (q : S →+* T) :
    rightFreeLinearMapScalarExtension R ι κ (q.comp f) g =
      rightFreeLinearMapScalarExtension S ι κ q
        (rightFreeLinearMapScalarExtension R ι κ f g) := by
  apply LinearMap.pi_ext
  intro j t
  funext i
  simp [rightFreeLinearMapScalarExtension_single]

open Classical in
@[simp]
theorem rightFreeLinearMapScalarExtension_ringHom_id :
    rightFreeLinearMapScalarExtension R ι κ (RingHom.id R) g = g := by
  apply LinearMap.ext
  intro x
  simpa only [RingHom.id_apply] using
    rightFreeLinearMapScalarExtension_coefficients (RingHom.id R) g x

variable [Fintype κ] (e : (ι → R) ≃ₗ[Rᵐᵒᵖ] (κ → R))

open Classical in
theorem rightFreeScalarExtensionEquiv_toLinearMap :
    (rightFreeScalarExtensionEquiv R ι κ f e).toLinearMap =
      rightFreeLinearMapScalarExtension R ι κ f e.toLinearMap := by
  apply LinearMap.ext
  intro y
  rfl

open Classical in
/-- Transport of a specified equivalence acts by its mapped coefficients on the
left, just as transport of its underlying right-linear map does. -/
theorem rightFreeScalarExtensionEquiv_apply (y : ι → S) (i : κ) :
    rightFreeScalarExtensionEquiv R ι κ f e y i =
      ∑ j, f (e (Pi.single j 1) i) * y j := by
  exact (congrArg (fun h : (ι → S) →ₗ[Sᵐᵒᵖ] (κ → S) ↦ h y i)
    (rightFreeScalarExtensionEquiv_toLinearMap f e)).trans
      (rightFreeLinearMapScalarExtension_apply f e.toLinearMap y i)

open Classical in
@[simp]
theorem rightFreeScalarExtensionEquiv_symm :
    (rightFreeScalarExtensionEquiv R ι κ f e).symm =
      rightFreeScalarExtensionEquiv R κ ι f e.symm := by
  apply LinearEquiv.ext
  intro y
  rfl

open Classical in
theorem rightFreeScalarExtensionEquiv_trans [Fintype ν]
    (d : (κ → R) ≃ₗ[Rᵐᵒᵖ] (ν → R)) :
    rightFreeScalarExtensionEquiv R ι ν f (e.trans d) =
      (rightFreeScalarExtensionEquiv R ι κ f e).trans
        (rightFreeScalarExtensionEquiv R κ ν f d) := by
  apply LinearEquiv.toLinearMap_injective
  simpa only [rightFreeScalarExtensionEquiv_toLinearMap, LinearEquiv.coe_trans] using
    (rightFreeLinearMapScalarExtension_map_comp f e.toLinearMap d.toLinearMap)

open Classical in
@[simp]
theorem rightFreeScalarExtensionEquiv_refl :
    rightFreeScalarExtensionEquiv R ι ι f (LinearEquiv.refl _ _) =
      LinearEquiv.refl _ _ := by
  apply LinearEquiv.toLinearMap_injective
  simpa only [rightFreeScalarExtensionEquiv_toLinearMap, LinearEquiv.refl_toLinearMap] using
    (rightFreeLinearMapScalarExtension_id (ι := ι) f)

open Classical in
theorem rightFreeScalarExtensionEquiv_ringHom_comp (q : S →+* T) :
    rightFreeScalarExtensionEquiv R ι κ (q.comp f) e =
      rightFreeScalarExtensionEquiv S ι κ q (rightFreeScalarExtensionEquiv R ι κ f e) := by
  apply LinearEquiv.toLinearMap_injective
  simpa only [rightFreeScalarExtensionEquiv_toLinearMap] using
    (rightFreeLinearMapScalarExtension_ringHom_comp f e.toLinearMap q)

open Classical in
@[simp]
theorem rightFreeScalarExtensionEquiv_ringHom_id :
    rightFreeScalarExtensionEquiv R ι κ (RingHom.id R) e = e := by
  apply LinearEquiv.toLinearMap_injective
  simpa only [rightFreeScalarExtensionEquiv_toLinearMap] using
    (rightFreeLinearMapScalarExtension_ringHom_id e.toLinearMap)

end CharacteristicLaws

section TensorCompatibility

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]

open Classical in
/-- The finite-coordinate construction agrees with unbundled Ring scalar
extension. Independent index universes are retained without using `mapIso`. -/
theorem rightFreeLinearMapScalarExtension_eq_rightExtension
    (f : R →+* S) (g : (ι → R) →ₗ[Rᵐᵒᵖ] (κ → R)) :
    rightFreeLinearMapScalarExtension R ι κ f g =
      LinearEquiv.arrowCongrAddEquiv
        (ModuleCat.RightExtension.rightFreeLinearEquiv f ι)
        (ModuleCat.RightExtension.rightFreeLinearEquiv f κ)
        (ModuleCat.RightExtension.map f g) := by
  have h :
      (rightFreeLinearMapScalarExtension R ι κ f g).comp
          (ModuleCat.RightExtension.rightFreeLinearEquiv f ι).toLinearMap =
        (ModuleCat.RightExtension.rightFreeLinearEquiv f κ).toLinearMap.comp
          (ModuleCat.RightExtension.map f g) := by
    apply ModuleCat.RightExtension.linearMap_ext f
    intro x s
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      ModuleCat.RightExtension.map_tmul, ModuleCat.RightExtension.rightFreeLinearEquiv_tmul]
    have hsmul : (fun j ↦ f (x j) * s) =
        MulOpposite.op s • (fun j ↦ f (x j)) := rfl
    rw [hsmul, map_smul, rightFreeLinearMapScalarExtension_coefficients]
    rfl
  apply LinearMap.ext
  intro y
  change rightFreeLinearMapScalarExtension R ι κ f g y =
    ModuleCat.RightExtension.rightFreeLinearEquiv f κ
      (ModuleCat.RightExtension.map f g
        ((ModuleCat.RightExtension.rightFreeLinearEquiv f ι).symm y))
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply] using
    DFunLike.congr_fun h ((ModuleCat.RightExtension.rightFreeLinearEquiv f ι).symm y)

/-- The tensor-map bridge with the caller's coordinate equality decisions. -/
theorem rightFreeLinearMapScalarExtension_eq_rightExtension_of_decidableEq
    [DecidableEq ι] [DecidableEq κ]
    (f : R →+* S) (g : (ι → R) →ₗ[Rᵐᵒᵖ] (κ → R)) :
    rightFreeLinearMapScalarExtension R ι κ f g =
      LinearEquiv.arrowCongrAddEquiv
        (ModuleCat.RightExtension.rightFreeLinearEquiv f ι)
        (ModuleCat.RightExtension.rightFreeLinearEquiv f κ)
        (ModuleCat.RightExtension.map f g) := by
  cases Subsingleton.elim ‹DecidableEq ι› (Classical.decEq ι)
  cases Subsingleton.elim ‹DecidableEq κ› (Classical.decEq κ)
  exact rightFreeLinearMapScalarExtension_eq_rightExtension f g

open Classical in
/-- Pure-tensor compatibility with the existing canonical Ring equivalences. -/
theorem rightFreeLinearMapScalarExtension_tmul
    (f : R →+* S) (g : (ι → R) →ₗ[Rᵐᵒᵖ] (κ → R)) (x : ι → R) (s : S) :
    rightFreeLinearMapScalarExtension R ι κ f g
        (ModuleCat.RightExtension.rightFreeLinearEquiv f ι
          (ModuleCat.RightExtension.tmul f x s)) =
      ModuleCat.RightExtension.rightFreeLinearEquiv f κ
        (ModuleCat.RightExtension.tmul f (g x) s) := by
  rw [rightFreeLinearMapScalarExtension_eq_rightExtension]
  change ModuleCat.RightExtension.rightFreeLinearEquiv f κ
    (ModuleCat.RightExtension.map f g
      ((ModuleCat.RightExtension.rightFreeLinearEquiv f ι).symm
        (ModuleCat.RightExtension.rightFreeLinearEquiv f ι
          (ModuleCat.RightExtension.tmul f x s)))) = _
  rw [LinearEquiv.symm_apply_apply, ModuleCat.RightExtension.map_tmul]

/-- Pure-tensor compatibility with the caller's coordinate equality decisions. -/
theorem rightFreeLinearMapScalarExtension_tmul_of_decidableEq
    [DecidableEq ι] [DecidableEq κ]
    (f : R →+* S) (g : (ι → R) →ₗ[Rᵐᵒᵖ] (κ → R)) (x : ι → R) (s : S) :
    rightFreeLinearMapScalarExtension R ι κ f g
        (ModuleCat.RightExtension.rightFreeLinearEquiv f ι
          (ModuleCat.RightExtension.tmul f x s)) =
      ModuleCat.RightExtension.rightFreeLinearEquiv f κ
        (ModuleCat.RightExtension.tmul f (g x) s) := by
  cases Subsingleton.elim ‹DecidableEq ι› (Classical.decEq ι)
  cases Subsingleton.elim ‹DecidableEq κ› (Classical.decEq κ)
  exact rightFreeLinearMapScalarExtension_tmul f g x s

open Classical in
/-- The transported specified equivalence has the unbundled tensor map as its
underlying map; this bridge allows independent source and target universes. -/
theorem rightFreeScalarExtensionEquiv_toLinearMap_eq_rightExtension
    (f : R →+* S) (e : (ι → R) ≃ₗ[Rᵐᵒᵖ] (κ → R)) :
    (rightFreeScalarExtensionEquiv R ι κ f e).toLinearMap =
      LinearEquiv.arrowCongrAddEquiv
        (ModuleCat.RightExtension.rightFreeLinearEquiv f ι)
        (ModuleCat.RightExtension.rightFreeLinearEquiv f κ)
        (ModuleCat.RightExtension.map f e.toLinearMap) := by
  rw [rightFreeScalarExtensionEquiv_toLinearMap]
  exact rightFreeLinearMapScalarExtension_eq_rightExtension f e.toLinearMap

/-- The underlying tensor-map bridge for a specified equivalence, using the
caller's coordinate equality decisions. -/
theorem rightFreeScalarExtensionEquiv_toLinearMap_eq_rightExtension_of_decidableEq
    [DecidableEq ι] [DecidableEq κ]
    (f : R →+* S) (e : (ι → R) ≃ₗ[Rᵐᵒᵖ] (κ → R)) :
    (rightFreeScalarExtensionEquiv R ι κ f e).toLinearMap =
      LinearEquiv.arrowCongrAddEquiv
        (ModuleCat.RightExtension.rightFreeLinearEquiv f ι)
        (ModuleCat.RightExtension.rightFreeLinearEquiv f κ)
        (ModuleCat.RightExtension.map f e.toLinearMap) := by
  cases Subsingleton.elim ‹DecidableEq ι› (Classical.decEq ι)
  cases Subsingleton.elim ‹DecidableEq κ› (Classical.decEq κ)
  exact rightFreeScalarExtensionEquiv_toLinearMap_eq_rightExtension f e

end TensorCompatibility

section SquareScalarExtension

variable (R : Type uR) [Semiring R]
variable (ι : Type uι) [Fintype ι]

/-- The square specialization of specified finite right-free map transport.
No coordinate equality decision is required. -/
noncomputable def rightEndomorphismScalarExtension
    {S : Type uS} [Semiring S] (f : R →+* S)
    (g : Module.End Rᵐᵒᵖ (ι → R)) :
    Module.End Sᵐᵒᵖ (ι → S) :=
  rightFreeLinearMapScalarExtension R ι ι f g

/-- The old square operation is the specialization of the rectangular one. -/
theorem rightEndomorphismScalarExtension_eq_rightFreeLinearMapScalarExtension
    {S : Type uS} [Semiring S] (f : R →+* S)
    (g : Module.End Rᵐᵒᵖ (ι → R)) :
    rightEndomorphismScalarExtension R ι f g =
      rightFreeLinearMapScalarExtension R ι ι f g := rfl

variable [DecidableEq ι]

/-- Scalar extension of a finite free right-module endomorphism acts on a
standard basis vector by applying the coefficient homomorphism coordinatewise. -/
@[simp]
theorem rightEndomorphismScalarExtension_single
    {S : Type uS} [Semiring S] (f : R →+* S)
    (g : Module.End Rᵐᵒᵖ (ι → R)) (j : ι) :
    rightEndomorphismScalarExtension R ι f g (Pi.single j 1) =
      fun i ↦ f (g (Pi.single j 1) i) := by
  cases Subsingleton.elim ‹DecidableEq ι› (Classical.decEq ι)
  simpa only [rightEndomorphismScalarExtension, mul_one] using
    rightFreeLinearMapScalarExtension_single f g j (1 : S)

/-- The matrix of a scalar-extended finite free right-module endomorphism is
obtained by applying the coefficient homomorphism entrywise. -/
theorem rightEndomorphismMatrixEquiv_scalarExtension
    {S : Type uS} [Semiring S] (f : R →+* S)
    (g : Module.End Rᵐᵒᵖ (ι → R)) :
    f.mapMatrix (rightEndomorphismMatrixEquiv R ι g) =
      rightEndomorphismMatrixEquiv S ι
        (rightEndomorphismScalarExtension R ι f g) := by
  ext i j
  simp

end SquareScalarExtension

section RingSquareCompatibility

variable (R : Type uR) [Ring R]
variable (ι : Type uι) [Fintype ι] [DecidableEq ι]

/-- Compatibility with the original Ring tensor-conjugation implementation,
not just with its coordinate signature. -/
theorem rightEndomorphismScalarExtension_eq_tensor
    {S : Type uS} [Ring S] (f : R →+* S)
    (g : Module.End Rᵐᵒᵖ (ι → R)) :
    rightEndomorphismScalarExtension R ι f g =
      (ModuleCat.RightExtension.rightFreeLinearEquiv f ι).toLinearMap.comp
        ((ModuleCat.RightExtension.map f g).comp
          (ModuleCat.RightExtension.rightFreeLinearEquiv f ι).symm.toLinearMap) := by
  rw [rightEndomorphismScalarExtension,
    rightFreeLinearMapScalarExtension_eq_rightExtension_of_decidableEq]
  ext y
  rfl

omit [DecidableEq ι] in
/-- Bijectivity of a finite free right-module endomorphism is reflected from
its scalar extension to a quasi-regular quotient. -/
theorem rightEndomorphism_bijective_of_quotientScalarExtension_bijective
    (I : TwoSidedIdeal R) (hI : I.IsQuasiregular)
    (g : Module.End Rᵐᵒᵖ (ι → R))
    (hg : Bijective (rightEndomorphismScalarExtension R ι
      (Ideal.Quotient.mk I.asIdeal) g)) :
    Bijective g := by
  classical
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

end RingSquareCompatibility

end Module
