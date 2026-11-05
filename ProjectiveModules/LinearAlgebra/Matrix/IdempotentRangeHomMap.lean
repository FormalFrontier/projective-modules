/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Matrix.IdempotentRangeHom
public import ProjectiveModules.Module.RightEndomorphismMatrix
public import ProjectiveModules.Module.RightExtensionMatrixRange

/-!
# Coefficient change of idempotent range homomorphisms

Coefficient maps induce additive maps on right-linear homomorphisms between finite
idempotent column ranges. They act by entrywise coefficient change on normalized
matrices, using the range-Hom equivalence and the induced column action. Over rings,
this agrees with the extension-of-scalars comparison of the two ranges.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix

universe uR uS uT uι uκ uν

namespace Matrix
section Semiring

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [Semiring R] [Semiring S] [Semiring T]
variable {ι : Type uι} {κ : Type uκ} {ν : Type uν}
variable [Fintype ι] [Fintype κ] [Fintype ν]

namespace normalizedHom
variable {A : Matrix ι ι R} {B : Matrix κ κ R}

/-- Coefficient change of normalized matrices; no idempotence hypothesis. -/
noncomputable def map (φ : R →+* S) :
    normalizedHom A B →+ normalizedHom (A.map φ) (B.map φ) where
  toFun Y := ⟨(Y : Matrix κ ι R).map φ, by
    rcases (mem_normalizedHom A B (Y : Matrix κ ι R)).mp Y.property with ⟨hBY, hYA⟩
    apply (mem_normalizedHom (A.map φ) (B.map φ) _).mpr
    constructor
    · rw [← Matrix.map_mul, hBY]
    · rw [← Matrix.map_mul, hYA]⟩
  map_zero' := by
    apply Subtype.ext
    funext i j
    exact φ.map_zero
  map_add' := by
    intro Y Z
    apply Subtype.ext
    funext i j
    exact φ.map_add _ _

@[simp] theorem coe_map (φ : R →+* S) (Y : normalizedHom A B) :
    (map φ Y : Matrix κ ι S) = (Y : Matrix κ ι R).map φ :=
  rfl

end normalizedHom

variable {A : Matrix ι ι R} {B : Matrix κ κ R}

/-- Additive coefficient change on right-linear maps between idempotent column ranges. -/
noncomputable def rangeHomMap (φ : R →+* S)
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B) :
    ((mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ]
      (mulVecBilin R Rᵐᵒᵖ B).range) →+
    ((mulVecBilin S Sᵐᵒᵖ (A.map φ)).range →ₗ[Sᵐᵒᵖ]
      (mulVecBilin S Sᵐᵒᵖ (B.map φ)).range) :=
  (normalizedHom.toRangeHom (A := A.map φ) (B := B.map φ)).comp
    ((normalizedHom.map (A := A) (B := B) φ).comp
      (rangeHomEquiv hA hB).toAddMonoidHom)

/-- The classifier intertwines coefficient change with entrywise matrix change.
The image-idempotence proofs are typing witnesses, not additional restrictions. -/
@[simp]
theorem rangeHomEquiv_rangeHomMap (φ : R →+* S)
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B)
    (hAφ : IsIdempotentElem (A.map φ))
    (hBφ : IsIdempotentElem (B.map φ))
    (g : (mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ]
      (mulVecBilin R Rᵐᵒᵖ B).range) :
    rangeHomEquiv hAφ hBφ (rangeHomMap φ hA hB g) =
      normalizedHom.map φ (rangeHomEquiv hA hB g) := by
  exact rangeHomEquiv_toRangeHom hAφ hBφ _

/-- Coefficient change on columns in the image of the source matrix. -/
theorem rangeHomMap_apply_projected (φ : R →+* S)
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B)
    (g : (mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ]
      (mulVecBilin R Rᵐᵒᵖ B).range) (x : ι → R) :
    ((rangeHomMap φ hA hB g)
      ((mulVecBilin S Sᵐᵒᵖ (A.map φ)).rangeRestrict
        (fun j ↦ φ (x j))) : κ → S) =
      fun k ↦ φ ((g ((mulVecBilin R Rᵐᵒᵖ A).rangeRestrict x) :
        κ → R) k) := by
  change ((normalizedHom.toRangeHom
      (normalizedHom.map φ (rangeHomEquiv hA hB g)))
      ((mulVecBilin S Sᵐᵒᵖ (A.map φ)).rangeRestrict
        (fun j ↦ φ (x j))) : κ → S) = _
  rw [normalizedHom.toRangeHom_apply]
  funext k
  change (∑ j, φ ((rangeHomEquiv hA hB g : Matrix κ ι R) k j) *
      (∑ l, φ (A j l) * φ (x l))) =
    φ ((g ((mulVecBilin R Rᵐᵒᵖ A).rangeRestrict x) : κ → R) k)
  simp only [← _root_.map_mul, ← _root_.map_sum]
  exact congrArg φ (congrFun (rangeHomEquiv_apply_mulVec hA hB g
    ((mulVecBilin R Rᵐᵒᵖ A).rangeRestrict x)) k)

/-- Identity coefficient transition, not identity morphism. -/
theorem rangeHomMap_id_coefficients
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B)
    (g : (mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ]
      (mulVecBilin R Rᵐᵒᵖ B).range) :
    rangeHomMap (RingHom.id R) hA hB g = g := by
  apply (rangeHomEquiv hA hB).injective
  apply Subtype.ext
  exact congrArg Subtype.val
    (rangeHomEquiv_rangeHomMap (RingHom.id R) hA hB hA hB g)

/-- Composition of coefficient changes. -/
theorem rangeHomMap_comp_coefficients (φ : R →+* S) (ψ : S →+* T)
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B)
    (hAφ : IsIdempotentElem (A.map φ))
    (hBφ : IsIdempotentElem (B.map φ))
    (g : (mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ]
      (mulVecBilin R Rᵐᵒᵖ B).range) :
    rangeHomMap ψ hAφ hBφ (rangeHomMap φ hA hB g) =
      rangeHomMap (ψ.comp φ) hA hB g := by
  have hAψφ : IsIdempotentElem ((A.map φ).map ψ) := by
    classical
    exact hAφ.map (ψ.mapMatrix)
  have hBψφ : IsIdempotentElem ((B.map φ).map ψ) := by
    classical
    exact hBφ.map (ψ.mapMatrix)
  apply (rangeHomEquiv hAψφ hBψφ).injective
  apply Subtype.ext
  have h₁ := congrArg Subtype.val
    (rangeHomEquiv_rangeHomMap ψ hAφ hBφ hAψφ hBψφ
      (rangeHomMap φ hA hB g))
  have h₂ := congrArg
    (fun Y : normalizedHom (A.map φ) (B.map φ) ↦
      (Y : Matrix κ ι S).map ψ)
    (rangeHomEquiv_rangeHomMap φ hA hB hAφ hBφ g)
  have h₃ := congrArg Subtype.val
    (rangeHomEquiv_rangeHomMap (ψ.comp φ) hA hB hAψφ hBψφ g)
  exact h₁.trans (h₂.trans h₃.symm)

/-- Coefficient change preserves the identity range homomorphism. -/
@[simp] theorem rangeHomMap_id (φ : R →+* S)
    (hA : IsIdempotentElem A) :
    rangeHomMap φ hA hA
      (LinearMap.id : (mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ]
        (mulVecBilin R Rᵐᵒᵖ A).range) =
      (LinearMap.id : (mulVecBilin S Sᵐᵒᵖ (A.map φ)).range →ₗ[Sᵐᵒᵖ]
        (mulVecBilin S Sᵐᵒᵖ (A.map φ)).range) := by
  have hAφ : IsIdempotentElem (A.map φ) := by
    classical
    exact hA.map (φ.mapMatrix)
  apply (rangeHomEquiv hAφ hAφ).injective
  rw [rangeHomEquiv_rangeHomMap φ hA hA hAφ hAφ]
  apply Subtype.ext
  simp only [normalizedHom.coe_map, coe_rangeHomEquiv_id]

/-- Coefficient change preserves composition of range homomorphisms. -/
theorem rangeHomMap_comp (φ : R →+* S) {C : Matrix ν ν R}
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B)
    (hC : IsIdempotentElem C)
    (g : (mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ]
      (mulVecBilin R Rᵐᵒᵖ B).range)
    (h : (mulVecBilin R Rᵐᵒᵖ B).range →ₗ[Rᵐᵒᵖ]
      (mulVecBilin R Rᵐᵒᵖ C).range) :
    rangeHomMap φ hA hC (h.comp g) =
      (rangeHomMap φ hB hC h).comp (rangeHomMap φ hA hB g) := by
  have hAφ : IsIdempotentElem (A.map φ) := by
    classical
    exact hA.map (φ.mapMatrix)
  have hBφ : IsIdempotentElem (B.map φ) := by
    classical
    exact hB.map (φ.mapMatrix)
  have hCφ : IsIdempotentElem (C.map φ) := by
    classical
    exact hC.map (φ.mapMatrix)
  apply (rangeHomEquiv hAφ hCφ).injective
  rw [rangeHomEquiv_rangeHomMap φ hA hC hAφ hCφ]
  apply Subtype.ext
  simp only [normalizedHom.coe_map,
    coe_rangeHomEquiv_comp hA hB hC g h,
    coe_rangeHomEquiv_comp hAφ hBφ hCφ
      (rangeHomMap φ hA hB g) (rangeHomMap φ hB hC h),
    Matrix.map_mul, rangeHomEquiv_rangeHomMap]

end Semiring

section RingComparison
variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]
variable {A : Matrix ι ι R} {B : Matrix κ κ R}

/-- Over rings, coefficient change agrees with extension of scalars. -/
theorem rangeHomMap_eq_rightExtension (φ : R →+* S)
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B)
    (g : (mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ]
      (mulVecBilin R Rᵐᵒᵖ B).range) :
    rangeHomMap φ hA hB g =
      LinearEquiv.arrowCongrAddEquiv
        (ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv φ A hA)
        (ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv φ B hB)
        (ModuleCat.RightExtension.map φ g) := by
  have hAφ : IsIdempotentElem (A.map φ) := by
    classical
    exact hA.map (φ.mapMatrix)
  have hBφ : IsIdempotentElem (B.map φ) := by
    classical
    exact hB.map (φ.mapMatrix)
  have hcomp :
      (rangeHomMap φ hA hB g).comp
          (ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv φ A hA).toLinearMap =
        (ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv φ B hB).toLinearMap.comp
          (ModuleCat.RightExtension.map φ g) := by
    apply ModuleCat.RightExtension.linearMap_ext φ
    intro v s
    apply Subtype.ext
    change (rangeHomMap φ hA hB g
        (ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv φ A hA
          (ModuleCat.RightExtension.tmul φ v s)) : κ → S) =
      (ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv φ B hB
        (ModuleCat.RightExtension.map φ g
          (ModuleCat.RightExtension.tmul φ v s)) : κ → S)
    have hcoord := rangeHomEquiv_apply_mulVec hAφ hBφ
      (rangeHomMap φ hA hB g)
      (ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv φ A hA
        (ModuleCat.RightExtension.tmul φ v s))
    rw [rangeHomEquiv_rangeHomMap φ hA hB hAφ hBφ] at hcoord
    rw [← hcoord]
    simp only [ModuleCat.RightExtension.map_tmul,
      ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv_tmul]
    funext k
    change (∑ j, φ ((rangeHomEquiv hA hB g : Matrix κ ι R) k j) *
        (φ ((v : ι → R) j) * s)) = φ ((g v : κ → R) k) * s
    simp only [← mul_assoc]
    rw [← Finset.sum_mul]
    simp only [← _root_.map_mul, ← _root_.map_sum]
    exact congrArg (fun r : R ↦ φ r * s)
      (congrFun (rangeHomEquiv_apply_mulVec hA hB g v) k)
  apply LinearMap.ext
  intro v
  change rangeHomMap φ hA hB g v =
    ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv φ B hB
      (ModuleCat.RightExtension.map φ g
        ((ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv φ A hA).symm v))
  have hv := DFunLike.congr_fun hcomp
    ((ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv φ A hA).symm v)
  change rangeHomMap φ hA hB g
      (ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv φ A hA
        ((ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv φ A hA).symm v)) =
    ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv φ B hB
      (ModuleCat.RightExtension.map φ g
        ((ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv φ A hA).symm v)) at hv
  simpa only [LinearEquiv.apply_symm_apply] using hv

end RingComparison
end Matrix
