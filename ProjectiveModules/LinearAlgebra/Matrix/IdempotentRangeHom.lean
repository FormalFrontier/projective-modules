/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv
public import ProjectiveModules.LinearAlgebra.Matrix.IdempotentRanges

/-!
# Matrices for homomorphisms between idempotent ranges

The additive correspondence between right-linear maps of idempotent ranges and
normalized rectangular matrices is characterized by its action on columns.
-/

@[expose] public section

universe u v w

namespace Matrix

variable {R : Type u} [Semiring R]
variable {ι : Type v} [Fintype ι] {κ : Type w} [Fintype κ]
variable {A : Matrix ι ι R} {B : Matrix κ κ R}

/-- The inverse correspondence is the induced map of right ranges. -/
@[simp]
theorem rangeHomEquiv_symm_apply (hA : IsIdempotentElem A)
    (hB : IsIdempotentElem B) (Y : normalizedHom A B) :
    (rangeHomEquiv hA hB).symm Y = normalizedHom.toRangeHom Y :=
  rfl

/-- Reconstructing a range map from its coordinate matrix returns that map. -/
@[simp]
theorem toRangeHom_rangeHomEquiv (hA : IsIdempotentElem A)
    (hB : IsIdempotentElem B)
    (f : (mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ] (mulVecBilin R Rᵐᵒᵖ B).range) :
    normalizedHom.toRangeHom (rangeHomEquiv hA hB f) = f := by
  simpa only [rangeHomEquiv_symm_apply] using
    (rangeHomEquiv hA hB).symm_apply_apply f

/-- The matrix of an induced range map is its original normalized matrix. -/
@[simp]
theorem rangeHomEquiv_toRangeHom (hA : IsIdempotentElem A)
    (hB : IsIdempotentElem B) (Y : normalizedHom A B) :
    rangeHomEquiv hA hB (normalizedHom.toRangeHom Y) = Y := by
  simpa only [rangeHomEquiv_symm_apply] using
    (rangeHomEquiv hA hB).apply_symm_apply Y

/-- The map corresponding to a normalized matrix acts by column multiplication. -/
@[simp]
theorem coe_rangeHomEquiv_symm_apply (hA : IsIdempotentElem A)
    (hB : IsIdempotentElem B) (Y : normalizedHom A B)
    (v : (mulVecBilin R Rᵐᵒᵖ A).range) :
    ((rangeHomEquiv hA hB).symm Y v : κ → R) =
      (Y : Matrix κ ι R) *ᵥ (v : ι → R) := by
  exact normalizedHom.toRangeHom_apply Y v

/-- The coordinate matrix reproduces the original homomorphism on its source range. -/
theorem rangeHomEquiv_apply_mulVec (hA : IsIdempotentElem A)
    (hB : IsIdempotentElem B)
    (f : (mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ] (mulVecBilin R Rᵐᵒᵖ B).range)
    (v : (mulVecBilin R Rᵐᵒᵖ A).range) :
    (rangeHomEquiv hA hB f : Matrix κ ι R) *ᵥ (v : ι → R) = (f v : κ → R) := by
  have h := congrArg
    (fun g : (mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ] (mulVecBilin R Rᵐᵒᵖ B).range =>
      (g v : κ → R)) ((rangeHomEquiv hA hB).symm_apply_apply f)
  simpa only [coe_rangeHomEquiv_symm_apply] using h

/-- Equality-induced range comparisons do not change the coordinate matrix of a
range homomorphism. -/
theorem coe_rangeHomEquiv_arrowCongrAddEquiv_ofEq
    {A' : Matrix ι ι R} {B' : Matrix κ κ R}
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B)
    (hA' : IsIdempotentElem A') (hB' : IsIdempotentElem B')
    (eA : A = A') (eB : B = B')
    (g : (mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ]
      (mulVecBilin R Rᵐᵒᵖ B).range) :
    (rangeHomEquiv hA' hB'
        (LinearEquiv.arrowCongrAddEquiv
          (LinearEquiv.ofEq _ _
            (congrArg (fun C : Matrix ι ι R =>
              (mulVecBilin R Rᵐᵒᵖ C).range) eA))
          (LinearEquiv.ofEq _ _
            (congrArg (fun C : Matrix κ κ R =>
              (mulVecBilin R Rᵐᵒᵖ C).range) eB)) g) : Matrix κ ι R) =
      (rangeHomEquiv hA hB g : Matrix κ ι R) := by
  cases eA
  cases eB
  rfl

/-- The identity range map corresponds to the idempotent matrix itself. -/
@[simp]
theorem rangeHomEquiv_id (hA : IsIdempotentElem A) :
    rangeHomEquiv hA hA LinearMap.id = normalizedHom.id hA := by
  apply (rangeHomEquiv hA hA).symm.injective
  simp only [AddEquiv.symm_apply_apply, rangeHomEquiv_symm_apply,
    normalizedHom.toRangeHom_id]

/-- The underlying matrix of the identity range map is its idempotent. -/
theorem coe_rangeHomEquiv_id (hA : IsIdempotentElem A) :
    (rangeHomEquiv hA hA LinearMap.id : Matrix ι ι R) = A := by
  simp only [rangeHomEquiv_id, normalizedHom.coe_id]

section Composition

universe z

variable {η : Type z} [Fintype η] {C : Matrix η η R}

/-- The correspondence preserves composition of range maps. -/
@[simp]
theorem rangeHomEquiv_comp (hA : IsIdempotentElem A) (hB : IsIdempotentElem B)
    (hC : IsIdempotentElem C)
    (f : (mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ] (mulVecBilin R Rᵐᵒᵖ B).range)
    (g : (mulVecBilin R Rᵐᵒᵖ B).range →ₗ[Rᵐᵒᵖ] (mulVecBilin R Rᵐᵒᵖ C).range) :
    rangeHomEquiv hA hC (g.comp f) =
      normalizedHom.comp (rangeHomEquiv hB hC g) (rangeHomEquiv hA hB f) := by
  apply (rangeHomEquiv hA hC).symm.injective
  simp only [AddEquiv.symm_apply_apply, rangeHomEquiv_symm_apply,
    normalizedHom.toRangeHom_comp, toRangeHom_rangeHomEquiv]

/-- The coordinate of a composite is the product of the coordinates in function order. -/
theorem coe_rangeHomEquiv_comp (hA : IsIdempotentElem A) (hB : IsIdempotentElem B)
    (hC : IsIdempotentElem C)
    (f : (mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ] (mulVecBilin R Rᵐᵒᵖ B).range)
    (g : (mulVecBilin R Rᵐᵒᵖ B).range →ₗ[Rᵐᵒᵖ] (mulVecBilin R Rᵐᵒᵖ C).range) :
    (rangeHomEquiv hA hC (g.comp f) : Matrix η ι R) =
      (rangeHomEquiv hB hC g : Matrix η κ R) *
        (rangeHomEquiv hA hB f : Matrix κ ι R) := by
  exact congrArg Subtype.val (rangeHomEquiv_comp hA hB hC f g)

end Composition

end Matrix
