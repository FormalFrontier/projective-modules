/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.RightExtensionRange
public import ProjectiveModules.Module.RightEndomorphismMatrix
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Scalar extension of idempotent matrix images

For an idempotent finite matrix over an arbitrary ring, scalar extension of its
original right-module range is canonically equivalent to the range of its
entrywise image. Vectors are columns with entries in the original rings;
coefficients multiply on the left and opposite scalars act on the right.
The comparison sends a pure tensor to the column with coordinates `f (x i) * s`.

No flatness or commutativity assumption is needed. The index type may be empty,
and the rings may be zero rings. Equality decisions for the finite index type
are used only inside the construction, not required of callers.

## References

The idempotent-matrix description of finite projective modules is presented in
C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*.
The construction specializes the split-image comparison of
`ProjectiveModules.Module.RightExtensionRange` and uses the original finite-free
and matrix scalar-extension interfaces of Formal Frontier Agents. Restriction
of a linear equivalence to corresponding submodules uses Mathlib's
`LinearEquiv.ofSubmodules` API, contributed by Johannes Hölzl, Mario Carneiro,
Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis and Heather Macbeth.
-/

@[expose] public section

universe uR uS uι

open scoped Matrix

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable {ι : Type uι} [Fintype ι]

private theorem isIdempotentElem_mulVecBilin
    (A : Matrix ι ι R) (hA : IsIdempotentElem A) :
    IsIdempotentElem (Matrix.mulVecBilin R Rᵐᵒᵖ A) := by
  apply LinearMap.ext
  intro x
  change A *ᵥ (A *ᵥ x) = A *ᵥ x
  rw [Matrix.mulVec_mulVec, hA]

private theorem rightFreeLinearEquiv_map_range [DecidableEq ι]
    (f : R →+* S) (A : Matrix ι ι R) :
    (LinearMap.range (map f (Matrix.mulVecBilin R Rᵐᵒᵖ A))).map
        (rightFreeLinearEquiv f ι).toLinearMap =
      LinearMap.range (Matrix.mulVecBilin S Sᵐᵒᵖ (A.map f)) := by
  let C := rightFreeLinearEquiv f ι
  have hconj : C.toLinearMap.comp
      ((map f (Matrix.mulVecBilin R Rᵐᵒᵖ A)).comp C.symm.toLinearMap) =
      Matrix.mulVecBilin S Sᵐᵒᵖ (A.map f) :=
    (Module.rightEndomorphismScalarExtension_eq_tensor R ι f
      (Matrix.mulVecBilin R Rᵐᵒᵖ A)).symm.trans
        (Module.rightEndomorphismScalarExtension_mulVecBilin (R := R) (ι := ι) f A)
  calc
    _ = LinearMap.range (C.toLinearMap.comp
        (map f (Matrix.mulVecBilin R Rᵐᵒᵖ A))) :=
      (LinearMap.range_comp _ _).symm
    _ = LinearMap.range ((C.toLinearMap.comp
        (map f (Matrix.mulVecBilin R Rᵐᵒᵖ A))).comp C.symm.toLinearMap) :=
      (LinearMap.range_comp_of_range_eq_top _ C.symm.range).symm
    _ = LinearMap.range (Matrix.mulVecBilin S Sᵐᵒᵖ (A.map f)) := by
      rw [LinearMap.comp_assoc, hconj]

/-- Scalar extension of the original range of an idempotent finite matrix is
the range of its entrywise image. The equivalence preserves the column-vector
convention and the canonical right scalar actions. This is the change-of-rings
comparison for the idempotent-matrix description of projective modules in
C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter I. -/
@[no_expose]
noncomputable def idempotentMatrixRangeLinearEquiv
    (f : R →+* S) (A : Matrix ι ι R) (hA : IsIdempotentElem A) :
    Obj f (LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ A)) ≃ₗ[Sᵐᵒᵖ]
      LinearMap.range (Matrix.mulVecBilin S Sᵐᵒᵖ (A.map f)) := by
  classical
  exact (idempotentRangeLinearEquiv f (Matrix.mulVecBilin R Rᵐᵒᵖ A)
    (isIdempotentElem_mulVecBilin A hA)).trans
      ((rightFreeLinearEquiv f ι).ofSubmodules _ _ (rightFreeLinearEquiv_map_range f A))

/-- The ambient column of the comparison is finite-free scalar extension of
the original range inclusion. -/
@[simp] theorem idempotentMatrixRangeLinearEquiv_apply
    (f : R →+* S) (A : Matrix ι ι R) (hA : IsIdempotentElem A)
    (z : Obj f (LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ A))) :
    (idempotentMatrixRangeLinearEquiv f A hA z : ι → S) =
      rightFreeTo f ι
        (map f (LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ A)).subtype z) := by
  classical
  change rightFreeLinearEquiv f ι
      (idempotentRangeLinearEquiv f (Matrix.mulVecBilin R Rᵐᵒᵖ A)
        (isIdempotentElem_mulVecBilin A hA) z : Obj f (ι → R)) = _
  rw [idempotentRangeLinearEquiv_apply]
  rfl

/-- The matrix-range comparison commutes with inclusion into the target
column module and finite-free scalar extension. -/
theorem idempotentMatrixRangeLinearEquiv_subtype_comp
    (f : R →+* S) (A : Matrix ι ι R) (hA : IsIdempotentElem A) :
    (LinearMap.range (Matrix.mulVecBilin S Sᵐᵒᵖ (A.map f))).subtype.comp
        (idempotentMatrixRangeLinearEquiv f A hA).toLinearMap =
      (rightFreeTo f ι).comp
        (map f (LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ A)).subtype) := by
  apply LinearMap.ext
  intro z
  exact idempotentMatrixRangeLinearEquiv_apply f A hA z

/-- On a pure tensor, the comparison applies the ring homomorphism to each
original column entry and multiplies the coefficient on the right. -/
theorem idempotentMatrixRangeLinearEquiv_tmul
    (f : R →+* S) (A : Matrix ι ι R) (hA : IsIdempotentElem A)
    (x : LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ A)) (s : S) :
    (idempotentMatrixRangeLinearEquiv f A hA (tmul f x s) : ι → S) =
      fun i => f ((x : ι → R) i) * s := by
  rw [idempotentMatrixRangeLinearEquiv_apply, map_tmul,
    Submodule.subtype_apply, rightFreeTo_tmul]

end ModuleCat.RightExtension
