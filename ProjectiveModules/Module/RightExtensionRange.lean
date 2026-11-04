/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.RightExtension
public import Mathlib.LinearAlgebra.Projection

/-!
# Scalar extension of the range of an idempotent

Extension of scalars for right modules over arbitrary rings commutes with taking
an idempotent's range. The comparison is induced by the original range inclusion,
and its inverse is induced by the original range corestriction. No flatness or
finiteness assumption is needed: extension of scalars preserves the splitting.

## References

The construction uses Mathlib's projection and `LinearEquiv.ofLeftInverse` APIs,
following the retract argument of `Module.reductionRangeEquiv` for module reduction.
The finite-matrix case is the scalar-extension comparison in idempotent presentations
of projective modules; see Charles A. Weibel, *The K-book: An Introduction to
Algebraic K-theory*, Chapter I.
-/

@[expose] public section

universe uR uS uM

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable (f : R →+* S)

/-- Scalar extension commutes with the range of an idempotent endomorphism of a
right module. The forward map is induced by the original range inclusion, and
the inverse by the original range corestriction. The range-splitting argument
follows `Module.reductionRangeEquiv`. -/
def idempotentRangeLinearEquiv (p : M →ₗ[Rᵐᵒᵖ] M) (hp : IsIdempotentElem p) :
    Obj f (LinearMap.range p) ≃ₗ[Sᵐᵒᵖ] LinearMap.range (map f p) := by
  have hsplit : p.rangeRestrict.comp (LinearMap.range p).subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (LinearMap.IsIdempotentElem.mem_range_iff hp).mp x.property
  have hleft : Function.LeftInverse (map f p.rangeRestrict)
      (map f (LinearMap.range p).subtype) := by
    have hmap : (map f p.rangeRestrict).comp
        (map f (LinearMap.range p).subtype) = LinearMap.id := by
      rw [← map_comp, hsplit, map_id]
    intro z
    exact LinearMap.congr_fun hmap z
  have hfactor : (map f (LinearMap.range p).subtype).comp
      (map f p.rangeRestrict) = map f p := by
    rw [← map_comp, LinearMap.subtype_comp_rangeRestrict]
  have hrange : LinearMap.range (map f (LinearMap.range p).subtype) =
      LinearMap.range (map f p) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      refine ⟨map f (LinearMap.range p).subtype z, ?_⟩
      rw [← hfactor, LinearMap.comp_apply, hleft z]
    · rintro _ ⟨y, rfl⟩
      exact ⟨map f p.rangeRestrict y, LinearMap.congr_fun hfactor y⟩
  exact (LinearEquiv.ofLeftInverse hleft).trans (LinearEquiv.ofEq _ _ hrange)

/-- The comparison has ambient value given by scalar extension of the original
range inclusion. -/
@[simp] theorem idempotentRangeLinearEquiv_apply
    (p : M →ₗ[Rᵐᵒᵖ] M) (hp : IsIdempotentElem p)
    (z : Obj f (LinearMap.range p)) :
    (idempotentRangeLinearEquiv f p hp z : Obj f M) =
      map f (LinearMap.range p).subtype z := by
  simp only [idempotentRangeLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofLeftInverse_apply]

/-- Composing the comparison with the extended range inclusion gives scalar
extension of the original range inclusion. -/
theorem idempotentRangeLinearEquiv_subtype_comp
    (p : M →ₗ[Rᵐᵒᵖ] M) (hp : IsIdempotentElem p) :
    (LinearMap.range (map f p)).subtype.comp
        (idempotentRangeLinearEquiv f p hp).toLinearMap =
      map f (LinearMap.range p).subtype := by
  apply LinearMap.ext
  intro z
  exact idempotentRangeLinearEquiv_apply f p hp z

/-- On pure tensors, the comparison is induced by inclusion of the original
idempotent range. -/
theorem idempotentRangeLinearEquiv_tmul
    (p : M →ₗ[Rᵐᵒᵖ] M) (hp : IsIdempotentElem p)
    (x : LinearMap.range p) (s : S) :
    (idempotentRangeLinearEquiv f p hp (tmul f x s) : Obj f M) =
      tmul f (x : M) s := by
  rw [idempotentRangeLinearEquiv_apply, map_tmul, Submodule.subtype_apply]

/-- The inverse comparison is scalar extension of the original range
corestriction, evaluated on the ambient value. -/
@[simp] theorem idempotentRangeLinearEquiv_symm_apply
    (p : M →ₗ[Rᵐᵒᵖ] M) (hp : IsIdempotentElem p)
    (y : LinearMap.range (map f p)) :
    (idempotentRangeLinearEquiv f p hp).symm y =
      map f p.rangeRestrict (y : Obj f M) := by
  simp only [idempotentRangeLinearEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.ofLeftInverse_symm_apply, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply]

end ModuleCat.RightExtension
