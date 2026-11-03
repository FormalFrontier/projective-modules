/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Reduction

/-!
# Reduction of the range of an idempotent

For an idempotent endomorphism, reduction of its range is canonically equivalent
to the range of its reduction. The comparison is induced by the range inclusion,
and its inverse is induced by the range corestriction.

The construction reduces the splitting of the range inclusion and uses Mathlib's
`LinearEquiv.ofLeftInverse`, followed by `LinearEquiv.ofEq` for the equality of
the two reduced ranges. No nilpotence or finiteness assumption is needed.
-/

@[expose] public section

universe u v

namespace Module

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (I : Ideal R) [I.IsTwoSided]

/-- Reduction commutes with taking the range of an idempotent endomorphism.
The forward map is induced by the range inclusion, and the inverse by the range
corestriction. -/
def reductionRangeEquiv (e : Module.End R M) (he : IsIdempotentElem e) :
    Reduction I (LinearMap.range e) ≃ₗ[R ⧸ I] LinearMap.range (reductionMap I e) := by
  have hleft : Function.LeftInverse (reductionMap I e.rangeRestrict)
      (reductionMap I (LinearMap.range e).subtype) := by
    have hsplit : e.rangeRestrict.comp (LinearMap.range e).subtype = LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact (LinearMap.IsIdempotentElem.mem_range_iff he).mp x.property
    have hred : (reductionMap I e.rangeRestrict).comp
        (reductionMap I (LinearMap.range e).subtype) = LinearMap.id := by
      rw [← reductionMap_comp, hsplit, reductionMap_id]
    intro a
    exact LinearMap.congr_fun hred a
  have hrange : LinearMap.range (reductionMap I (LinearMap.range e).subtype) =
      LinearMap.range (reductionMap I e) := by
    have hfactor : (reductionMap I (LinearMap.range e).subtype).comp
        (reductionMap I e.rangeRestrict) = reductionMap I e := by
      rw [← reductionMap_comp, LinearMap.subtype_comp_rangeRestrict]
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      refine ⟨reductionMap I (LinearMap.range e).subtype a, ?_⟩
      rw [← hfactor, LinearMap.comp_apply, hleft a]
    · rintro _ ⟨b, rfl⟩
      exact ⟨reductionMap I e.rangeRestrict b, LinearMap.congr_fun hfactor b⟩
  exact (LinearEquiv.ofLeftInverse hleft).trans (LinearEquiv.ofEq _ _ hrange)

/-- The comparison has ambient value given by the reduced range inclusion. -/
@[simp] theorem reductionRangeEquiv_apply
    (e : Module.End R M) (he : IsIdempotentElem e)
    (a : Reduction I (LinearMap.range e)) :
    (reductionRangeEquiv I e he a : Reduction I M) =
      reductionMap I (LinearMap.range e).subtype a := by
  simp only [reductionRangeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofLeftInverse_apply]

/-- Composing the comparison with the reduced range inclusion gives reduction
of the original range inclusion. -/
@[simp] theorem reductionRangeEquiv_subtype_comp
    (e : Module.End R M) (he : IsIdempotentElem e) :
    (LinearMap.range (reductionMap I e)).subtype.comp
        (reductionRangeEquiv I e he).toLinearMap =
      reductionMap I (LinearMap.range e).subtype := by
  apply LinearMap.ext
  intro a
  exact reductionRangeEquiv_apply I e he a

/-- On representatives, the comparison is induced by inclusion of the range. -/
theorem reductionRangeEquiv_mk
    (e : Module.End R M) (he : IsIdempotentElem e) (x : LinearMap.range e) :
    (reductionRangeEquiv I e he (reductionMk I (LinearMap.range e) x) :
        Reduction I M) = reductionMk I M (x : M) := by
  rw [reductionRangeEquiv_apply, reductionMap_mk, Submodule.subtype_apply]

/-- The inverse comparison is the reduced range corestriction on ambient values. -/
@[simp] theorem reductionRangeEquiv_symm_apply
    (e : Module.End R M) (he : IsIdempotentElem e)
    (z : LinearMap.range (reductionMap I e)) :
    (reductionRangeEquiv I e he).symm z =
      reductionMap I e.rangeRestrict (z : Reduction I M) := by
  simp only [reductionRangeEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.ofLeftInverse_symm_apply, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply]

/-- The inverse linear map is reduction of the range corestriction after inclusion. -/
@[simp] theorem reductionRangeEquiv_symm_toLinearMap
    (e : Module.End R M) (he : IsIdempotentElem e) :
    (reductionRangeEquiv I e he).symm.toLinearMap =
      (reductionMap I e.rangeRestrict).comp
        (LinearMap.range (reductionMap I e)).subtype := by
  apply LinearMap.ext
  intro z
  exact reductionRangeEquiv_symm_apply I e he z

/-- The inverse sends a representative in the reduced image to the class of its
range corestriction. -/
theorem reductionRangeEquiv_symm_mk
    (e : Module.End R M) (he : IsIdempotentElem e) (y : M) :
    (reductionRangeEquiv I e he).symm
        ⟨reductionMk I M (e y), ⟨reductionMk I M y, reductionMap_mk I e y⟩⟩ =
      reductionMk I (LinearMap.range e) (e.rangeRestrict y) := by
  rw [reductionRangeEquiv_symm_apply, reductionMap_mk]
  apply congrArg (reductionMk I (LinearMap.range e))
  apply Subtype.ext
  exact (LinearMap.IsIdempotentElem.mem_range_iff he).mp ⟨y, rfl⟩

/-- Reduction of the inclusion of an idempotent range is injective. -/
theorem reductionMap_range_subtype_injective
    (e : Module.End R M) (he : IsIdempotentElem e) :
    Function.Injective (reductionMap I (LinearMap.range e).subtype) := by
  intro a b h
  apply (reductionRangeEquiv I e he).injective
  apply Subtype.ext
  simpa only [reductionRangeEquiv_apply] using h

/-- A range element reduces to zero in the ambient module exactly when it reduces
to zero in the range of the idempotent. -/
theorem reductionMk_range_eq_zero_iff
    (e : Module.End R M) (he : IsIdempotentElem e) (x : LinearMap.range e) :
    reductionMk I M (x : M) = 0 ↔
      reductionMk I (LinearMap.range e) x = 0 := by
  constructor
  · intro hx
    apply reductionMap_range_subtype_injective I e he
    simpa only [reductionMap_mk, Submodule.subtype_apply, map_zero] using hx
  · intro hx
    have h := congrArg (reductionMap I (LinearMap.range e).subtype) hx
    simpa only [reductionMap_mk, Submodule.subtype_apply, map_zero] using h

end Module
