/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.Trace.Cyclicity
import ProjectiveModulesTests.IdempotentSpanSemiringClient

/-!
# Cyclicity between a nonfree ideal and the regular module

Over the canonical commutative semiring `ℕ × ℕ`, inclusion of the ideal generated
by `(1, 0)` and its principal-ideal projection have nonzero composites. Their
composite on the ideal is the identity, whereas their composite on the regular
module sends `(a, b)` to `(a, 0)` and is not the identity. The ideal is finite
projective and nonfree, so the two modules are not linearly equivalent.

Both contraction traces are independently evaluated as `(1, 0)` using the
rank-one characteristic formula. Cyclicity is then applied to the same inclusion
and projection. The canonical additions on the scalars and the ideal have no
additive inverses of their specified nonzero generators.

The ideal and projection use the idempotent-span API by Formal Frontier Agents,
including Prism, in `ProjectiveModules.Module.LocallyConstantRank`; see
`docs/CREDITS.md`. The rank-one trace formula uses the tensor–Hom and contraction
formalization by Oliver Nash and Antoine Labelle credited in
`ProjectiveModules.Module.Trace.Basic`.
-/

noncomputable section

namespace ProjectiveModulesTests.FiniteProjectiveTraceCyclicityClient

private abbrev NatPair : Type := ℕ × ℕ
private abbrev firstIdempotent : NatPair := (1, 0)
private abbrev firstIdeal : Ideal NatPair := Ideal.span {firstIdempotent}
private abbrev generator : firstIdeal :=
  ⟨firstIdempotent, Ideal.mem_span_singleton_self firstIdempotent⟩
private abbrev inclusion : firstIdeal →ₗ[NatPair] NatPair := firstIdeal.subtype
private abbrev projection : NatPair →ₗ[NatPair] firstIdeal :=
  IsIdempotentElem.spanProjection firstIdempotent

private abbrev firstIdealFinite : Module.Finite NatPair firstIdeal :=
  IdempotentSpanSemiringClient.legacy_nat_product_projective_nonfree.1
private abbrev firstIdealProjective : Module.Projective NatPair firstIdeal :=
  IdempotentSpanSemiringClient.legacy_nat_product_projective_nonfree.2.1

private theorem firstIdempotent_isIdempotent : IsIdempotentElem firstIdempotent := by
  change firstIdempotent * firstIdempotent = firstIdempotent
  ext <;> simp [firstIdempotent]

private theorem firstIdempotent_ne_zero : firstIdempotent ≠ 0 := by
  intro h
  have hfirst := congrArg Prod.fst h
  simp at hfirst

private theorem firstIdempotent_ne_one : firstIdempotent ≠ 1 := by
  intro h
  have hsecond := congrArg Prod.snd h
  simp at hsecond

private theorem inclusion_generator : inclusion generator = firstIdempotent := rfl

private theorem projection_one : projection 1 = generator :=
  IsIdempotentElem.spanProjection_apply_one firstIdempotent

private theorem generator_ne_zero : generator ≠ 0 := by
  intro h
  exact firstIdempotent_ne_zero (congrArg (fun x : firstIdeal ↦ (x : NatPair)) h)

/-- The nonfree ideal cannot be equivalent to the free regular module. -/
private theorem nonfree_source_not_equivalent :
    ¬ Module.Free NatPair firstIdeal ∧ ¬ Nonempty (firstIdeal ≃ₗ[NatPair] NatPair) := by
  have hnonfree := IdempotentSpanSemiringClient.legacy_nat_product_projective_nonfree.2.2
  refine ⟨hnonfree, ?_⟩
  rintro ⟨h⟩
  exact hnonfree (Module.Free.of_equiv h.symm)

/-- The two canonical additions genuinely need only additive commutative monoids. -/
private theorem generators_have_no_additive_inverse :
    (¬ ∃ r : NatPair, firstIdempotent + r = 0) ∧
      (¬ ∃ x : firstIdeal, generator + x = 0) := by
  constructor
  · rintro ⟨r, h⟩
    have hfirst := congrArg Prod.fst h
    simp [firstIdempotent] at hfirst
  · rintro ⟨x, h⟩
    have hfirst := congrArg (fun y : firstIdeal ↦ (y : NatPair).1) h
    simp [generator, firstIdempotent] at hfirst

/-- Projection after inclusion is the identity on the ideal carrier. -/
private theorem retraction :
    projection.comp inclusion = (LinearMap.id : firstIdeal →ₗ[NatPair] firstIdeal) :=
  firstIdempotent_isIdempotent.spanProjection_comp_subtype

/-- Inclusion after projection is right multiplication by the proper idempotent. -/
private theorem ambient_projector_apply (r : NatPair) :
    (inclusion.comp projection) r = r * firstIdempotent ∧
      (inclusion.comp projection) r = (r.1, 0) := by
  have hr : (inclusion.comp projection) r = r * firstIdempotent :=
    IsIdempotentElem.spanProjection_apply firstIdempotent r
  refine ⟨hr, ?_⟩
  calc
    (inclusion.comp projection) r = r * firstIdempotent := hr
    _ = (r.1, 0) := by ext <;> simp [firstIdempotent]

/-- The ambient composite sends one to the proper idempotent and is not the identity. -/
private theorem ambient_projector_not_identity :
    (inclusion.comp projection) 1 = firstIdempotent ∧
      inclusion.comp projection ≠ (LinearMap.id : NatPair →ₗ[NatPair] NatPair) := by
  have hone : (inclusion.comp projection) 1 = firstIdempotent := by
    rw [(ambient_projector_apply 1).1, one_mul]
  refine ⟨hone, ?_⟩
  intro h
  have hvalue := DFunLike.congr_fun h 1
  rw [hone, LinearMap.id_apply] at hvalue
  exact firstIdempotent_ne_one hvalue

private theorem composite_values :
    (projection.comp inclusion) generator = generator ∧
      (inclusion.comp projection) 1 = firstIdempotent := by
  constructor
  · rw [retraction, LinearMap.id_apply]
  · exact ambient_projector_not_identity.1

/-- Both maps and both composites have specified nonzero values. -/
private theorem maps_and_composites_nonzero :
    inclusion ≠ 0 ∧ projection ≠ 0 ∧
      projection.comp inclusion ≠ 0 ∧ inclusion.comp projection ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hvalue := DFunLike.congr_fun h generator
    rw [inclusion_generator, LinearMap.zero_apply] at hvalue
    exact firstIdempotent_ne_zero hvalue
  · intro h
    have hvalue := DFunLike.congr_fun h 1
    rw [projection_one, LinearMap.zero_apply] at hvalue
    exact generator_ne_zero hvalue
  · intro h
    have hvalue := DFunLike.congr_fun h generator
    rw [composite_values.1, LinearMap.zero_apply] at hvalue
    exact generator_ne_zero hvalue
  · intro h
    have hvalue := DFunLike.congr_fun h 1
    rw [composite_values.2, LinearMap.zero_apply] at hvalue
    exact firstIdempotent_ne_zero hvalue

/-- The existing projection is a rank-one map into the ideal, not a new action. -/
private theorem projection_rankOne :
    projection = (LinearMap.id : NatPair →ₗ[NatPair] NatPair).smulRight generator := by
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  simpa only [projection, LinearMap.smulRight_apply, LinearMap.id_apply,
    Submodule.coe_smul, smul_eq_mul] using
    IsIdempotentElem.spanProjection_apply firstIdempotent r

/-- Compose the rank-one projection with inclusion on its source. -/
private theorem retraction_rankOne :
    projection.comp inclusion = inclusion.smulRight generator := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, projection_rankOne,
    LinearMap.smulRight_apply, LinearMap.id_apply]

/-- Compose the same rank-one projection with inclusion on its target. -/
private theorem ambient_projector_rankOne :
    inclusion.comp projection =
      (LinearMap.id : NatPair →ₗ[NatPair] NatPair).smulRight firstIdempotent := by
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, projection_rankOne, LinearMap.smulRight_apply,
    LinearMap.id_apply, inclusion.map_smul, inclusion_generator]

/-- The rank-one characteristic formula computes each composite trace independently. -/
private theorem independent_composite_traces :
    @LinearMap.traceOfFiniteProjective NatPair _ firstIdeal _ _
        firstIdealFinite firstIdealProjective (projection.comp inclusion) = firstIdempotent ∧
      LinearMap.traceOfFiniteProjective NatPair NatPair (inclusion.comp projection) =
        firstIdempotent := by
  let : Module.Finite NatPair firstIdeal := firstIdealFinite
  let : Module.Projective NatPair firstIdeal := firstIdealProjective
  constructor
  · simpa only [retraction_rankOne, inclusion_generator] using
      (LinearMap.traceOfFiniteProjective_smulRight NatPair firstIdeal inclusion generator)
  · simpa only [ambient_projector_rankOne, LinearMap.id_apply] using
      (LinearMap.traceOfFiniteProjective_smulRight NatPair NatPair
        (LinearMap.id : NatPair →ₗ[NatPair] NatPair) firstIdempotent)

/-- Cyclicity applies to these nonzero maps on the two inequivalent carriers. -/
private theorem mixed_cyclicity_with_values :
    @LinearMap.traceOfFiniteProjective NatPair _ firstIdeal _ _
        firstIdealFinite firstIdealProjective (projection.comp inclusion) =
      LinearMap.traceOfFiniteProjective NatPair NatPair (inclusion.comp projection) ∧
    @LinearMap.traceOfFiniteProjective NatPair _ firstIdeal _ _
        firstIdealFinite firstIdealProjective (projection.comp inclusion) = firstIdempotent ∧
      LinearMap.traceOfFiniteProjective NatPair NatPair (inclusion.comp projection) =
        firstIdempotent ∧ firstIdempotent ≠ 0 ∧
    @LinearMap.traceOfFiniteProjective NatPair _ firstIdeal _ _
        firstIdealFinite firstIdealProjective (projection.comp inclusion) ≠ 0 ∧
      LinearMap.traceOfFiniteProjective NatPair NatPair (inclusion.comp projection) ≠ 0 := by
  let : Module.Finite NatPair firstIdeal := firstIdealFinite
  let : Module.Projective NatPair firstIdeal := firstIdealProjective
  refine ⟨LinearMap.traceOfFiniteProjective_comp_comm NatPair firstIdeal NatPair
      inclusion projection,
    independent_composite_traces.1, independent_composite_traces.2,
    firstIdempotent_ne_zero, ?_, ?_⟩
  · rw [independent_composite_traces.1]
    exact firstIdempotent_ne_zero
  · rw [independent_composite_traces.2]
    exact firstIdempotent_ne_zero

end ProjectiveModulesTests.FiniteProjectiveTraceCyclicityClient
