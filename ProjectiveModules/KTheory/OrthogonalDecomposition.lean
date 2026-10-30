/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Product
public import ProjectiveModules.Module.CommutingProjections
public import ProjectiveModules.Module.ProjectiveKernel
public import ProjectiveModules.Module.ProjectivePi
public import Mathlib.Algebra.Module.NatInt

/-!
# Classes of orthogonal summands

A finite complete orthogonal family of endomorphisms decomposes the class of a
finite projective right module as the sum of the classes of its ranges. Idempotence
and finite projectivity of the ranges are derived from the original hypotheses.
The additive groups in the class expressions are induced by the original ring
actions, preserving the additive monoids and modules.

The module decompositions and range retractions are those of Mathlib and
`CompleteOrthogonalIdempotents.piRangeEquiv`. The binary case uses the range and kernel
of the original endomorphism. Finite dependent-product additivity is supplied by
`KTheory.K0.of_pi`.

## References

* Mathlib, `Mathlib.RingTheory.Idempotents` and `Mathlib.LinearAlgebra.Projection`.
* `CompleteOrthogonalIdempotents.piRangeEquiv` for the finite orthogonal decomposition.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe uR uP uι

open scoped BigOperators

namespace KTheory.K0

variable (R : Type uR) [Ring R]

variable {P : Type uP} [AddCommMonoid P] [μ : Module Rᵐᵒᵖ P]
variable [hfinite : Module.Finite Rᵐᵒᵖ P] [hprojective : Module.Projective Rᵐᵒᵖ P]

/-- A finite complete orthogonal family decomposes the class of the original module
as the sum of its range classes. Range finiteness and projectivity are conclusions.

The decomposition is `CompleteOrthogonalIdempotents.piRangeEquiv`; additivity of
its finite dependent product is `KTheory.K0.of_pi`. -/
theorem of_eq_sum_range
    {ι : Type uι} [Fintype ι] (e : ι → Module.End Rᵐᵒᵖ P)
    (hsum : ∑ i, e i = LinearMap.id)
    (hortho : ∀ i j, i ≠ j → (e i).comp (e j) = 0) :
    ∃ hfiniteRange : ∀ i, Module.Finite Rᵐᵒᵖ (e i).range,
      ∃ hprojectiveRange : ∀ i, Module.Projective Rᵐᵒᵖ (e i).range,
        @of R _ P (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
            μ hfinite hprojective =
          ∑ i, @of R _ (e i).range (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
            inferInstance (hfiniteRange i) (hprojectiveRange i) := by
  classical
  have hcomplete : CompleteOrthogonalIdempotents e :=
    CompleteOrthogonalIdempotents.iff_ortho_complete.mpr ⟨hortho, hsum⟩
  let hfiniteRange : ∀ i, Module.Finite Rᵐᵒᵖ (e i).range := fun i => inferInstance
  let hprojectiveRange : ∀ i, Module.Projective Rᵐᵒᵖ (e i).range := fun i =>
    Module.Projective.range_of_isIdempotentElem (e i) (hcomplete.idem i)
  refine ⟨hfiniteRange, hprojectiveRange, ?_⟩
  let : ∀ i, Module.Finite Rᵐᵒᵖ (e i).range := hfiniteRange
  let : ∀ i, Module.Projective Rᵐᵒᵖ (e i).range := hprojectiveRange
  obtain ⟨hfinitePi, hprojectivePi, hpi⟩ := of_pi R (fun i => (e i).range)
  let : Module.Finite Rᵐᵒᵖ (∀ i, (e i).range) := hfinitePi
  let : Module.Projective Rᵐᵒᵖ (∀ i, (e i).range) := hprojectivePi
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ
  let : AddCommGroup (∀ i, (e i).range) :=
    Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ
  exact (of_eq_of_equiv R P hcomplete.piRangeEquiv).trans hpi

/-- An idempotent splits the class of a finite projective right module into its range
and kernel classes. The finite-projective structures on both summands are derived. -/
theorem of_eq_range_add_ker (e : Module.End Rᵐᵒᵖ P) (he : IsIdempotentElem e) :
    ∃ hfiniteRange : Module.Finite Rᵐᵒᵖ e.range,
      ∃ hprojectiveRange : Module.Projective Rᵐᵒᵖ e.range,
        ∃ hfiniteKer : Module.Finite Rᵐᵒᵖ e.ker,
          ∃ hprojectiveKer : Module.Projective Rᵐᵒᵖ e.ker,
            @of R _ P (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
                μ hfinite hprojective =
              @of R _ e.range (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
                  inferInstance hfiniteRange hprojectiveRange +
                @of R _ e.ker (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
                  inferInstance hfiniteKer hprojectiveKer := by
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ
  let hfiniteRange : Module.Finite Rᵐᵒᵖ e.range := Module.Finite.range e
  let hprojectiveRange : Module.Projective Rᵐᵒᵖ e.range :=
    Module.Projective.range_of_isIdempotentElem e he
  let hfiniteKer : Module.Finite Rᵐᵒᵖ e.ker := by
    rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub he]
    exact Module.Finite.range (1 - e)
  let hprojectiveKer : Module.Projective Rᵐᵒᵖ e.ker := by
    rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub he]
    exact Module.Projective.range_of_isIdempotentElem (1 - e) he.one_sub
  let : AddCommGroup e.range := Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ
  let : AddCommGroup e.ker := Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ
  refine ⟨hfiniteRange, hprojectiveRange, hfiniteKer, hprojectiveKer, ?_⟩
  calc
    of R P = of R (e.range × e.ker) :=
      (of_eq_of_equiv R _
        (Submodule.prodEquivOfIsCompl e.range e.ker
          (LinearMap.IsIdempotentElem.isCompl he))).symm
    _ = of R e.range + of R e.ker := of_prod R _ _

/-- The range of the zero endomorphism has zero class, and its kernel has the class of
its finite projective right module. -/
theorem of_range_ker_zero :
  ∃ hfiniteRange : Module.Finite Rᵐᵒᵖ (0 : Module.End Rᵐᵒᵖ P).range,
    ∃ hprojectiveRange : Module.Projective Rᵐᵒᵖ (0 : Module.End Rᵐᵒᵖ P).range,
      ∃ hfiniteKer : Module.Finite Rᵐᵒᵖ (0 : Module.End Rᵐᵒᵖ P).ker,
        ∃ hprojectiveKer : Module.Projective Rᵐᵒᵖ (0 : Module.End Rᵐᵒᵖ P).ker,
          @of R _ (0 : Module.End Rᵐᵒᵖ P).range
              (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
              inferInstance hfiniteRange hprojectiveRange = 0 ∧
            @of R _ (0 : Module.End Rᵐᵒᵖ P).ker
                (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
                inferInstance hfiniteKer hprojectiveKer =
              @of R _ P (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
                μ hfinite hprojective := by
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ
  let hfiniteRange : Module.Finite Rᵐᵒᵖ (0 : Module.End Rᵐᵒᵖ P).range :=
    Module.Finite.range (0 : Module.End Rᵐᵒᵖ P)
  let hprojectiveRange : Module.Projective Rᵐᵒᵖ (0 : Module.End Rᵐᵒᵖ P).range :=
    Module.Projective.range_of_isIdempotentElem _ IsIdempotentElem.zero
  let E := LinearEquiv.ofTop (0 : Module.End Rᵐᵒᵖ P).ker LinearMap.ker_zero
  let hfiniteKer : Module.Finite Rᵐᵒᵖ (0 : Module.End Rᵐᵒᵖ P).ker :=
    Module.Finite.equiv E.symm
  let hprojectiveKer : Module.Projective Rᵐᵒᵖ (0 : Module.End Rᵐᵒᵖ P).ker :=
    Module.Projective.of_equiv E.symm
  let : AddCommGroup (0 : Module.End Rᵐᵒᵖ P).range :=
    Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ
  let : AddCommGroup (0 : Module.End Rᵐᵒᵖ P).ker :=
    Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ
  refine ⟨hfiniteRange, hprojectiveRange, hfiniteKer, hprojectiveKer, ?_, ?_⟩
  · let : Subsingleton (0 : Module.End Rᵐᵒᵖ P).range := by
      rw [LinearMap.range_zero]
      infer_instance
    exact of_zero R _
  · exact of_eq_of_equiv R _ E

/-- The range of the identity has the class of its finite projective right module,
and its kernel has zero class. -/
theorem of_range_ker_id :
  ∃ hfiniteRange : Module.Finite Rᵐᵒᵖ (LinearMap.id : Module.End Rᵐᵒᵖ P).range,
    ∃ hprojectiveRange : Module.Projective Rᵐᵒᵖ (LinearMap.id : Module.End Rᵐᵒᵖ P).range,
      ∃ hfiniteKer : Module.Finite Rᵐᵒᵖ (LinearMap.id : Module.End Rᵐᵒᵖ P).ker,
        ∃ hprojectiveKer : Module.Projective Rᵐᵒᵖ (LinearMap.id : Module.End Rᵐᵒᵖ P).ker,
          @of R _ (LinearMap.id : Module.End Rᵐᵒᵖ P).range
              (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
              inferInstance hfiniteRange hprojectiveRange =
            @of R _ P (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
              μ hfinite hprojective ∧
            @of R _ (LinearMap.id : Module.End Rᵐᵒᵖ P).ker
              (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
              inferInstance hfiniteKer hprojectiveKer = 0 := by
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ
  let hfiniteRange : Module.Finite Rᵐᵒᵖ (LinearMap.id : Module.End Rᵐᵒᵖ P).range :=
    Module.Finite.range (LinearMap.id : Module.End Rᵐᵒᵖ P)
  let hprojectiveRange : Module.Projective Rᵐᵒᵖ
      (LinearMap.id : Module.End Rᵐᵒᵖ P).range :=
    Module.Projective.range_of_isIdempotentElem _ IsIdempotentElem.one
  let hfiniteKer : Module.Finite Rᵐᵒᵖ (LinearMap.id : Module.End Rᵐᵒᵖ P).ker := by
    rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub
      (p := (LinearMap.id : Module.End Rᵐᵒᵖ P)) IsIdempotentElem.one]
    exact Module.Finite.range (1 - (LinearMap.id : Module.End Rᵐᵒᵖ P))
  let hprojectiveKer : Module.Projective Rᵐᵒᵖ
      (LinearMap.id : Module.End Rᵐᵒᵖ P).ker := by
    rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub
      (p := (LinearMap.id : Module.End Rᵐᵒᵖ P)) IsIdempotentElem.one]
    exact Module.Projective.range_of_isIdempotentElem
      (1 - (LinearMap.id : Module.End Rᵐᵒᵖ P)) IsIdempotentElem.one.one_sub
  let : AddCommGroup (LinearMap.id : Module.End Rᵐᵒᵖ P).range :=
    Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ
  let : AddCommGroup (LinearMap.id : Module.End Rᵐᵒᵖ P).ker :=
    Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ
  refine ⟨hfiniteRange, hprojectiveRange, hfiniteKer, hprojectiveKer, ?_, ?_⟩
  · exact of_eq_of_equiv R _ (LinearEquiv.ofTop _ LinearMap.range_id)
  · let : Subsingleton (LinearMap.id : Module.End Rᵐᵒᵖ P).ker := by
      rw [LinearMap.ker_id]
      infer_instance
    exact of_zero R _

end KTheory.K0
