/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.DiagonalQuotient
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import StableRange.Module.SplitSurjective

/-!
# Projective splittings of diagonal quotients

For linear maps `f : X →ₗ[S] M` and `g : X →ₗ[S] N`, projectivity of
`(M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g)` splits the canonical projection
from `(M × N) ⧸ LinearMap.range (f.prod g)` onto this product of cokernels.
The resulting product equivalence has the projection as its second coordinate and sends
`quotientKerEquiv f g k`, included in the diagonal quotient, to `(k, 0)`.
The two splitting statements assert existence, without choosing a canonical splitting.
Under the same projectivity hypothesis, the diagonal quotient is projective if and only if
`X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g)` is projective. This criterion uses stability of
projectivity under linear equivalences, products and retracts.
The same splitting gives `finite_iff`: the diagonal quotient is finitely generated exactly
when both the source kernel-sum quotient and the product of cokernels are finitely generated.
The scalar ring may be noncommutative or zero, and the modules have independent universes.

## References

* The diagonal-quotient characteristic interface in
  `ProjectiveModules.Module.DiagonalQuotient`.
* Stable Range's kernel-product equivalence for a specified linear right inverse and its
  coordinate formulas in `StableRange.Module.SplitSurjective`.
* Mathlib's projective lifting, equivalence and retract interfaces in
  `Mathlib.Algebra.Module.Projective`.
* Mathlib's product transport, inclusion and projection interfaces in
  `Mathlib.LinearAlgebra.Prod`, and its linear-equivalence identity, composition and inverse
  characteristics in `Mathlib.Algebra.Module.Equiv.Defs`.
* Mathlib's finite-generation transport and product interfaces in
  `Mathlib.RingTheory.Finiteness.Basic` and `Mathlib.RingTheory.Finiteness.Prod`.
* Mathlib's linear-map extensionality interface in
  `Mathlib.Algebra.Module.LinearMap.Defs`.
-/

@[expose] public section

universe uS uX uM uN

namespace LinearMap.DiagonalQuotient

variable {S : Type uS} [Ring S]
variable {X : Type uX} {M : Type uM} {N : Type uN}
variable [AddCommGroup X] [AddCommGroup M] [AddCommGroup N]
variable [Module S X] [Module S M] [Module S N]
variable (f : X →ₗ[S] M) (g : X →ₗ[S] N)

section

variable [Module.Projective S ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g))]

/-- The projection to a projective product of cokernels admits a linear section. -/
theorem exists_section :
    ∃ s : ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g)) →ₗ[S]
        ((M × N) ⧸ LinearMap.range (f.prod g)),
      ∀ z, projection f g (s z) = z := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (projection f g)
    (LinearMap.id :
      ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g)) →ₗ[S]
        (M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g))
    (projection_surjective f g)
  refine ⟨s, ?_⟩
  intro z
  exact congrArg
    (fun a : ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g)) →ₗ[S]
      (M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g) => a z) hs

/-- A projective product of cokernels gives a product decomposition of the diagonal
quotient, compatible with both the projection and its canonical kernel equivalence. -/
theorem exists_equiv_prod :
    ∃ e : ((M × N) ⧸ LinearMap.range (f.prod g)) ≃ₗ[S]
        ((X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g)) ×
          ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g))),
      (∀ d, (e d).2 = projection f g d) ∧
        ∀ k, e (quotientKerEquiv f g k : (M × N) ⧸ LinearMap.range (f.prod g)) =
          (k, 0) := by
  obtain ⟨s, hs⟩ := exists_section f g
  have hπs : (projection f g).comp s = LinearMap.id := by
    apply LinearMap.ext
    intro z
    exact hs z
  let a : (LinearMap.ker (projection f g) ×
      ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g))) ≃ₗ[S]
      ((M × N) ⧸ LinearMap.range (f.prod g)) :=
    LinearMap.kerProdEquivOfRightInverse (projection f g) s hπs
  have ha (t : LinearMap.ker (projection f g)) :
      a (t, 0) = (t : (M × N) ⧸ LinearMap.range (f.prod g)) := by
    simpa only [map_zero, add_zero] using
      (LinearMap.kerProdEquivOfRightInverse_apply (projection f g) s hπs (t, 0))
  have ha_symm (t : LinearMap.ker (projection f g)) :
      a.symm (t : (M × N) ⧸ LinearMap.range (f.prod g)) = (t, 0) := by
    have ht := congrArg a.symm (ha t)
    simpa only [LinearEquiv.symm_apply_apply] using ht.symm
  refine ⟨a.symm.trans ((quotientKerEquiv f g).symm.prodCongr
    (LinearEquiv.refl S ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g)))), ?_, ?_⟩
  · intro d
    simpa only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      LinearEquiv.refl_apply] using
      (LinearMap.kerProdEquivOfRightInverse_symm_snd (projection f g) s hπs d)
  · intro k
    rw [LinearEquiv.trans_apply, ha_symm, LinearEquiv.prodCongr_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.refl_apply]

end

/-- If the product of the range quotients is projective, projectivity of the diagonal
quotient is equivalent to projectivity of the source modulo the sum of the two kernels.
This follows from the product decomposition and Mathlib's stability of projectivity under
linear equivalences, products and retracts. -/
theorem projective_iff
    [Module.Projective S ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g))] :
    Module.Projective S ((M × N) ⧸ LinearMap.range (f.prod g)) ↔
      Module.Projective S (X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g)) := by
  obtain ⟨e, _, _⟩ := exists_equiv_prod f g
  constructor
  · intro hD
    have : Module.Projective S ((M × N) ⧸ LinearMap.range (f.prod g)) := hD
    have : Module.Projective S
        ((X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g)) ×
          ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g))) :=
      Module.Projective.of_equiv' e
    refine Module.Projective.of_split
      (LinearMap.inl S (X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g))
        ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g)))
      (LinearMap.fst S (X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g))
        ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g)))
      (LinearMap.fst_comp_inl S (X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g))
        ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g)))
  · intro hK
    have : Module.Projective S (X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g)) := hK
    refine Module.Projective.of_equiv' e.symm

/-- If the product of cokernels is projective, the diagonal quotient is finitely generated
if and only if the source kernel-sum quotient and the product of cokernels are both
finitely generated. -/
theorem finite_iff
    [Module.Projective S ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g))] :
    Module.Finite S ((M × N) ⧸ LinearMap.range (f.prod g)) ↔
      Module.Finite S (X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g)) ∧
        Module.Finite S ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g)) := by
  obtain ⟨e, _, _⟩ := exists_equiv_prod f g
  constructor
  · intro hD
    have hProd := (Module.Finite.equiv_iff e).mp hD
    constructor
    · exact Module.Finite.of_surjective (hM := hProd)
        (LinearMap.fst S (X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g))
          ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g)))
        (fun k => ⟨(k, 0), by simp only [LinearMap.fst_apply]⟩)
    · exact Module.Finite.of_surjective (hM := hProd)
        (LinearMap.snd S (X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g))
          ((M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g)))
        (fun z => ⟨(0, z), by simp only [LinearMap.snd_apply]⟩)
  · rintro ⟨hK, hE⟩
    exact (Module.Finite.equiv_iff e).mpr (Module.Finite.prod (hM := hK) (hN := hE))

end LinearMap.DiagonalQuotient
