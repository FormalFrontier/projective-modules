/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.LinearAlgebra.Quotient.Basic
public import AdicModules.LinearAlgebra.Quotient.DFinsupp
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Idempotents
public import ProjectiveModules.Module.ProjectiveReduction
public import ProjectiveModules.Module.ReductionEndomorphism
public import ProjectiveModules.Module.ReductionRange
public import ProjectiveModules.Module.ReductionSelf

/-!
# Lifting projective modules modulo a nilpotent ideal

Every projective module over the quotient of a ring by a nilpotent two-sided
ideal is the reduction of a projective module over the original ring. If the
quotient-ring module is finitely generated, its lift is finitely generated too.
The ring need not be commutative, and the general lifting theorem has no
finite-generation hypothesis.

The construction splits evaluation from the free module indexed by the original
quotient-ring module, lifts the resulting idempotent, and takes its range. The
free-reduction comparison uses the canonical ideal quotient of a dependent
direct sum and the reduction of the left regular module. Finite generation is
then reflected along reduction using a uniform power of the ideal that
annihilates the lift.

## References

* Kevin Buzzard and Antoine Labelle, *Projective modules*,
  `Mathlib.Algebra.Module.Projective`: free-module splittings and projective
  direct summands.
* Andrew Yang, *Idempotents in rings*, `Mathlib.RingTheory.Idempotents`:
  `exists_isIdempotentElem_eq_of_ker_isNilpotent`.
* AdicModules, `AdicModules.LinearAlgebra.Quotient.DFinsupp` and
  `AdicModules.LinearAlgebra.Quotient.Basic`: ideal quotients of dependent direct
  sums and finite generation under a nilpotent ideal action.
-/

@[expose] public section

universe uR uP uF

namespace Module

variable {R : Type uR} [Ring R] (I : Ideal R) [I.IsTwoSided]

private theorem exists_projective_lift_of_reduction_retract (hI : IsNilpotent I)
    {F : Type uF} [AddCommGroup F] [Module R F] [Module.Projective R F]
    {Pbar : Type uP} [AddCommGroup Pbar] [Module (R ⧸ I) Pbar]
    (p0 : Pbar →ₗ[R ⧸ I] Reduction I F)
    (q0 : Reduction I F →ₗ[R ⧸ I] Pbar)
    (hleft : Function.LeftInverse q0 p0) :
    ∃ P : ModuleCat.{uF} R,
      Module.Projective R P ∧ Nonempty (Reduction I P ≃ₗ[R ⧸ I] Pbar) := by
  let e0 : Module.End (R ⧸ I) (Reduction I F) := p0.comp q0
  have he0 : IsIdempotentElem e0 := by
    change e0 * e0 = e0
    apply LinearMap.ext
    intro x
    change p0 (q0 (p0 (q0 x))) = p0 (q0 x)
    rw [hleft (q0 x)]
  have hrange : LinearMap.range e0 = LinearMap.range p0 := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨q0 x, rfl⟩
    · rintro _ ⟨x, rfl⟩
      refine ⟨p0 x, ?_⟩
      change p0 (q0 (p0 x)) = p0 x
      rw [hleft x]
  have he0_range : e0 ∈ RingHom.range (R := Module.End R F)
      (S := Module.End (R ⧸ I) (Reduction I F))
      (reductionEnd I F) := by
    obtain ⟨f, hf⟩ := exists_reductionMap_eq_of_projective I e0
    exact ⟨f, hf⟩
  have hnil : ∀ f ∈ RingHom.ker (reductionEnd I F), IsNilpotent f := by
    obtain ⟨n, hn⟩ := reductionEnd_ker_isNilpotent I F hI
    intro f hf
    exact ⟨n, Ideal.pow_eq_zero_of_mem hn le_rfl hf⟩
  obtain ⟨e, he, he_lift⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
    (R := Module.End R F)
    (S := Module.End (R ⧸ I) (Reduction I F))
    (reductionEnd I F) hnil e0 he0_range he0
  have hred : reductionMap I e = e0 := he_lift
  have hrange_lift : LinearMap.range (reductionMap I e) = LinearMap.range p0 := by
    rw [hred, hrange]
  have hsplit : e.rangeRestrict.comp (LinearMap.range e).subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (LinearMap.IsIdempotentElem.mem_range_iff he).mp x.property
  refine ⟨ModuleCat.of R (LinearMap.range e), ?_, ⟨?_⟩⟩
  · exact Module.Projective.of_split (LinearMap.range e).subtype e.rangeRestrict hsplit
  · exact (reductionRangeEquiv I e he).trans
      ((LinearEquiv.ofEq _ _ hrange_lift).trans (LinearEquiv.ofLeftInverse hleft).symm)

private theorem exists_projective_lift_of_free_comparison (hI : IsNilpotent I)
    {Pbar : Type uP} [AddCommGroup Pbar] [Module (R ⧸ I) Pbar]
    [Module.Projective (R ⧸ I) Pbar]
    (E : Reduction I (Pbar →₀ R) ≃ₗ[R ⧸ I] (Pbar →₀ (R ⧸ I))) :
    ∃ P : ModuleCat.{max uR uP} R,
      Module.Projective R P ∧ Nonempty (Reduction I P ≃ₗ[R ⧸ I] Pbar) := by
  let π : (Pbar →₀ (R ⧸ I)) →ₗ[R ⧸ I] Pbar :=
    Finsupp.linearCombination (R ⧸ I) (id : Pbar → Pbar)
  obtain ⟨τ, hτ⟩ : ∃ τ : Pbar →ₗ[R ⧸ I] (Pbar →₀ (R ⧸ I)),
      π.comp τ = LinearMap.id :=
    projective_lifting_property π LinearMap.id
      (Finsupp.linearCombination_id_surjective (R ⧸ I) Pbar)
  let p0 : Pbar →ₗ[R ⧸ I] Reduction I (Pbar →₀ R) := E.symm.toLinearMap.comp τ
  let q0 : Reduction I (Pbar →₀ R) →ₗ[R ⧸ I] Pbar := π.comp E.toLinearMap
  have hleft : Function.LeftInverse q0 p0 := by
    intro x
    change π (E (E.symm (τ x))) = x
    rw [E.apply_symm_apply]
    exact LinearMap.congr_fun hτ x
  exact exists_projective_lift_of_reduction_retract I hI (F := Pbar →₀ R) p0 q0 hleft

/-- Every projective module over a quotient by a nilpotent two-sided ideal lifts
to a projective module over the original ring. No finite-generation hypothesis
is needed. The proof uses Mathlib's projective splitting and idempotent-lifting
constructions, together with AdicModules' comparison for dependent direct sums. -/
theorem exists_projective_lift (hI : IsNilpotent I)
    {Pbar : Type uP} [AddCommGroup Pbar] [Module (R ⧸ I) Pbar]
    [Module.Projective (R ⧸ I) Pbar] :
    ∃ P : ModuleCat.{max uR uP} R,
      Module.Projective R P ∧ Nonempty (Reduction I P ≃ₗ[R ⧸ I] Pbar) := by
  classical
  refine exists_projective_lift_of_free_comparison I hI (Pbar := Pbar) ?_
  exact
    (reductionEquiv I
      (finsuppLequivDFinsupp (ι := Pbar) (M := R) R)).trans
      ((Ideal.quotientDFinsupp I (fun _ : Pbar => R)).trans
        ((DFinsupp.mapRange.linearEquiv (R := R ⧸ I)
          (fun _ : Pbar => reductionSelfEquiv I)).trans
          (finsuppLequivDFinsupp (ι := Pbar) (M := R ⧸ I) (R ⧸ I)).symm))

/-- Every finitely generated projective module over a quotient by a nilpotent
two-sided ideal lifts to a finitely generated projective module over the original
ring. The lift from `exists_projective_lift` is finite by AdicModules' criterion
for finite generation when a power of the ideal annihilates the module. -/
theorem exists_finite_projective_lift (hI : IsNilpotent I)
    {Pbar : Type uP} [AddCommGroup Pbar] [Module (R ⧸ I) Pbar]
    [Module.Projective (R ⧸ I) Pbar] [Module.Finite (R ⧸ I) Pbar] :
    ∃ P : ModuleCat.{max uR uP} R,
      Module.Projective R P ∧ Module.Finite R P ∧
        Nonempty (Reduction I P ≃ₗ[R ⧸ I] Pbar) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_projective_lift I hI (Pbar := Pbar)
  have : Module.Finite (R ⧸ I) (Reduction I P) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  -- The identity semilinear map compares the two canonical scalar rings on reduction.
  have hfinite : Module.Finite R (Reduction I P) :=
    (LinearMap.finite_iff_of_bijective
      (Module.IsTorsionBySet.semilinearMap
        (Module.isTorsionBySet_quotient_ideal_smul P I))
      Function.bijective_id).mpr inferInstance
  obtain ⟨n, hn⟩ := hI
  have hkill : (I ^ n) • (⊤ : Submodule R P) = ⊥ := by
    rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul]
  refine ⟨P, hP, ?_, ⟨e⟩⟩
  exact (Module.finite_iff_quotient_smul_of_pow_smul_top_eq_bot I n hkill).mpr hfinite

end Module
