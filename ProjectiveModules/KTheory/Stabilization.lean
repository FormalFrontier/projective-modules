/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
public import ProjectiveModules.Module.FiniteStabilization
import Mathlib.LinearAlgebra.StdBasis

/-!
# Difference representatives and common stabilization in K₀

Every element of `KTheory.K0 R` has a chosen representation as a difference of
finite projective right-module generators. `K0.representative` returns the two
objects in the complete ring-universe reference category, and
`K0.representative_spec` reconstructs the element. This choice is not asserted
to be unique or additive.

Two generators are equal exactly when their modules become linearly equivalent
after adjoining one common finite projective module. The input carriers may
have independent universes, while the stabilizer belongs to
`ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ`. The ring is arbitrary, including the
zero ring. Direct sum is modeled by the product of module carriers.

The common projective stabilizer can be replaced by one standard finite free
module `Fin n → Rᵐᵒᵖ` on both sides. Equality of differences is characterized
by stabilization of the cross-sums `P × Q'` and `P' × Q`. The natural number
is existential, with no invariant-basis-number or prescribed-rank condition.

Equality in `ProjectiveClass R` means module isomorphism. Equality in `K0 R`
means equality after group completion and does not require cancellation of
projective modules.

## References and credits

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter II, group completion and K₀.
* Mathlib's additive Grothendieck group and localization section and equality
  APIs.
* Projective Modules' finite-projective representatives, isomorphism-class
  API, and finite-projective-to-free common-stabilizer API.
* Formal Frontier's Algebraic Direct Limits object-class stabilization
  formalization, whose passage from class witnesses to object witnesses this
  module follows without importing a separate completion framework.
-/

@[expose] public section

universe u v w x y

namespace KTheory.K0

variable (R : Type u) [Ring R]

private theorem exists_representative_pair (z : K0 R) :
    ∃ PQ : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ ×
        ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ,
      z = of R PQ.1 - of R PQ.2 := by
  let f := AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass R))
  obtain ⟨P, hP⟩ := ProjectiveClass.of_surjective R (f.sec z).1
  obtain ⟨Q, hQ⟩ := ProjectiveClass.of_surjective R ((f.sec z).2 : ProjectiveClass R)
  refine ⟨(P, Q), eq_sub_iff_add_eq.mpr ?_⟩
  have hs : z + ofClass R ((f.sec z).2 : ProjectiveClass R) =
      ofClass R (f.sec z).1 :=
    AddSubmonoid.LocalizationMap.sec_spec (f := f) z
  simpa only [← hP, ← hQ, ofClass_of] using hs

/-- A chosen pair of finite projective right modules whose generator difference
is the given K₀ element. Both objects have carriers in the ring universe.
No uniqueness or additivity of this choice is asserted. -/
@[no_expose] noncomputable def representative (z : K0 R) :
    ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ ×
      ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ :=
  Classical.choose (exists_representative_pair R z)

/-- The chosen module pair reconstructs its K₀ element, as in the
difference-of-generators description of group completion in Weibel's
*The K-book*, Chapter II. -/
theorem representative_spec (z : K0 R) :
    z = of R (representative R z).1 - of R (representative R z).2 :=
  Classical.choose_spec (exists_representative_pair R z)

/-- Every K₀ element is a difference of finite projective right-module
generators, with both modules in the ring-universe reference category. -/
theorem exists_sub (z : K0 R) :
    ∃ P Q : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ, z = of R P - of R Q :=
  ⟨(representative R z).1, (representative R z).2, representative_spec R z⟩

/-- Two finite projective right-module generators agree exactly when adjoining
one common finite projective module makes the inputs linearly equivalent.
This is the group-completion stabilization criterion of Weibel's *The K-book*,
Chapter II, applied to direct-sum isomorphism classes; no module cancellation
hypothesis is required. The two input carrier universes are independent. -/
theorem of_eq_iff_exists_projective_stabilizer
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (N : Type w) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    of R M = of R N ↔
      ∃ T : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ,
        Nonempty ((M × T) ≃ₗ[Rᵐᵒᵖ] (N × T)) := by
  constructor
  · intro h
    have hclass : ofClass R (ProjectiveClass.of R M) =
        ofClass R (ProjectiveClass.of R N) := h
    obtain ⟨c, hc⟩ :=
      (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass R))).eq_iff_exists.mp
        hclass
    obtain ⟨T, hT⟩ := ProjectiveClass.of_surjective R (c : ProjectiveClass R)
    refine ⟨T, (ProjectiveClass.of_eq_iff R (M × T) (N × T)).mp ?_⟩
    simpa only [ProjectiveClass.of_prod, ← hT, add_comm] using hc
  · rintro ⟨T, ⟨e⟩⟩
    have he := of_eq_of_equiv R (M × T) e
    simp only [of_prod] at he
    exact add_right_cancel he

/-- Two finite projective right-module generators agree exactly when their
modules become linearly equivalent after adjoining the same standard finite
free module. This is the finite-free form of the stabilization criterion in
Weibel's *The K-book*, Chapter II. The witness rank is existential, and no
invariant-basis-number, nontriviality or module cancellation premise is used. -/
theorem of_eq_iff_exists_free_stabilizer
    (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]
    (Q : Type w) [AddCommGroup Q] [Module Rᵐᵒᵖ Q]
    [Module.Finite Rᵐᵒᵖ Q] [Module.Projective Rᵐᵒᵖ Q] :
    of R P = of R Q ↔
      ∃ n : ℕ, Nonempty ((P × (Fin n → Rᵐᵒᵖ)) ≃ₗ[Rᵐᵒᵖ]
        (Q × (Fin n → Rᵐᵒᵖ))) := by
  constructor
  · intro h
    obtain ⟨T, ⟨e⟩⟩ := (of_eq_iff_exists_projective_stabilizer R P Q).mp h
    exact Module.Projective.exists_free_stabilizer (R := Rᵐᵒᵖ) e
  · rintro ⟨n, ⟨e⟩⟩
    let finitePiFree : Module.Free Rᵐᵒᵖ (Fin n → Rᵐᵒᵖ) := Module.Free.pi _ _
    exact (of_eq_iff_exists_projective_stabilizer R P Q).mpr
      ⟨ModuleCat.FiniteProjective.of Rᵐᵒᵖ (Fin n → Rᵐᵒᵖ), ⟨e⟩⟩

/-- Two differences of finite projective right-module generators agree exactly
when the cross-sums become linearly equivalent after adjoining one common
finite projective module. This is the difference form of Weibel's group-
completion stabilization criterion in *The K-book*, Chapter II. The four input
carrier universes are independent, and cancellation is used only in K₀. -/
theorem sub_eq_sub_iff_exists_projective_stabilizer
    (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]
    (Q : Type w) [AddCommGroup Q] [Module Rᵐᵒᵖ Q]
    [Module.Finite Rᵐᵒᵖ Q] [Module.Projective Rᵐᵒᵖ Q]
    (P' : Type x) [AddCommGroup P'] [Module Rᵐᵒᵖ P']
    [Module.Finite Rᵐᵒᵖ P'] [Module.Projective Rᵐᵒᵖ P']
    (Q' : Type y) [AddCommGroup Q'] [Module Rᵐᵒᵖ Q']
    [Module.Finite Rᵐᵒᵖ Q'] [Module.Projective Rᵐᵒᵖ Q'] :
    of R P - of R Q = of R P' - of R Q' ↔
      ∃ T : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ,
        Nonempty (((P × Q') × T) ≃ₗ[Rᵐᵒᵖ] ((P' × Q) × T)) := by
  rw [sub_eq_sub_iff_add_eq_add, ← of_prod R P Q', ← of_prod R P' Q]
  exact of_eq_iff_exists_projective_stabilizer R (P × Q') (P' × Q)

/-- Two differences of finite projective right-module generators agree exactly
when the cross-sums become linearly equivalent after adjoining the same
standard finite free module. This is the finite-free difference form of the
stabilization criterion in Weibel's *The K-book*, Chapter II. No module
cancellation or invariant-basis-number hypothesis is assumed. -/
theorem sub_eq_sub_iff_exists_free_stabilizer
    (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]
    (Q : Type w) [AddCommGroup Q] [Module Rᵐᵒᵖ Q]
    [Module.Finite Rᵐᵒᵖ Q] [Module.Projective Rᵐᵒᵖ Q]
    (P' : Type x) [AddCommGroup P'] [Module Rᵐᵒᵖ P']
    [Module.Finite Rᵐᵒᵖ P'] [Module.Projective Rᵐᵒᵖ P']
    (Q' : Type y) [AddCommGroup Q'] [Module Rᵐᵒᵖ Q']
    [Module.Finite Rᵐᵒᵖ Q'] [Module.Projective Rᵐᵒᵖ Q'] :
    of R P - of R Q = of R P' - of R Q' ↔
      ∃ n : ℕ, Nonempty (((P × Q') × (Fin n → Rᵐᵒᵖ)) ≃ₗ[Rᵐᵒᵖ]
        ((P' × Q) × (Fin n → Rᵐᵒᵖ))) := by
  rw [sub_eq_sub_iff_add_eq_add, ← of_prod R P Q', ← of_prod R P' Q]
  exact of_eq_iff_exists_free_stabilizer R (P × Q') (P' × Q)

end KTheory.K0
