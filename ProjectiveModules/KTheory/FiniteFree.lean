/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.ScalarExtension
public import ProjectiveModules.KTheory.Stabilization
import GroupTheory.MonoidLocalization.GrothendieckGroup
import ProjectiveModules.KTheory.Product

/-!
# Finite free classes and denominators in K₀

The classes of the finite free right modules `Fin n → Rᵐᵒᵖ` are cofinal in the
additive monoid `KTheory.ProjectiveClass R`: every projective class has a complement
to one of these classes. Consequently, every element of `KTheory.K0 R` is the class
of a finite projective right module minus the class of a finite free right module.

Scalar extension has cofinal image on projective classes: every target class has a
complement whose sum is extended from a finite free source module. Consequently,
injectivity of the projective-class map implies injectivity of the induced K₀ map.

The finite projective representative uses `ModuleCat.FiniteProjective` in the
universe of the coefficient ring, as in `KTheory.K0.exists_sub`. The class maps
also accept modules in independent carrier universes. No cancellation of
projective classes, invariant basis number or nontriviality of the ring is assumed.
-/

@[expose] public section

universe u v

namespace KTheory

variable (R : Type u) [Ring R]

namespace ProjectiveClass

/-- Every finite projective right-module class has a complement to a finite free class. -/
theorem exists_add_eq_free (c : ProjectiveClass R) :
    ∃ (n : ℕ) (d : ProjectiveClass R), c + d = of R (Fin n → Rᵐᵒᵖ) := by
  have hc : (fun _ : Unit ↦ c) ∈ Set.range (piMap (fun _ : Unit ↦ R)) := by
    obtain ⟨a, ha⟩ := (piEquiv (fun _ : Unit ↦ R)).surjective (fun _ ↦ c)
    refine ⟨a, ?_⟩
    rw [← piEquiv_toAddMonoidHom_eq_piMap (fun _ : Unit ↦ R)]
    exact ha
  obtain ⟨n, hn⟩ := (mem_range_piMap_iff (fun _ : Unit ↦ R) (fun _ ↦ c)).mp hc
  obtain ⟨d, hd⟩ := hn ()
  exact ⟨n, d, hd.trans (of_fin_fun_eq_nsmul R n).symm⟩

variable {R} {S : Type v} [Ring S]

/-- Every target projective class has a complement whose sum is extended from the source. -/
theorem exists_add_eq_map (φ : R →+* S) (c : ProjectiveClass S) :
    ∃ (d : ProjectiveClass S) (a : ProjectiveClass R), c + d = map φ a := by
  obtain ⟨n, d, hd⟩ := exists_add_eq_free S c
  refine ⟨d, of R (Fin n → Rᵐᵒᵖ), ?_⟩
  simpa only [of_fin_fun_eq_nsmul, map_nsmul, map_of_self] using hd

end ProjectiveClass

namespace K0

/-- Every element of K₀ is a finite projective class minus a finite free class. -/
theorem exists_sub_free (z : K0 R) :
    ∃ (P : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ) (n : ℕ),
      z = of R P - of R (Fin n → Rᵐᵒᵖ) := by
  obtain ⟨n, c, hc⟩ :=
    Algebra.GrothendieckAddGroup.exists_eq_sub_of_cofinal
      (fun n : ℕ => ProjectiveClass.of R (Fin n → Rᵐᵒᵖ))
      (ProjectiveClass.exists_add_eq_free R) z
  obtain ⟨P, rfl⟩ := ProjectiveClass.of_surjective R c
  refine ⟨P, n, ?_⟩
  have hrep : z = ofClass R (ProjectiveClass.of R P) -
      ofClass R (ProjectiveClass.of R (Fin n → Rᵐᵒᵖ)) := hc
  simpa only [ofClass_of] using hrep

variable {R} {S : Type v} [Ring S]

/-- Injectivity on projective classes implies injectivity on K₀ under scalar extension. -/
theorem map_injective (φ : R →+* S) (h : Function.Injective (ProjectiveClass.map φ)) :
    Function.Injective (map φ) := by
  have hmap : map φ =
      Algebra.GrothendieckAddGroup.lift ((ofClass S).comp (ProjectiveClass.map φ)) := by
    apply hom_ext_ofClass R
    intro a
    rw [map_ofClass]
    exact (Algebra.GrothendieckAddGroup.lift_of
      ((ofClass S).comp (ProjectiveClass.map φ)) a).symm
  rw [hmap]
  apply Algebra.GrothendieckAddGroup.lift_of_comp_injective_of_cofinal
    (ProjectiveClass.map φ) h
  intro c
  obtain ⟨d, a, ha⟩ := ProjectiveClass.exists_add_eq_map φ c
  exact ⟨a, d, ha⟩

end K0

end KTheory
