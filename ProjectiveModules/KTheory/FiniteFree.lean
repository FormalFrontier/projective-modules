/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Stabilization
import GroupTheory.MonoidLocalization.GrothendieckGroup
import ProjectiveModules.KTheory.Product

/-!
# Finite free classes and denominators in K₀

The classes of the finite free right modules `Fin n → Rᵐᵒᵖ` are cofinal in the
additive monoid `KTheory.ProjectiveClass R`: every projective class has a complement
to one of these classes. Consequently, every element of `KTheory.K0 R` is the class
of a finite projective right module minus the class of a finite free right module.

The finite projective representative uses `ModuleCat.FiniteProjective` in the
universe of the coefficient ring, as in `KTheory.K0.exists_sub`. The class maps
also accept modules in independent carrier universes. No cancellation of
projective classes, invariant basis number or nontriviality of the ring is assumed.
-/

@[expose] public section

universe u

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

end K0

end KTheory
