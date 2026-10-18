/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.RankBound
import ProjectiveModules.KTheory.ZeroRing
import Mathlib.Algebra.Ring.Rat

/-!
# Rank bounds for a countable product of rational fields

The evaluation maps from `ℕ → ℚ` give the uniform rank bound, while the
comparison to the product of the factor K₀ groups is not surjective. The
inverse rank equivalence represents the growing integer family by multiples
of the regular right-module generator. Empty and two-element index types
illustrate the boundaries of the infinite-index conclusion.

See `ProjectiveModules.KTheory.RankBound` for the general statements, the
finite-complement and rank argument, and its mathematical and formalization
references.
-/

open KTheory

example (x : K0 (ℕ → ℚ)) :
    ∃ n : ℕ, ∀ i : ℕ,
      |K0.finrankEquiv ℚ (K0.piMap (fun _ : ℕ ↦ ℚ) x i)| ≤ (n : ℤ) := by
  simpa only [K0.piMap_apply] using
    K0.exists_uniform_abs_finrank_map_le (fun _ : ℕ ↦ ℚ)
      (fun i ↦ Pi.evalRingHom (fun _ : ℕ ↦ ℚ) i) x

example : ¬ Function.Surjective (K0.piMap (fun _ : ℕ ↦ ℚ)) :=
  K0.not_surjective_piMap (fun _ : ℕ ↦ ℚ)

example (n : ℕ) :
    (K0.finrankEquiv ℚ).symm (n : ℤ) = (n : ℤ) • K0.of ℚ ℚᵐᵒᵖ :=
  K0.finrankEquiv_symm_apply ℚ (n : ℤ)

example (x : K0 (Empty → ℚ)) :
    x = 0 ∧ ∀ i : Empty,
      |K0.finrankEquiv ℚ
        (K0.map (Pi.evalRingHom (fun _ : Empty ↦ ℚ) i) x)| ≤ (0 : ℤ) := by
  exact ⟨Subsingleton.elim _ _, fun i ↦ nomatch i⟩

example : Function.Surjective (K0.piMap (fun _ : Fin 2 ↦ ℚ)) :=
  (K0.piEquiv (fun _ : Fin 2 ↦ ℚ)).surjective
