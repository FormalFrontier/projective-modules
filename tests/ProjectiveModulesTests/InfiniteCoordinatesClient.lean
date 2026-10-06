/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Free.InfiniteCoordinates
import Mathlib.Data.ZMod.Basic

/-!
# Infinite free coordinate clients

These examples use the library through a focused import, including natural
coefficients, reindexed and differently sized universes, and boundary cases.
-/

open Cardinal

private theorem natural_reindexing :
    Nonempty ((ℕ →₀ ℕ) ≃ₗ[ℕ] ((ℕ × Fin 1) →₀ ℕ)) :=
  ⟨Finsupp.domLCongr (Equiv.prodUnique ℕ (Fin 1)).symm⟩

private theorem natural_reindexing_indices : Nonempty (ℕ ≃ ℕ × Fin 1) :=
  (Finsupp.nonempty_linearEquiv_iff_equiv (R := ℕ)).mp natural_reindexing

private noncomputable def chosen_reindexing : ℕ ≃ ℕ × Fin 1 :=
  ((Finsupp.basisSingleOne (R := ℕ) (ι := ℕ)).map
    (Finsupp.domLCongr (Equiv.prodUnique ℕ (Fin 1)).symm)).indexEquivOfInfinite
      (Finsupp.basisSingleOne (R := ℕ) (ι := ℕ × Fin 1))

private theorem universe_reindexing :
    Nonempty ((ULift.{1} ℕ →₀ ℕ) ≃ₗ[ℕ] (ℕ →₀ ℕ)) :=
  ⟨Finsupp.domLCongr Equiv.ulift⟩

private theorem universe_indices : Nonempty (ULift.{1} ℕ ≃ ℕ) :=
  (Finsupp.nonempty_linearEquiv_iff_equiv (R := ℕ)).mp universe_reindexing

private theorem universe_basis_cardinality :
    Cardinal.lift.{1} #ℕ = Cardinal.lift.{0} #(ULift.{1} ℕ) :=
  mk_eq_mk_of_basis_of_infinite
    (Finsupp.basisSingleOne (R := ℕ) (ι := ℕ))
    ((Finsupp.basisSingleOne (R := ℕ) (ι := ULift.{1} ℕ)).map
      (Finsupp.domLCongr Equiv.ulift))

private theorem endomorphism_coefficients :
    Nonempty ((ℕ →₀ Module.End ℚ (ℕ →₀ ℚ)) ≃ₗ[Module.End ℚ (ℕ →₀ ℚ)]
      ((ℕ × Fin 1) →₀ Module.End ℚ (ℕ →₀ ℚ))) :=
  ⟨Finsupp.domLCongr (Equiv.prodUnique ℕ (Fin 1)).symm⟩

private theorem endomorphism_indices : Nonempty (ℕ ≃ ℕ × Fin 1) :=
  (Finsupp.nonempty_linearEquiv_iff_equiv
    (R := Module.End ℚ (ℕ →₀ ℚ))).mp endomorphism_coefficients

private theorem no_empty_coordinates :
    ¬ Nonempty ((ℕ →₀ ℕ) ≃ₗ[ℕ] (Fin 0 →₀ ℕ)) :=
  Finsupp.not_nonempty_linearEquiv_of_infinite_finite

private theorem empty_coordinates :
    Nonempty ((Fin 0 →₀ ℕ) ≃ₗ[ℕ] (Fin 0 →₀ ℕ)) :=
  ⟨LinearEquiv.refl ℕ _⟩

private theorem zero_scalar_boundary :
    Nonempty ((ℕ →₀ ZMod 1) ≃ₗ[ZMod 1] (Fin 0 →₀ ZMod 1)) := by
  let : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
  exact ⟨LinearEquiv.ofSubsingleton _ _⟩
