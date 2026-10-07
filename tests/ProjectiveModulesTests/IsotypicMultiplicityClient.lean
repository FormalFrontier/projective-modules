/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules

/-!
# Fixed-simple multiplicity clients

These clients import the public aggregate and instantiate cardinal uniqueness
and multiplicity at zero, one, finite and infinite indices, including indices
in independent universes and a noncommutative endomorphism-ring coefficient.
-/

set_option warningAsError true

namespace ProjectiveModulesTests.IsotypicMultiplicityClient

open Cardinal

universe u v w

private theorem one_copy :
    (IsIsotypicOfType.of_isSimpleModule ℚ ℚ).multiplicity = 1 :=
  IsIsotypicOfType.multiplicity_self ℚ ℚ

private theorem isotypic_finsupp {A : Type u} [Ring A]
    {S : Type v} [AddCommGroup S] [Module A S] [IsSimpleModule A S]
    (ι : Type w) : IsIsotypicOfType A (ι →₀ S) S := by
  intro m _
  obtain ⟨x, hx⟩ := @exists_ne m (IsSimpleModule.nontrivial A m) 0
  have hcoe : (x : ι →₀ S) ≠ 0 := by
    intro h
    apply hx
    exact Subtype.ext h
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hcoe
  let projection : m →ₗ[A] S := (Finsupp.lapply i).comp m.subtype
  have hp : projection ≠ 0 := by
    intro h
    have heq := congrArg (fun f : m →ₗ[A] S => f x) h
    exact hi (by simpa [projection] using heq)
  exact ⟨LinearEquiv.ofBijective projection (LinearMap.bijective_of_ne_zero hp)⟩

private theorem isotypic_three_functions : IsIsotypicOfType ℚ (Fin 3 → ℚ) ℚ :=
  (Finsupp.linearEquivFunOnFinite ℚ ℚ (Fin 3)).isIsotypicOfType_iff.mp
    (isotypic_finsupp (A := ℚ) (S := ℚ) (Fin 3))

private theorem three_copies :
    Cardinal.lift.{0} isotypic_three_functions.multiplicity =
      Cardinal.lift.{0} (#(Fin 3)) :=
  isotypic_three_functions.lift_multiplicity_eq_of_linearEquiv_finsupp
    (Finsupp.linearEquivFunOnFinite ℚ ℚ (Fin 3)).symm

private theorem infinite_decomposition :
    Cardinal.lift.{1} (isotypic_finsupp (A := ℚ) (S := ℚ) ℕ).multiplicity =
      Cardinal.lift.{0} (#(ULift.{1} ℕ)) :=
  (isotypic_finsupp (A := ℚ) (S := ℚ) ℕ).lift_multiplicity_eq_of_linearEquiv_finsupp
    (Finsupp.domLCongr (R := ℚ) (M := ℚ) (Equiv.ulift.{1}).symm)

private theorem infinite_equivalent_modules :
    Cardinal.lift.{1} (isotypic_finsupp (A := ℚ) (S := ℚ) ℕ).multiplicity =
      Cardinal.lift.{0} (isotypic_finsupp (A := ℚ) (S := ℚ) (ULift.{1} ℕ)).multiplicity :=
  IsIsotypicOfType.lift_multiplicity_eq_of_linearEquiv
    (isotypic_finsupp (A := ℚ) (S := ℚ) ℕ)
    (isotypic_finsupp (A := ℚ) (S := ℚ) (ULift.{1} ℕ))
    (Finsupp.domLCongr (R := ℚ) (M := ℚ) (Equiv.ulift.{1}).symm)

private theorem empty_index :
    (IsIsotypicOfType.of_subsingleton ℚ (Empty →₀ ℚ) ℚ).multiplicity = 0 :=
  IsIsotypicOfType.multiplicity_eq_zero_of_subsingleton _

public theorem finite_index :
    Cardinal.lift.{0} (#(Fin 1)) = Cardinal.lift.{0} (#Unit) :=
  Finsupp.lift_cardinalMk_eq_of_linearEquiv
    (Finsupp.domLCongr (R := ℚ) (M := ℚ) finOneEquiv)

private theorem infinite_index :
    Cardinal.lift.{0} (#(ULift.{1} ℕ)) = Cardinal.lift.{1} (#ℕ) :=
  Finsupp.lift_cardinalMk_eq_of_linearEquiv
    (Finsupp.domLCongr (R := ℚ) (M := ℚ) (Equiv.ulift.{1}))

private theorem independent_universes :
    Cardinal.lift.{0} (#(ULift.{1} (Fin 3))) =
      Cardinal.lift.{1} (#(Fin 3)) :=
  Finsupp.lift_cardinalMk_eq_of_linearEquiv
    (Finsupp.domLCongr (R := ℚ) (M := ℚ) (Equiv.ulift.{1}))

private theorem noncommutative_coefficients :
    Cardinal.lift.{0} (isotypic_finsupp
      (A := Module.End ℚ (Fin 2 → ℚ)) (S := Fin 2 → ℚ) (Fin 2)).multiplicity =
      Cardinal.lift.{0} (#(Fin 2)) :=
  (isotypic_finsupp (A := Module.End ℚ (Fin 2 → ℚ))
    (S := Fin 2 → ℚ) (Fin 2)).lift_multiplicity_eq_of_linearEquiv_finsupp
      (LinearEquiv.refl (Module.End ℚ (Fin 2 → ℚ)) (Fin 2 →₀ Fin 2 → ℚ))

private theorem zero_simple_boundary :
    Nonempty (((Unit →₀ (Empty →₀ ℚ)) ≃ₗ[ℚ] (Empty →₀ (Empty →₀ ℚ)))) ∧
      (#Unit : Cardinal) ≠ #Empty := by
  refine ⟨⟨LinearEquiv.ofSubsingleton _ _⟩, ?_⟩
  simp

end ProjectiveModulesTests.IsotypicMultiplicityClient
