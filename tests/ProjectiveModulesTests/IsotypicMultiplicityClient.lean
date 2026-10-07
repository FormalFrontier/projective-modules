/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules
public import Mathlib.Algebra.Quaternion
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.SimpleRing.Congr

/-!
# Fixed-simple multiplicity clients

These clients import the public aggregate and instantiate cardinal uniqueness
and multiplicity at zero, one, finite and infinite indices, including indices
in independent universes and a noncommutative endomorphism-ring coefficient.
The change-of-ring clients use a lifted opposite matrix ring and its chosen
matrix presentation over the opposite quaternion division ring.
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

open scoped Quaternion

private abbrev quaternionMatrixOpp :=
  (Matrix (Fin 2) (Fin 2) (Quaternion ℚ))ᵐᵒᵖ

private abbrev quaternionRow := Fin 2 → Quaternion ℚ

private abbrev liftedMatrixOpp := ULift.{1} quaternionMatrixOpp

private def liftedRingEquiv : liftedMatrixOpp ≃+* quaternionMatrixOpp :=
  ULift.ringEquiv

private def chosenMatrixPresentation :
    liftedMatrixOpp ≃+* Matrix (Fin 2) (Fin 2) (Quaternion ℚ)ᵐᵒᵖ :=
  liftedRingEquiv.trans RingEquiv.mopMatrix.symm

private instance : IsSimpleRing liftedMatrixOpp :=
  IsSimpleRing.of_ringEquiv liftedRingEquiv.symm inferInstance

private instance : IsSemisimpleRing liftedMatrixOpp :=
  liftedRingEquiv.symm.isSemisimpleRing

attribute [local instance] RingHomInvPair.of_ringEquiv

private def liftedModuleEquiv {U : Type u} [AddCommGroup U] [Module quaternionMatrixOpp U] :
    ULift.{2} U ≃ₛₗ[(liftedRingEquiv : liftedMatrixOpp →+* quaternionMatrixOpp)] U where
  __ := (ULift.moduleEquiv : ULift.{2} U ≃ₗ[quaternionMatrixOpp] U).toAddEquiv
  map_smul' _ _ := rfl

private instance : IsSimpleModule liftedMatrixOpp (ULift.{2} quaternionRow) := by
  let equivalence := liftedModuleEquiv (U := quaternionRow)
  exact (equivalence.toLinearMap.isSimpleModule_iff_of_bijective
    equivalence.bijective).mpr inferInstance

private def transportedOppScalar : (Quaternion ℚ)ᵐᵒᵖ →+* liftedMatrixOpp :=
  liftedRingEquiv.symm.toRingHom.comp (RingHom.op (Matrix.scalar (Fin 2)))

private theorem chosen_scalar_presentation (scalar : (Quaternion ℚ)ᵐᵒᵖ) :
    chosenMatrixPresentation (transportedOppScalar scalar) =
      (RingEquiv.mopMatrix.symm) ((RingHom.op (Matrix.scalar (Fin 2))) scalar) := rfl

private theorem transported_row_action (scalar : (Quaternion ℚ)ᵐᵒᵖ)
    (row : quaternionRow) :
    (transportedOppScalar scalar • (ULift.up row : ULift.{2} quaternionRow)).down =
      scalar • row := by
  exact Matrix.op_scalar_smul_row (Fin 2) (Quaternion ℚ) scalar row

private def quaternionI : Quaternion ℚ := ⟨0, 1, 0, 0⟩
private def quaternionJ : Quaternion ℚ := ⟨0, 0, 1, 0⟩

private theorem transported_row_noncentral :
    (transportedOppScalar (MulOpposite.op quaternionI) •
      (ULift.up (Pi.single 0 quaternionJ : quaternionRow) : ULift.{2} quaternionRow)).down 0 =
        quaternionJ * quaternionI ∧
    (transportedOppScalar (MulOpposite.op quaternionI) •
      (ULift.up (Pi.single 0 quaternionJ : quaternionRow) : ULift.{2} quaternionRow)).down 0 ≠
        quaternionI * quaternionJ := by
  have action : (transportedOppScalar (MulOpposite.op quaternionI) •
      (ULift.up (Pi.single 0 quaternionJ : quaternionRow) : ULift.{2} quaternionRow)).down 0 =
        quaternionJ * quaternionI := by
    rw [transported_row_action]
    simp [MulOpposite.smul_eq_mul_unop]
  have noncommutative : quaternionI * quaternionJ ≠ quaternionJ * quaternionI := by
    intro equality
    have imaginaryPart := congrArg (fun value : Quaternion ℚ => value.imK) equality
    norm_num [Quaternion.imK_mul, quaternionI, quaternionJ] at imaginaryPart
  exact ⟨action, fun equality => noncommutative (action.symm.trans equality).symm⟩

private theorem transportedWitness (ι : Type w) :
    IsIsotypicOfType liftedMatrixOpp (ULift.{2} (ι →₀ quaternionRow))
      (ULift.{2} quaternionRow) :=
  IsSimpleRing.isIsotypicOfType _ _ _

private theorem rowWitness (ι : Type w) :
    IsIsotypicOfType quaternionMatrixOpp (ι →₀ quaternionRow) quaternionRow :=
  IsSimpleRing.isIsotypicOfType _ _ _

private theorem transported_zero :
    (transportedWitness Empty).multiplicity = 0 ∧
    (rowWitness Empty).multiplicity = 0 := by
  exact ⟨IsIsotypicOfType.multiplicity_eq_zero_of_subsingleton _,
    IsIsotypicOfType.multiplicity_eq_zero_of_subsingleton _⟩

private theorem transported_three :
    Cardinal.lift.{0} (transportedWitness (Fin 3)).multiplicity =
      Cardinal.lift.{2} (#(Fin 3)) := by
  calc
    _ = Cardinal.lift.{2} (rowWitness (Fin 3)).multiplicity :=
      (transportedWitness (Fin 3)).lift_multiplicity_eq_of_semilinearEquiv
        (rowWitness (Fin 3)) liftedRingEquiv (liftedModuleEquiv (U := Fin 3 →₀ quaternionRow))
        (liftedModuleEquiv (U := quaternionRow))
    _ = Cardinal.lift.{2} (#(Fin 3)) := by
      simpa using congrArg (Cardinal.lift.{2})
        ((rowWitness (Fin 3)).lift_multiplicity_eq_of_linearEquiv_finsupp
          (LinearEquiv.refl _ _))

private theorem transported_infinite :
    Cardinal.lift.{1} (transportedWitness (ULift.{1} ℕ)).multiplicity =
      Cardinal.lift.{2} (#(ULift.{1} ℕ)) := by
  calc
    _ = Cardinal.lift.{2} (rowWitness (ULift.{1} ℕ)).multiplicity :=
      (transportedWitness (ULift.{1} ℕ)).lift_multiplicity_eq_of_semilinearEquiv
        (rowWitness (ULift.{1} ℕ)) liftedRingEquiv
        (liftedModuleEquiv (U := ULift.{1} ℕ →₀ quaternionRow))
        (liftedModuleEquiv (U := quaternionRow))
    _ = Cardinal.lift.{2} (#(ULift.{1} ℕ)) := by
      simpa using congrArg (Cardinal.lift.{2})
        ((rowWitness (ULift.{1} ℕ)).lift_multiplicity_eq_of_linearEquiv_finsupp
          (LinearEquiv.refl _ _))

private abbrev presentedMatrix := Matrix (Fin 2) (Fin 2) (Quaternion ℚ)ᵐᵒᵖ

private instance : Module presentedMatrix quaternionRow :=
  Module.compHom quaternionRow
    (RingEquiv.mopMatrix : presentedMatrix ≃+* quaternionMatrixOpp).toRingHom

private def presentedRowEquiv :
    ULift.{2} quaternionRow ≃ₛₗ[
      (chosenMatrixPresentation : liftedMatrixOpp →+* presentedMatrix)] quaternionRow := by
  refine { (ULift.moduleEquiv : ULift.{2} quaternionRow ≃ₗ[quaternionMatrixOpp]
      quaternionRow).toAddEquiv with
    map_smul' := ?_ }
  intro scalar value
  change (scalar.down • value.down) =
    ((RingEquiv.mopMatrix : presentedMatrix ≃+* quaternionMatrixOpp)
      ((RingEquiv.mopMatrix.symm : quaternionMatrixOpp ≃+* presentedMatrix)
        scalar.down)) • value.down
  rw [RingEquiv.apply_symm_apply]

private instance : IsSimpleModule presentedMatrix quaternionRow := by
  let equivalence := presentedRowEquiv
  exact (equivalence.toLinearMap.isSimpleModule_iff_of_bijective
    equivalence.bijective).mp inferInstance

private theorem transported_one_chosen_presentation :
    Cardinal.lift.{0} (IsIsotypicOfType.of_isSimpleModule liftedMatrixOpp
      (ULift.{2} quaternionRow)).multiplicity = Cardinal.lift.{2} (#Unit) := by
  calc
    _ = Cardinal.lift.{2} (IsIsotypicOfType.of_isSimpleModule presentedMatrix
        quaternionRow).multiplicity :=
      (IsIsotypicOfType.of_isSimpleModule liftedMatrixOpp
        (ULift.{2} quaternionRow)).lift_multiplicity_eq_of_semilinearEquiv
          (IsIsotypicOfType.of_isSimpleModule presentedMatrix quaternionRow)
          chosenMatrixPresentation presentedRowEquiv presentedRowEquiv
    _ = Cardinal.lift.{2} (#Unit) := by
      simpa using congrArg (Cardinal.lift.{2})
        (IsIsotypicOfType.multiplicity_self presentedMatrix quaternionRow)

private theorem fixed_ring_specialization :
    Cardinal.lift.{1} (isotypic_finsupp (A := ℚ) (S := ℚ) ℕ).multiplicity =
      Cardinal.lift.{0} (isotypic_finsupp (A := ℚ) (S := ℚ) (ULift.{1} ℕ)).multiplicity :=
  (isotypic_finsupp (A := ℚ) (S := ℚ) ℕ).lift_multiplicity_eq_of_semilinearEquiv
    (isotypic_finsupp (A := ℚ) (S := ℚ) (ULift.{1} ℕ)) (RingEquiv.refl ℚ)
    (Finsupp.domLCongr (R := ℚ) (M := ℚ) (Equiv.ulift.{1}).symm)
    (LinearEquiv.refl ℚ ℚ)

end ProjectiveModulesTests.IsotypicMultiplicityClient
