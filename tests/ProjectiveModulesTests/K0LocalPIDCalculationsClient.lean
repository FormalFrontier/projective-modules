/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Rank
import ProjectiveModules.KTheory.ZeroRing
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Local and principal ideal domain dimension clients

The local examples use the stock ring of 2-adic integers: the nonzero scalar
`2` is not a unit, so this is genuinely a local nondivision example. The
canonical Jacobson residue dimension detects its regular K₀ generator.
For the integers, fraction-field dimension detects both the regular generator
and the two-coordinate module. These observers use only scalar extension and
division-ring dimension, independently of the classification statements.

The free-module inputs come from the existing projective-module theorems over
local rings and principal ideal domains, applied to the opposite scalar ring.
The subsingleton ring `ZMod 1` retains its separate zero K₀ boundary.
-/

@[expose] public section

universe u

open KTheory

namespace ProjectiveModulesTests.K0LocalPIDCalculationsClient

-- The natural finite-projective freeness premises have actual stock providers.
private theorem local_projective_free (R : Type u) [Ring R] [IsLocalRing R] :
    ∀ X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ, Module.Free Rᵐᵒᵖ X := by
  intro X
  exact Module.Projective.free_of_isLocalRing

private theorem pid_projective_free (R : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] :
    ∀ X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ, Module.Free Rᵐᵒᵖ X := by
  let : IsPrincipalIdealRing Rᵐᵒᵖ :=
    IsPrincipalIdealRing.of_surjective (RingEquiv.toOpposite R).toRingHom
      (RingEquiv.toOpposite R).surjective
  intro X
  exact Module.Projective.free_of_pid Rᵐᵒᵖ X

-- Locality supplies canonical maximality and the unit-complement property.
private theorem local_jacobson_properties (R : Type u) [Ring R] [IsLocalRing R] :
    (Ring.jacobson R).IsMaximal ∧
      (Ring.jacobson R) ≠ ⊤ ∧
      ∀ r : R, r ∉ Ring.jacobson R → IsUnit r := by
  refine ⟨IsLocalRing.isMaximal_ringJacobson R, (Ring.jacobson_lt_top R).ne, ?_⟩
  intro r hr
  by_contra h
  exact hr ((IsLocalRing.mem_ringJacobson_iff r).mpr h)

-- Nat.fact_prime_two supplies the prime input; all ring instances are stock.
private theorem padic_standard_model :
    IsLocalRing (PadicInt 2) ∧ IsDomain (PadicInt 2) ∧ CharZero (PadicInt 2) ∧
      (2 : PadicInt 2) ≠ 0 ∧ ¬ IsUnit (2 : PadicInt 2) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact Nat.cast_ne_zero.mpr (by decide : (2 : ℕ) ≠ 0)
  · simpa only [mem_nonunits_iff, Nat.cast_ofNat] using (PadicInt.p_nonunit (p := 2))

private theorem padic_regular_dimension :
    K0.localDimensionHom (PadicInt 2)
      (K0.of (PadicInt 2) (PadicInt 2)ᵐᵒᵖ) = 1 :=
  K0.localDimensionHom_of_self (PadicInt 2)

private theorem padic_regular_ne_zero :
    K0.of (PadicInt 2) (PadicInt 2)ᵐᵒᵖ ≠ 0 := by
  intro h
  have impossible : (1 : ℤ) = 0 := by
    simpa only [padic_regular_dimension, map_zero] using
      congrArg (K0.localDimensionHom (PadicInt 2)) h
  exact one_ne_zero impossible

-- The generic class-map theorem consumes canonical local projective freeness.
example :
    Function.Bijective
      (ProjectiveClass.map (Ideal.Quotient.mk (Ring.jacobson (PadicInt 2)))) := by
  let : (Ring.jacobson (PadicInt 2)).IsMaximal :=
    (local_jacobson_properties (PadicInt 2)).1
  let : DivisionRing (PadicInt 2 ⧸ Ring.jacobson (PadicInt 2)) :=
    Ideal.Quotient.divisionRing (Ring.jacobson (PadicInt 2))
  exact ProjectiveClass.map_bijective_of_projective_free _
    (local_projective_free (PadicInt 2))

example : Function.Bijective (K0.localDimensionHom (PadicInt 2)) :=
  K0.localDimensionHom_bijective (PadicInt 2)

private theorem integer_regular_dimension :
    ((K0.finrankHom (FractionRing ℤ)).comp
      (K0.map (algebraMap ℤ (FractionRing ℤ)))) (K0.of ℤ ℤᵐᵒᵖ) = 1 :=
  K0.finrankHom_map_of_self (algebraMap ℤ (FractionRing ℤ))

private theorem integer_plane_dimension :
    ((K0.finrankHom (FractionRing ℤ)).comp
      (K0.map (algebraMap ℤ (FractionRing ℤ))))
        (K0.of ℤ (Fin 2 → ℤᵐᵒᵖ)) = 2 := by
  have plane : K0.of ℤ (Fin 2 → ℤᵐᵒᵖ) = 2 • K0.of ℤ ℤᵐᵒᵖ := by
    rw [← K0.ofClass_of, ProjectiveClass.of_fin_fun_eq_nsmul, map_nsmul, K0.ofClass_of]
  rw [plane, map_nsmul, integer_regular_dimension]
  simp

private theorem integer_regular_ne_zero : K0.of ℤ ℤᵐᵒᵖ ≠ 0 := by
  intro h
  have impossible : (1 : ℤ) = 0 := by
    simpa only [integer_regular_dimension, map_zero] using
      congrArg ((K0.finrankHom (FractionRing ℤ)).comp
        (K0.map (algebraMap ℤ (FractionRing ℤ)))) h
  exact one_ne_zero impossible

-- The integer PID premise is discharged, rather than assumed of the model.
example :
    Function.Bijective (ProjectiveClass.map (algebraMap ℤ (FractionRing ℤ))) :=
  ProjectiveClass.map_bijective_of_projective_free _ (pid_projective_free ℤ)

example :
    Function.Bijective
      ((K0.finrankHom (FractionRing ℤ)).comp
        (K0.map (algebraMap ℤ (FractionRing ℤ)))) :=
  K0.pidDimension_bijective ℤ

-- The zero ring is neither a local nor a domain model for these calculations.
example (x : K0 (ZMod 1)) : x = 0 := Subsingleton.elim _ _

end ProjectiveModulesTests.K0LocalPIDCalculationsClient

/-!
## Equivalence computations

The additive equivalences compute the same residue and fraction-field dimensions
as the observers above. Their inverses also compute negative integer multiples.
The round-trip law uses the standard additive-equivalence simp API.
-/

namespace ProjectiveModulesTests.K0LocalPIDCalculationsClient

-- The regular residue module has dimension one by the module evaluation API.
example :
    (Module.finrank (PadicInt 2 ⧸ Ring.jacobson (PadicInt 2))ᵐᵒᵖ
      (ModuleCat.RightExtension.Obj
        (Ideal.Quotient.mk (Ring.jacobson (PadicInt 2))) (PadicInt 2)ᵐᵒᵖ) : ℤ) = 1 := by
  rw [← K0.localEquivInt_of_module, K0.localEquivInt_of_self]

example :
    (K0.localEquivInt (PadicInt 2)).symm (-3 : ℤ) =
        (-3 : ℤ) • K0.of (PadicInt 2) (PadicInt 2)ᵐᵒᵖ ∧
      K0.localEquivInt (PadicInt 2)
        ((-3 : ℤ) • K0.of (PadicInt 2) (PadicInt 2)ᵐᵒᵖ) = -3 := by
  refine ⟨K0.localEquivInt_symm_apply (PadicInt 2) (-3), ?_⟩
  rw [map_zsmul, K0.localEquivInt_of_self]
  simp

-- The whole forward-hom equation recovers two copies of the regular generator.
example :
    (K0.localEquivInt (PadicInt 2)).symm
        (K0.localDimensionHom (PadicInt 2)
          (K0.of (PadicInt 2) (PadicInt 2)ᵐᵒᵖ +
            K0.of (PadicInt 2) (PadicInt 2)ᵐᵒᵖ)) =
      2 • K0.of (PadicInt 2) (PadicInt 2)ᵐᵒᵖ := by
  have forward := congrArg (fun F : K0 (PadicInt 2) →+ ℤ ↦
      F (K0.of (PadicInt 2) (PadicInt 2)ᵐᵒᵖ +
        K0.of (PadicInt 2) (PadicInt 2)ᵐᵒᵖ))
    (K0.localEquivInt_toAddMonoidHom (PadicInt 2))
  rw [← forward]
  simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply, two_nsmul]

-- The existing plane observer computes both the equivalence and its inverse.
example :
    K0.pidEquivInt ℤ (K0.of ℤ (Fin 2 → ℤᵐᵒᵖ)) = 2 ∧
      (K0.pidEquivInt ℤ).symm 2 = K0.of ℤ (Fin 2 → ℤᵐᵒᵖ) ∧
      (Module.finrank (FractionRing ℤ)ᵐᵒᵖ
        (ModuleCat.RightExtension.Obj (algebraMap ℤ (FractionRing ℤ))
          (Fin 2 → ℤᵐᵒᵖ)) : ℤ) = 2 := by
  have dimension : K0.pidEquivInt ℤ (K0.of ℤ (Fin 2 → ℤᵐᵒᵖ)) = 2 := by
    have forward := congrArg (fun F : K0 ℤ →+ ℤ ↦ F (K0.of ℤ (Fin 2 → ℤᵐᵒᵖ)))
      (K0.pidEquivInt_toAddMonoidHom ℤ)
    exact forward.trans integer_plane_dimension
  refine ⟨dimension, ?_, ?_⟩
  · apply (K0.pidEquivInt ℤ).injective
    rw [AddEquiv.apply_symm_apply, K0.pidEquivInt_of_module_finrank,
      Module.finrank_fin_fun, Nat.cast_ofNat]
  · exact (K0.pidEquivInt_of_module ℤ (Fin 2 → ℤᵐᵒᵖ)).symm.trans dimension

example :
    (K0.pidEquivInt ℤ).symm (-3 : ℤ) = (-3 : ℤ) • K0.of ℤ ℤᵐᵒᵖ ∧
      K0.pidEquivInt ℤ ((-3 : ℤ) • K0.of ℤ ℤᵐᵒᵖ) = -3 := by
  refine ⟨K0.pidEquivInt_symm_apply ℤ (-3), ?_⟩
  rw [map_zsmul, K0.pidEquivInt_of_self]
  simp

end ProjectiveModulesTests.K0LocalPIDCalculationsClient
