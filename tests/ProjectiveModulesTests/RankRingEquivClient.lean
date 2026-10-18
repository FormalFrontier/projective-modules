/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Integer rank ring equivalences on free-module classes

The rational, 2-adic integer and integer examples use each ring equivalence's
multiplication law on the classes of independently lifted rank-two and
rank-three right modules. The inverse computations include a negative integer.
Forgetting multiplication retains the entire old additive equivalence, with
its original scalar dictionaries.

The 2-adic model is not a field: its nonzero scalar `2` is not a unit, while
its regular K₀ class is nonzero. The local and domain classification hypotheses
exclude the zero scalar ring; its zero K₀ boundary is covered separately by
`K0ZeroRingClient`. The old division-ring and noncommutative-local additive
interfaces remain usable without commutativity hypotheses.

## References and credits

These examples reuse Projective Modules' rank, module-class and tensor-ring
APIs, Mathlib's rational, integer and 2-adic instances, and standard finite free
right-module models.
-/

universe u v w

open KTheory

namespace ProjectiveModulesTests.RankRingEquivClient

-- The entire additive objects retain the original, explicitly supplied dictionaries.
example (K : Type u) [Field K] :
    (K0.finrankRingEquiv K).toAddEquiv =
      @KTheory.K0.finrankEquiv K (inferInstance : Field K).toDivisionRing := rfl

example (R : Type u) [CommRing R] [IsLocalRing R] :
    (K0.localRingEquivInt R).toAddEquiv =
      @KTheory.K0.localEquivInt R (inferInstance : CommRing R).toRing
        (inferInstance : IsLocalRing R) := rfl

example (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    (K0.pidRingEquivInt R).toAddEquiv =
      @KTheory.K0.pidEquivInt R (inferInstance : CommRing R)
        (inferInstance : IsDomain R) (inferInstance : IsPrincipalIdealRing R) := rfl

-- Both factors are module classes, with independent carrier lifts and right actions.
example :
    K0.finrankRingEquiv ℚ
      (K0.of ℚ (ULift.{v} (Fin 2 → ℚᵐᵒᵖ)) *
        K0.of ℚ (ULift.{w} (Fin 3 → ℚᵐᵒᵖ))) = 6 := by
  calc
    _ = K0.finrankRingEquiv ℚ (K0.of ℚ (ULift.{v} (Fin 2 → ℚᵐᵒᵖ))) *
        K0.finrankRingEquiv ℚ (K0.of ℚ (ULift.{w} (Fin 3 → ℚᵐᵒᵖ))) :=
      (K0.finrankRingEquiv ℚ).map_mul _ _
    _ = 6 := by
      simpa only [K0.of_ulift, K0.finrankRingEquiv_of_module,
        Module.finrank_fin_fun, Nat.cast_ofNat] using (show (2 : ℤ) * 3 = 6 from rfl)

example :
    (K0.finrankRingEquiv ℚ).symm (-3 : ℤ) =
        (-3 : ℤ) • K0.of ℚ ℚᵐᵒᵖ ∧
      K0.finrankRingEquiv ℚ ((-3 : ℤ) • K0.of ℚ ℚᵐᵒᵖ) = -3 := by
  refine ⟨K0.finrankRingEquiv_symm_apply ℚ (-3), ?_⟩
  rw [← K0.finrankRingEquiv_symm_apply ℚ (-3)]
  exact (K0.finrankRingEquiv ℚ).apply_symm_apply (-3)

-- Keep the stock 2-adic scalar dictionary, rather than transporting a field model.
private theorem padic_dictionary :
    (inferInstance : CommRing (PadicInt 2)) = PadicInt.instCommRing := rfl

example :
    K0.localRingEquivInt (PadicInt 2)
      (K0.of (PadicInt 2) (ULift.{v} (Fin 2 → (PadicInt 2)ᵐᵒᵖ)) *
        K0.of (PadicInt 2) (ULift.{w} (Fin 3 → (PadicInt 2)ᵐᵒᵖ))) = 6 := by
  have coordinates (n : ℕ) :
      K0.localRingEquivInt (PadicInt 2)
        (K0.of (PadicInt 2) (Fin n → (PadicInt 2)ᵐᵒᵖ)) = (n : ℤ) := by
    rw [← K0.ofClass_of, ProjectiveClass.of_fin_fun_eq_nsmul, map_nsmul,
      K0.ofClass_of, map_nsmul, K0.of_self, map_one]
    simp
  calc
    _ = K0.localRingEquivInt (PadicInt 2)
          (K0.of (PadicInt 2) (ULift.{v} (Fin 2 → (PadicInt 2)ᵐᵒᵖ))) *
        K0.localRingEquivInt (PadicInt 2)
          (K0.of (PadicInt 2) (ULift.{w} (Fin 3 → (PadicInt 2)ᵐᵒᵖ))) :=
      (K0.localRingEquivInt (PadicInt 2)).map_mul _ _
    _ = 6 := by
      simpa only [K0.of_ulift, coordinates, Nat.cast_ofNat] using
        (show (2 : ℤ) * 3 = 6 from rfl)

example :
    (K0.localRingEquivInt (PadicInt 2)).symm (-3 : ℤ) =
        (-3 : ℤ) • K0.of (PadicInt 2) (PadicInt 2)ᵐᵒᵖ ∧
      K0.localRingEquivInt (PadicInt 2)
        ((-3 : ℤ) • K0.of (PadicInt 2) (PadicInt 2)ᵐᵒᵖ) = -3 := by
  refine ⟨K0.localRingEquivInt_symm_apply (PadicInt 2) (-3), ?_⟩
  rw [← K0.localRingEquivInt_symm_apply (PadicInt 2) (-3)]
  exact (K0.localRingEquivInt (PadicInt 2)).apply_symm_apply (-3)

example :
    (2 : PadicInt 2) ≠ 0 ∧ ¬ IsUnit (2 : PadicInt 2) ∧
      K0.of (PadicInt 2) (PadicInt 2)ᵐᵒᵖ ≠ 0 := by
  refine ⟨Nat.cast_ne_zero.mpr (by decide : (2 : ℕ) ≠ 0), ?_, ?_⟩
  · simpa only [mem_nonunits_iff, Nat.cast_ofNat] using (PadicInt.p_nonunit (p := 2))
  · intro equality
    have impossible : (1 : ℤ) = 0 := by
      simpa only [K0.of_self, map_one, map_zero] using
        congrArg (K0.localRingEquivInt (PadicInt 2)) equality
    exact one_ne_zero impossible

example :
    K0.pidRingEquivInt ℤ
      (K0.of ℤ (ULift.{v} (Fin 2 → ℤᵐᵒᵖ)) *
        K0.of ℤ (ULift.{w} (Fin 3 → ℤᵐᵒᵖ))) = 6 := by
  calc
    _ = K0.pidRingEquivInt ℤ (K0.of ℤ (ULift.{v} (Fin 2 → ℤᵐᵒᵖ))) *
        K0.pidRingEquivInt ℤ (K0.of ℤ (ULift.{w} (Fin 3 → ℤᵐᵒᵖ))) :=
      (K0.pidRingEquivInt ℤ).map_mul _ _
    _ = 6 := by
      simpa only [K0.of_ulift, K0.pidRingEquivInt_of_module_finrank,
        Module.finrank_fin_fun, Nat.cast_ofNat] using (show (2 : ℤ) * 3 = 6 from rfl)

example :
    (K0.pidRingEquivInt ℤ).symm (-3 : ℤ) = (-3 : ℤ) • K0.of ℤ ℤᵐᵒᵖ ∧
      K0.pidRingEquivInt ℤ ((-3 : ℤ) • K0.of ℤ ℤᵐᵒᵖ) = -3 := by
  refine ⟨K0.pidRingEquivInt_symm_apply ℤ (-3), ?_⟩
  rw [← K0.pidRingEquivInt_symm_apply ℤ (-3)]
  exact (K0.pidRingEquivInt ℤ).apply_symm_apply (-3)

-- Compatibility checks use only the old additive APIs and do not assume commutativity.
example (D : Type u) [DivisionRing D] :
    K0.finrankEquiv D
      (K0.of D (Fin 2 → Dᵐᵒᵖ) + K0.of D Dᵐᵒᵖ) = 3 := by
  simpa only [map_add, K0.finrankEquiv_of_module, Module.finrank_fin_fun,
    Module.finrank_self, Nat.cast_ofNat, Nat.cast_one] using
      (show (2 : ℤ) + 1 = 3 from rfl)

example (R : Type u) [Ring R] [IsLocalRing R] :
    K0.localEquivInt R (K0.of R (Rᵐᵒᵖ × Rᵐᵒᵖ)) = 2 := by
  simpa only [K0.of_prod, map_add, K0.localEquivInt_of_self] using
    (show (1 : ℤ) + 1 = 2 from rfl)

end ProjectiveModulesTests.RankRingEquivClient
