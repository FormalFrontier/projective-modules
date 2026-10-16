/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.ExteriorPower.BaseChange
import ProjectiveModules.ExteriorPower.Invertible
import ProjectiveModules.ExteriorPower.StalkRank
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis

/-!
# Clients of homogeneous base change, invertibility and exterior vanishing

The positive example is the integer plane in degree two. Scalar extension to
`ZMod 2` uses the public image equality, not a fixed-degree carrier equivalence.
The top-exterior client supplies the exact constant-stalk-rank equation using
the standard basis and Mathlib's free-module rank computation. The degree-zero
control over `ZMod 1` also checks that no nontrivial-ring assumption is required.
The integer plane vanishes in degree three, and the rational zero module in
degree zero shows that the stalk-rank bound must be strict.
-/

open scoped TensorProduct

namespace ProjectiveModulesTests.ExteriorPowerSupportClient

private instance planeFree : Module.Free ℤ (Fin 2 → ℤ) :=
  Module.Free.of_basis (Pi.basisFun ℤ (Fin 2))

private instance planeFinite : Module.Finite ℤ (Fin 2 → ℤ) :=
  Module.Finite.of_basis (Pi.basisFun ℤ (Fin 2))

private instance planeProjective : Module.Projective ℤ (Fin 2 → ℤ) :=
  Module.Projective.of_basis (Pi.basisFun ℤ (Fin 2))

private theorem integerPlane_baseChange :
    (⋀[ZMod 2]^2 (ZMod 2 ⊗[ℤ] (Fin 2 → ℤ))).map
        (ExteriorAlgebra.equivBaseChange
          (R := ℤ) (S := ZMod 2) (M := Fin 2 → ℤ)).toLinearEquiv.toLinearMap =
      (⋀[ℤ]^2 (Fin 2 → ℤ)).baseChange (ZMod 2) :=
  ExteriorAlgebra.equivBaseChange_map_exteriorPower
    (R := ℤ) (S := ZMod 2) (M := Fin 2 → ℤ) 2

private theorem integerPlane_topExterior_invertible : Module.Invertible ℤ (⋀[ℤ]^2 (Fin 2 → ℤ)) := by
  apply exteriorPower.invertible_of_rankAtStalk_eq (R := ℤ) (M := Fin 2 → ℤ) 2
  funext p
  simpa [Module.finrank_fin_fun] using
    congrFun (Module.rankAtStalk_eq_finrank_of_free (R := ℤ) (M := Fin 2 → ℤ)) p

private theorem zeroRing_degreeZero_invertible : Module.Invertible (ZMod 1) (⋀[ZMod 1]^0 (ZMod 1)) :=
  exteriorPower.invertible_of_rankAtStalk_eq (R := ZMod 1) (M := ZMod 1) 0
    (Module.rankAtStalk_eq_zero_of_subsingleton (R := ZMod 1) (M := ZMod 1))

private theorem integerPlane_degreeThree_subsingleton : Subsingleton (⋀[ℤ]^3 (Fin 2 → ℤ)) := by
  apply exteriorPower.subsingleton_of_rankAtStalk_lt (R := ℤ) (M := Fin 2 → ℤ) 3
  intro p
  have hr : Module.rankAtStalk (R := ℤ) (Fin 2 → ℤ) p = 2 := by
    simpa [Module.finrank_fin_fun] using
      congrFun (Module.rankAtStalk_eq_finrank_of_free (R := ℤ) (M := Fin 2 → ℤ)) p
  rw [hr]
  exact Nat.lt_succ_self 2

private theorem zeroRing_degreeZero_subsingleton : Subsingleton (⋀[ZMod 1]^0 (ZMod 1)) :=
  exteriorPower.subsingleton_of_rankAtStalk_lt (R := ZMod 1) (M := ZMod 1) 0
    (fun p ↦ isEmptyElim p)

private theorem rationalZeroModule_degreeZero_strictness : (∀ p : PrimeSpectrum ℚ,
    Module.rankAtStalk (R := ℚ) (Fin 0 → ℚ) p ≤ 0) ∧
    ¬ Subsingleton (⋀[ℚ]^0 (Fin 0 → ℚ)) := by
  constructor
  · intro p
    have hr : Module.rankAtStalk (R := ℚ) (Fin 0 → ℚ) p = 0 := by
      simpa [Module.finrank_fin_fun] using
        congrFun (Module.rankAtStalk_eq_finrank_of_free (R := ℚ) (M := Fin 0 → ℚ)) p
    exact hr.le
  · intro hs
    let e := exteriorPower.zeroEquiv ℚ (Fin 0 → ℚ)
    have h := congrArg e (@Subsingleton.elim _ hs (e.symm 0) (e.symm 1))
    exact (zero_ne_one : (0 : ℚ) ≠ 1) (by simpa using h)

end ProjectiveModulesTests.ExteriorPowerSupportClient
