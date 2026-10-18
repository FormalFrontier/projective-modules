/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.RankLocallyConstant
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Locally constant rank formulas

The formulas compare bundled Nat-valued locally constant functions using
canonical module structures and pointwise semiring operations.

The rational function modules have two and three coordinates; their product
and tensor product have five and six coordinates, respectively. Independent
`ULift` universes occur in both finite indices and carriers. The integer
rank-two module supplies a scalar-extension example over `ℚ`. The zero ring
and an empty finite index are separate boundary cases.
-/

open scoped BigOperators TensorProduct

universe uR uM uN uι uJ

private theorem rankLocallyConstant_coordinates (R : Type uR) [CommRing R] (n : ℕ) :
    Module.rankLocallyConstant R (ULift.{uι} (Fin n) → ULift.{uM} R) =
      (n : LocallyConstant (PrimeSpectrum R) ℕ) := by
  have hline : Module.rankLocallyConstant R (ULift.{uM} R) = 1 := by
    calc
      Module.rankLocallyConstant R (ULift.{uM} R) = Module.rankLocallyConstant R R :=
        Module.rankLocallyConstant_eq_of_equiv (R := R) (M := ULift.{uM} R) (N := R)
          (e := ULift.moduleEquiv (R := R) (M := R))
      _ = 1 := Module.rankLocallyConstant_self (R := R)
  rw [Module.rankLocallyConstant_pi (R := R) (ι := ULift.{uι} (Fin n))
    (M := fun _ => ULift.{uM} R)]
  simp [hline, finsum_eq_sum_of_fintype]

-- The two factors retain independent index and carrier universes.
example :
    Module.rankLocallyConstant ℚ
        ((ULift.{uι} (Fin 2) → ULift.{uM} ℚ) ×
          (ULift.{uJ} (Fin 3) → ULift.{uN} ℚ)) = 5 ∧
      Module.rankLocallyConstant ℚ
        ((ULift.{uι} (Fin 2) → ULift.{uM} ℚ) ⊗[ℚ]
          (ULift.{uJ} (Fin 3) → ULift.{uN} ℚ)) = 6 := by
  have h₂ : Module.rankLocallyConstant ℚ (ULift.{uι} (Fin 2) → ULift.{uM} ℚ) = 2 :=
    rankLocallyConstant_coordinates (R := ℚ) (n := 2)
  have h₃ : Module.rankLocallyConstant ℚ (ULift.{uJ} (Fin 3) → ULift.{uN} ℚ) = 3 :=
    rankLocallyConstant_coordinates (R := ℚ) (n := 3)
  constructor
  · rw [Module.rankLocallyConstant_prod (R := ℚ)
      (M := ULift.{uι} (Fin 2) → ULift.{uM} ℚ)
      (N := ULift.{uJ} (Fin 3) → ULift.{uN} ℚ), h₂, h₃]
    ext p
    rfl
  · rw [Module.rankLocallyConstant_tensorProduct (R := ℚ)
      (M := ULift.{uι} (Fin 2) → ULift.{uM} ℚ)
      (N := ULift.{uJ} (Fin 3) → ULift.{uN} ℚ), h₂, h₃]
    ext p
    rfl

-- Scalar extension uses the spectrum pullback, without classifying primes.
example :
    Module.rankLocallyConstant ℚ
      (ℚ ⊗[ℤ] (ULift.{uι} (Fin 2) → ULift.{uM} ℤ)) = 2 := by
  rw [Module.rankLocallyConstant_baseChange (R := ℤ) (S := ℚ)
    (M := ULift.{uι} (Fin 2) → ULift.{uM} ℤ)]
  rw [rankLocallyConstant_coordinates (R := ℤ) (n := 2)]
  ext p
  rfl

-- Constants zero and one agree on the empty spectrum, not in ℕ.
example :
    Module.rankLocallyConstant (ZMod 1) (ZMod 1) = 0 ∧
      (0 : LocallyConstant (PrimeSpectrum (ZMod 1)) ℕ) = 1 := by
  refine ⟨Module.rankLocallyConstant_eq_zero_of_subsingleton
    (R := ZMod 1) (M := ZMod 1), ?_⟩
  ext p
  exact isEmptyElim p

-- An empty index gives the zero module even though the coefficient ring is nonzero.
example :
    Module.rankLocallyConstant ℚ (ULift.{uι} (Fin 0) → ULift.{uM} ℚ) = 0 := by
  exact Module.rankLocallyConstant_eq_zero_of_subsingleton (R := ℚ)
    (M := ULift.{uι} (Fin 0) → ULift.{uM} ℚ)
