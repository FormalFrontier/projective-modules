/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.TensorProduct
import ProjectiveModules.KTheory.Rank
import ProjectiveModules.KTheory.ZeroRing
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.Nat.Cast.Basic

/-!
# Tensor-semiring arithmetic on projective classes

Over the rationals, natural-number classes multiply three by two to give six,
and the additive dimension map proves that the result is nonzero. A nested
raw tensor computation also exercises the associativity, commutativity, unit,
distribution and scaling API, followed by the existing additive completion map.
Over the one-element scalar ring, the semiring unit is zero.
-/

public section

namespace KTheory.ProjectiveClass

example :
    (K0.ofClass ℚ : ProjectiveClass ℚ →+ K0 ℚ)
      (tensorMul ℚ
        (tensorMul ℚ (3 • of ℚ ℚᵐᵒᵖ) (of ℚ ℚᵐᵒᵖ))
        (tensorMul ℚ (of ℚ ℚᵐᵒᵖ) (2 • of ℚ ℚᵐᵒᵖ))) =
      6 • K0.of ℚ ℚᵐᵒᵖ := by
  have h :
      tensorMul ℚ
        (tensorMul ℚ (3 • of ℚ ℚᵐᵒᵖ) (of ℚ ℚᵐᵒᵖ))
        (tensorMul ℚ (of ℚ ℚᵐᵒᵖ) (2 • of ℚ ℚᵐᵒᵖ)) =
          6 • of ℚ ℚᵐᵒᵖ := by
    rw [tensorMul_assoc, regular_tensorMul, regular_tensorMul, tensorMul_comm]
    rw [show (6 : ℕ) = 3 + 3 from rfl, add_nsmul, two_nsmul,
      add_tensorMul, regular_tensorMul]
  rw [h]
  simpa only [K0.ofClass_of] using
    (K0.ofClass ℚ : ProjectiveClass ℚ →+ K0 ℚ).map_nsmul 6 (of ℚ ℚᵐᵒᵖ)

example :
    ((3 : ℕ) : ProjectiveClass ℚ) * ((2 : ℕ) : ProjectiveClass ℚ) =
        ((6 : ℕ) : ProjectiveClass ℚ) ∧
      ((6 : ℕ) : ProjectiveClass ℚ) ≠ 0 := by
  constructor
  · exact (Nat.cast_mul 3 2).symm
  · intro h
    have hdim : (6 : ℕ) = 0 := by
      calc
        (6 : ℕ) = 6 • (finrankHom ℚ) (of ℚ ℚᵐᵒᵖ) := by
          simp only [finrankHom_of_self, Nat.nsmul_eq_mul, mul_one]
        _ = (finrankHom ℚ) (6 • of ℚ ℚᵐᵒᵖ) := by
          exact ((finrankHom ℚ).map_nsmul 6 (of ℚ ℚᵐᵒᵖ)).symm
        _ = (finrankHom ℚ) ((6 : ℕ) : ProjectiveClass ℚ) :=
          congrArg (finrankHom ℚ) (natCast_eq_nsmul ℚ 6).symm
        _ = (finrankHom ℚ) 0 := congrArg (finrankHom ℚ) h
        _ = 0 := (finrankHom ℚ).map_zero
    exact (Nat.succ_ne_zero 5) hdim

example (R : Type*) [CommRing R] (n : ℕ) (a : ProjectiveClass R) :
    (n : ProjectiveClass R) * (a + 0) + a = (n + 1) • a := by
  simp [add_mul]

example : (1 : ProjectiveClass PUnit.{1}) = 0 :=
  Subsingleton.elim _ _

end KTheory.ProjectiveClass
