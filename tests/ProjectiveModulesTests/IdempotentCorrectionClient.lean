/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.RingTheory.IdempotentCorrection
public import Mathlib.Data.ZMod.Basic

/-!
# Correcting a non-idempotent element of `ZMod 4`

The element `3` has nonzero idempotence error `2`, whose square vanishes. The correction
has value `1`, computed from the characteristic difference identity, and is idempotent
by the square-zero-error theorem.
-/

@[expose] public section

example :
    (3 : ZMod 4) * 3 - 3 = 2 ∧
      (2 : ZMod 4) ≠ 0 ∧
      ¬ IsIdempotentElem (3 : ZMod 4) ∧
      ((3 : ZMod 4) * 3 - 3) * ((3 : ZMod 4) * 3 - 3) = 0 ∧
      idempotentCorrection (3 : ZMod 4) = 1 ∧
      IsIdempotentElem (idempotentCorrection (3 : ZMod 4)) := by
  have herror : (3 : ZMod 4) * 3 - 3 = 2 := by decide
  have hnonzero : (2 : ZMod 4) ≠ 0 := by decide
  have hsquare : ((3 : ZMod 4) * 3 - 3) * ((3 : ZMod 4) * 3 - 3) = 0 := by decide
  have hnot : ¬ IsIdempotentElem (3 : ZMod 4) := by
    intro h
    have hz : (3 : ZMod 4) * 3 - 3 = 0 :=
      sub_eq_zero.mpr (isIdempotentElem_iff.mp h)
    exact hnonzero (herror.symm.trans hz)
  have hclose : idempotentCorrection (3 : ZMod 4) - 3 = 2 :=
    (idempotentCorrection_sub_self (3 : ZMod 4)).trans (by decide)
  have hvalue : idempotentCorrection (3 : ZMod 4) = 1 := by
    calc
      idempotentCorrection (3 : ZMod 4) =
          (idempotentCorrection (3 : ZMod 4) - 3) + 3 := (sub_add_cancel _ _).symm
      _ = (2 : ZMod 4) + 3 := congrArg (fun x : ZMod 4 => x + 3) hclose
      _ = 1 := by decide
  exact ⟨herror, hnonzero, hnot, hsquare, hvalue,
    isIdempotentElem_idempotentCorrection (3 : ZMod 4) hsquare⟩
