/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.Nakayama
import ProjectiveModules.Module.NilpotentEndomorphism
import Mathlib.Tactic.NormNum

/-!
# Finite-range Jacobson perturbation clients

On the common commutative-ring scalar floor, the Jacobson criterion recovers the
nilradical-image unit conclusion using the stock inclusion of the nilradical in
the Jacobson radical. The nilpotent-endomorphism criterion also holds over
commutative semirings.

The empty module checks that a zero scalar endomorphism can be a unit without
forcing the scalar ring to be zero. The rank-one map `m ↦ 2 * m` on `ℤ` has
unit difference `-id` from the identity, although the map is not nilpotent.
-/

universe u v

-- This bridge keeps all the hypotheses of the nilradical-image criterion on the
-- common CommRing floor, and uses the Jacobson ideal corollary instead.
example {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (T : Module.End R M) (I : Ideal R) (hfg : (LinearMap.range T).FG)
    (hT : LinearMap.range T ≤ I • (⊤ : Submodule R M))
    (hI : I ≤ nilradical R) : IsUnit (1 - T) := by
  exact Module.End.isUnit_one_sub_of_fg_range_le_ideal_smul_of_le_jacobson
    T I hfg hT (hI.trans Ideal.radical_le_jacobson)

example (R : Type u) [CommRing R] :
    IsUnit (0 : Module.End R (Fin 0 → R)) := by
  have h := Module.End.isUnit_one_sub_of_fg_range_le_jacobson
    (0 : Module.End R (Fin 0 → R))
    (by rw [LinearMap.range_zero]; exact Submodule.fg_bot)
    (by rw [LinearMap.range_zero]; exact bot_le)
  have hz : (1 : Module.End R (Fin 0 → R)) - 0 = 0 := by
    ext f j
    exact Fin.elim0 j
  rw [hz] at h
  exact h

-- This unit criterion applies beyond nilpotent perturbations.
example :
    IsUnit ((1 : Module.End ℤ ℤ) -
      ((2 : ℤ) • (LinearMap.id : Module.End ℤ ℤ)).smulRight (1 : ℤ)) ∧
    ¬ IsNilpotent (((2 : ℤ) • (LinearMap.id : Module.End ℤ ℤ)).smulRight (1 : ℤ)) := by
  let T := ((2 : ℤ) • (LinearMap.id : Module.End ℤ ℤ)).smulRight (1 : ℤ)
  have hpow (n : ℕ) : (T ^ n) (1 : ℤ) = 2 ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, ih]
        simp [T, LinearMap.smulRight_apply, pow_succ']
  constructor
  · apply (LinearMap.isUnit_one_sub_smulRight_iff _ _).mpr
    norm_num
  · rintro ⟨n, hn⟩
    have hzero : (2 : ℤ) ^ n = 0 := by
      exact (hpow n).symm.trans
        (congrArg (fun f : Module.End ℤ ℤ => f (1 : ℤ)) hn)
    exact (pow_ne_zero n (by norm_num : (2 : ℤ) ≠ 0)) hzero
