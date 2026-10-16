/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.RightExtensionQuotient
import ProjectiveModules.Module.RightExtensionComparison
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Integer reduction and right-extension kernels

Reduction modulo two has a nonzero kernel vector on the right regular
integer module, while the image of its unit survives. The opposite ring
homomorphism, extended by `fromSemilinear`, observes these images. The
identity map on the same module gives the zero-kernel boundary.

The quotient coordinates use Mathlib's first isomorphism equivalence. All
declarations in this module are private importing examples.
-/

public section

noncomputable section

namespace ProjectiveModulesTests.RightExtensionQuotient

open ModuleCat.RightExtension

private def modTwo : ℤ →+* ZMod 2 :=
  Int.castRingHom (ZMod 2)

private def observer : Obj modTwo ℤᵐᵒᵖ →ₗ[(ZMod 2)ᵐᵒᵖ] (ZMod 2)ᵐᵒᵖ :=
  fromSemilinear modTwo (RingHom.op modTwo).toSemilinearMap

private def quotientCoordinates : ℤ ⧸ RingHom.ker modTwo ≃+* ZMod 2 :=
  modTwo.quotientKerEquivOfSurjective ZMod.intCast_surjective

private theorem modTwo_contract :
    Function.Surjective modTwo ∧
    (∀ n : ℤ, quotientCoordinates (Ideal.Quotient.mk (RingHom.ker modTwo) n) =
      modTwo n) ∧
    (∀ (m : ℤᵐᵒᵖ) (s : ZMod 2),
      observer (tmul modTwo m s) = MulOpposite.op s • (RingHom.op modTwo) m) ∧
    (tmulOne modTwo : ℤᵐᵒᵖ →ₛₗ[RingHom.op modTwo] Obj modTwo ℤᵐᵒᵖ).ker =
      idealSubmodule (M := ℤᵐᵒᵖ) (RingHom.ker modTwo) ∧
    (MulOpposite.op (2 : ℤ) ≠ 0 ∧
      MulOpposite.op (2 : ℤ) ∈
        idealSubmodule (M := ℤᵐᵒᵖ) (RingHom.ker modTwo) ∧
      tmulOne modTwo (MulOpposite.op (2 : ℤ)) = 0) ∧
    (observer (tmulOne modTwo (MulOpposite.op (1 : ℤ))) = 1 ∧
      tmulOne modTwo (MulOpposite.op (1 : ℤ)) ≠ 0) ∧
    (tmulOne modTwo (MulOpposite.op (3 : ℤ)) =
        tmulOne modTwo (MulOpposite.op (1 : ℤ)) ∧
      MulOpposite.op (3 : ℤ) - MulOpposite.op (1 : ℤ) ∈
        idealSubmodule (M := ℤᵐᵒᵖ) (RingHom.ker modTwo)) ∧
    ((tmulOne (RingHom.id ℤ) :
        ℤᵐᵒᵖ →ₛₗ[RingHom.op (RingHom.id ℤ)] Obj (RingHom.id ℤ) ℤᵐᵒᵖ).ker = ⊥ ∧
      Function.Injective (tmulOne (RingHom.id ℤ) :
        ℤᵐᵒᵖ → Obj (RingHom.id ℤ) ℤᵐᵒᵖ) ∧
      ∀ m : ℤᵐᵒᵖ,
        idLinearEquiv ℤ ℤᵐᵒᵖ (tmulOne (RingHom.id ℤ) m) = m) := by
  have hf : Function.Surjective modTwo := ZMod.intCast_surjective
  have htwo : modTwo (2 : ℤ) = 0 := by
    simpa only [modTwo, Int.coe_castRingHom, Int.cast_two, Nat.cast_ofNat] using
      ZMod.natCast_self 2
  have hopTwo : (RingHom.op modTwo) (MulOpposite.op (2 : ℤ)) = 0 :=
    congrArg MulOpposite.op htwo
  have hkill : tmulOne modTwo (MulOpposite.op (2 : ℤ)) = 0 := by
    simpa only [smul_eq_mul, mul_one, hopTwo, zero_smul] using
      (tmulOne modTwo).map_smulₛₗ (MulOpposite.op (2 : ℤ)) (1 : ℤᵐᵒᵖ)
  have hmem : MulOpposite.op (2 : ℤ) ∈
      idealSubmodule (M := ℤᵐᵒᵖ) (RingHom.ker modTwo) :=
    (tmulOne_eq_zero_iff_of_surjective modTwo hf _).mp hkill
  have hone : observer (tmulOne modTwo (MulOpposite.op (1 : ℤ))) = 1 := by
    simp only [observer, tmulOne_apply, fromSemilinear_tmul,
      MulOpposite.op_one, one_smul, RingHom.coe_toSemilinearMap, map_one]
  have hdiff : MulOpposite.op (3 : ℤ) - MulOpposite.op (1 : ℤ) =
      MulOpposite.op (2 : ℤ) := by
    rfl
  have hdiffmem : MulOpposite.op (3 : ℤ) - MulOpposite.op (1 : ℤ) ∈
      idealSubmodule (M := ℤᵐᵒᵖ) (RingHom.ker modTwo) := by
    rw [hdiff]
    exact hmem
  have hrecover : ∀ m : ℤᵐᵒᵖ,
      idLinearEquiv ℤ ℤᵐᵒᵖ (tmulOne (RingHom.id ℤ) m) = m := by
    intro m
    simp only [tmulOne_apply, idLinearEquiv_tmul, MulOpposite.op_one, one_smul]
  have hinj : Function.Injective (tmulOne (RingHom.id ℤ) :
      ℤᵐᵒᵖ → Obj (RingHom.id ℤ) ℤᵐᵒᵖ) := by
    intro m n h
    calc
      m = idLinearEquiv ℤ ℤᵐᵒᵖ (tmulOne (RingHom.id ℤ) m) := (hrecover m).symm
      _ = idLinearEquiv ℤ ℤᵐᵒᵖ (tmulOne (RingHom.id ℤ) n) :=
        congrArg (idLinearEquiv ℤ ℤᵐᵒᵖ) h
      _ = n := hrecover n
  refine ⟨hf, ?_, ?_, tmulOne_ker_of_surjective modTwo hf,
    ⟨by decide, hmem, hkill⟩, ⟨hone, ?_⟩, ⟨?_, hdiffmem⟩,
    ⟨LinearMap.ker_eq_bot.mpr hinj, hinj, hrecover⟩⟩
  · intro n
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hf n
  · intro m s
    exact fromSemilinear_tmul modTwo _ m s
  · intro h
    have hzero := congrArg observer h
    rw [hone, _root_.map_zero] at hzero
    exact one_ne_zero hzero
  · exact (tmulOne_eq_iff_of_surjective modTwo hf _ _).mpr hdiffmem

end ProjectiveModulesTests.RightExtensionQuotient
