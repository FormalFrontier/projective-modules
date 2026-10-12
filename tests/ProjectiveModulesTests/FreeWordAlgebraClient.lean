/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Free.FreeWordAlgebra
import ProjectiveModules.Free.InvariantBasisNumber
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Free-word semiring clients

The rational word ring on the Boolean alphabet is nonzero and noncommutative. Its usual
augmentation sends every word to `1`, not to `0`. It supplies a unital coefficient-return
homomorphism to `ℚ`, giving the rank condition and invariant basis number via the existing
pullback API. On coefficient vectors, augmenting the two-letter map gives addition and
identifies the two coordinate vectors.

The fixtures and assertions are private: this test module checks the public word-map and
rank-condition APIs without adding a second public interface for the rational example.

## References

* Mathlib, `Mathlib.Algebra.MonoidAlgebra.Basic`: the canonical lift and its monomial API.
* `ProjectiveModules.Free.InvariantBasisNumber`: rank-condition and invariant-basis-number
  pullback along a unital semiring homomorphism.
-/

noncomputable section

private abbrev WordRing := MonoidAlgebra ℚ (FreeMonoid Bool)

private abbrev x : WordRing := MonoidAlgebra.single (FreeMonoid.of false) 1

private abbrev y : WordRing := MonoidAlgebra.single (FreeMonoid.of true) 1

private def augmentation : WordRing →+* ℚ :=
  (MonoidAlgebra.lift ℚ ℚ (FreeMonoid Bool) (1 : FreeMonoid Bool →* ℚ)).toRingHom

private theorem augmentation_single (w : FreeMonoid Bool) (q : ℚ) :
    augmentation (MonoidAlgebra.single w q) = q := by
  simp [augmentation]

example : Nontrivial WordRing := inferInstance

example : x ≠ 0 := MonoidAlgebra.single_ne_zero.mpr one_ne_zero

example : y ≠ 0 := MonoidAlgebra.single_ne_zero.mpr one_ne_zero

private theorem generators_ne : x ≠ y := by
  intro h
  have hw := MonoidAlgebra.single_left_injective (R := ℚ) (M := FreeMonoid Bool)
    one_ne_zero h
  have hletters : false = true := FreeMonoid.of_injective hw
  cases hletters

example : x * y ≠ y * x := by
  intro h
  have hwords : FreeMonoid.of false * FreeMonoid.of true =
      FreeMonoid.of true * FreeMonoid.of false :=
    MonoidAlgebra.single_left_injective (R := ℚ) (M := FreeMonoid Bool) one_ne_zero
      (by simpa only [MonoidAlgebra.single_mul_single, one_mul] using h)
  have hlist := congrArg FreeMonoid.toList hwords
  simp at hlist

example : MonoidAlgebra.freeWordPairMap false true (![1, 0] : Fin 2 → WordRing) = x := by
  simp

example : MonoidAlgebra.freeWordPairMap false true (![0, 1] : Fin 2 → WordRing) = y := by
  simp

example : augmentation x = 1 := augmentation_single _ _

example : augmentation y = 1 := augmentation_single _ _

example : ¬ Function.Injective augmentation := by
  intro h
  apply generators_ne
  apply h
  simp only [augmentation_single]

private theorem augmentation_pairMap (v : Fin 2 → WordRing) :
    augmentation (MonoidAlgebra.freeWordPairMap false true v) =
      augmentation (v 0) + augmentation (v 1) := by
  simp only [MonoidAlgebra.freeWordPairMap_apply, map_add, map_mul,
    augmentation_single, mul_one]

private theorem augmentation_pairMap_coefficients (v : Fin 2 → ℚ) :
    augmentation (MonoidAlgebra.freeWordPairMap false true
      (fun i ↦ algebraMap ℚ WordRing (v i))) = v 0 + v 1 := by
  rw [augmentation_pairMap]
  simp [augmentation, MonoidAlgebra.coe_algebraMap]

example : ¬ Function.Injective (fun v : Fin 2 → ℚ ↦
    augmentation (MonoidAlgebra.freeWordPairMap false true
      (fun i ↦ algebraMap ℚ WordRing (v i)))) := by
  intro h
  have heq : (![1, 0] : Fin 2 → ℚ) = ![0, 1] :=
    h (by simp only [augmentation_pairMap_coefficients]; simp)
  have h10 : (1 : ℚ) = 0 := congrFun heq 0
  exact one_ne_zero h10

example : RankCondition WordRing := augmentation.rankCondition

example : InvariantBasisNumber WordRing := augmentation.invariantBasisNumber

-- These two consequences use the two-letter headlines.
example : Function.Injective
    ((LinearEquiv.piUnique WordRing (fun _ : Fin 1 ↦ WordRing)).symm.toLinearMap.comp
      (MonoidAlgebra.freeWordPairMap (K := ℚ) false true)) :=
  (LinearEquiv.piUnique WordRing (fun _ : Fin 1 ↦ WordRing)).symm.injective.comp
    (MonoidAlgebra.freeWordPairMap_injective false true (by intro h; cases h))

example : ¬ StrongRankCondition WordRing :=
  MonoidAlgebra.not_strongRankCondition_freeMonoid false true (by intro h; cases h)

-- Repeating a letter identifies distinct vectors over nontrivial coefficients.
example : ¬ Function.Injective (MonoidAlgebra.freeWordPairMap (K := ℚ) false false) := by
  intro h
  have heq : (![1, 0] : Fin 2 → WordRing) = ![0, 1] := h (by simp)
  have h10 : (1 : WordRing) = 0 := congrFun heq 0
  exact one_ne_zero h10
