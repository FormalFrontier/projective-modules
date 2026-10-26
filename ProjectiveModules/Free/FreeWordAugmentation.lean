/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.MonoidAlgebra.Lift

/-!
# The zero-generator augmentation of a free-word semiring

The homomorphism `MonoidAlgebra.freeMonoidAugmentation` fixes constant coefficients
and sends each letter monomial to zero. It is defined for any coefficient semiring,
including noncommutative and trivial semirings, and any alphabet. The coefficient and
alphabet universes are independent. The theorem `freeMonoidAugmentation_apply`
identifies its value on every element with the coefficient of the empty word.

The coefficient-sum augmentation instead uses the constant-one word map. These
choices coincide for an empty alphabet or trivial coefficients. The construction
uses `FreeMonoid.lift` and `MonoidAlgebra.liftNCRingHom`; commutation with coefficients
follows from the zero-generator word map itself.

## References

* Mathlib, `Mathlib.Algebra.FreeMonoid.Basic`: the universal word map and word induction.
* Mathlib, `Mathlib.Algebra.MonoidAlgebra.Lift`: the noncommutative lifting construction
  and its monomial computation rule.

Formal Frontier agents developed this module with AI assistance.
-/

@[expose] public section

universe u v

namespace MonoidAlgebra

variable {K : Type u} [Semiring K] {α : Type v}

/-- The zero-generator augmentation of the free-word monoid algebra.

It fixes constant coefficients and sends every letter monomial to zero. No
commutativity assumption on the coefficient semiring is needed: the word map sends
the empty word to one and every nonempty word to zero, which commute with all
coefficients. -/
noncomputable def freeMonoidAugmentation (K : Type u) (α : Type v) [Semiring K] :
    MonoidAlgebra K (FreeMonoid α) →+* K := by
  have commute_freeMonoid_lift_zero (k : K) (w : FreeMonoid α) :
      Commute k (FreeMonoid.lift (fun _ : α ↦ (0 : K)) w) := by
    change k * FreeMonoid.lift (fun _ : α ↦ (0 : K)) w =
      FreeMonoid.lift (fun _ : α ↦ (0 : K)) w * k
    induction w using FreeMonoid.inductionOn' with
    | one => simp only [map_one, mul_one, one_mul]
    | of_mul a w _ =>
      simp only [map_mul, FreeMonoid.lift_eval_of, zero_mul, mul_zero]
  exact liftNCRingHom (RingHom.id K) (FreeMonoid.lift (fun _ : α ↦ (0 : K)))
    (fun k w ↦ commute_freeMonoid_lift_zero k w)

/-- On a monomial, the zero-generator augmentation multiplies its coefficient by
its word's value under the zero-generator word map. -/
theorem freeMonoidAugmentation_single (w : FreeMonoid α) (k : K) :
    freeMonoidAugmentation K α (single w k) =
      k * FreeMonoid.lift (fun _ : α ↦ (0 : K)) w := by
  simp only [freeMonoidAugmentation, liftNCRingHom_single, RingHom.id_apply]

/-- The zero-generator augmentation fixes constant monomials. -/
theorem freeMonoidAugmentation_single_one (k : K) :
    freeMonoidAugmentation K α (single 1 k) = k := by
  rw [freeMonoidAugmentation_single, map_one, mul_one]

/-- The zero-generator augmentation kills letter monomials with any coefficient. -/
theorem freeMonoidAugmentation_single_of (a : α) (k : K) :
    freeMonoidAugmentation K α (single (FreeMonoid.of a) k) = 0 := by
  rw [freeMonoidAugmentation_single, FreeMonoid.lift_eval_of, mul_zero]

/-- The zero-generator augmentation returns the coefficient of the empty word. -/
@[simp]
theorem freeMonoidAugmentation_apply (x : MonoidAlgebra K (FreeMonoid α)) :
    freeMonoidAugmentation K α x = x.coeff 1 := by
  refine MonoidAlgebra.induction_linear x ?_ ?_ ?_
  · simp only [map_zero, coeff_zero, Finsupp.zero_apply]
  · intro x y hx hy
    simp only [map_add, coeff_add, Finsupp.add_apply, hx, hy]
  · intro w k
    refine FreeMonoid.casesOn w ?_ ?_
    · simp only [freeMonoidAugmentation_single_one, coeff_single, Finsupp.single_eq_same]
    · intro a w
      have hw : FreeMonoid.of a * w ≠ 1 := by
        intro h
        exact List.cons_ne_nil a (FreeMonoid.toList w)
          (by simpa only [FreeMonoid.toList_of_mul, FreeMonoid.toList_one] using
            congrArg FreeMonoid.toList h)
      simp only [freeMonoidAugmentation_single, map_mul, FreeMonoid.lift_eval_of,
        zero_mul, mul_zero, coeff_single, Finsupp.single_eq_of_ne' hw]

end MonoidAlgebra
