/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Stabilization
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Invariant basis number and the regular class in K₀

A unital ring has invariant basis number exactly when its regular right-module
class has infinite additive order in K₀. The regular module has carrier `Rᵐᵒᵖ`
and its canonical left `Rᵐᵒᵖ`-module structure. The statements include the zero ring.

## References

- C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter II, for the finite-free stabilization background used in this derivation.
- `ProjectiveModules.KTheory.Stabilization`, for the formal finite-free
  stabilization criterion and K₀ class interfaces used here.
- Mathlib's formalizations of invariant basis number, opposite rings and finite
  cardinality, and its natural- and integer-multiple additive-order interfaces.
-/

@[expose] public section

universe u

namespace KTheory.K0

/-- A ring has invariant basis number if and only if integer multiples of its
regular right-module class give an injective homomorphism into K₀.

This criterion is derived from finite-free stabilization, following the
background in Weibel's *The K-book*, Chapter II, through
`of_eq_iff_exists_free_stabilizer`. -/
theorem invariantBasisNumber_iff_injective_zmultiplesHom (R : Type u) [Ring R] :
    InvariantBasisNumber R ↔
      Function.Injective (zmultiplesHom (K0 R) (of R Rᵐᵒᵖ)) := by
  have hfree (n : ℕ) : of R (Fin n → Rᵐᵒᵖ) = n • of R Rᵐᵒᵖ := by
    simpa only [map_nsmul, ofClass_of] using
      congrArg (ofClass R) (ProjectiveClass.of_fin_fun_eq_nsmul R n)
  change InvariantBasisNumber R ↔
    Function.Injective (fun z : ℤ => z • of R Rᵐᵒᵖ)
  rw [injective_zsmul_iff_not_isOfFinAddOrder,
    ← injective_nsmul_iff_not_isOfFinAddOrder]
  constructor
  · intro hR
    have : InvariantBasisNumber R := hR
    intro n m hnm
    obtain ⟨k, ⟨e⟩⟩ :=
      (of_eq_iff_exists_free_stabilizer R (Fin n → Rᵐᵒᵖ) (Fin m → Rᵐᵒᵖ)).mp
        (by simpa only [hfree] using hnm)
    have hcard := card_eq_of_linearEquiv Rᵐᵒᵖ
      ((LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin k) Rᵐᵒᵖ Rᵐᵒᵖ).trans
        (e.trans
          (LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin k) Rᵐᵒᵖ Rᵐᵒᵖ).symm))
    exact Nat.add_right_cancel
      (by simpa only [Fintype.card_sum, Fintype.card_fin] using hcard)
  · intro hinj
    apply (MulOpposite.invariantBasisNumber_iff (R := R)).mp
    constructor
    intro n m e
    apply hinj
    simpa only [hfree] using of_eq_of_equiv R (Fin n → Rᵐᵒᵖ) e

/-- A ring has invariant basis number if and only if its regular right-module
class has infinite additive order in K₀, expressed by additive order zero.

This follows from `invariantBasisNumber_iff_injective_zmultiplesHom` and
Mathlib's additive-order interfaces, using the same finite-free stabilization
background from Weibel's *The K-book*, Chapter II. -/
theorem invariantBasisNumber_iff_addOrderOf_eq_zero (R : Type u) [Ring R] :
    InvariantBasisNumber R ↔ addOrderOf (of R Rᵐᵒᵖ) = 0 := by
  rw [invariantBasisNumber_iff_injective_zmultiplesHom]
  change Function.Injective (fun z : ℤ => z • of R Rᵐᵒᵖ) ↔
    addOrderOf (of R Rᵐᵒᵖ) = 0
  rw [injective_zsmul_iff_not_isOfFinAddOrder, addOrderOf_eq_zero_iff]

end KTheory.K0
