/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Cyclic additive traces and invariant basis number

An additive map that identifies `xy` with `yx` identifies the traces of opposite
rectangular matrix products. Distinct natural multiples of the image of one then
detect the ranks of mutually inverse finite matrices over a semiring. The target
requires only an additive commutative monoid, not a multiplication.

## References

* P. M. Cohn, *Some remarks on the invariant basis property*, §3, Proposition 3.1
  and its corollary.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Exercise I.1.2.
* Mathlib, `Mathlib.LinearAlgebra.Matrix.Trace` and
  `Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber`.
-/

@[expose] public section

universe uR uA uM uN

namespace Matrix

variable {m : Type uM} {n : Type uN} [Fintype m] [Fintype n]

variable {R : Type uR} {A : Type uA} [AddCommMonoid R] [Mul R] [AddCommMonoid A]

/-- A cyclic additive map identifies traces of opposite rectangular matrix products,
including products with empty index types. The multiplication on `R` need not be
associative or distributive.

This generalizes the finite-sum trace argument in P. M. Cohn, *Some remarks on the
invariant basis property*, §3, from rings and additive commutators to a cyclic
additive map between additive commutative monoids, with only a multiplication on
the source. -/
theorem trace_mul_comm_of_addMonoidHom (τ : R →+ A)
    (hcyc : ∀ x y : R, τ (x * y) = τ (y * x))
    (X : Matrix m n R) (Y : Matrix n m R) :
    τ (trace (X * Y)) = τ (trace (Y * X)) := by
  calc
    τ (trace (X * Y)) = ∑ i : m, ∑ j : n, τ (X i j * Y j i) := by
      simp only [trace, diag_apply, mul_apply, map_sum]
    _ = ∑ j : n, ∑ i : m, τ (Y j i * X i j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      exact hcyc _ _
    _ = τ (trace (Y * X)) := by
      simp only [trace, diag_apply, mul_apply, map_sum]

end Matrix

namespace Matrix

variable {m : Type uM} {n : Type uN} [Fintype m] [Fintype n]
variable {R : Type uR} [AddCommMonoid R] [CommMagma R]

/-- The identity additive map specializes the cyclic trace identity to the
commutative-multiplication setting of `Matrix.trace_mul_comm`. -/
theorem trace_mul_comm_of_addMonoidHom_id
    (X : Matrix m n R) (Y : Matrix n m R) :
    trace (X * Y) = trace (Y * X) := by
  simpa using trace_mul_comm_of_addMonoidHom (AddMonoidHom.id R)
    (by intro x y; exact congrArg (AddMonoidHom.id R) (mul_comm x y)) X Y

end Matrix

namespace AddMonoidHom

variable {R : Type uR} {A : Type uA} [Semiring R] [AddCommMonoid A]

/-- A cyclic additive map with distinct natural multiples of its value at one
implies invariant basis number for the source semiring. No multiplication on the
target or rank condition on the source is required.

This sufficient criterion generalizes P. M. Cohn, *Some remarks on the invariant
basis property*, §3, Proposition 3.1 and its corollary, from the ring and
additive-commutator quotient setting to semirings and arbitrary additive
commutative-monoid targets. C. A. Weibel, *The K-book*, Exercise I.1.2 motivates
the invariant-basis-number application. The cyclic map and its injectivity
condition are hypotheses; no trace on a universal ring is constructed here. -/
theorem invariantBasisNumber_of_cyclic (τ : R →+ A)
    (hcyc : ∀ x y : R, τ (x * y) = τ (y * x))
    (hinj : Function.Injective (fun n : ℕ => n • τ (1 : R))) :
    InvariantBasisNumber R := by
  apply invariantBasisNumber_iff_matrix.mpr
  intro n m X Y hXY hYX
  apply hinj
  have htrace := Matrix.trace_mul_comm_of_addMonoidHom τ hcyc X Y
  simpa only [hXY, hYX, Matrix.trace_one, Fintype.card_fin, ← nsmul_one,
    map_nsmul] using htrace

end AddMonoidHom
