/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Spans of finite matrix combinations

A matrix with a left inverse preserves the span of a finite family under left
scalar combinations. In particular, multiplying a matrix by a unit on the left
preserves the span of its rows, with no restriction on its column type.
-/

@[expose] public section

open scoped BigOperators Matrix

universe uR uM uI uK

namespace Submodule

/-- Finite scalar combinations indexed by a matrix with a left inverse span the
same submodule as the original family. -/
theorem span_range_matrix_smul_of_leftInverse
    {R : Type uR} [Semiring R] {M : Type uM} [AddCommMonoid M] [Module R M]
    {i : Type uI} {k : Type uK} [Fintype i] [Fintype k] [DecidableEq k]
    (P : Matrix i k R) (Q : Matrix k i R) (hQP : Q * P = 1) (v : k → M) :
    span R (Set.range (fun a => ∑ b, P a b • v b)) = span R (Set.range v) := by
  apply le_antisymm
  · refine span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    exact sum_mem fun b _ => smul_mem _ _ (subset_span ⟨b, rfl⟩)
  · refine span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    have hrecover : (∑ a, Q b a • (∑ c, P a c • v c)) = v b := by
      calc
        (∑ a, Q b a • (∑ c, P a c • v c)) =
            ∑ a, ∑ c, (Q b a * P a c) • v c := by
          simp only [Finset.smul_sum, smul_smul]
        _ = ∑ c, ∑ a, (Q b a * P a c) • v c := Finset.sum_comm
        _ = ∑ c, (Q * P) b c • v c := by
          simp only [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun c _ => ?_
          classical
          have hsum (s : Finset i) :
              (∑ a ∈ s, Q b a * P a c) • v c =
                ∑ a ∈ s, (Q b a * P a c) • v c := by
            induction s using Finset.induction_on with
            | empty => simp
            | @insert a s ha ih =>
                simp only [Finset.sum_insert ha, add_smul, ih]
          exact (hsum Finset.univ).symm
        _ = v b := by simp [hQP, Matrix.one_apply]
    rw [← hrecover]
    exact sum_mem fun a _ => smul_mem _ _ (subset_span ⟨a, rfl⟩)

/-- A unit matrix preserves the span of a finite family under left scalar
combinations. -/
theorem span_range_matrix_smul
    {R : Type uR} [Semiring R] {M : Type uM} [AddCommMonoid M] [Module R M]
    {i : Type uI} [Fintype i] [DecidableEq i]
    (P : Matrix i i R) (hP : IsUnit P) (v : i → M) :
    span R (Set.range (fun a => ∑ b, P a b • v b)) = span R (Set.range v) := by
  rcases hP with ⟨u, rfl⟩
  exact span_range_matrix_smul_of_leftInverse
    (u : Matrix i i R) (↑(u⁻¹)) u.inv_val v

end Submodule

namespace Matrix

/-- Multiplication by a unit matrix on the left preserves the submodule spanned
by the rows, even when the column type is infinite. -/
theorem span_range_rows_mul_of_isUnit
    {R : Type uR} [Semiring R] {i : Type uI} [Fintype i] [DecidableEq i]
    {k : Type uK} (P : Matrix i i R) (hP : IsUnit P) (A : Matrix i k R) :
    Submodule.span R (Set.range (P * A)) = Submodule.span R (Set.range A) := by
  have hrows : (fun a => ∑ b, P a b • A b) = P * A := by
    funext a c
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simpa only [hrows] using
    (Submodule.span_range_matrix_smul (R := R) (M := k → R) P hP A)

end Matrix
