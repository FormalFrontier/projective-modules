/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Nil left ideals and the Jacobson radical

Every left ideal consisting of nilpotent elements lies in the Jacobson radical of the zero
ideal. The proof uses Mathlib's unit criterion for nilpotent elements and its left-inverse
characterization of membership in the Jacobson radical.
-/

@[expose] public section

universe u v

/-- A left ideal whose elements are nilpotent lies in the Jacobson radical of the zero
ideal. -/
theorem Ideal.le_jacobson_bot_of_isNilpotent_mem
    {R : Type u} [Ring R] (I : Ideal R)
    (hnil : ∀ x ∈ I, IsNilpotent x) :
    I ≤ Ideal.jacobson (⊥ : Ideal R) := by
  intro x hx
  have hunit : ∀ r : R, IsUnit (1 - r * x) := by
    intro r
    exact (hnil (r * x) (I.mul_mem_left r hx)).isUnit_one_sub
  refine Ideal.mem_jacobson_iff.mpr ?_
  intro y
  have hy : IsUnit (y * x + 1) := by
    simpa only [neg_mul, sub_neg_eq_add, add_comm] using hunit (-y)
  rcases hy with ⟨u, hu⟩
  refine ⟨↑(u⁻¹), ?_⟩
  apply Ideal.mem_bot.mpr
  have hu_inv : (↑(u⁻¹) : R) * (y * x + 1) = 1 := by
    rw [← hu]
    simp
  calc
    (↑(u⁻¹) : R) * y * x + ↑(u⁻¹) - 1 =
        (↑(u⁻¹) : R) * (y * x + 1) - 1 := by rw [mul_add, mul_one, mul_assoc]
    _ = 0 := by rw [hu_inv, sub_self]

/-- A nil kernel lies in the Jacobson radical without a surjectivity assumption. -/
private theorem kernel_le_jacobson_bot_of_isNilpotent_mem
    {R : Type u} {S : Type v} [Ring R] [Semiring S] (f : R →+* S)
    (hnil : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
    RingHom.ker f ≤ Ideal.jacobson (⊥ : Ideal R) :=
  Ideal.le_jacobson_bot_of_isNilpotent_mem (RingHom.ker f) hnil
