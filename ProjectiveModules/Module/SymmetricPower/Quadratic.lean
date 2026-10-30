/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.SymmetricPower.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# Diagonal products in the second symmetric power

In characteristic two the mixed coordinate functional on the second symmetric power
of `R × R` vanishes on diagonal products, but not on the product of the coordinate vectors.
-/

@[expose] public section

noncomputable section

universe u

namespace SymmetricPower

variable (R : Type u) [CommSemiring R]

/-- The mixed coordinate of a symmetric product of pairs of scalars. -/
def mixedCoeff : SymmetricPower R (ULift.{u} (Fin 2)) (R × R) →ₗ[R] R := by
  let m : MultilinearMap R (fun _ : ULift.{u} (Fin 2) => R × R) R :=
    { toFun v := (v (ULift.up 0)).1 * (v (ULift.up 1)).2 +
        (v (ULift.up 0)).2 * (v (ULift.up 1)).1
      map_update_add' := by
        intro _ v i x y
        rcases i with ⟨i⟩
        fin_cases i <;>
          simp [Function.update, add_mul, mul_add, add_assoc, add_left_comm]
      map_update_smul' := by
        intro _ v i c x
        rcases i with ⟨i⟩
        fin_cases i <;>
          simp [Function.update, smul_eq_mul, mul_add, mul_assoc, mul_comm] }
  refine lift m ?_
  intro e v
  change (v (e (ULift.up 0))).1 * (v (e (ULift.up 1))).2 +
      (v (e (ULift.up 0))).2 * (v (e (ULift.up 1))).1 =
    (v (ULift.up 0)).1 * (v (ULift.up 1)).2 +
      (v (ULift.up 0)).2 * (v (ULift.up 1)).1
  have cases2 (i : ULift.{u} (Fin 2)) :
      i = ULift.up 0 ∨ i = ULift.up 1 := by
    rcases i with ⟨i⟩
    fin_cases i <;> simp
  have hne : (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≠ ULift.up 1 := by decide
  rcases cases2 (e (ULift.up 0)) with h0 | h0 <;>
    rcases cases2 (e (ULift.up 1)) with h1 | h1
  · exact (hne (e.injective (h0.trans h1.symm))).elim
  · simp only [h0, h1]
  · simp only [h0, h1]
    ac_rfl
  · exact (hne (e.injective (h0.trans h1.symm))).elim

/-- The mixed coordinate of a pure product is its symmetric bilinear cross term. -/
@[simp] theorem mixedCoeff_tprod (v : ULift.{u} (Fin 2) → R × R) :
    mixedCoeff R (tprod R v) = (v (ULift.up 0)).1 * (v (ULift.up 1)).2 +
      (v (ULift.up 0)).2 * (v (ULift.up 1)).1 := by
  simp only [mixedCoeff, lift_tprod]
  rfl

/-- In characteristic two the mixed coordinate vanishes on every diagonal product. -/
theorem mixedCoeff_tprod_self [CharP R 2] (v : R × R) :
    mixedCoeff R (tprod R (fun _ : ULift.{u} (Fin 2) => v)) = 0 := by
  have htwo : (2 : R) = 0 := by
    simpa only [Nat.cast_ofNat] using (CharP.cast_eq_zero R 2)
  rw [mixedCoeff_tprod, mul_comm v.2 v.1, ← two_mul, htwo, zero_mul]

/-- The mixed coordinate kills the entire span of diagonal products in characteristic two. -/
theorem span_diagonal_le_ker_mixedCoeff [CharP R 2] :
    Submodule.span R (Set.range fun v : R × R =>
      tprod R (fun _ : ULift.{u} (Fin 2) => v)) ≤ LinearMap.ker (mixedCoeff R) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, rfl⟩
  exact mixedCoeff_tprod_self R v

/-- The mixed coordinate of the product of the two coordinate vectors is one. -/
theorem mixedCoeff_tprod_coordinate_vectors :
    mixedCoeff R (tprod R (fun i : ULift.{u} (Fin 2) =>
      if i.down = 0 then ((1 : R), 0) else (0, 1))) = 1 := by
  rw [mixedCoeff_tprod]
  simp

/-- In characteristic two the product of the coordinate vectors is outside the span of diagonals. -/
theorem tprod_coordinate_vectors_not_mem_span_diagonal [CharP R 2] :
    tprod R (fun i : ULift.{u} (Fin 2) =>
      if i.down = 0 then ((1 : R), 0) else (0, 1)) ∉
      Submodule.span R (Set.range fun v : R × R =>
        tprod R (fun _ : ULift.{u} (Fin 2) => v)) := by
  intro h
  have hz : mixedCoeff R (tprod R (fun i : ULift.{u} (Fin 2) =>
      if i.down = 0 then ((1 : R), 0) else (0, 1))) = 0 :=
    span_diagonal_le_ker_mixedCoeff R h
  rw [mixedCoeff_tprod_coordinate_vectors] at hz
  have hd : 2 ∣ 1 := (CharP.cast_eq_zero_iff R 2 1).mp (by simpa using hz)
  exact (by decide : ¬ (2 : ℕ) ∣ 1) hd

/-- Diagonal products do not span the second symmetric power of `R × R` in characteristic two. -/
theorem span_diagonal_ne_top [CharP R 2] :
    Submodule.span R (Set.range fun v : R × R =>
      tprod R (fun _ : ULift.{u} (Fin 2) => v)) ≠ ⊤ := by
  intro h
  exact tprod_coordinate_vectors_not_mem_span_diagonal R (by rw [h]; trivial)

/-- Over the two-element field, diagonal products form a proper submodule of the second
symmetric power of the rank-two free module. -/
theorem span_diagonal_zmod_two_ne_top :
    Submodule.span (ZMod 2) (Set.range fun v : ZMod 2 × ZMod 2 =>
      tprod (ZMod 2) (fun _ : ULift.{0} (Fin 2) => v)) ≠ ⊤ :=
  span_diagonal_ne_top (ZMod 2)

end SymmetricPower
