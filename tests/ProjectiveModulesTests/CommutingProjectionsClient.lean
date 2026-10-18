/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Pi
public import ProjectiveModules.Module.CommutingProjections

/-!
# Three commuting bit projections over the natural numbers

On the module of integer-valued functions on `Fin 3 → Bool`, the projection
indexed by `i : Fin 3` keeps exactly the coordinates whose `i`th bit is true.
The additive group and natural-number scalar action are pointwise. Direct
coordinate calculations prove idempotence and pairwise commutation.

Every Boolean choice has a coordinate delta function in the intersection of
its selected ranges and kernels. Its value at that choice is `1`, so each of
the eight joint blocks has a nonzero member. No decomposition is used in these
calculations.

The simultaneous decomposition sends each delta function to its own joint
component and zero elsewhere. Its inverse inclusion sum recovers the same
function.
-/

@[expose] public section

namespace ThreeBitProjections

/-- Keep the function coordinates whose selected bit is true. -/
def bitProjection (i : Fin 3) : Module.End ℕ ((Fin 3 → Bool) → ℤ) where
  toFun f ω := if ω i then f ω else 0
  map_add' f g := by
    funext ω
    cases h : ω i <;> simp [h]
  map_smul' n f := by
    funext ω
    cases h : ω i <;> simp [h]

/-- Evaluation of a bit projection at a Boolean coordinate. -/
@[simp]
theorem bitProjection_apply (i : Fin 3) (f : (Fin 3 → Bool) → ℤ)
    (ω : Fin 3 → Bool) :
    bitProjection i f ω = if ω i then f ω else 0 := rfl

/-- Each bit projection is idempotent under endomorphism composition. -/
theorem bitProjection_isIdempotent (i : Fin 3) :
    IsIdempotentElem (bitProjection i) := by
  change bitProjection i * bitProjection i = bitProjection i
  apply LinearMap.ext
  intro f
  funext ω
  cases h : ω i <;> simp [h]

/-- The three bit projections commute pairwise. -/
theorem bitProjection_pairwise_commute :
    Pairwise (fun i j : Fin 3 => Commute (bitProjection i) (bitProjection j)) := by
  intro i j _
  change bitProjection i * bitProjection j = bitProjection j * bitProjection i
  apply LinearMap.ext
  intro f
  funext ω
  cases hi : ω i <;> cases hj : ω j <;> simp [hi, hj]

/-- The integer-valued delta function at a Boolean coordinate. -/
def coordinateDelta (ε : Fin 3 → Bool) : (Fin 3 → Bool) → ℤ :=
  fun ω => if ω = ε then 1 else 0

/-- Evaluation of a coordinate delta function. -/
@[simp]
theorem coordinateDelta_apply (ε ω : Fin 3 → Bool) :
    coordinateDelta ε ω = if ω = ε then 1 else 0 := rfl

private theorem bitProjection_coordinateDelta (i : Fin 3) (ε : Fin 3 → Bool) :
    bitProjection i (coordinateDelta ε) = if ε i then coordinateDelta ε else 0 := by
  funext ω
  by_cases h : ω = ε
  · subst ω
    cases hε : ε i <;> simp [hε]
  · cases hω : ω i <;> cases hε : ε i <;> simp [h, hω]

/-- Every range/kernel choice contains its nonzero coordinate delta function. -/
theorem coordinateDelta_witness (ε : Fin 3 → Bool) :
    coordinateDelta ε ∈ (⨅ i : Fin 3,
      if ε i then (bitProjection i).range else (bitProjection i).ker) ∧
    coordinateDelta ε ε = 1 ∧ coordinateDelta ε ≠ 0 := by
  constructor
  · refine (Submodule.mem_iInf _).2 ?_
    intro i
    cases hε : ε i with
    | false =>
      change coordinateDelta ε ∈ (bitProjection i).ker
      apply LinearMap.mem_ker.mpr
      simpa [hε] using bitProjection_coordinateDelta i ε
    | true =>
      change coordinateDelta ε ∈ (bitProjection i).range
      apply LinearMap.mem_range.mpr
      refine ⟨coordinateDelta ε, ?_⟩
      simpa [hε] using bitProjection_coordinateDelta i ε
  · constructor
    · simp
    · intro h
      have hone : (1 : ℤ) = 0 := by
        simpa using congrArg (fun f : (Fin 3 → Bool) → ℤ => f ε) h
      exact one_ne_zero hone

private theorem coordinateDelta_decomposition (ε : Fin 3 → Bool) :
    (∀ η : Fin 3 → Bool,
      (LinearMap.commutingIdempotentsPiEquiv bitProjection bitProjection_isIdempotent
        bitProjection_pairwise_commute (coordinateDelta ε) η : (Fin 3 → Bool) → ℤ) =
          if η = ε then coordinateDelta ε else 0) ∧
    (LinearMap.commutingIdempotentsPiEquiv bitProjection bitProjection_isIdempotent
      bitProjection_pairwise_commute).symm
        (LinearMap.commutingIdempotentsPiEquiv bitProjection bitProjection_isIdempotent
          bitProjection_pairwise_commute (coordinateDelta ε)) = coordinateDelta ε := by
  classical
  have hmem : coordinateDelta ε ∈ LinearMap.jointBlock bitProjection ε :=
    (LinearMap.mem_jointBlock_iff bitProjection bitProjection_isIdempotent ε _).mpr
      (fun i ↦ bitProjection_coordinateDelta i ε)
  have hcomponents : ∀ η : Fin 3 → Bool,
      (LinearMap.commutingIdempotentsPiEquiv bitProjection bitProjection_isIdempotent
        bitProjection_pairwise_commute (coordinateDelta ε) η : (Fin 3 → Bool) → ℤ) =
          if η = ε then coordinateDelta ε else 0 := by
    intro η
    rw [LinearMap.commutingIdempotentsPiEquiv_apply, LinearMap.jointComponent_apply]
    by_cases hη : η = ε <;>
      simpa [hη] using
        LinearMap.jointProjector_apply_jointBlock bitProjection bitProjection_isIdempotent
          bitProjection_pairwise_commute η ε ⟨coordinateDelta ε, hmem⟩
  refine ⟨hcomponents, ?_⟩
  rw [LinearMap.commutingIdempotentsPiEquiv_symm_apply]
  simp only [hcomponents, finsum_eq_sum_of_fintype]
  simp

end ThreeBitProjections
