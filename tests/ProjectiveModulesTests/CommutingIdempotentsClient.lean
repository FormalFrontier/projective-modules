/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.CommutingIdempotents

/-!
# Four-coordinate commuting projections

On `(ℤ × ℤ) × (ℤ × ℤ)`, two coordinate projections have four nonzero
range/kernel intersections. The scalar semiring is `ℕ`, not a ring. The
projections and the witnesses are defined independently of any decomposition
equivalence. At `((1, 2), (3, 4))`, the four complementary endomorphism products
extract the four coordinates, and the sum of their values recovers the vector.

## References and credits

This model uses Mathlib's endomorphism ring, range/kernel submodules and product
linear maps, alongside its projection formalization.
-/

@[expose] public section

universe uR uM

namespace ProjectiveModulesTests.CommutingIdempotents

private abbrev Coordinates := (ℤ × ℤ) × (ℤ × ℤ)

private def p : Module.End ℕ Coordinates :=
  (LinearMap.id : Module.End ℕ (ℤ × ℤ)).prodMap 0

private def q : Module.End ℕ Coordinates :=
  ((LinearMap.fst ℕ ℤ ℤ).prod (0 : (ℤ × ℤ) →ₗ[ℕ] ℤ)).prodMap
    ((LinearMap.fst ℕ ℤ ℤ).prod (0 : (ℤ × ℤ) →ₗ[ℕ] ℤ))

private theorem p_idempotent : IsIdempotentElem p := by
  change p * p = p
  apply LinearMap.ext
  intro x
  rfl

private theorem q_idempotent : IsIdempotentElem q := by
  change q * q = q
  apply LinearMap.ext
  intro x
  rfl

private theorem commute_p_q : Commute p q := by
  change p * q = q * p
  apply LinearMap.ext
  intro x
  rfl

private def e00 : Coordinates := ((1, 0), (0, 0))
private def e01 : Coordinates := ((0, 1), (0, 0))
private def e10 : Coordinates := ((0, 0), (1, 0))
private def e11 : Coordinates := ((0, 0), (0, 1))

private theorem intersections_nonzero :
    (∃ z : ↥(LinearMap.range p ⊓ LinearMap.range q), z ≠ 0) ∧
      (∃ z : ↥(LinearMap.range p ⊓ LinearMap.ker q), z ≠ 0) ∧
      (∃ z : ↥(LinearMap.ker p ⊓ LinearMap.range q), z ≠ 0) ∧
      (∃ z : ↥(LinearMap.ker p ⊓ LinearMap.ker q), z ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨⟨e00, ?_⟩, ?_⟩
    · exact ⟨LinearMap.mem_range.mpr ⟨e00, rfl⟩,
        LinearMap.mem_range.mpr ⟨e00, rfl⟩⟩
    · intro h
      have h' : e00 = (0 : Coordinates) := congrArg Subtype.val h
      simp [e00] at h'
  · refine ⟨⟨e01, ?_⟩, ?_⟩
    · exact ⟨LinearMap.mem_range.mpr ⟨e01, rfl⟩, LinearMap.mem_ker.mpr rfl⟩
    · intro h
      have h' : e01 = (0 : Coordinates) := congrArg Subtype.val h
      simp [e01] at h'
  · refine ⟨⟨e10, ?_⟩, ?_⟩
    · exact ⟨LinearMap.mem_ker.mpr rfl, LinearMap.mem_range.mpr ⟨e10, rfl⟩⟩
    · intro h
      have h' : e10 = (0 : Coordinates) := congrArg Subtype.val h
      simp [e10] at h'
  · refine ⟨⟨e11, ?_⟩, ?_⟩
    · exact ⟨LinearMap.mem_ker.mpr rfl, LinearMap.mem_ker.mpr rfl⟩
    · intro h
      have h' : e11 = (0 : Coordinates) := congrArg Subtype.val h
      simp [e11] at h'

private def vector : Coordinates := ((1, 2), (3, 4))

private theorem product_coordinates :
    (p * q) vector = ((1, 0), (0, 0)) ∧
      (p * (1 - q)) vector = ((0, 2), (0, 0)) ∧
      ((1 - p) * q) vector = ((0, 0), (3, 0)) ∧
      ((1 - p) * (1 - q)) vector = ((0, 0), (0, 4)) ∧
      ((p * q) vector + (p * (1 - q)) vector) +
        (((1 - p) * q) vector + ((1 - p) * (1 - q)) vector) = vector := by
  decide

private theorem commutingIdempotentsEquiv_coordinates :
    let e := LinearMap.commutingIdempotentsEquiv p q p_idempotent q_idempotent commute_p_q
    let z := e vector
    (z.1.1 : Coordinates) = ((1, 0), (0, 0)) ∧
      (z.1.2 : Coordinates) = ((0, 2), (0, 0)) ∧
      (z.2.1 : Coordinates) = ((0, 0), (3, 0)) ∧
      (z.2.2 : Coordinates) = ((0, 0), (0, 4)) ∧
      e.symm z = vector := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (LinearMap.commutingIdempotentsEquiv_apply_fst_fst
      p q p_idempotent q_idempotent commute_p_q vector).trans product_coordinates.1
  · exact (LinearMap.commutingIdempotentsEquiv_apply_fst_snd
      p q p_idempotent q_idempotent commute_p_q vector).trans product_coordinates.2.1
  · exact (LinearMap.commutingIdempotentsEquiv_apply_snd_fst
      p q p_idempotent q_idempotent commute_p_q vector).trans product_coordinates.2.2.1
  · exact (LinearMap.commutingIdempotentsEquiv_apply_snd_snd
      p q p_idempotent q_idempotent commute_p_q vector).trans product_coordinates.2.2.2.1
  · refine (LinearMap.commutingIdempotentsEquiv_symm_apply
      p q p_idempotent q_idempotent commute_p_q _).trans ?_
    rw [LinearMap.commutingIdempotentsEquiv_apply_fst_fst,
      LinearMap.commutingIdempotentsEquiv_apply_fst_snd,
      LinearMap.commutingIdempotentsEquiv_apply_snd_fst,
      LinearMap.commutingIdempotentsEquiv_apply_snd_snd,
      product_coordinates.2.2.2.2]

/-- For the zero and identity endomorphisms, only the third of the four products
survives, and the sum of their values is the original vector. -/
theorem zero_one_product_coordinates {R : Type uR} [Semiring R]
    {M : Type uM} [AddCommGroup M] [Module R M] (x : M) :
    ((((0 : Module.End R M) * 1) x,
        ((0 : Module.End R M) * (1 - 1)) x),
      ((((1 : Module.End R M) - 0) * 1) x,
        (((1 : Module.End R M) - 0) * (1 - 1)) x)) = ((0, 0), (x, 0)) ∧
      (((0 : Module.End R M) * 1) x +
        ((0 : Module.End R M) * (1 - 1)) x) +
        ((((1 : Module.End R M) - 0) * 1) x +
          (((1 : Module.End R M) - 0) * (1 - 1)) x) = x := by
  simp

end ProjectiveModulesTests.CommutingIdempotents
