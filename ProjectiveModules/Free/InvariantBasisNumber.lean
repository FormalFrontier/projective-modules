/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber

/-!
# Pullback of rank conditions along semiring homomorphisms

The rank condition and invariant basis number pull back along a unital semiring
homomorphism. The matrix characterizations in Mathlib express both properties
using finite rectangular matrix products; a homomorphism carries such products
and their identities to the target. Neither pullback asserts a strong rank
condition, which concerns injective maps rather than surjective maps or
equivalences.

The target hypotheses exclude the zero semiring: its free modules do not have
invariant basis number. In particular, neither statement needs an additional
nontriviality assumption.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Definition I.1.1 (motivation from maps to division rings).
* Mathlib, `Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber` (matrix
  characterizations and opposite-ring equivalences).
-/

@[expose] public section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [Semiring R] [Semiring S]

/-- The rank condition descends along any unital semiring homomorphism,
without an injectivity or surjectivity assumption. -/
theorem rankCondition (f : R →+* S) [RankCondition S] : RankCondition R := by
  apply rankCondition_iff_matrix.mpr
  intro n m a b h
  apply (rankCondition_iff_matrix.mp (inferInstance : RankCondition S)) n m (a.map f) (b.map f)
  simp only [← Matrix.map_mul, h, Matrix.map_one f (map_zero f) (map_one f)]

/-- Invariant basis number descends along any unital semiring homomorphism.
The target need only have invariant basis number, not the rank condition. -/
theorem invariantBasisNumber (f : R →+* S) [InvariantBasisNumber S] :
    InvariantBasisNumber R := by
  apply invariantBasisNumber_iff_matrix.mpr
  intro n m a b hab hba
  apply (invariantBasisNumber_iff_matrix.mp (inferInstance : InvariantBasisNumber S))
    n m (a.map f) (b.map f)
  · simp only [← Matrix.map_mul, hab, Matrix.map_one f (map_zero f) (map_one f)]
  · simp only [← Matrix.map_mul, hba, Matrix.map_one f (map_zero f) (map_one f)]

end RingHom
