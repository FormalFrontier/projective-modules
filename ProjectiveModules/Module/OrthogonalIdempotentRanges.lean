/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.LinearAlgebra.Pi

/-!
# Products of ranges of orthogonal idempotents

A finite complete family of orthogonal endomorphisms of a semimodule gives a canonical
linear equivalence with the product of their ranges. Its coordinates are the given
endomorphisms, and its inverse sums the ambient values of the coordinates.

`CompleteOrthogonalIdempotents.linearEquivPiRange` uses Mathlib's complete orthogonal
idempotent predicate on the endomorphism semiring. Completeness is an input. No commutativity
of the scalar semiring or additive inverses in the semimodule are required.

`LinearMap.mapRangeOfIntertwines` restricts an intertwining linear map to the corresponding
ranges, without requiring idempotence. The product decomposition is natural for every
intertwiner, not only for linear equivalences. Empty families and zero ranges are allowed.
-/

@[expose] public section

open scoped BigOperators

universe uR uI uM uN uP

variable {R : Type uR} [Semiring R]
variable {I : Type uI}
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {N : Type uN} [AddCommMonoid N] [Module R N]
variable {P : Type uP} [AddCommMonoid P] [Module R P]

namespace LinearMap

/-- An intertwiner induces a linear map between the ranges, with the same ambient value. -/
noncomputable def mapRangeOfIntertwines
    (T : M →ₗ[R] N) {p : Module.End R M} {q : Module.End R N}
    (h : T.comp p = q.comp T) : LinearMap.range p →ₗ[R] LinearMap.range q where
  toFun x := ⟨T (x : M), by
    obtain ⟨m, hm⟩ := x.property
    exact ⟨T m, (congrArg (fun U : M →ₗ[R] N => U m) h).symm.trans (congrArg T hm)⟩⟩
  map_add' x y := Subtype.ext (T.map_add (x : M) (y : M))
  map_smul' r x := Subtype.ext (T.map_smul r (x : M))

/-- The map on ranges has ambient value given by the original linear map. -/
@[simp]
theorem mapRangeOfIntertwines_apply
    (T : M →ₗ[R] N) {p : Module.End R M} {q : Module.End R N}
    (h : T.comp p = q.comp T) (x : LinearMap.range p) :
    (T.mapRangeOfIntertwines h x : N) = T (x : M) := rfl

/-- The identity intertwiner induces the identity on the range. -/
@[simp]
theorem mapRangeOfIntertwines_id (p : Module.End R M) :
    (LinearMap.id : M →ₗ[R] M).mapRangeOfIntertwines (p := p) (q := p) (by simp) =
      LinearMap.id := by
  ext x
  rfl

/-- Restriction of intertwiners to ranges preserves composition. -/
theorem mapRangeOfIntertwines_comp
    (T : M →ₗ[R] N) (U : N →ₗ[R] P)
    {p : Module.End R M} {q : Module.End R N} {r : Module.End R P}
    (hT : T.comp p = q.comp T) (hU : U.comp q = r.comp U) :
    (U.comp T).mapRangeOfIntertwines
        (by rw [LinearMap.comp_assoc, hT, ← LinearMap.comp_assoc, hU,
          LinearMap.comp_assoc]) =
      (U.mapRangeOfIntertwines hU).comp (T.mapRangeOfIntertwines hT) := by
  ext x
  rfl

end LinearMap

namespace OrthogonalIdempotents

variable {e : I → Module.End R M}

/-- On the range of one projection, every other projection vanishes. -/
theorem apply_coe_range [DecidableEq I] (he : OrthogonalIdempotents e) (i j : I)
    (x : LinearMap.range (e j)) :
    e i (x : M) = if i = j then (x : M) else 0 := by
  obtain ⟨m, hm⟩ := x.property
  rw [← hm]
  have h := congrArg (fun p : Module.End R M => p m)
    (he.mul_eq i j)
  by_cases hij : i = j
  · subst j
    simpa using h
  · simpa [hij] using h

variable [Fintype I]

/-- A projection recovers its coordinate from the sum of range elements. -/
theorem apply_sum_coe (he : OrthogonalIdempotents e)
    (x : ∀ i : I, LinearMap.range (e i)) (i : I) :
    e i (∑ j, (x j : M)) = (x i : M) := by
  classical
  simp [map_sum, he.apply_coe_range]

end OrthogonalIdempotents

namespace CompleteOrthogonalIdempotents

variable [Fintype I]
variable {e : I → Module.End R M}

/-- Completeness reconstructs a vector as the sum of its projections. -/
theorem sum_apply (he : CompleteOrthogonalIdempotents e) (m : M) :
    ∑ i, e i m = m := by
  simpa using congrArg (fun p : Module.End R M => p m) he.complete

/-- A finite complete orthogonal family identifies a semimodule with the product of its
ranges. The coordinates are the projections and the inverse is the sum of ambient values. -/
noncomputable def linearEquivPiRange (he : CompleteOrthogonalIdempotents e) :
    M ≃ₗ[R] (∀ i : I, LinearMap.range (e i)) where
  toFun m i := ⟨e i m, ⟨m, rfl⟩⟩
  invFun x := ∑ i, (x i : M)
  map_add' m n := by
    funext i
    exact Subtype.ext ((e i).map_add m n)
  map_smul' r m := by
    funext i
    exact Subtype.ext ((e i).map_smul r m)
  left_inv := he.sum_apply
  right_inv x := by
    funext i
    exact Subtype.ext (he.toOrthogonalIdempotents.apply_sum_coe x i)

/-- The ambient value of a coordinate of the decomposition is the given projection. -/
@[simp]
theorem linearEquivPiRange_apply_coe
    (he : CompleteOrthogonalIdempotents e) (m : M) (i : I) :
    ((he.linearEquivPiRange m) i : M) = e i m := rfl

/-- The inverse decomposition sums the ambient values of the coordinates. -/
@[simp]
theorem linearEquivPiRange_symm_apply
    (he : CompleteOrthogonalIdempotents e) (x : ∀ i : I, LinearMap.range (e i)) :
    he.linearEquivPiRange.symm x = ∑ i, (x i : M) := rfl

/-- Vectors are equal exactly when all their projections agree. -/
theorem eq_iff_forall_apply_eq
    (he : CompleteOrthogonalIdempotents e) (m n : M) :
    m = n ↔ ∀ i : I, e i m = e i n := by
  constructor
  · rintro rfl i
    rfl
  · intro h
    apply he.linearEquivPiRange.injective
    funext i
    apply Subtype.ext
    simpa only [linearEquivPiRange_apply_coe] using h i

/-- The product coordinates commute with every intertwining linear map. -/
theorem linearEquivPiRange_natural
    {f : I → Module.End R N}
    (he : CompleteOrthogonalIdempotents e) (hf : CompleteOrthogonalIdempotents f)
    (T : M →ₗ[R] N) (hT : ∀ i : I, T.comp (e i) = (f i).comp T) (m : M) :
    hf.linearEquivPiRange (T m) =
      fun i => T.mapRangeOfIntertwines (hT i) ((he.linearEquivPiRange m) i) := by
  funext i
  apply Subtype.ext
  simp only [linearEquivPiRange_apply_coe, LinearMap.mapRangeOfIntertwines_apply]
  exact (congrArg (fun U : M →ₗ[R] N => U m) (hT i)).symm

/-- Summation of range coordinates commutes with every intertwining linear map. -/
theorem linearEquivPiRange_symm_natural
    {f : I → Module.End R N}
    (he : CompleteOrthogonalIdempotents e) (hf : CompleteOrthogonalIdempotents f)
    (T : M →ₗ[R] N) (hT : ∀ i : I, T.comp (e i) = (f i).comp T)
    (x : ∀ i : I, LinearMap.range (e i)) :
    T (he.linearEquivPiRange.symm x) =
      hf.linearEquivPiRange.symm (fun i => T.mapRangeOfIntertwines (hT i) (x i)) := by
  simp only [linearEquivPiRange_symm_apply, map_sum,
    LinearMap.mapRangeOfIntertwines_apply]

end CompleteOrthogonalIdempotents
