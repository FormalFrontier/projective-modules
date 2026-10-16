/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.RankFiberDecomposition
import ProjectiveModules.Module.ComponentwiseFree
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Commuting refinements of complete orthogonal idempotents

The product family retains every pair of indices, including pairs whose
product is zero. Cross-commutation is the only additional multiplicative
hypothesis over a semiring. The rank-fiber application uses the canonical
quotient algebra on a component of a product module.

The coordinate example uses the two coordinate idempotents of `Fin 2 → ℤ`;
its product family has two zero off-diagonal entries. The empty family over
the zero ring gives the boundary example.

## References

The family predicates and mapping operation are from Mathlib's
`Mathlib.RingTheory.Idempotents` (Andrew Yang). The finite-projective
application uses `ProjectiveModules.Module.RankFiberDecomposition`.
-/

universe u v w

/-- Cartesian refinement of two complete orthogonal families whose entries
commute across the two families. -/
private def IdempotentRefinement : Prop :=
  ∀ (S : Type u) (I : Type v) (J : Type w)
    [Semiring S] [Fintype I] [Fintype J]
    (e : I → S) (f : J → S),
    CompleteOrthogonalIdempotents e →
    CompleteOrthogonalIdempotents f →
    (∀ i j, Commute (e i) (f j)) →
    CompleteOrthogonalIdempotents (fun ij : I × J ↦ e ij.1 * f ij.2)

/-- The common rank-fiber refinement, over the component's quotient ring. -/
private theorem rankFiberProductIdempotents_complete
    (R : Type u) (P : Type v) (Q : Type w) [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Projective R Q]
    (d : Module.rankFiberIndex R (P × Q)) :
    CompleteOrthogonalIdempotents
      (fun ij : Module.rankFiberIndex R P × Module.rankFiberIndex R Q ↦
        algebraMap R (Module.rankFiberRing R (P × Q) d)
          (Module.rankFiberIdempotent R P ij.1 *
            Module.rankFiberIdempotent R Q ij.2)) := by
  let φ : R →+* Module.rankFiberRing R (P × Q) d := algebraMap R _
  have he := CompleteOrthogonalIdempotents.map φ
    (Module.rankFiberIdempotents_complete R P)
  have hf := CompleteOrthogonalIdempotents.map φ
    (Module.rankFiberIdempotents_complete R Q)
  have h := CompleteOrthogonalIdempotents.prod_mul he hf
    (fun _ _ ↦ Commute.all _ _)
  simpa only [Function.comp_apply, ← map_mul] using h

private def coordinateIdempotents : Fin 2 → (Fin 2 → ℤ) :=
  fun i ↦ Pi.single i 1

private theorem coordinateIdempotents_complete :
    CompleteOrthogonalIdempotents coordinateIdempotents :=
  CompleteOrthogonalIdempotents.single (fun _ : Fin 2 ↦ ℤ)

private theorem coordinateIdempotents_commute (i j : Fin 2) :
    Commute (coordinateIdempotents i) (coordinateIdempotents j) :=
  Commute.all _ _

private theorem coordinatePartition_nontrivial :
    coordinateIdempotents 0 ≠ 0 ∧ coordinateIdempotents 1 ≠ 0 ∧
      coordinateIdempotents 0 * coordinateIdempotents 1 = 0 := by
  decide

private theorem coordinateRefinement_complete :
    CompleteOrthogonalIdempotents
      (fun ij : Fin 2 × Fin 2 ↦
        coordinateIdempotents ij.1 * coordinateIdempotents ij.2) :=
  CompleteOrthogonalIdempotents.prod_mul coordinateIdempotents_complete
    coordinateIdempotents_complete coordinateIdempotents_commute

private def emptyIdempotents : Fin 0 → ZMod 1 := fun i ↦ i.elim0

private theorem emptyIdempotents_complete :
    CompleteOrthogonalIdempotents emptyIdempotents :=
  CompleteOrthogonalIdempotents.of_subsingleton

private theorem emptyRefinement_complete :
    CompleteOrthogonalIdempotents
      (fun ij : Fin 0 × Fin 0 ↦ emptyIdempotents ij.1 * emptyIdempotents ij.2) :=
  CompleteOrthogonalIdempotents.of_subsingleton
