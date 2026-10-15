/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Finiteness.Basic
public import ProjectiveModules.Module.ProjectivePi
public import ProjectiveModules.Module.Trace.Basic

import ProjectiveModules.Module.Trace.Cyclicity

/-!
# Finite-projective trace on finite dependent products

For an arbitrary endomorphism of a finite dependent product of finite projective
modules, coordinate projections and single-coordinate inclusions determine its
diagonal endomorphisms. The finite-projective trace is the sum of their traces.
The formula uses the canonical pointwise module structures and does not require
a basis or additive inverses. For maps in opposite directions between two finite
products, the trace of their composite is the sum of the traces of the composites
of their rectangular coordinate blocks. Only the source factors need be finite
projective.

The index type is assumed finite without choosing an enumeration in the
statement. The sum is written with `finsum`, and the existing single-coordinate
inclusion is instantiated with classical decidable equality. The proof uses the
canonical finite-product linear-map equivalence and cyclicity of the
finite-projective trace.

## References

The coordinate-map API is from the formalization by Johannes Hölzl, Mario
Carneiro, Kevin Buzzard, Yury Kudryashov and Eric Wieser in
`Mathlib.LinearAlgebra.Pi`. Finite sums without enumeration data are from
Kexing Ying, Kevin Buzzard and Yury Kudryashov's formalization in
`Mathlib.Algebra.BigOperators.Finprod`. The contraction and dual tensor–Hom
formalization underlying the trace is by Oliver Nash and Antoine Labelle in
`Mathlib.LinearAlgebra.Contraction`.
-/

@[expose] public section

universe uR uι uκ uM uN

namespace LinearMap

/-- The finite-projective trace of an arbitrary endomorphism of a finite dependent
product is the sum of the traces of its diagonal coordinate composites. -/
theorem traceOfFiniteProjective_pi
    (R : Type uR) [CommSemiring R]
    {ι : Type uι} [Finite ι]
    (M : ι → Type uM)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Finite R (M i)] [∀ i, Module.Projective R (M i)]
    (f : (∀ i, M i) →ₗ[R] (∀ i, M i)) :
    traceOfFiniteProjective R (∀ i, M i) f =
      ∑ᶠ i : ι, traceOfFiniteProjective R (M i)
        ((LinearMap.proj (R := R) (φ := M) i).comp
          (f.comp (@LinearMap.single R ι _ M _ _ (Classical.decEq ι) i))) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hsum : (∑ i : ι, (f.comp (single R M i)).comp (proj i)) = f := by
    simpa only [lsum_apply, lsum_symm_apply] using
      (lsum R M R).apply_symm_apply f
  rw [finsum_eq_sum_of_fintype]
  calc
    traceOfFiniteProjective R (∀ i, M i) f =
        traceOfFiniteProjective R (∀ i, M i)
          (∑ i : ι, (f.comp (single R M i)).comp (proj i)) :=
      congrArg (traceOfFiniteProjective R (∀ i, M i)) hsum.symm
    _ = ∑ i : ι, traceOfFiniteProjective R (∀ i, M i)
        ((f.comp (single R M i)).comp (proj i)) := by rw [map_sum]
    _ = ∑ i : ι, traceOfFiniteProjective R (M i)
        ((proj i).comp (f.comp (single R M i))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact traceOfFiniteProjective_comp_comm R (∀ i, M i) (M i)
        (proj i) (f.comp (single R M i))

/-- The finite-projective trace of a composite through a finite dependent product
is the sum of the traces of the composites of its rectangular coordinate blocks.
The intermediate factors need not be finitely generated or projective. -/
theorem traceOfFiniteProjective_pi_comp
    (R : Type uR) [CommSemiring R]
    {ι : Type uι} [Finite ι] {κ : Type uκ} [Finite κ]
    (M : ι → Type uM) (N : κ → Type uN)
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ j, AddCommMonoid (N j)] [∀ j, Module R (N j)]
    [∀ i, Module.Finite R (M i)] [∀ i, Module.Projective R (M i)]
    (f : (∀ i, M i) →ₗ[R] (∀ j, N j))
    (g : (∀ j, N j) →ₗ[R] (∀ i, M i)) :
    traceOfFiniteProjective R (∀ i, M i) (g.comp f) =
      ∑ᶠ i : ι, ∑ᶠ j : κ, traceOfFiniteProjective R (M i)
        (((LinearMap.proj (R := R) (φ := M) i).comp
            (g.comp (@LinearMap.single R κ _ N _ _ (Classical.decEq κ) j))).comp
          ((LinearMap.proj (R := R) (φ := N) j).comp
            (f.comp (@LinearMap.single R ι _ M _ _ (Classical.decEq ι) i)))) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  have hsum : (∑ j : κ, (g.comp (single R N j)).comp (proj j)) = g := by
    simpa only [lsum_apply, lsum_symm_apply] using
      (lsum R N R).apply_symm_apply g
  rw [traceOfFiniteProjective_pi R M]
  apply finsum_congr
  intro i
  rw [finsum_eq_sum_of_fintype, ← map_sum]
  apply congrArg (traceOfFiniteProjective R (M i))
  calc
    (proj i).comp ((g.comp f).comp (single R M i)) =
        (proj i).comp
          ((∑ j : κ, (g.comp (single R N j)).comp (proj j)).comp
            (f.comp (single R M i))) := by
      rw [hsum]
      simp only [comp_assoc]
    _ = ∑ j : κ, ((proj i).comp (g.comp (single R N j))).comp
        ((proj j).comp (f.comp (single R M i))) := by
      ext x
      simp only [comp_apply, sum_apply, map_sum]

end LinearMap
