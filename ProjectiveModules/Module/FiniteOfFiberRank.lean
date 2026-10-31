/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.DualSaturation
public import ProjectiveModules.Module.SmallFiberRank
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dimension.Subsingleton
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite generation from rank-one residue fibers

An arbitrary projective module over a commutative ring is finitely generated if its
residue tensor fiber at every maximal ideal has cardinal rank one.

Nonzero fibers force the dual evaluations to generate the unit ideal. A finite
expression for one, together with proportionality of dual evaluations in rank at
most one, gives a finite dual identity. Mathlib's contraction criterion then gives
finite generation. No finite-generation hypothesis or localization of Hom is used.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter I,
  Section 2, Exercise 13. The formulation below uses left modules over a commutative
  ring and only maximal ideals, rather than the source's all-prime hypothesis.
* Mathlib's finite-generation criterion using `dualTensorHom`.
-/

@[expose] public section

universe u v

open scoped BigOperators TensorProduct

namespace Module.Projective

/-- A projective module whose maximal residue tensor fibers have cardinal rank one
is finitely generated. No finite generation is assumed. The maximal-ideal hypothesis
is weaker than the all-prime hypothesis in Weibel, *The K-book*, I.2, Exercise 13.
The rank is a cardinal, not the natural-number-valued `Module.finrank`. -/
theorem finite_of_residue_rank_eq_one
    {R : Type u} [CommRing R]
    {P : Type v} [AddCommMonoid P] [Module R P] [Module.Projective R P]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Module.rank (R ⧸ m) ((R ⧸ m) ⊗[R] P) = 1) :
    Module.Finite R P := by
  classical
  have hfib (m : Ideal R) [hm : m.IsMaximal] :
      Nontrivial ((R ⧸ m) ⊗[R] P) := by
    let : Nontrivial (R ⧸ m) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top hm)
    rcases subsingleton_or_nontrivial ((R ⧸ m) ⊗[R] P) with hs | hn
    · let : Subsingleton ((R ⧸ m) ⊗[R] P) := hs
      have hzero : Module.rank (R ⧸ m) ((R ⧸ m) ⊗[R] P) = 0 := by simp
      exact False.elim (zero_ne_one (hzero.symm.trans (h m)))
    · exact hn
  have hle (m : Ideal R) [m.IsMaximal] :
      Module.rank (R ⧸ m) ((R ⧸ m) ⊗[R] P) ≤ 1 := (h m).le
  let eval : ((P →ₗ[R] R) × P) → R := fun z => z.1 z.2
  have htop : Ideal.span (Set.range eval) = ⊤ := by
    apply ideal_eq_top_of_forall_dual_apply_mem hfib
    intro φ x
    exact Ideal.subset_span ⟨(φ, x), rfl⟩
  have hone : (1 : R) ∈ Submodule.span R (Set.range eval) := by
    rw [Ideal.submodule_span_eq, htop]
    trivial
  obtain ⟨s, hs⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hone
  apply Module.Finite.of_one_mem_range_dualTensorHom
  refine ⟨∑ i ∈ s.support, s i • (i.1 ⊗ₜ[R] i.2), ?_⟩
  ext x
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    dualTensorHom_apply, Module.End.one_apply]
  calc
    ∑ i ∈ s.support, s i • (i.1 x • i.2) =
        ∑ i ∈ s.support, s i • (i.1 i.2 • x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [dual_apply_smul_comm_of_residue_rank_le_one hle i.1 x i.2]
    _ = (∑ i ∈ s.support, s i • eval i) • x := by
      simp only [Finset.sum_smul, smul_smul, smul_eq_mul, eval]
    _ = x := by
      change (s.sum fun i a => a • eval i) • x = x
      rw [hs, one_smul]

end Module.Projective
