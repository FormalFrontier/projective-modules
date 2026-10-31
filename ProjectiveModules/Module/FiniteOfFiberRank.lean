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
import ProjectiveModules.ExteriorPower.FiniteSupport
import ProjectiveModules.ExteriorPower.Projective
import ProjectiveModules.ExteriorPower.Rank
import ProjectiveModules.ExteriorPower.Surjectivity
import ProjectiveModules.Localization.TensorProduct
import ProjectiveModules.Module.LocalFiberBasis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.LocalProperties.Exactness

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

namespace Module.Projective

/-- A projective module whose maximal residue tensor fibers all have the same finite
cardinal rank is finitely generated. No finite generation of the original module is
assumed. This includes rank zero and the zero ring. See Weibel, *The K-book*,
Chapter I, §2, for the finite-rank finiteness criterion. -/
theorem finite_of_residue_rank_eq_nat
    {R : Type u} [CommRing R]
    {P : Type v} [AddCommMonoid P] [Module R P] [Module.Projective R P]
    (r : ℕ)
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Module.rank (R ⧸ m) ((R ⧸ m) ⊗[R] P) = (r : Cardinal)) :
    Module.Finite R P := by
  classical
  -- This enrichment keeps the original additive monoid and scalar action.
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
  -- The top exterior power has rank-one residue fibers, even in degree zero.
  let : Module.Finite R (⋀[R]^r P) := finite_of_residue_rank_eq_one fun m hm => by
    let : m.IsMaximal := hm
    let : Field (R ⧸ m) := Ideal.Quotient.field m
    exact exteriorPower.rank_baseChange_eq_one_of_rank_eq_nat r (h m)
  obtain ⟨s, hs⟩ := exteriorPower.exists_finset_surjective (R := R) (M := P) r
  let N : Submodule R P := Submodule.span R (s : Set P)
  let f : N →ₗ[R] P := N.subtype
  let : Module.Finite R N := Module.Finite.span_finset R s
  have hf : Function.Surjective (exteriorPower.map r f) := hs
  -- Over each maximal localization the target is free of rank r. Naturality
  -- transports the surjective base change of the exterior map to its top power.
  have hlocal (m : Ideal R) [m.IsMaximal] :
      Function.Surjective (f.baseChange (Localization.AtPrime m)) := by
    obtain ⟨b⟩ := nonempty_basis_atPrime_of_residue_rank_eq m r (h m)
    apply (exteriorPower.map_surjective_iff_of_basis b
      (f.baseChange (Localization.AtPrime m))).mp
    let eN := exteriorPower.baseChangeEquiv
      (R := R) (S := Localization.AtPrime m) (M := N) r
    let eP := exteriorPower.baseChangeEquiv
      (R := R) (S := Localization.AtPrime m) (M := P) r
    intro y
    obtain ⟨x, hx⟩ := LinearMap.baseChange_surjective (Localization.AtPrime m) hf (eP.symm y)
    refine ⟨eN x, ?_⟩
    have hnat : eP ((exteriorPower.map r f).baseChange (Localization.AtPrime m) x) =
        exteriorPower.map r (f.baseChange (Localization.AtPrime m)) (eN x) :=
      LinearMap.congr_fun
        (exteriorPower.baseChangeEquiv_naturality (S := Localization.AtPrime m) r f) x
    calc
      exteriorPower.map r (f.baseChange (Localization.AtPrime m)) (eN x) =
          eP ((exteriorPower.map r f).baseChange (Localization.AtPrime m) x) := hnat.symm
      _ = y := by rw [hx]; exact eP.apply_symm_apply y
  -- The stock local-global criterion uses canonical localized modules. Compare
  -- these with the tensor localizations, rather than testing arbitrary cokernels
  -- on residue fields or invoking Nakayama before finite generation is known.
  have hsurj : Function.Surjective f := by
    apply surjective_of_localized_maximal f
    intro m hm
    let eN := LocalizedModule.equivTensorProduct m.primeCompl N
    let eP := LocalizedModule.equivTensorProduct m.primeCompl P
    intro y
    obtain ⟨x, hx⟩ := hlocal m (eP y)
    refine ⟨eN.symm x, eP.injective ?_⟩
    calc
      eP (LocalizedModule.map m.primeCompl f (eN.symm x)) =
          f.baseChange (Localization.AtPrime m) (eN (eN.symm x)) :=
        LocalizedModule.equivTensorProduct_map m.primeCompl f (eN.symm x)
      _ = eP y := by rw [eN.apply_symm_apply, hx]
  exact Module.Finite.of_surjective f hsurj

end Module.Projective
