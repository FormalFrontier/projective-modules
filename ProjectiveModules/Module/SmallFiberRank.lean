/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.LocalRing
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Functional proportionality from small residue fibers

For a projective module whose maximal residue fibers have cardinal rank at
most one, every functional satisfies `φ x • y = φ y • x`. The module need not
be finitely generated, and zero fibers are allowed.

This is the rank-at-most-one step in the maximal-fiber argument associated
with Weibel, *The K-book*, Chapter I, Section 2, Exercise 13. The proof combines
local freeness of projective modules with Mathlib's base change of bases,
cardinal bound for linear independence, extension of a given functional,
and detection of equality in maximal localizations.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter I, §2.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Module.Projective

private theorem dual_apply_smul_comm_of_subsingleton_basis
    {A : Type*} [CommSemiring A]
    {Q : Type*} [AddCommMonoid Q] [Module A Q]
    {J : Type*} [Subsingleton J] (b : Module.Basis J A Q)
    (φ : Q →ₗ[A] A) (x y : Q) :
    (φ x) • y = (φ y) • x := by
  classical
  rcases isEmpty_or_nonempty J with hJ | hJ
  · let : IsEmpty J := hJ
    have hrange : Set.range b = ∅ := by
      ext q
      constructor
      · rintro ⟨j, _⟩
        exact isEmptyElim j
      · intro hq
        cases hq
    have hx : x = 0 := by
      simpa [hrange] using b.mem_span x
    have hy : y = 0 := by
      simpa [hrange] using b.mem_span y
    simp [hx, hy]
  · let j : J := Classical.choice hJ
    have hrange : Set.range b = {b j} := by
      ext q
      constructor
      · rintro ⟨i, rfl⟩
        exact Set.mem_singleton_iff.mpr (congrArg b (Subsingleton.elim i j))
      · intro hq
        exact ⟨j, (Set.mem_singleton_iff.mp hq).symm⟩
    have hx : x ∈ Submodule.span A ({b j} : Set Q) := by
      rw [← hrange]
      exact b.mem_span x
    have hy : y ∈ Submodule.span A ({b j} : Set Q) := by
      rw [← hrange]
      exact b.mem_span y
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [map_smul, smul_eq_mul, smul_smul]
    congr 1
    ac_rfl

/-- In a projective module with maximal residue fibers of cardinal rank at
most one, every functional has proportional evaluations. No finite generation
is assumed, and the fiber rank is a cardinal rather than `Module.finrank`. -/
theorem dual_apply_smul_comm_of_residue_rank_le_one
    {R : Type u} [CommRing R]
    {P : Type v} [AddCommMonoid P] [Module R P] [Module.Projective R P]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Module.rank (R ⧸ m) ((R ⧸ m) ⊗[R] P) ≤ 1)
    (φ : P →ₗ[R] R) (x y : P) :
    (φ x) • y = (φ y) • x := by
  classical
  let : ∀ (m : Ideal R) [m.IsMaximal], m.IsPrime :=
    fun _ hm => Ideal.IsMaximal.isPrime hm
  apply Module.eq_of_localization_maximal
    (Mₚ := fun (m : Ideal R) [hm' : m.IsMaximal] => Localization.AtPrime m ⊗[R] P)
    (f := fun (m : Ideal R) [hm' : m.IsMaximal] =>
      TensorProduct.mk R (Localization.AtPrime m) P 1)
  intro m hm
  let L := Localization.AtPrime m
  let Q := L ⊗[R] P
  let j : P →ₗ[R] Q := TensorProduct.mk R L P 1
  change j ((φ x) • y) = j ((φ y) • x)
  -- The additive group is promoted on the same carrier and the original
  -- additive monoid and both module structures are retained.
  let am : AddCommMonoid Q := inferInstance
  let rmod : Module R Q := inferInstance
  let lmod : Module L Q := inferInstance
  let qGroup : AddCommGroup Q := Module.addCommMonoidToAddCommGroup L (M := Q)
  have : qGroup.toAddCommMonoid = am := by rfl
  let : AddCommGroup Q := qGroup
  let : Module R Q := rmod
  let : Module L Q := lmod
  let : Module.Projective L L := Module.Projective.of_free
  let : Module.Projective L Q := Module.Projective.tensorProduct
  let : Module.Free L Q := Module.Projective.free_of_isLocalRing
  let J := Module.Free.ChooseBasisIndex L Q
  let b : Module.Basis J L Q := Module.Free.chooseBasis L Q
  let K := R ⧸ m
  let : Nontrivial K :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top hm)
  let q : R →+* K := Ideal.Quotient.mk m
  have hq : ∀ s : m.primeCompl, IsUnit (q s) := by
    intro s
    have hs : q s ≠ 0 := by
      intro hs
      exact s.property (Ideal.Quotient.eq_zero_iff_mem.mp hs)
    obtain ⟨z, hz⟩ := Ideal.Quotient.exists_inv hs
    exact isUnit_iff_exists.mpr ⟨z, hz, by simpa only [mul_comm] using hz⟩
  let f : L →+* K := IsLocalization.lift (S := L) hq
  let : Algebra L K := f.toAlgebra
  have hf (r : R) :
      algebraMap L K (algebraMap R L r) = algebraMap R K r := by
    calc
      algebraMap L K (algebraMap R L r) = f (algebraMap R L r) :=
        congrArg (fun t : L →+* K => t (algebraMap R L r))
          (RingHom.algebraMap_toAlgebra f)
      _ = q r := IsLocalization.lift_eq (S := L) hq r
      _ = algebraMap R K r :=
        (congrArg (fun t : R →+* K => t r) (Ideal.Quotient.algebraMap_eq m)).symm
  let : IsScalarTower R L K :=
    IsScalarTower.of_algebraMap_eq (fun r => (hf r).symm)
  have hj : IsBaseChange L j :=
    IsLocalizedModule.isBaseChange m.primeCompl L j
  let W := K ⊗[L] Q
  let g : Q →ₗ[L] W := TensorProduct.mk L K Q 1
  have hg : IsBaseChange K g :=
    TensorProduct.isBaseChange (R := L) (M := Q) (S := K)
  have hcomp : IsBaseChange K ((g.restrictScalars R).comp j) := hj.comp hg
  let e : K ⊗[R] P ≃ₗ[K] W := hcomp.equiv
  let c : Module.Basis J K (K ⊗[R] P) := (hg.basis b).map e.symm
  have hcard : Cardinal.mk J ≤ 1 := by
    apply Cardinal.lift_le_one_iff.mp
    exact c.linearIndependent.cardinal_lift_le_rank.trans
      (Cardinal.lift_le_one_iff.mpr (h m))
  let : Subsingleton J := Cardinal.le_one_iff_subsingleton.mp hcard
  let ψ : Q →ₗ[L] L := hj.toDual φ
  have hloc : (ψ (j x)) • j y = (ψ (j y)) • j x :=
    dual_apply_smul_comm_of_subsingleton_basis b ψ (j x) (j y)
  calc
    j ((φ x) • y) = (algebraMap R L (φ x)) • j y := by
      rw [j.map_smul]
      exact (IsScalarTower.algebraMap_smul L (φ x) (j y)).symm
    _ = (algebraMap R L (φ y)) • j x := by
      simpa only [ψ, IsBaseChange.toDual_comp_apply] using hloc
    _ = j ((φ y) • x) := by
      rw [j.map_smul]
      exact IsScalarTower.algebraMap_smul L (φ y) (j x)

end Module.Projective
