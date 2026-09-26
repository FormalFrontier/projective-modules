/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import GeneralLinearGroups.LocalQuotient
public import ProjectiveModules.Module.ProjectiveComplement
public import ProjectiveModules.Module.RightEndomorphismMatrix
public import ProjectiveModules.Module.RightExtensionFiniteResidue
public import ProjectiveModules.Module.RightExtensionFree
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Finite projective right modules over local rings

Let `I` be a proper two-sided ideal of a possibly noncommutative ring `R`, and
suppose every element outside `I` is a unit.  This file proves that every
finitely generated projective right `R`-module is finite free.  More precisely,
it constructs a finite standard-coordinate equivalence whose basis reduces to
the canonical finite basis of the quotient module over the division ring
`R ⧸ I`.

The proof chooses compatible residue bases for a projective module and a finite
projective complement.  Lifting the combined basis gives an endomorphism of a
finite free right module.  Its quotient is bijective, and quasi-regular matrix
reflection makes the original endomorphism bijective.
-/

@[expose] public section

universe uR uP

namespace Module.Projective

variable {R : Type uR} [Ring R]
variable {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P]
variable [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]

/-- A finite projective right module over a ring with a proper two-sided ideal
whose complement consists of units has a finite standard-coordinate
equivalence.  The standard basis reduces to the canonical basis of the
quotient module, so the rank is exactly its residue-module finrank. -/
theorem exists_rightFreeLinearEquiv_of_isUnit_compl
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤)
    (hunit : ∀ x ∉ I, IsUnit x) :
    let _ : I.asIdeal.IsMaximal :=
      I.isMaximal_asIdeal_of_isUnit_compl hI hunit
    let _ : DivisionRing (R ⧸ I.asIdeal) :=
      I.quotientDivisionRing hI hunit
    let _ : Module.Free (R ⧸ I.asIdeal)ᵐᵒᵖ
        (ModuleCat.RightExtension.IdealQuotient (M := P) I.asIdeal) :=
      Module.Free.of_divisionRing (R ⧸ I.asIdeal)ᵐᵒᵖ
        (ModuleCat.RightExtension.IdealQuotient (M := P) I.asIdeal)
    ∃ e :
        (Fin (Module.finrank (R ⧸ I.asIdeal)ᵐᵒᵖ
          (ModuleCat.RightExtension.IdealQuotient (M := P) I.asIdeal)) → R) ≃ₗ[Rᵐᵒᵖ] P,
      ∀ i,
        Submodule.Quotient.mk (p :=
          ModuleCat.RightExtension.idealSubmodule (M := P) I.asIdeal)
            (e (Pi.single i 1)) =
          Module.finBasis (R ⧸ I.asIdeal)ᵐᵒᵖ
            (ModuleCat.RightExtension.IdealQuotient (M := P) I.asIdeal) i := by
  classical
  dsimp
  let _ : I.asIdeal.IsMaximal :=
    I.isMaximal_asIdeal_of_isUnit_compl hI hunit
  let _ : DivisionRing (R ⧸ I.asIdeal) :=
    I.quotientDivisionRing hI hunit
  have hquasi : I.IsQuasiregular :=
    (I.isQuasiregular_iff_forall_isUnit_one_add).mpr (by
      intro x hx
      apply hunit (1 + x)
      intro hone
      have hmem := I.add_mem hone (I.neg_mem hx)
      exact hI (I.eq_top (by simpa using hmem)))
  obtain ⟨n, Q, hQgroup, hQmodule, hQfinite, ⟨e₀⟩⟩ :=
    exists_finite_complement_linearEquiv (R := Rᵐᵒᵖ) (P := P)
  let _ : AddCommGroup Q := hQgroup
  let _ : Module Rᵐᵒᵖ Q := hQmodule
  let _ : Module.Finite Rᵐᵒᵖ Q := hQfinite
  let e : (P × Q) ≃ₗ[Rᵐᵒᵖ] (Fin n → R) :=
    e₀.trans (Module.rightFreeCoordEquiv R (Fin n))
  let _ := ModuleCat.RightExtension.idealQuotientFree_of_isMaximal
    (M := P) I.asIdeal
  let _ := ModuleCat.RightExtension.idealQuotientFree_of_isMaximal
    (M := Q) I.asIdeal
  let p := Module.finrank (R ⧸ I.asIdeal)ᵐᵒᵖ
    (ModuleCat.RightExtension.IdealQuotient (M := P) I.asIdeal)
  let q := Module.finrank (R ⧸ I.asIdeal)ᵐᵒᵖ
    (ModuleCat.RightExtension.IdealQuotient (M := Q) I.asIdeal)
  let bP := Module.finBasis (R ⧸ I.asIdeal)ᵐᵒᵖ
    (ModuleCat.RightExtension.IdealQuotient (M := P) I.asIdeal)
  let bQ := Module.finBasis (R ⧸ I.asIdeal)ᵐᵒᵖ
    (ModuleCat.RightExtension.IdealQuotient (M := Q) I.asIdeal)
  let liftP : Fin p → P := fun i ↦ Classical.choose
    ((Submodule.Quotient.mk_surjective
      (ModuleCat.RightExtension.idealSubmodule (M := P) I.asIdeal)) (bP i))
  let liftQ : Fin q → Q := fun i ↦ Classical.choose
    ((Submodule.Quotient.mk_surjective
      (ModuleCat.RightExtension.idealSubmodule (M := Q) I.asIdeal)) (bQ i))
  have hliftP (i : Fin p) :
      Submodule.Quotient.mk (p :=
        ModuleCat.RightExtension.idealSubmodule (M := P) I.asIdeal) (liftP i) =
        bP i :=
    Classical.choose_spec
      ((Submodule.Quotient.mk_surjective
        (ModuleCat.RightExtension.idealSubmodule (M := P) I.asIdeal)) (bP i))
  have hliftQ (i : Fin q) :
      Submodule.Quotient.mk (p :=
        ModuleCat.RightExtension.idealSubmodule (M := Q) I.asIdeal) (liftQ i) =
        bQ i :=
    Classical.choose_spec
      ((Submodule.Quotient.mk_surjective
        (ModuleCat.RightExtension.idealSubmodule (M := Q) I.asIdeal)) (bQ i))
  let eBar :
      (ModuleCat.RightExtension.IdealQuotient (M := P) I.asIdeal ×
          ModuleCat.RightExtension.IdealQuotient (M := Q) I.asIdeal) ≃ₗ[
        (R ⧸ I.asIdeal)ᵐᵒᵖ] (Fin n → R ⧸ I.asIdeal) :=
    (ModuleCat.RightExtension.idealQuotientProdLinearEquiv
        (M := P) (N := Q) I.asIdeal).symm.trans <|
      (ModuleCat.RightExtension.idealQuotientMapLinearEquiv I.asIdeal e).trans <|
        ModuleCat.RightExtension.idealQuotientRightFreeLinearEquiv
          (Fin n) I.asIdeal
  have hdim : p + q = n := by
    have h := eBar.finrank_eq
    rw [Module.finrank_prod,
      ← (Module.rightFreeCoordEquiv (R ⧸ I.asIdeal) (Fin n)).finrank_eq,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    simpa [p, q] using h
  let idx : Fin p ⊕ Fin q ≃ Fin n :=
    finSumFinEquiv.trans (finCongr hdim)
  let sumLift : Fin p ⊕ Fin q → P × Q :=
    Sum.elim (fun i ↦ (liftP i, 0)) (fun j ↦ (0, liftQ j))
  let liftN : Fin n → P × Q := fun k ↦ sumLift (idx.symm k)
  let blockMap : (Fin n → R) →ₗ[Rᵐᵒᵖ] P × Q :=
    (Fintype.linearCombination Rᵐᵒᵖ liftN).comp
      (Module.rightFreeCoordEquiv R (Fin n)).symm.toLinearMap
  have hblockMap_single (k : Fin n) :
      blockMap (Pi.single k 1) = liftN k := by
    have hcoord :
        (Module.rightFreeCoordEquiv R (Fin n)).symm (Pi.single k 1) =
          Pi.single k (1 : Rᵐᵒᵖ) := by
      ext i
      by_cases h : i = k <;> simp [h]
    change (Fintype.linearCombination Rᵐᵒᵖ liftN)
      ((Module.rightFreeCoordEquiv R (Fin n)).symm (Pi.single k 1)) = liftN k
    rw [hcoord, Fintype.linearCombination_apply_single, one_smul]
  let g : Module.End Rᵐᵒᵖ (Fin n → R) :=
    e.toLinearMap.comp blockMap
  let bPQ := bP.prod bQ
  let bN := bPQ.reindex idx
  have hbN_mk (k : Fin n) :
      bN k =
        (Submodule.Quotient.mk (p :=
            ModuleCat.RightExtension.idealSubmodule (M := P) I.asIdeal)
          (liftN k).1,
        Submodule.Quotient.mk (p :=
            ModuleCat.RightExtension.idealSubmodule (M := Q) I.asIdeal)
          (liftN k).2) := by
    change (bPQ.reindex idx) k = _
    rw [Module.Basis.reindex_apply]
    generalize hs : idx.symm k = s
    cases s with
    | inl i =>
        simp [bPQ, liftN, sumLift, hs, hliftP]
    | inr j =>
        simp [bPQ, liftN, sumLift, hs, hliftQ]
  let bOut := bN.map eBar
  let barE : (Fin n → R ⧸ I.asIdeal) ≃ₗ[(R ⧸ I.asIdeal)ᵐᵒᵖ]
      (Fin n → R ⧸ I.asIdeal) :=
    (Module.rightFreeCoordEquiv (R ⧸ I.asIdeal) (Fin n)).symm.trans
      bOut.equivFun.symm
  have hbarE_single (k : Fin n) :
      barE (Pi.single k 1) = eBar (bN k) := by
    have hcoord :
        (Module.rightFreeCoordEquiv (R ⧸ I.asIdeal) (Fin n)).symm
            (Pi.single k 1) =
          Pi.single k (1 : (R ⧸ I.asIdeal)ᵐᵒᵖ) := by
      ext i
      by_cases h : i = k <;> simp [h]
    change bOut.equivFun.symm
      ((Module.rightFreeCoordEquiv (R ⧸ I.asIdeal) (Fin n)).symm
        (Pi.single k 1)) = eBar (bN k)
    rw [hcoord, Basis.equivFun_symm_single]
    rfl
  have hg_single (k : Fin n) :
      g (Pi.single k 1) = e (liftN k) := by
    change e (blockMap (Pi.single k 1)) = e (liftN k)
    rw [hblockMap_single]
  have htest_single (k : Fin n) :
      Module.rightEndomorphismScalarExtension R (Fin n)
          (Ideal.Quotient.mk I.asIdeal) g (Pi.single k 1) =
        barE (Pi.single k 1) := by
    rw [Module.rightEndomorphismScalarExtension_single, hbarE_single, hbN_mk,
      hg_single]
    change (fun i ↦ Ideal.Quotient.mk I.asIdeal (e (liftN k) i)) =
      (ModuleCat.RightExtension.idealQuotientRightFreeLinearEquiv
        (Fin n) I.asIdeal)
        ((ModuleCat.RightExtension.idealQuotientMapLinearEquiv I.asIdeal e)
          ((ModuleCat.RightExtension.idealQuotientProdLinearEquiv
            (M := P) (N := Q) I.asIdeal).symm
            (Submodule.Quotient.mk (liftN k).1,
              Submodule.Quotient.mk (liftN k).2)))
    have hprod :
        (ModuleCat.RightExtension.idealQuotientProdLinearEquiv
          (M := P) (N := Q) I.asIdeal).symm
            (Submodule.Quotient.mk (liftN k).1,
              Submodule.Quotient.mk (liftN k).2) =
          Submodule.Quotient.mk (p :=
            ModuleCat.RightExtension.idealSubmodule (M := P × Q) I.asIdeal)
            (liftN k) := by
      apply (ModuleCat.RightExtension.idealQuotientProdLinearEquiv
        (M := P) (N := Q) I.asIdeal).injective
      rw [LinearEquiv.apply_symm_apply]
      exact (ModuleCat.RightExtension.idealQuotientProdLinearEquiv_mk
        (M := P) (N := Q) I.asIdeal (liftN k).1 (liftN k).2).symm
    rw [hprod,
      ModuleCat.RightExtension.idealQuotientMapLinearEquiv_mk,
      ModuleCat.RightExtension.idealQuotientRightFreeLinearEquiv_mk]
  have hmap :
      Module.rightEndomorphismScalarExtension R (Fin n)
          (Ideal.Quotient.mk I.asIdeal) g =
        barE.toLinearMap := by
    apply LinearMap.pi_ext
    intro k x
    have hx : Pi.single k x =
        MulOpposite.op x • (Pi.single k 1 : Fin n → R ⧸ I.asIdeal) := by
      ext i
      by_cases h : i = k <;> simp [h]
    rw [hx, map_smul, map_smul]
    simpa using congrArg (fun y ↦ MulOpposite.op x • y) (htest_single k)
  have hgBar : Function.Bijective
      (Module.rightEndomorphismScalarExtension R (Fin n)
        (Ideal.Quotient.mk I.asIdeal) g) := by
    rw [hmap]
    exact barE.bijective
  have hg : Function.Bijective g :=
    Module.rightEndomorphism_bijective_of_quotientScalarExtension_bijective
      R (Fin n) I hquasi g hgBar
  let fP : (Fin p → R) →ₗ[Rᵐᵒᵖ] P :=
    (Fintype.linearCombination Rᵐᵒᵖ liftP).comp
      (Module.rightFreeCoordEquiv R (Fin p)).symm.toLinearMap
  let fQ : (Fin q → R) →ₗ[Rᵐᵒᵖ] Q :=
    (Fintype.linearCombination Rᵐᵒᵖ liftQ).comp
      (Module.rightFreeCoordEquiv R (Fin q)).symm.toLinearMap
  let pairMap : ((Fin p → R) × (Fin q → R)) →ₗ[Rᵐᵒᵖ] P × Q :=
    (fP.comp (LinearMap.fst Rᵐᵒᵖ (Fin p → R) (Fin q → R))).prod
      (fQ.comp (LinearMap.snd Rᵐᵒᵖ (Fin p → R) (Fin q → R)))
  let sumSplit : (Fin p ⊕ Fin q → R) ≃ₗ[Rᵐᵒᵖ]
      (Fin p → R) × (Fin q → R) :=
    LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) Rᵐᵒᵖ R
  let sumMap : (Fin p ⊕ Fin q → R) →ₗ[Rᵐᵒᵖ] P × Q :=
    (Fintype.linearCombination Rᵐᵒᵖ sumLift).comp
      (Module.rightFreeCoordEquiv R (Fin p ⊕ Fin q)).symm.toLinearMap
  let coordReindex : (Fin p ⊕ Fin q → R) ≃ₗ[Rᵐᵒᵖ] (Fin n → R) :=
    LinearEquiv.piCongrLeft Rᵐᵒᵖ (fun _ : Fin n ↦ R) idx
  have hsumMap_single (s : Fin p ⊕ Fin q) :
      sumMap (Pi.single s 1) = sumLift s := by
    have hcoord :
        (Module.rightFreeCoordEquiv R (Fin p ⊕ Fin q)).symm
            (Pi.single s 1) =
          Pi.single s (1 : Rᵐᵒᵖ) := by
      ext t
      by_cases h : t = s <;> simp [h]
    change (Fintype.linearCombination Rᵐᵒᵖ sumLift)
      ((Module.rightFreeCoordEquiv R (Fin p ⊕ Fin q)).symm
        (Pi.single s 1)) = sumLift s
    rw [hcoord, Fintype.linearCombination_apply_single, one_smul]
  have hcoordReindex_single (s : Fin p ⊕ Fin q) :
      coordReindex (Pi.single s 1) = Pi.single (idx s) 1 := by
    ext k
    dsimp [coordReindex, LinearEquiv.piCongrLeft,
      LinearEquiv.piCongrLeft']
    rw [Equiv.piCongrLeft'_symm]
    by_cases h : k = idx s
    · subst k
      simp
    · have hs : idx.symm k ≠ s := by
        intro hs
        apply h
        simpa using congrArg idx hs
      simp [h, hs]
  have hblock_sum : blockMap.comp coordReindex.toLinearMap = sumMap := by
    apply LinearMap.pi_ext
    intro s x
    have hx : Pi.single s x =
        MulOpposite.op x • (Pi.single s 1 : Fin p ⊕ Fin q → R) := by
      ext t
      by_cases h : t = s <;> simp [h]
    rw [hx, map_smul, map_smul]
    congr 1
    change blockMap (coordReindex (Pi.single s 1)) =
      sumMap (Pi.single s 1)
    rw [hcoordReindex_single, hblockMap_single, hsumMap_single]
    simp [liftN]
  have hblockBij : Function.Bijective blockMap := by
    constructor
    · intro x y hxy
      apply hg.injective
      change e (blockMap x) = e (blockMap y)
      rw [hxy]
    · intro z
      obtain ⟨x, hx⟩ := hg.surjective (e z)
      refine ⟨x, e.injective ?_⟩
      change e (blockMap x) = e z
      exact hx
  have hsumBij : Function.Bijective sumMap := by
    rw [← hblock_sum]
    exact hblockBij.comp coordReindex.bijective
  have hfP_single (i : Fin p) : fP (Pi.single i 1) = liftP i := by
    have hcoord :
        (Module.rightFreeCoordEquiv R (Fin p)).symm (Pi.single i 1) =
          Pi.single i (1 : Rᵐᵒᵖ) := by
      ext j
      by_cases h : j = i <;> simp [h]
    change (Fintype.linearCombination Rᵐᵒᵖ liftP)
      ((Module.rightFreeCoordEquiv R (Fin p)).symm (Pi.single i 1)) = liftP i
    rw [hcoord, Fintype.linearCombination_apply_single, one_smul]
  have hfQ_single (j : Fin q) : fQ (Pi.single j 1) = liftQ j := by
    have hcoord :
        (Module.rightFreeCoordEquiv R (Fin q)).symm (Pi.single j 1) =
          Pi.single j (1 : Rᵐᵒᵖ) := by
      ext k
      by_cases h : k = j <;> simp [h]
    change (Fintype.linearCombination Rᵐᵒᵖ liftQ)
      ((Module.rightFreeCoordEquiv R (Fin q)).symm (Pi.single j 1)) = liftQ j
    rw [hcoord, Fintype.linearCombination_apply_single, one_smul]
  have hpairMap_single (s : Fin p ⊕ Fin q) :
      pairMap (sumSplit (Pi.single s 1)) = sumLift s := by
    cases s with
    | inl i =>
        have hsplit : sumSplit (Pi.single (Sum.inl i) 1) =
            (Pi.single i 1, 0) := by
          ext j <;> simp [sumSplit, Pi.single_apply, Sum.inl.injEq]
        rw [hsplit]
        simp [pairMap, sumLift, hfP_single]
    | inr j =>
        have hsplit : sumSplit (Pi.single (Sum.inr j) 1) =
            (0, Pi.single j 1) := by
          ext i <;> simp [sumSplit, Pi.single_apply, Sum.inr.injEq]
        rw [hsplit]
        simp [pairMap, sumLift, hfQ_single]
  have hpair_sum : pairMap.comp sumSplit.toLinearMap = sumMap := by
    apply LinearMap.pi_ext
    intro s x
    have hx : Pi.single s x =
        MulOpposite.op x • (Pi.single s 1 : Fin p ⊕ Fin q → R) := by
      ext t
      by_cases h : t = s <;> simp [h]
    rw [hx, map_smul, map_smul]
    congr 1
    change pairMap (sumSplit (Pi.single s 1)) = sumMap (Pi.single s 1)
    exact (hpairMap_single s).trans (hsumMap_single s).symm
  have hpairBij : Function.Bijective pairMap := by
    constructor
    · intro x y hxy
      apply sumSplit.symm.injective
      apply hsumBij.injective
      have hx := DFunLike.congr_fun hpair_sum (sumSplit.symm x)
      have hy := DFunLike.congr_fun hpair_sum (sumSplit.symm y)
      simpa only [LinearMap.comp_apply, LinearEquiv.apply_symm_apply] using
        hx.symm.trans (hxy.trans hy)
    · intro z
      obtain ⟨w, hw⟩ := hsumBij.surjective z
      refine ⟨sumSplit w, ?_⟩
      have h : pairMap (sumSplit w) = sumMap w := by
        change (pairMap.comp sumSplit.toLinearMap) w = sumMap w
        exact DFunLike.congr_fun hpair_sum w
      exact h.trans hw
  have hfP : Function.Bijective fP := by
    constructor
    · intro x y hxy
      have hpair : pairMap (x, 0) = pairMap (y, 0) := by
        simp [pairMap, hxy]
      exact congrArg Prod.fst (hpairBij.injective hpair)
    · intro z
      obtain ⟨xy, hxy⟩ := hpairBij.surjective (z, 0)
      refine ⟨xy.1, ?_⟩
      have h := congrArg Prod.fst hxy
      simpa [pairMap] using h
  let pEquiv : (Fin p → R) ≃ₗ[Rᵐᵒᵖ] P :=
    LinearEquiv.ofBijective fP hfP
  have hpEquiv_single (i : Fin p) :
      pEquiv (Pi.single i 1) = liftP i := by
    exact hfP_single i
  refine ⟨pEquiv, ?_⟩
  intro i
  rw [hpEquiv_single, hliftP]

/-- Every finitely generated projective right module over a ring with a proper
two-sided ideal whose complement consists of units is free. -/
theorem free_of_isUnit_compl
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤)
    (hunit : ∀ x ∉ I, IsUnit x) :
    Module.Free Rᵐᵒᵖ P := by
  classical
  let _ : I.asIdeal.IsMaximal :=
    I.isMaximal_asIdeal_of_isUnit_compl hI hunit
  let _ : DivisionRing (R ⧸ I.asIdeal) :=
    I.quotientDivisionRing hI hunit
  let _ : Module.Free (R ⧸ I.asIdeal)ᵐᵒᵖ
      (ModuleCat.RightExtension.IdealQuotient (M := P) I.asIdeal) :=
    Module.Free.of_divisionRing (R ⧸ I.asIdeal)ᵐᵒᵖ
      (ModuleCat.RightExtension.IdealQuotient (M := P) I.asIdeal)
  obtain ⟨e, _⟩ :=
    exists_rightFreeLinearEquiv_of_isUnit_compl (P := P) I hI hunit
  let _ : Module.Free Rᵐᵒᵖ
      (Fin (Module.finrank (R ⧸ I.asIdeal)ᵐᵒᵖ
        (ModuleCat.RightExtension.IdealQuotient (M := P) I.asIdeal)) → R) :=
    Module.Free.of_equiv (Module.rightFreeCoordEquiv R _)
  exact Module.Free.of_equiv e

end Module.Projective
