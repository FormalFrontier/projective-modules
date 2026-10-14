/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.ProjectiveKernel
import ProjectiveModules.Module.RightRegular
import ProjectiveModules.Module.RightExtensionIdeal
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Ring.Prod
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Split kernels with idempotent targets

The projection onto the idempotent span of `(1, 0)` in `ℤ × ℤ` has a
nonfree projective target and a nonzero kernel. The additional product
controls separate finiteness of the source from projectivity of the source.
The right regular action and the idempotent-span maps use the library's
existing constructions and Mathlib's opposite-ring module structures.
-/

noncomputable section

namespace ProjectiveModulesTests.SplitKernel

abbrev A := ℤ × ℤ
abbrev S := Aᵐᵒᵖ
abbrev e : A := (1, 0)
abbrev b : S := MulOpposite.op e
abbrev I : Ideal S := Ideal.span {b}
abbrev J : Ideal S := Ideal.span {1 - b}

lemma he : IsIdempotentElem e :=
  Prod.ext (mul_one (1 : ℤ)) (mul_zero (0 : ℤ))

lemma hb : IsIdempotentElem b := congrArg (MulOpposite.op : A → S) he.eq

lemma hb0 : b ≠ 0 :=
  fun h ↦ one_ne_zero (congrArg (fun x : S ↦ x.unop.1) h)

lemma hb1 : b ≠ 1 :=
  fun h ↦ zero_ne_one (congrArg (fun x : S ↦ x.unop.2) h)

instance : Module.Finite S I := Module.Finite.span_singleton S b
instance : Module.Projective S I := hb.projective_span
instance : Nontrivial I := Submodule.nontrivial_span_singleton hb0

example : ¬ Module.Free S I := hb.not_free_span hb0 hb1

def opEquiv : A ≃ₗ[S] S := MulOpposite.opLinearEquiv S

def projection : S →ₗ[S] I := IsIdempotentElem.spanProjection b

def q : A →ₗ[S] I := projection.comp opEquiv.toLinearMap

def sectionMap : I →ₗ[S] A := opEquiv.symm.toLinearMap.comp I.subtype

lemma q_sectionMap (x : I) : q (sectionMap x) = x := by
  simpa only [q, sectionMap, projection, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Submodule.subtype_apply] using
    hb.spanProjection_apply_coe x

lemma q_comp_sectionMap : q.comp sectionMap = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact q_sectionMap x

example : Function.Surjective q :=
  LinearMap.surjective_of_comp_eq_id sectionMap q q_comp_sectionMap

/-- The complementary idempotent span is the other summand of the regular module. -/
def complementarySplit : (I × J) ≃ₗ[S] A := hb.spanProdEquiv.trans opEquiv.symm

def nonzeroKernelVector : LinearMap.ker q := ⟨(0, 1), by
  apply Subtype.ext
  simp [q, projection, opEquiv, b, e, ← MulOpposite.op_mul]⟩

example : nonzeroKernelVector ≠ 0 :=
  fun h ↦ one_ne_zero (congrArg (fun k : LinearMap.ker q ↦ k.val.2) h)

example : Module.Finite S (LinearMap.ker q) :=
  LinearMap.finite_splitKernel sectionMap q q_comp_sectionMap

example : Module.Projective S (LinearMap.ker q) :=
  LinearMap.projective_splitKernel sectionMap q q_comp_sectionMap

example (x : A) :
    (LinearMap.splitKernelProjection sectionMap q q_comp_sectionMap x : A) =
      x - sectionMap (q x) :=
  LinearMap.splitKernelProjection_apply sectionMap q q_comp_sectionMap x

example :
    (LinearMap.splitKernelProjection sectionMap q q_comp_sectionMap).comp
      (LinearMap.ker q).subtype = LinearMap.id :=
  LinearMap.splitKernelProjection_comp_subtype sectionMap q q_comp_sectionMap

-- No projectivity of this finite source is supplied.
abbrev T := S ⧸ Ideal.span {(2 : S)}
def finiteMap : (I × T) →ₗ[S] I := LinearMap.fst S I T
def finiteSection : I →ₗ[S] (I × T) := LinearMap.inl S I T

example : Module.Finite S (I × T) := inferInstance

example : Module.Finite S (LinearMap.ker finiteMap) :=
  LinearMap.finite_splitKernel finiteSection finiteMap (LinearMap.fst_comp_inl S I T)

-- This projective source has an infinite free summand; no finiteness is supplied.
abbrev W := ℕ →₀ S
def projectiveMap : (I × W) →ₗ[S] I := LinearMap.fst S I W
def projectiveSection : I →ₗ[S] (I × W) := LinearMap.inl S I W

example : Module.Projective S (I × W) := inferInstance

example : Module.Projective S (LinearMap.ker projectiveMap) :=
  LinearMap.projective_splitKernel projectiveSection projectiveMap
    (LinearMap.fst_comp_inl S I W)

def sourceDown : ULift.{1} A ≃ₗ[S] A := ULift.moduleEquiv
def targetDown : ULift.{2} I ≃ₗ[S] I := ULift.moduleEquiv

def liftedQ : ULift.{1} A →ₗ[S] ULift.{2} I :=
  targetDown.symm.toLinearMap.comp (q.comp sourceDown.toLinearMap)

def liftedSection : ULift.{2} I →ₗ[S] ULift.{1} A :=
  sourceDown.symm.toLinearMap.comp (sectionMap.comp targetDown.toLinearMap)

lemma liftedQ_comp_section : liftedQ.comp liftedSection = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [liftedQ, liftedSection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply, q_sectionMap,
    LinearMap.id_apply]

example : Module.Finite S (LinearMap.ker liftedQ) :=
  LinearMap.finite_splitKernel liftedSection liftedQ liftedQ_comp_section

example : Module.Projective S (LinearMap.ker liftedQ) :=
  LinearMap.projective_splitKernel liftedSection liftedQ liftedQ_comp_section

-- The target of a surjective zero map is zero.
def zeroSection : PUnit →ₗ[S] A := 0
def zeroRetraction : A →ₗ[S] PUnit := 0

lemma zeroRetraction_comp : zeroRetraction.comp zeroSection = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

example : Module.Finite S (LinearMap.ker zeroRetraction) :=
  LinearMap.finite_splitKernel zeroSection zeroRetraction zeroRetraction_comp

example : Module.Projective S (LinearMap.ker zeroRetraction) :=
  LinearMap.projective_splitKernel zeroSection zeroRetraction zeroRetraction_comp

example : Module.Finite S (LinearMap.ker (LinearMap.id (R := S) (M := A))) :=
  LinearMap.finite_splitKernel LinearMap.id LinearMap.id (by simp)

end ProjectiveModulesTests.SplitKernel

namespace ProjectiveModulesTests.SplitKernel

-- A nonfree product domain retracts onto the regular module.
private abbrev idealProductDomain := I × S

private instance idealProductDomain_finite : Module.Finite S idealProductDomain := inferInstance
private instance idealProductDomain_projective :
    Module.Projective S idealProductDomain := inferInstance

private def idealProductRetraction : idealProductDomain →ₗ[S] S := LinearMap.snd S I S
private def idealProductSection : S →ₗ[S] idealProductDomain := LinearMap.inr S I S

private theorem idealProductRetraction_comp_section :
    idealProductRetraction.comp idealProductSection = LinearMap.id :=
  LinearMap.snd_comp_inr S I S

private def idealProductFirstPrime : PrimeSpectrum S :=
  ⟨RingHom.ker ((RingHom.fst ℤ ℤ).comp (RingEquiv.toOpposite A).symm.toRingHom),
    RingHom.ker_isPrime _⟩

private def idealProductSecondPrime : PrimeSpectrum S :=
  ⟨RingHom.ker ((RingHom.snd ℤ ℤ).comp (RingEquiv.toOpposite A).symm.toRingHom),
    RingHom.ker_isPrime _⟩

private theorem idealProductFirstPrime_notMem : b ∉ idealProductFirstPrime.asIdeal := by
  change (1 : ℤ) ≠ 0
  exact one_ne_zero

private theorem idealProductSecondPrime_mem : b ∈ idealProductSecondPrime.asIdeal := by
  change (0 : ℤ) = 0
  rfl

-- The two coordinate stalks have different ranks, even after adding a regular summand.
private theorem idealProductDomain_stalk_ranks :
    Module.rankAtStalk (R := S) idealProductDomain idealProductFirstPrime = 2 ∧
      Module.rankAtStalk (R := S) idealProductDomain idealProductSecondPrime = 1 := by
  have hfirst := hb.rankAtStalk_span_eq_one idealProductFirstPrime
    idealProductFirstPrime_notMem
  have hsecond := hb.rankAtStalk_span_eq_zero idealProductSecondPrime
    idealProductSecondPrime_mem
  have hprod := Module.rankAtStalk_prod (R := S) I S
  have hself := Module.rankAtStalk_self (R := S)
  constructor
  · calc
      Module.rankAtStalk (R := S) idealProductDomain idealProductFirstPrime =
          Module.rankAtStalk (R := S) I idealProductFirstPrime +
            Module.rankAtStalk (R := S) S idealProductFirstPrime := congrFun hprod _
      _ = 2 := by
        rw [hfirst, congrFun hself idealProductFirstPrime]
        change (1 : ℕ) + 1 = 2
        rfl
  · calc
      Module.rankAtStalk (R := S) idealProductDomain idealProductSecondPrime =
          Module.rankAtStalk (R := S) I idealProductSecondPrime +
            Module.rankAtStalk (R := S) S idealProductSecondPrime := congrFun hprod _
      _ = 1 := by
        rw [hsecond, congrFun hself idealProductSecondPrime]
        change (0 : ℕ) + 1 = 1
        rfl

private theorem idealProductDomain_not_free : ¬ Module.Free S idealProductDomain := by
  intro hfree
  let _ : Module.Free S idealProductDomain := hfree
  have hconstant := Module.rankAtStalk_eq_finrank_of_free (R := S) (M := idealProductDomain)
  have h := (congrFun hconstant idealProductFirstPrime).trans
    (congrFun hconstant idealProductSecondPrime).symm
  rw [idealProductDomain_stalk_ranks.1, idealProductDomain_stalk_ranks.2] at h
  exact (by decide : (2 : ℕ) ≠ 1) h

private def idealProductKernelEquiv : I ≃ₗ[S] LinearMap.ker idealProductRetraction :=
  (LinearEquiv.ofInjective (LinearMap.inl S I S) LinearMap.inl_injective).trans
    (LinearEquiv.ofEq _ _ (LinearMap.range_inl S I S))

private theorem idealProductKernel_not_free :
    ¬ Module.Free S (LinearMap.ker idealProductRetraction) := by
  intro hfree
  exact hb.not_free_span hb0 hb1 (Module.Free.of_equiv' hfree idealProductKernelEquiv.symm)

private def idealProductKernelVector : LinearMap.ker idealProductRetraction :=
  ⟨(ModuleCat.RightExtension.spanGenerator e, 0), rfl⟩

private theorem idealProductKernelVector_ne_zero : idealProductKernelVector ≠ 0 :=
  fun h ↦ hb0 (congrArg (fun k : LinearMap.ker idealProductRetraction ↦ (k.val.1 : S)) h)

-- The kernel has an annihilator; the domain's regular summand is faithful.
private theorem idealProductKernel_annihilator (k : LinearMap.ker idealProductRetraction) :
    (1 - b : S) ≠ 0 ∧ (1 - b) • k = 0 := by
  refine ⟨sub_ne_zero.mpr (Ne.symm hb1), ?_⟩
  obtain ⟨x, rfl⟩ := idealProductKernelEquiv.surjective k
  rw [← map_smul, hb.one_sub_smul_span, map_zero]

private def idealProductProjection : idealProductDomain →ₗ[S]
    LinearMap.ker idealProductRetraction :=
  LinearMap.splitKernelProjection idealProductSection idealProductRetraction
    idealProductRetraction_comp_section

private theorem idealProductProjection_apply (x : idealProductDomain) :
    (idealProductProjection x : idealProductDomain) = (x.1, 0) := by
  calc
    (idealProductProjection x : idealProductDomain) =
        x - idealProductSection (idealProductRetraction x) :=
      LinearMap.splitKernelProjection_apply _ _ _ x
    _ = (x.1, 0) := Prod.ext (sub_zero x.1) (sub_self x.2)

private theorem idealProductProjection_fixes (k : LinearMap.ker idealProductRetraction) :
    idealProductProjection k = k :=
  DFunLike.congr_fun (LinearMap.splitKernelProjection_comp_subtype
    idealProductSection idealProductRetraction idealProductRetraction_comp_section) k

private theorem idealProductProjection_section (s : S) :
    idealProductProjection (idealProductSection s) = 0 := by
  apply Subtype.ext
  rw [idealProductProjection_apply]
  rfl

private theorem idealProductProjection_ne_zero : idealProductProjection ≠ 0 := by
  intro h
  have hv := idealProductProjection_fixes idealProductKernelVector
  rw [h, LinearMap.zero_apply] at hv
  exact idealProductKernelVector_ne_zero hv.symm

private theorem idealProductKernel_finite :
    Module.Finite S (LinearMap.ker idealProductRetraction) :=
  LinearMap.finite_splitKernel idealProductSection idealProductRetraction
    idealProductRetraction_comp_section

private theorem idealProductKernel_projective :
    Module.Projective S (LinearMap.ker idealProductRetraction) :=
  LinearMap.projective_splitKernel idealProductSection idealProductRetraction
    idealProductRetraction_comp_section

-- The zero scalar ring requires no nontriviality assumption.
private theorem zeroRing_splitKernel :
    (0 : PUnit) = 1 ∧
      Module.Finite PUnit (LinearMap.ker (LinearMap.id (R := PUnit) (M := PUnit))) ∧
      Module.Projective PUnit (LinearMap.ker (LinearMap.id (R := PUnit) (M := PUnit))) :=
  ⟨Subsingleton.elim _ _, LinearMap.finite_splitKernel LinearMap.id LinearMap.id (by simp),
    LinearMap.projective_splitKernel LinearMap.id LinearMap.id (by simp)⟩

private theorem zeroRing_splitKernelProjection (x : PUnit) :
    LinearMap.splitKernelProjection (LinearMap.id (R := PUnit) (M := PUnit))
      LinearMap.id (by simp) x = 0 :=
  Subsingleton.elim _ _

end ProjectiveModulesTests.SplitKernel
