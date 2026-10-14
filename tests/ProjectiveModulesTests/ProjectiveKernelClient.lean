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
