/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.Product
import ProjectiveModules.KTheory.RankBound
import Mathlib.Algebra.Field.Rat

/-!
# A corner module over a product ring

The two rational factors have ranks zero and one. Their coefficient product is
nonzero and finite projective, and its complementary corner completes it to one
copy of the regular right module. Its coordinate classes lie in the image of
`KTheory.ProjectiveClass.piMap` without invoking an arbitrary-product image theorem.

## References and credits

* Projective Modules' finite-projective right coefficient products and finite
  product equivalence on projective classes.
* Mathlib's regular modules, finite function modules, and rational field.
-/

@[expose] public section

universe uI uR

namespace KTheory.ProjectiveClass

private abbrev rationalFamily (_ : Bool) := ℚ

private abbrev rationalProduct := Bool → ℚ

-- These are the original right-factor module dictionaries, not modules over ℚ
-- substituted for modules over ℚᵐᵒᵖ using commutativity.
private noncomputable def cornerFactors :
    Bool → ModuleCat.FiniteProjective ℚᵐᵒᵖ
  | false => ModuleCat.FiniteProjective.of ℚᵐᵒᵖ (Fin 0 → ℚᵐᵒᵖ)
  | true => ModuleCat.FiniteProjective.of ℚᵐᵒᵖ ℚᵐᵒᵖ

private noncomputable def corner : ModuleCat.FiniteProjective rationalProductᵐᵒᵖ :=
  ModuleCat.FiniteProjective.pi rationalFamily cornerFactors

private noncomputable def cornerComplement :
    ModuleCat.FiniteProjective rationalProductᵐᵒᵖ :=
  ModuleCat.FiniteProjective.pi rationalFamily (fun b => cornerFactors (!b))

-- The carrier is the ordinary dependent function carrier. At true it contains 1.
private theorem corner_nonzero : ∃ x : corner, x ≠ 0 := by
  refine ⟨ModuleCat.FiniteProjective.piMk rationalFamily cornerFactors
    (fun b => match b with | false => 0 | true => (1 : ℚᵐᵒᵖ)), ?_⟩
  intro hx
  have h : (1 : ℚᵐᵒᵖ) = 0 := congrArg (fun y : corner => y true) hx
  exact one_ne_zero h

private theorem corner_not_free : ¬ Module.Free rationalProductᵐᵒᵖ corner := by
  intro hfree
  letI : Nontrivial corner := by
    obtain ⟨x, hx⟩ := corner_nonzero
    exact ⟨⟨x, 0, hx⟩⟩
  letI : Module.Free rationalProductᵐᵒᵖ corner := hfree
  haveI : FaithfulSMul rationalProductᵐᵒᵖ corner := inferInstance
  have hzero :
      (MulOpposite.op (fun b : Bool => if b then (0 : ℚ) else 1) :
        rationalProductᵐᵒᵖ) = 0 :=
    FaithfulSMul.eq_of_smul_eq_smul fun y : corner => by
      rw [zero_smul]
      apply (ModuleCat.FiniteProjective.pi_ext_iff
        rationalFamily cornerFactors _ _).2
      intro b
      change
        ((MulOpposite.op (fun b : Bool => if b then (0 : ℚ) else 1) •
          (y : ModuleCat.FiniteProjective.pi rationalFamily cornerFactors)) b) =
        (0 : cornerFactors b)
      refine (ModuleCat.FiniteProjective.pi_smul_apply rationalFamily
        cornerFactors (fun b : Bool => if b then (0 : ℚ) else 1) y b).trans ?_
      cases b
      · change (MulOpposite.op (1 : ℚ) • y false : Fin 0 → ℚᵐᵒᵖ) = 0
        exact @Subsingleton.elim (Fin 0 → ℚᵐᵒᵖ) inferInstance _ _
      · change MulOpposite.op (0 : ℚ) • y true = 0
        simp only [MulOpposite.op_zero, zero_smul]
  have h := congrArg (fun a : rationalProductᵐᵒᵖ => a.unop false) hzero
  change (1 : ℚ) = 0 at h
  exact one_ne_zero h

private def coordinateRank : Bool → ℕ
  | false => 0
  | true => 1

private noncomputable def coordinateClass (b : Bool) : ProjectiveClass ℚ :=
  coordinateRank b • of ℚ ℚᵐᵒᵖ

private noncomputable def complementaryClass (b : Bool) : ProjectiveClass ℚ :=
  coordinateRank (!b) • of ℚ ℚᵐᵒᵖ

private theorem varying_ranks : coordinateRank false = 0 ∧ coordinateRank true = 1 :=
  ⟨rfl, rfl⟩

private theorem uniform_one (b : Bool) :
    coordinateClass b + complementaryClass b = 1 • of ℚ ℚᵐᵒᵖ := by
  cases b <;> simp [coordinateClass, complementaryClass, coordinateRank]

private theorem corner_coordinates :
    piMap rationalFamily (of rationalProduct corner) = coordinateClass := by
  calc
    piMap rationalFamily (of rationalProduct corner) =
        piEquiv rationalFamily (of rationalProduct corner) :=
      congrArg (fun f : ProjectiveClass rationalProduct →+
        (Bool → ProjectiveClass ℚ) => f (of rationalProduct corner))
        (piEquiv_toAddMonoidHom_eq_piMap rationalFamily).symm
    _ = (fun b => of ℚ (cornerFactors b)) := by
      simpa only [corner, rationalProduct, rationalFamily,
        AddEquiv.apply_symm_apply] using
        (congrArg (piEquiv rationalFamily)
          (piEquiv_symm_of_module rationalFamily cornerFactors)).symm
    _ = coordinateClass := by
      funext b
      cases b <;> simp [cornerFactors, coordinateClass, coordinateRank]

private theorem complement_coordinates :
    piMap rationalFamily (of rationalProduct cornerComplement) =
      complementaryClass := by
  calc
    piMap rationalFamily (of rationalProduct cornerComplement) =
        piEquiv rationalFamily (of rationalProduct cornerComplement) :=
      congrArg (fun f : ProjectiveClass rationalProduct →+
        (Bool → ProjectiveClass ℚ) => f (of rationalProduct cornerComplement))
        (piEquiv_toAddMonoidHom_eq_piMap rationalFamily).symm
    _ = (fun b => of ℚ (cornerFactors (!b))) := by
      simpa only [cornerComplement, rationalProduct, rationalFamily,
        AddEquiv.apply_symm_apply] using
        (congrArg (piEquiv rationalFamily)
          (piEquiv_symm_of_module rationalFamily
            (fun b => cornerFactors (!b)))).symm
    _ = complementaryClass := by
      funext b
      cases b with
      | false =>
          change of ℚ (cornerFactors true) = complementaryClass false
          simp [Bool.not_false, cornerFactors, complementaryClass, coordinateRank]
      | true =>
          change of ℚ (cornerFactors false) = complementaryClass true
          simp [Bool.not_true, cornerFactors, complementaryClass, coordinateRank]

-- Equality is detected using the proved finite equivalence, not an
-- arbitrary-product injectivity or image assertion.
private theorem corner_bound :
    of rationalProduct corner + of rationalProduct cornerComplement =
      1 • of rationalProduct rationalProductᵐᵒᵖ := by
  apply (piEquiv rationalFamily).injective
  change (piEquiv rationalFamily).toAddMonoidHom _ =
    (piEquiv rationalFamily).toAddMonoidHom _
  rw [piEquiv_toAddMonoidHom_eq_piMap rationalFamily, map_add,
    corner_coordinates, complement_coordinates, one_nsmul]
  funext b
  simpa only [Pi.add_apply, piMap_of_self, one_nsmul] using uniform_one b

-- This is a proposition about the two specified module carriers; no equivalence
-- is selected to manufacture a module or any of its dictionaries.
private theorem corner_finite_free_summand :
    Nonempty ((corner × cornerComplement) ≃ₗ[rationalProductᵐᵒᵖ]
      (Fin 1 → rationalProductᵐᵒᵖ)) := by
  apply (of_eq_iff rationalProduct (corner × cornerComplement)
    (Fin 1 → rationalProductᵐᵒᵖ)).1
  rw [of_prod, of_fin_fun_eq_nsmul]
  exact corner_bound

-- A positive image witness is the class of the specified module, not an inverse
-- of an arbitrary-product classification statement.
example : coordinateClass ∈ Set.range (piMap rationalFamily) ∧
    ∃ n : ℕ, ∀ b, ∃ q : ProjectiveClass ℚ,
      coordinateClass b + q = n • of ℚ ℚᵐᵒᵖ := by
  exact ⟨⟨of rationalProduct corner, corner_coordinates⟩,
    ⟨1, fun b => ⟨complementaryClass b, uniform_one b⟩⟩⟩

-- Empty indices require neither a nonempty index nor linked index/ring universes.
example {I : Type uI} [IsEmpty I] (Ri : I → Type uR) [∀ i, Ring (Ri i)] :
    (fun i => (0 : ProjectiveClass (Ri i))) ∈ Set.range (piMap Ri) ∧
      ∃ n : ℕ, ∀ i, ∃ q : ProjectiveClass (Ri i),
        (0 : ProjectiveClass (Ri i)) + q = n • of (Ri i) (Ri i)ᵐᵒᵖ := by
  constructor
  · exact ⟨0, map_zero (piMap Ri)⟩
  · exact ⟨0, fun i => isEmptyElim i⟩

-- Over zero factors the regular family has the uniform bound n = 0, even for
-- arbitrary index universes. No nontriviality assumption is imposed on a factor.
example {I : Type uI} (Ri : I → Type uR) [∀ i, Ring (Ri i)]
    [∀ i, Subsingleton (Ri i)] :
    (fun i => of (Ri i) (Ri i)ᵐᵒᵖ) ∈ Set.range (piMap Ri) ∧
      ∃ n : ℕ, ∀ i, ∃ q : ProjectiveClass (Ri i),
        of (Ri i) (Ri i)ᵐᵒᵖ + q = n • of (Ri i) (Ri i)ᵐᵒᵖ := by
  constructor
  · refine ⟨0, ?_⟩
    funext i
    simp
  · exact ⟨0, fun i => ⟨0, by simp⟩⟩

end KTheory.ProjectiveClass

/-!
# Bounded signed classes over products of rational fields

Examples of uniformly bounded signed K₀ families over products of rational fields.

## References and credits

* Projective Modules' classification of K₀ over division rings by integer rank.
* Mathlib's finite-dimensional modules and rational field.
-/

namespace KTheory.K0

private noncomputable def signedRationalClasses (i : ℕ) : K0 ℚ :=
  (finrankEquiv ℚ).symm (if Even i then (-2 : ℤ) else 3)

private theorem signedRationalClasses_bound (i : ℕ) :
    |finrankEquiv ℚ (signedRationalClasses i)| ≤ (3 : ℤ) := by
  by_cases hi : Even i <;> norm_num [signedRationalClasses, hi]

example : signedRationalClasses 0 ≠ signedRationalClasses 1 := by
  intro h
  have hr := congrArg (finrankEquiv ℚ) h
  norm_num [signedRationalClasses] at hr

-- A nonconstant bounded signed family has a unique class over the product ring.
example : ∃! x : K0 (ℕ → ℚ),
    piMap (fun _ : ℕ => ℚ) x = signedRationalClasses := by
  obtain ⟨x, hx⟩ :=
    (mem_range_piMap_iff (fun _ : ℕ => ℚ) signedRationalClasses).2
      ⟨3, signedRationalClasses_bound⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact (piMap_injective (fun _ : ℕ => ℚ)) (hy.trans hx.symm)

end KTheory.K0
