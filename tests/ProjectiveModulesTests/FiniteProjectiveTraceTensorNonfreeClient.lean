/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Trace.TensorProduct
public import ProjectiveModulesTests.IdempotentSpanSemiringClient
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Tensor traces on a nonfree ideal over the natural-number product semiring

Let `R = ℕ × ℕ`, `e = (1, 0)` and `I = Ideal.span {e}` with their canonical
operations. Both `I` and `I ⊗[R] I` are nonzero finite projective modules that
are not free. Multiplication of the underlying scalars detects the nonzero
pure tensor of the two canonical generators. The scalar `(0, 1)` annihilates
every element of the tensor product, ruling out freeness by faithfulness of a
nontrivial free module.

For the endomorphisms `f = 2 • id` and `g = 3 • id`, the contraction traces
are `(2, 0)` and `(3, 0)`. The trace of `TensorProduct.map f g` is `(6, 0)`.
These three values follow independently from the rank-one trace formula:
the inclusion of `I` and the multiplication pairing on `I ⊗[R] I` exhibit
the respective identity maps as rank-one maps. No tensor-trace identity is
used in these rank-one computations. A final example also computes the tensor
trace from the tensor-product identity and the two factor traces.

## References

The ideal's projectivity and nonfreeness reuse the idempotent-span
formalization in `ProjectiveModules.Module.LocallyConstantRank` and its
natural-number product client. The multiplication pairing uses Jz Pan's
`Submodule.mulMap` formalization in Mathlib. The trace calculations use the
contraction and dual tensor–Hom formalizations of Oliver Nash and Antoine
Labelle, through `LinearMap.traceOfFiniteProjective_smulRight`.
-/

open scoped TensorProduct

noncomputable section

namespace ProjectiveModulesTests.FiniteProjectiveTraceTensorNonfreeClient

abbrev R := ℕ × ℕ

def e : R := (1, 0)

abbrev I := Ideal.span {e}

abbrev T := I ⊗[R] I

lemma e_isIdempotent : IsIdempotentElem e := by
  change e * e = e
  ext <;> simp [e]

lemma e_ne_zero : e ≠ 0 := by
  intro h
  have hfst := congrArg Prod.fst h
  simp [e] at hfst

instance idealFinite : Module.Finite R I := Module.Finite.span_singleton R e

instance idealProjective : Module.Projective R I :=
  IdempotentSpanSemiringClient.legacy_nat_product_projective_nonfree.2.1

lemma ideal_not_free : ¬ Module.Free R I :=
  IdempotentSpanSemiringClient.legacy_nat_product_projective_nonfree.2.2

lemma tensor_finite_projective : Module.Finite R T ∧ Module.Projective R T :=
  ⟨inferInstance, inferInstance⟩

/-- The canonical generator of the principal ideal. -/
def v : I := ⟨e, Ideal.mem_span_singleton_self e⟩

@[simp]
lemma v_coe : (v : R) = e := rfl

lemma v_ne_zero : v ≠ 0 := by
  intro h
  exact e_ne_zero (congrArg (fun x : I ↦ (x : R)) h)

instance idealNontrivial : Nontrivial I :=
  nontrivial_iff.mpr ⟨v, 0, v_ne_zero⟩

lemma coe_smul_v (x : I) : (x : R) • v = x := by
  apply Subtype.ext
  change (x : R) * e = (x : R)
  have hx := congrArg (fun y : I ↦ (y : R)) (e_isIdempotent.smul_span x)
  change e * (x : R) = (x : R) at hx
  exact (mul_comm _ _).trans hx

lemma ideal_rankOne_id : I.subtype.smulRight v = (LinearMap.id : I →ₗ[R] I) := by
  apply LinearMap.ext
  intro x
  exact coe_smul_v x

lemma trace_ideal_id :
    LinearMap.traceOfFiniteProjective R I LinearMap.id = e := by
  calc
    LinearMap.traceOfFiniteProjective R I LinearMap.id =
        LinearMap.traceOfFiniteProjective R I (I.subtype.smulRight v) := by
      rw [ideal_rankOne_id]
    _ = (v : R) := by
      simp only [LinearMap.traceOfFiniteProjective_smulRight, Submodule.subtype_apply]
    _ = e := v_coe

/-- The tensor of the two canonical ideal generators. -/
def w : T := v ⊗ₜ[R] v

/-- The multiplication pairing on the two canonical submodules of `R`. -/
abbrev tensorEvaluation : T →ₗ[R] R := Submodule.mulMap I I

@[simp]
lemma tensorEvaluation_tmul (x y : I) :
    tensorEvaluation (x ⊗ₜ[R] y) = (x : R) * (y : R) :=
  Submodule.mulMap_tmul I I x y

@[simp]
lemma tensorEvaluation_w : tensorEvaluation w = e := by
  rw [w, tensorEvaluation_tmul, v_coe, e_isIdempotent.eq]

lemma w_ne_zero : w ≠ 0 := by
  intro h
  apply e_ne_zero
  simpa only [tensorEvaluation_w, map_zero] using congrArg tensorEvaluation h

instance tensorNontrivial : Nontrivial T :=
  nontrivial_iff.mpr ⟨w, 0, w_ne_zero⟩

lemma tensor_rankOne_id :
    tensorEvaluation.smulRight w = (LinearMap.id : T →ₗ[R] T) := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.smulRight_apply, tensorEvaluation_tmul, LinearMap.id_apply]
  change ((x : R) * (y : R)) • (v ⊗ₜ[R] v) = x ⊗ₜ[R] y
  rw [← TensorProduct.smul_tmul_smul, coe_smul_v, coe_smul_v]

lemma trace_tensor_id :
    LinearMap.traceOfFiniteProjective R T LinearMap.id = e := by
  rw [← tensor_rankOne_id, LinearMap.traceOfFiniteProjective_smulRight,
    tensorEvaluation_w]

def p : R := (0, 1)

lemma p_ne_zero : p ≠ 0 := by
  intro h
  have hsnd := congrArg Prod.snd h
  simp [p] at hsnd

lemma p_mul_e : p * e = 0 := by
  ext <;> simp [p, e]

lemma p_smul_ideal (x : I) : p • x = 0 := by
  calc
    p • x = p • (e • x) :=
      congrArg (fun y : I ↦ p • y) (e_isIdempotent.smul_span x).symm
    _ = (p * e) • x := (mul_smul p e x).symm
    _ = 0 := by rw [p_mul_e, zero_smul]

lemma p_smul_tensor (z : T) : p • z = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.smul_tmul', p_smul_ideal, TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

lemma tensor_not_free : ¬ Module.Free R T := by
  intro hfree
  let : Module.Free R T := hfree
  have hp : p = (0 : R) := eq_of_smul_eq_smul fun z : T ↦ by
    rw [p_smul_tensor, zero_smul]
  exact p_ne_zero hp

/-- Twice the identity on the nonfree ideal. -/
def f : I →ₗ[R] I := (2 : R) • LinearMap.id

/-- Three times the identity on the nonfree ideal. -/
def g : I →ₗ[R] I := (3 : R) • LinearMap.id

@[simp]
lemma f_apply (x : I) : f x = (2 : R) • x := rfl

@[simp]
lemma g_apply (x : I) : g x = (3 : R) • x := rfl

lemma trace_f : LinearMap.traceOfFiniteProjective R I f = (2, 0) := by
  calc
    LinearMap.traceOfFiniteProjective R I f = (2 : R) • e := by
      rw [f, map_smul, trace_ideal_id]
    _ = (2, 0) := rfl

lemma trace_g : LinearMap.traceOfFiniteProjective R I g = (3, 0) := by
  calc
    LinearMap.traceOfFiniteProjective R I g = (3 : R) • e := by
      rw [g, map_smul, trace_ideal_id]
    _ = (3, 0) := rfl

lemma trace_f_ne_zero : LinearMap.traceOfFiniteProjective R I f ≠ 0 := by
  rw [trace_f]
  intro h
  have hfst := congrArg Prod.fst h
  simp at hfst

lemma trace_g_ne_zero : LinearMap.traceOfFiniteProjective R I g ≠ 0 := by
  rw [trace_g]
  intro h
  have hfst := congrArg Prod.fst h
  simp at hfst

lemma f_v_ne_zero : f v ≠ 0 := by
  intro h
  have hfst := congrArg (fun x : I ↦ (x : R).1) h
  change (2 : ℕ) = 0 at hfst
  simp at hfst

lemma g_v_ne_zero : g v ≠ 0 := by
  intro h
  have hfst := congrArg (fun x : I ↦ (x : R).1) h
  change (3 : ℕ) = 0 at hfst
  simp at hfst

lemma f_ne_zero : f ≠ 0 := by
  intro h
  exact f_v_ne_zero (by rw [h, LinearMap.zero_apply])

lemma g_ne_zero : g ≠ 0 := by
  intro h
  exact g_v_ne_zero (by rw [h, LinearMap.zero_apply])

/-- The tensor product of the two specified endomorphisms. -/
def tensorMap : T →ₗ[R] T := TensorProduct.map f g

@[simp]
lemma tensorMap_tmul (x y : I) :
    tensorMap (x ⊗ₜ[R] y) = f x ⊗ₜ[R] g y :=
  TensorProduct.map_tmul f g x y

lemma tensorMap_eq_six_smul_id : tensorMap = (6 : R) • LinearMap.id := by
  calc
    tensorMap = ((2 : R) * (3 : R)) • LinearMap.id := by
      rw [tensorMap, f, g, TensorProduct.map_smul_left, TensorProduct.map_smul_right,
        TensorProduct.map_id, smul_smul]
    _ = (6 : R) • LinearMap.id := rfl

lemma trace_tensorMap :
    LinearMap.traceOfFiniteProjective R T tensorMap = (6, 0) := by
  calc
    LinearMap.traceOfFiniteProjective R T tensorMap = (6 : R) • e := by
      rw [tensorMap_eq_six_smul_id, map_smul, trace_tensor_id]
    _ = (6, 0) := rfl

lemma tensorEvaluation_tensorMap_w : tensorEvaluation (tensorMap w) = (6, 0) := by
  calc
    tensorEvaluation (tensorMap w) = (6 : R) • e := by
      rw [tensorMap_eq_six_smul_id, LinearMap.smul_apply, LinearMap.id_apply,
        map_smul, tensorEvaluation_w]
    _ = (6, 0) := rfl

lemma tensorMap_w_ne_zero : tensorMap w ≠ 0 := by
  intro h
  have hval : ((6, 0) : R) = 0 := by
    simpa only [tensorEvaluation_tensorMap_w, map_zero] using congrArg tensorEvaluation h
  have hfst := congrArg Prod.fst hval
  simp at hfst

lemma tensorMap_ne_zero : tensorMap ≠ 0 := by
  intro h
  exact tensorMap_w_ne_zero (by rw [h, LinearMap.zero_apply])

lemma trace_tensorMap_ne_zero : LinearMap.traceOfFiniteProjective R T tensorMap ≠ 0 := by
  rw [trace_tensorMap]
  intro h
  have hfst := congrArg Prod.fst h
  simp at hfst

lemma one_no_additive_inverse : ¬ ∃ r : R, (1 : R) + r = 0 := by
  rintro ⟨r, h⟩
  have hfst := congrArg Prod.fst h
  simp at hfst

example : LinearMap.traceOfFiniteProjective R T tensorMap = (6, 0) := by
  calc
    LinearMap.traceOfFiniteProjective R T tensorMap =
        LinearMap.traceOfFiniteProjective R I f *
          LinearMap.traceOfFiniteProjective R I g :=
      LinearMap.traceOfFiniteProjective_tensorProduct' R I I f g
    _ = (6, 0) := by
      rw [trace_f, trace_g]
      rfl

end ProjectiveModulesTests.FiniteProjectiveTraceTensorNonfreeClient
