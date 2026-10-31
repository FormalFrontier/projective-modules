/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Logic.Equiv.Sum
public import ProjectiveModules.Module.SymmetricPower.Basic

/-!
# Concatenation of symmetric products

For disjoint label types `I` and `J`, concatenation combines a symmetric product
labelled by `I` and one labelled by `J` into a product labelled by `I ⊕ J`.
It is defined over an arbitrary commutative semiring and uses no finiteness
assumption on the labels or the semimodule.

* `SymmetricPower.concat_tprod` evaluates concatenation on arbitrary labelled
  generator tensors.
* `SymmetricPower.concat_unique` characterizes the map by these values.
* `SymmetricPower.concat_surjective` follows because each total generator is
  the concatenation of its two restrictions.
* `SymmetricPower.concat_natural` expresses compatibility with linear maps.

Concatenation is not generally injective: permuting labels between the two
blocks can identify distinct generator tensors.

## Implementation notes

The construction curries the total multilinear product along a disjoint union,
uses the symmetric universal property in each block, and then tensor-lifts.
The generator formula is the interface to concatenation; the auxiliary lifts
remain private.

## References

The indexed symmetric powers and their spanning generators are those of
`Mathlib.LinearAlgebra.TensorPower.Symmetric`. The symmetric-lift API is supplied
by `ProjectiveModules.Module.SymmetricPower.Basic`.
-/

public section

open scoped TensorProduct

namespace SymmetricPower

noncomputable section

universe uR uP

variable {R I J : Type uR} [CommSemiring R]
variable {P : Type uP} [AddCommMonoid P] [Module R P]

private theorem tprod_sum_perm
    (eI : Equiv.Perm I) (eJ : Equiv.Perm J) (x : I → P) (y : J → P) :
    tprod R (Sum.elim (fun i => x (eI i)) (fun j => y (eJ j))) =
      tprod R (Sum.elim x y) := by
  have hfun :
      (fun s : I ⊕ J =>
        Sum.elim x y (Equiv.Perm.sumCongr eI eJ s)) =
      Sum.elim (fun i => x (eI i)) (fun j => y (eJ j)) := by
    funext s
    cases s <;> simp
  simpa only [hfun] using
    (tprod_equiv (R := R) (Equiv.Perm.sumCongr eI eJ) (Sum.elim x y))

private def concatRight (x : I → P) :
    SymmetricPower R J P →ₗ[R] SymmetricPower R (I ⊕ J) P :=
  lift ((tprod R (ι := I ⊕ J) (M := P)).currySum x) (by
    intro e y
    simpa [MultilinearMap.currySum_apply'] using
      (tprod_sum_perm (R := R) (Equiv.refl I) e x y))

private theorem concatRight_tprod (x : I → P) (y : J → P) :
    concatRight (R := R) (J := J) x (tprod R y) =
      tprod R (Sum.elim x y) := by
  simp only [concatRight, lift_tprod, MultilinearMap.currySum_apply']

private def concatMultilinear :
    MultilinearMap R (fun _ : I => P)
      (SymmetricPower R J P →ₗ[R] SymmetricPower R (I ⊕ J) P) := by
  classical
  refine
    { toFun := concatRight (R := R) (J := J)
      map_update_add' := ?_
      map_update_smul' := ?_ }
  · intro _ x i a b
    apply hom_ext
    intro y
    have h := congrArg
      (fun f : MultilinearMap R (fun _ : J => P)
        (SymmetricPower R (I ⊕ J) P) => f y)
      ((tprod R (ι := I ⊕ J) (M := P)).currySum.map_update_add x i a b)
    change
      ((tprod R (ι := I ⊕ J) (M := P)).currySum (Function.update x i (a + b))) y =
        ((tprod R (ι := I ⊕ J) (M := P)).currySum (Function.update x i a)) y +
          ((tprod R (ι := I ⊕ J) (M := P)).currySum (Function.update x i b)) y at h
    simpa only [LinearMap.add_apply, concatRight_tprod,
      MultilinearMap.currySum_apply'] using h
  · intro _ x i c a
    apply hom_ext
    intro y
    have h := congrArg
      (fun f : MultilinearMap R (fun _ : J => P)
        (SymmetricPower R (I ⊕ J) P) => f y)
      ((tprod R (ι := I ⊕ J) (M := P)).currySum.map_update_smul x i c a)
    change
      ((tprod R (ι := I ⊕ J) (M := P)).currySum (Function.update x i (c • a))) y =
        c • (((tprod R (ι := I ⊕ J) (M := P)).currySum (Function.update x i a)) y) at h
    simpa only [LinearMap.smul_apply, concatRight_tprod,
      MultilinearMap.currySum_apply'] using h

private theorem concatMultilinear_tprod (x : I → P) (y : J → P) :
    concatMultilinear (R := R) (J := J) x (tprod R y) =
      tprod R (Sum.elim x y) := by
  change concatRight (R := R) (J := J) x (tprod R y) = _
  exact concatRight_tprod x y

private def concatBilinear :
    SymmetricPower R I P →ₗ[R]
      SymmetricPower R J P →ₗ[R] SymmetricPower R (I ⊕ J) P :=
  lift (concatMultilinear (R := R) (I := I) (J := J) (P := P)) (by
    intro e x
    apply hom_ext
    intro y
    simpa [concatMultilinear_tprod] using
      (tprod_sum_perm (R := R) e (Equiv.refl J) x y))

/-- Concatenates symmetric products on two disjoint label types. -/
def concat :
    SymmetricPower R I P ⊗[R] SymmetricPower R J P →ₗ[R]
      SymmetricPower R (I ⊕ J) P :=
  TensorProduct.lift (concatBilinear (R := R) (I := I) (J := J) (P := P))

/-- Concatenation joins the two labelled families without a multiplicity factor. -/
@[simp] theorem concat_tprod (x : I → P) (y : J → P) :
    concat (tprod R x ⊗ₜ[R] tprod R y) = tprod R (Sum.elim x y) := by
  simp only [concat, TensorProduct.lift.tmul, concatBilinear,
    lift_tprod, concatMultilinear_tprod]

universe uQ uN

private theorem concat_tensor_hom_ext
    {N : Type uN} [AddCommMonoid N] [Module R N]
    {F G : SymmetricPower R I P ⊗[R] SymmetricPower R J P →ₗ[R] N}
    (h : ∀ (x : I → P) (y : J → P),
      F (tprod R x ⊗ₜ[R] tprod R y) =
        G (tprod R x ⊗ₜ[R] tprod R y)) :
    F = G := by
  apply TensorProduct.curry_injective
  apply hom_ext
  intro x
  apply hom_ext
  intro y
  simpa only [TensorProduct.curry_apply] using h x y

/-- The values on all labelled generator tensors determine concatenation. -/
theorem concat_unique
    (F : SymmetricPower R I P ⊗[R] SymmetricPower R J P →ₗ[R]
      SymmetricPower R (I ⊕ J) P)
    (h : ∀ (x : I → P) (y : J → P),
      F (tprod R x ⊗ₜ[R] tprod R y) = tprod R (Sum.elim x y)) :
    F = concat (R := R) (I := I) (J := J) (P := P) := by
  apply concat_tensor_hom_ext
  intro x y
  exact (h x y).trans
    (concat_tprod (R := R) (I := I) (J := J) (P := P) x y).symm

/-- Concatenation is surjective for arbitrary disjoint label types. -/
theorem concat_surjective :
    Function.Surjective (concat (R := R) (I := I) (J := J) (P := P)) := by
  apply LinearMap.range_eq_top.mp
  apply le_antisymm le_top
  rw [← span_tprod_eq_top (R := R) (ι := I ⊕ J) (M := P)]
  apply Submodule.span_le.mpr
  rintro _ ⟨z, rfl⟩
  apply LinearMap.mem_range.mpr
  refine ⟨tprod R (fun i : I => z (Sum.inl i)) ⊗ₜ[R]
    tprod R (fun j : J => z (Sum.inr j)), ?_⟩
  rw [concat_tprod]
  apply congrArg (fun w : (I ⊕ J) → P => tprod R w)
  funext s
  cases s <;> rfl

variable {Q : Type uQ} [AddCommMonoid Q] [Module R Q]

/-- Concatenation commutes with applying an R-linear map to each label. -/
theorem concat_natural (f : P →ₗ[R] Q) :
    (map (ι := I ⊕ J) f).comp
        (concat (R := R) (I := I) (J := J) (P := P)) =
      (concat (R := R) (I := I) (J := J) (P := Q)).comp
        (TensorProduct.map (map (ι := I) f) (map (ι := J) f)) := by
  apply concat_tensor_hom_ext
  intro x y
  simp only [LinearMap.comp_apply, concat_tprod,
    TensorProduct.map_tmul, map_tprod]
  apply congrArg (fun w : (I ⊕ J) → Q => tprod R w)
  funext s
  cases s <;> rfl

end

end SymmetricPower
