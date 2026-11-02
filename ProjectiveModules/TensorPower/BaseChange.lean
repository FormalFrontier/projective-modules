/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension of tensor powers

Extension of scalars commutes with every tensor power of a semimodule, including the
zeroth tensor power. The comparison is constructed from Mathlib's tensor-product
associativity, scalar-extension, empty-product and singleton equivalences.

`TensorPower.appendEquiv` identifies a tensor power tensored with one more factor with
the successor tensor power. Its pure-tensor formulas describe how to append or split off
the last factor.

The pure-tensor formulas in both directions and naturality with respect to module maps
characterize the scalar-extension comparison without choosing bases or imposing flatness
hypotheses.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open PiTensorProduct

universe uR uS uM uN

namespace TensorPower

variable (R : Type uR) [CommSemiring R]
variable (M : Type uM) [AddCommMonoid M] [Module R M]

/-- Appending one factor identifies a tensor power tensored with the semimodule with the
successor tensor power. The inverse splits off the last factor. -/
def appendEquiv (n : ℕ) :
    TensorPower R n M ⊗[R] M ≃ₗ[R] TensorPower R (n + 1) M :=
  (TensorProduct.congr (LinearEquiv.refl R (TensorPower R n M))
    (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 => M) 0).symm).trans
      TensorPower.mulEquiv

/-- Appending a pure tensor appends its last factor to the indexing tuple. -/
@[simp]
theorem appendEquiv_tprod (n : ℕ) (m : Fin n → M) (x : M) :
    appendEquiv R M n (tprod R m ⊗ₜ[R] x) = tprod R (Fin.snoc m x) := by
  simp only [appendEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, PiTensorProduct.subsingletonEquiv_symm_apply']
  simpa only [gMul_def, Fin.append_right_eq_snoc] using
    (tprod_mul_tprod R m (fun _ : Fin 1 => x))

/-- Splitting a pure tensor separates its initial tuple from its last factor. -/
@[simp]
theorem appendEquiv_symm_tprod (n : ℕ) (m : Fin (n + 1) → M) :
    (appendEquiv R M n).symm (tprod R m) =
      tprod R (fun i => m i.castSucc) ⊗ₜ[R] m (Fin.last n) := by
  apply (appendEquiv R M n).injective
  rw [LinearEquiv.apply_symm_apply, appendEquiv_tprod]
  exact congrArg (tprod R) (Fin.snoc_init_self m).symm

/-- The canonical scalar-extension equivalence for tensor powers of a semimodule.

The zeroth-degree comparison is the scalar-unit equivalence. In successor degrees,
we split off the last factor and use `TensorProduct.AlgebraTensorModule.distribBaseChange`.
-/
def baseChangeEquiv (R : Type uR) (S : Type uS) [CommSemiring R] [CommSemiring S]
    [Algebra R S] (n : ℕ) (M : Type uM) [AddCommMonoid M] [Module R M] :
    S ⊗[R] TensorPower R n M ≃ₗ[S] TensorPower S n (S ⊗[R] M) :=
  match n with
  | 0 =>
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
        (PiTensorProduct.isEmptyEquiv (R := R) (s := fun _ : Fin 0 => M) (Fin 0))).trans
        ((TensorProduct.AlgebraTensorModule.rid R S S).trans
          (PiTensorProduct.isEmptyEquiv (R := S)
            (s := fun _ : Fin 0 => S ⊗[R] M) (Fin 0)).symm)
  | n + 1 =>
      (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl S S) (appendEquiv R M n).symm).trans
        ((TensorProduct.AlgebraTensorModule.distribBaseChange R S (TensorPower R n M) M).trans
          ((TensorProduct.congr (baseChangeEquiv R S n M)
            (LinearEquiv.refl S (S ⊗[R] M))).trans
              (appendEquiv S (S ⊗[R] M) n)))

variable (S : Type uS) [CommSemiring S] [Algebra R S]

/-- Scalar extension sends a pure tensor power to the tensor power of the canonical images,
with the original coefficient acting on the result. This also holds in degree zero. -/
@[simp]
theorem baseChangeEquiv_tmul_tprod (n : ℕ) (s : S) (m : Fin n → M) :
    baseChangeEquiv R S n M (s ⊗ₜ[R] tprod R m) =
      s • tprod S (fun i => (1 : S) ⊗ₜ[R] m i) := by
  induction n with
  | zero =>
      apply (PiTensorProduct.isEmptyEquiv (R := S)
        (s := fun _ : Fin 0 => S ⊗[R] M) (Fin 0)).injective
      simp only [baseChangeEquiv, LinearEquiv.trans_apply,
        TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
        PiTensorProduct.isEmptyEquiv_apply_tprod, TensorProduct.AlgebraTensorModule.rid_tmul,
        one_smul, LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul]
      exact (_root_.mul_one s).symm
  | succ n ih =>
      simp only [baseChangeEquiv, LinearEquiv.trans_apply,
        TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
        appendEquiv_symm_tprod, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        TensorProduct.congr_tmul, ih]
      rw [← TensorProduct.smul_tmul', map_smul, appendEquiv_tprod]
      apply congrArg (fun v : Fin (n + 1) → S ⊗[R] M => s • tprod S v)
      funext i
      cases i using Fin.lastCases <;> simp

/-- In the inverse comparison, the coefficients of arbitrary pure factors multiply.
The empty product in degree zero is `1`. -/
@[simp]
theorem baseChangeEquiv_symm_tprod (n : ℕ) (a : Fin n → S) (m : Fin n → M) :
    (baseChangeEquiv R S n M).symm (tprod S (fun i => a i ⊗ₜ[R] m i)) =
      (∏ i, a i) ⊗ₜ[R] tprod R m := by
  apply (baseChangeEquiv R S n M).symm_apply_eq.mpr
  rw [baseChangeEquiv_tmul_tprod]
  calc
    tprod S (fun i => a i ⊗ₜ[R] m i) =
        tprod S (fun i => a i • ((1 : S) ⊗ₜ[R] m i)) := by
      congr 1
      funext i
      exact TensorProduct.tmul_eq_smul_one_tmul (a i) (m i)
    _ = (∏ i, a i) • tprod S (fun i => (1 : S) ⊗ₜ[R] m i) :=
      (tprod S).map_smul_univ a (fun i => (1 : S) ⊗ₜ[R] m i)

variable {M} {N : Type uN} [AddCommMonoid N] [Module R N]

/-- The tensor-power scalar-extension comparison is natural in the semimodule. -/
theorem baseChangeEquiv_naturality (n : ℕ) (f : M →ₗ[R] N) :
    (baseChangeEquiv R S n N).toLinearMap.comp
        ((PiTensorProduct.map fun _ : Fin n => f).baseChange S) =
      (PiTensorProduct.map fun _ : Fin n => f.baseChange S).comp
        (baseChangeEquiv R S n M).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  apply LinearMap.ext
  intro s
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro m
  simp

end TensorPower
