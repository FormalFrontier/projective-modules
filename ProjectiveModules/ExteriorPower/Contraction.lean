/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Contraction on exterior powers

Contraction lowers the exact word powers of the submodule of generators in a Clifford algebra.
For the zero quadratic form this gives a canonical linear family of maps between consecutive
exterior powers, using the existing submodules of the exterior algebra.

## Main definitions and results

* `CliffordAlgebra.contractLeft_mem_pow`: contraction sends the `(n + 1)`st word power of
  the generators into the `n`th word power, for every quadratic form.
* `exteriorPower.contractLeft`: the restriction of contraction to consecutive exterior powers,
  linear in the contracting functional.
* `exteriorPower.coe_contractLeft`: the restricted map has exactly the value of the ambient
  contraction.
* `exteriorPower.contractLeft_existsUnique`: the restriction is uniquely characterized by its
  ambient values.
* `exteriorPower.map_contractLeft` and `exteriorPower.map_comp_contractLeft`: contraction is
  natural under every linear map, with pullback of the contracting functional.
* `exteriorPower.contractLeft_comp_self` and `exteriorPower.contractLeft_comp_comm`: the
  restricted maps square to zero and anticommute, including in characteristic two.

The word-power statement does not assert an `ℕ`-grading for a general Clifford algebra.
In degree zero its target is the submodule of scalars, not the zero submodule.

## References

This development uses Mathlib's Clifford contraction formalization by Eric Wieser and its
existing exterior-power submodules; it does not construct a new ambient contraction.
-/

@[expose] public section

universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace CliffordAlgebra

/-- Contraction lowers exact word powers of the submodule of Clifford generators.
The zeroth power on the right is the submodule of scalars. -/
theorem contractLeft_mem_pow (Q : QuadraticForm R M) (ell : Module.Dual R M) (n : ℕ)
    {x : CliffordAlgebra Q} (hx : x ∈ (LinearMap.range (ι Q)) ^ (n + 1)) :
    contractLeft (Q := Q) ell x ∈ (LinearMap.range (ι Q)) ^ n := by
  induction n generalizing x with
  | zero =>
    simp only [zero_add, pow_one] at hx
    obtain ⟨m, rfl⟩ := hx
    rw [contractLeft_ι, pow_zero]
    exact Submodule.algebraMap_mem _
  | succ n ih =>
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · rintro a ⟨m, rfl⟩ b hb
      rw [contractLeft_ι_mul]
      refine Submodule.sub_mem _ (Submodule.smul_mem _ _ hb) ?_
      rw [pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ m) (ih hb)
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb

end CliffordAlgebra

namespace exteriorPower

/-- Contraction on consecutive exterior powers, linear in the contracting functional.
It is the restriction of Mathlib's contraction for the zero quadratic form. -/
noncomputable def contractLeft (n : ℕ) :
    Module.Dual R M →ₗ[R] (⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M) where
  toFun ell := (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) ell).restrict
    (fun _ hx => CliffordAlgebra.contractLeft_mem_pow (0 : QuadraticForm R M) ell n hx)
  map_add' ell mu := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) (ell + mu)
        (x : ExteriorAlgebra R M) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) ell
          (x : ExteriorAlgebra R M) +
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) mu
          (x : ExteriorAlgebra R M)
    simp only [map_add, LinearMap.add_apply]
  map_smul' r ell := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) (r • ell)
        (x : ExteriorAlgebra R M) =
      r • CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) ell
        (x : ExteriorAlgebra R M)
    simp only [map_smul, LinearMap.smul_apply]

/-- The restricted contraction has exactly the value of the ambient Clifford contraction. -/
@[simp]
theorem coe_contractLeft (n : ℕ) (ell : Module.Dual R M) (x : ⋀[R]^(n + 1) M) :
    (contractLeft n ell x : ExteriorAlgebra R M) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) ell
        (x : ExteriorAlgebra R M) :=
  rfl

/-- The canonical restriction is the unique linear map with the prescribed ambient values. -/
theorem contractLeft_existsUnique (ell : Module.Dual R M) (n : ℕ) :
    ∃! F : (⋀[R]^(n + 1) M) →ₗ[R] (⋀[R]^n M),
      ∀ x : ⋀[R]^(n + 1) M,
        (F x : ExteriorAlgebra R M) =
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) ell
            (x : ExteriorAlgebra R M) := by
  refine ⟨contractLeft n ell, fun x => coe_contractLeft n ell x, ?_⟩
  intro F hF
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact (hF x).trans (coe_contractLeft n ell x).symm

/-- Consecutive restricted contractions by the same functional compose to zero.
This is inherited from the ambient square-zero theorem, without assumptions on characteristic. -/
@[simp]
theorem contractLeft_comp_self (n : ℕ) (ell : Module.Dual R M) :
    (contractLeft n ell).comp (contractLeft (n + 1) ell) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (contractLeft n ell (contractLeft (n + 1) ell x) : ExteriorAlgebra R M) = 0
  simp only [coe_contractLeft, CliffordAlgebra.contractLeft_contractLeft]

/-- Restricted contractions anticommute, by the corresponding ambient contraction identity. -/
theorem contractLeft_comp_comm (n : ℕ) (ell mu : Module.Dual R M) :
    (contractLeft n ell).comp (contractLeft (n + 1) mu) =
      -(contractLeft n mu).comp (contractLeft (n + 1) ell) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (contractLeft n ell (contractLeft (n + 1) mu x) : ExteriorAlgebra R M) =
    -(contractLeft n mu (contractLeft (n + 1) ell x) : ExteriorAlgebra R M)
  simpa only [coe_contractLeft] using
    (CliffordAlgebra.contractLeft_comm (Q := (0 : QuadraticForm R M)) ell mu
      (x : ExteriorAlgebra R M))

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Restricted contraction is natural under every linear map, with pullback of the covector. -/
theorem map_contractLeft (n : ℕ) (f : M →ₗ[R] N) (ell : Module.Dual R N)
    (x : ⋀[R]^(n + 1) M) :
    map n f (contractLeft n (ell.comp f) x) = contractLeft n ell (map (n + 1) f x) := by
  apply Subtype.ext
  simpa only [coe_map, coe_contractLeft] using
    (ExteriorAlgebra.map_contractLeft f ell (x : ExteriorAlgebra R M))

/-- Naturality of restricted contraction as an equality of linear maps. -/
theorem map_comp_contractLeft (n : ℕ) (f : M →ₗ[R] N) (ell : Module.Dual R N) :
    (map n f).comp (contractLeft n (ell.comp f)) =
      (contractLeft n ell).comp (map (n + 1) f) := by
  apply LinearMap.ext
  intro x
  exact map_contractLeft n f ell x

end exteriorPower
