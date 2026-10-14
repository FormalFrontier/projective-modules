/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.ProjectiveKernel
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Split kernels over a semiring without additive inverses

The coefficient semiring `ℕ × ℤ` has no additive inverse of one. Restricting
scalars on `ℤ` along the second projection gives group-valued modules over
this semiring. The product projection has a nonzero target and nonzero kernel.
Finiteness and projectivity of the source are obtained independently from
Mathlib's regular module, restricted-scalar map and split-retract APIs.
-/

namespace ProjectiveModulesTests.SplitKernel.MixedProduct

abbrev R₀ := ℕ × ℤ

-- Only the library's canonical action restricted along snd; no new Module operations.
local instance : Module R₀ ℤ := Module.compHom ℤ (RingHom.snd ℕ ℤ)

example (a : R₀) (z : ℤ) : a • z = a.2 * z := rfl

-- The canonical addition cannot be ring addition: even 1 has no additive inverse.
lemma no_add_inverse_one : ¬ ∃ a : R₀, (1 : R₀) + a = 0 := by
  rintro ⟨a, h⟩
  have hfst : (1 : ℕ) + a.1 = 0 := congrArg (fun x : R₀ ↦ x.1) h
  rw [Nat.add_comm] at hfst
  exact Nat.succ_ne_zero a.1 hfst

-- Reuse the existing producer, rather than redefine the canonical linear map.
abbrev r₀ : R₀ →ₗ[R₀] ℤ := Module.compHom.toLinearMap (RingHom.snd ℕ ℤ)

lemma r₀_surjective : Function.Surjective r₀ := fun z ↦ ⟨(0, z), rfl⟩

-- A supported coordinate inclusion, not a unital homomorphism into R₀.
def i₀ : ℤ →ₗ[R₀] R₀ where
  toFun := fun z ↦ (0, z)
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun a _ ↦ Prod.ext (mul_zero a.1).symm rfl

lemma r₀_comp_i₀ : r₀.comp i₀ = LinearMap.id := rfl

def f : (ℤ × ℤ) →ₗ[R₀] ℤ := LinearMap.fst R₀ ℤ ℤ
def i : ℤ →ₗ[R₀] (ℤ × ℤ) := LinearMap.inl R₀ ℤ ℤ

lemma f_comp_i : f.comp i = LinearMap.id := LinearMap.fst_comp_inl R₀ ℤ ℤ
lemma f_surjective : Function.Surjective f := fun z ↦ ⟨(z, 0), rfl⟩

def k : LinearMap.ker f := ⟨(0, 1), rfl⟩

example : k ≠ 0 :=
  fun h ↦ one_ne_zero (congrArg (fun x : LinearMap.ker f ↦ x.val.2) h)

-- The kernel and target coordinates are both nonzero in this decomposition.
example : LinearMap.kerProdEquivOfRightInverse f i f_comp_i (k, 3) = (3, 1) := by
  simp [k, i]

example : (LinearMap.kerProdEquivOfRightInverse f i f_comp_i).symm (3, 1) =
    (k, 3) := by
  apply Prod.ext
  · apply Subtype.ext
    rw [LinearMap.kerProdEquivOfRightInverse_symm_fst]
    simp [f, i, k]
  · rw [LinearMap.kerProdEquivOfRightInverse_symm_snd]
    simp [f]

example :
    ((LinearMap.kerProdEquivOfRightInverse f i f_comp_i).symm (3, 1)).1 ≠ 0 ∧
      ((LinearMap.kerProdEquivOfRightInverse f i f_comp_i).symm (3, 1)).2 ≠ 0 := by
  constructor
  · intro h
    have hsnd := congrArg (fun k : LinearMap.ker f ↦ k.val.2) h
    rw [LinearMap.kerProdEquivOfRightInverse_symm_fst] at hsnd
    simp [f, i] at hsnd
  · rw [LinearMap.kerProdEquivOfRightInverse_symm_snd]
    simp [f]

example (x : ℤ × ℤ) :
    ((LinearMap.kerProdEquivOfRightInverse f i f_comp_i).symm x).1.val =
      (0, x.2) := by
  rw [LinearMap.kerProdEquivOfRightInverse_symm_fst]
  apply Prod.ext <;> simp [f, i]

example (x : ℤ × ℤ) :
    ((LinearMap.kerProdEquivOfRightInverse f i f_comp_i).symm x).2 = x.1 := by
  rw [LinearMap.kerProdEquivOfRightInverse_symm_snd]
  rfl

-- The natural-number coordinate of the scalar does not act on this source.
example : LinearMap.kerProdEquivOfRightInverse f i f_comp_i
    (((5, 2) : R₀) • (k, 3)) = (6, 2) := by
  rw [map_smul]
  have h : LinearMap.kerProdEquivOfRightInverse f i f_comp_i (k, 3) = (3, 1) := by
    simp [k, i]
  rw [h]
  rfl

example :
    LinearMap.kerProdEquivOfRightInverse f i f_comp_i
        ((LinearMap.kerProdEquivOfRightInverse f i f_comp_i).symm (3, 1)) = (3, 1) ∧
      (LinearMap.kerProdEquivOfRightInverse f i f_comp_i).symm
        (LinearMap.kerProdEquivOfRightInverse f i f_comp_i (k, 3)) = (k, 3) :=
  ⟨LinearEquiv.apply_symm_apply _ _, LinearEquiv.symm_apply_apply _ _⟩

-- The characteristic projection API is used without unfolding its definition.
def π : (ℤ × ℤ) →ₗ[R₀] LinearMap.ker f :=
  LinearMap.splitKernelProjection i f f_comp_i

example (x : ℤ × ℤ) : (π x : ℤ × ℤ) = x - i (f x) :=
  LinearMap.splitKernelProjection_apply i f f_comp_i x

example : π.comp (LinearMap.ker f).subtype = LinearMap.id :=
  LinearMap.splitKernelProjection_comp_subtype i f f_comp_i

example : (π (3, 1), f (3, 1)) = (k, 3) := by
  have h := LinearMap.congr_fun
    (LinearMap.splitKernelProjection_prod_eq_kerProdEquivOfRightInverse_symm
      f i f_comp_i) (3, 1)
  calc
    (π (3, 1), f (3, 1)) =
        (LinearMap.kerProdEquivOfRightInverse f i f_comp_i).symm (3, 1) := h
    _ = (k, 3) := by
      apply Prod.ext
      · apply Subtype.ext
        rw [LinearMap.kerProdEquivOfRightInverse_symm_fst]
        simp [f, i, k]
      · rw [LinearMap.kerProdEquivOfRightInverse_symm_snd]
        simp [f]

example (k : LinearMap.ker f) : π k = k :=
  LinearMap.splitKernelProjection_apply_coe i f f_comp_i k

section FiniteSource

-- The source is finite as the image of the regular module, then a product.
local instance : Module.Finite R₀ ℤ := Module.Finite.of_surjective r₀ r₀_surjective
example : Module.Finite R₀ (ℤ × ℤ) := inferInstance

example : Module.Finite R₀ (LinearMap.ker f) :=
  LinearMap.finite_splitKernel i f f_comp_i

end FiniteSource

section ProjectiveSource

-- No local finiteness instance is in scope here. The regular ambient R₀ is only
-- an additive monoid; the split-retract theorem does not require it to be a group.
local instance : Module.Projective R₀ ℤ := Module.Projective.of_split i₀ r₀ r₀_comp_i₀
example : Module.Projective R₀ (ℤ × ℤ) := inferInstance

-- Projectivity of the kernel does not use the finite-source instance above.
example : Module.Projective R₀ (LinearMap.ker f) :=
  LinearMap.projective_splitKernel i f f_comp_i

end ProjectiveSource
end ProjectiveModulesTests.SplitKernel.MixedProduct

namespace ProjectiveModulesTests.SplitKernel.OppositeMatrices

-- Mathlib's matrix units and regular-module instances supply the coefficient data.
private abbrev A := Matrix (Fin 2) (Fin 2) ℤ
private abbrev R := Aᵐᵒᵖ
private def e00 : A := Matrix.single 0 0 1
private def e01 : A := Matrix.single 0 1 1

private theorem e01_mul_e00 : e01 * e00 = 0 := by simp [e01, e00]
private theorem e00_mul_e01 : e00 * e01 = e01 := by simp [e00, e01]
private theorem e01_ne_zero : e01 ≠ 0 := by
  intro h
  have hentry : (1 : ℤ) = 0 := by
    simpa [e01] using congrArg (fun a : A ↦ a 0 1) h
  exact one_ne_zero hentry

-- Left multiplication in R becomes right multiplication after unop.
example (a x : R) : MulOpposite.unop (a • x) =
    MulOpposite.unop x * MulOpposite.unop a := rfl

example : MulOpposite.unop ((MulOpposite.op e00 : R) • MulOpposite.op e01) ≠
    e00 * e01 := by
  change e01 * e00 ≠ e00 * e01
  rw [e01_mul_e00, e00_mul_e01]
  exact Ne.symm e01_ne_zero

private def f : (R × R) →ₗ[R] R := LinearMap.snd R R R
private def s : R →ₗ[R] (R × R) := LinearMap.inr R R R
private theorem f_comp_s : f.comp s = LinearMap.id := LinearMap.snd_comp_inr R R R
private def π : (R × R) →ₗ[R] LinearMap.ker f :=
  LinearMap.splitKernelProjection s f f_comp_s

private theorem projection_apply (x : R × R) : (π x : R × R) = (x.1, 0) := by
  calc
    (π x : R × R) = x - s (f x) :=
      LinearMap.splitKernelProjection_apply s f f_comp_s x
    _ = (x.1, 0) := Prod.ext (sub_zero _) (sub_self _)

private theorem projection_retract : π.comp (LinearMap.ker f).subtype = LinearMap.id :=
  LinearMap.splitKernelProjection_comp_subtype s f f_comp_s

example (k : LinearMap.ker f) : π k = k := LinearMap.congr_fun projection_retract k

example (y : R) : π (s y) = 0 := by
  apply Subtype.ext
  rw [projection_apply]
  rfl

private def x : R × R := (MulOpposite.op e01, MulOpposite.op e00)

example : (π x : R × R) = (MulOpposite.op e01, 0) := projection_apply x

example : f x ≠ 0 := by
  intro h
  have hentry : (1 : ℤ) = 0 := by
    simpa [f, x, e00] using congrArg (fun r : R ↦ MulOpposite.unop r 0 0) h
  exact one_ne_zero hentry

private theorem projection_x_ne_zero : π x ≠ 0 := by
  intro h
  have hval : (π x : R × R) = 0 := congrArg Subtype.val h
  rw [projection_apply] at hval
  exact e01_ne_zero (congrArg (fun z : R × R ↦ MulOpposite.unop z.1) hval)

example (a : R) : π (a • x) = a • π x := π.map_smul a x

example : π (MulOpposite.op e00 • x) = 0 := by
  apply Subtype.ext
  rw [projection_apply]
  exact Prod.ext (congrArg MulOpposite.op e01_mul_e00) rfl

-- The complementary diagonal coefficient has a nonzero ordered projection value.
example : MulOpposite.unop
    ((π (MulOpposite.op (Matrix.single 1 1 1 : A) • x) : R × R).1) = e01 ∧ e01 ≠ 0 := by
  refine ⟨?_, e01_ne_zero⟩
  rw [projection_apply]
  change e01 * Matrix.single 1 1 1 = e01
  simp [e01]

-- The input witnesses use only Mathlib's regular module and product instances.
example : Module.Free R R := inferInstance
private theorem source_finite : Module.Finite R (R × R) := inferInstance
private theorem source_projective : Module.Projective R (R × R) := inferInstance

example : Module.Finite R (LinearMap.ker f) := by
  let _ : Module.Finite R (R × R) := source_finite
  exact LinearMap.finite_splitKernel s f f_comp_s

example : Module.Projective R (LinearMap.ker f) := by
  let _ : Module.Projective R (R × R) := source_projective
  exact LinearMap.projective_splitKernel s f f_comp_s

end ProjectiveModulesTests.SplitKernel.OppositeMatrices
