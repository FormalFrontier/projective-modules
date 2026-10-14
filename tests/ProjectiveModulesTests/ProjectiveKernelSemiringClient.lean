/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.ProjectiveKernel
import Mathlib.Algebra.Ring.Prod
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

-- The characteristic projection API is used without unfolding its definition.
def π : (ℤ × ℤ) →ₗ[R₀] LinearMap.ker f :=
  LinearMap.splitKernelProjection i f f_comp_i

example (x : ℤ × ℤ) : (π x : ℤ × ℤ) = x - i (f x) :=
  LinearMap.splitKernelProjection_apply i f f_comp_i x

example : π.comp (LinearMap.ker f).subtype = LinearMap.id :=
  LinearMap.splitKernelProjection_comp_subtype i f f_comp_i

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
