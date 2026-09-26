/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import ProjectiveModules.Invertible.Endomorphism

/-!
# Determinants from invertible exterior powers

This file defines the determinant of a module endomorphism whenever the
relevant exterior power is invertible. The induced exterior-power map is an
endomorphism of an invertible module, hence multiplication by a unique scalar.

No finite, projective, free, or rank hypothesis on the original module is
needed once invertibility of the exterior power is supplied.
-/

@[expose] public section

noncomputable section

universe u v

namespace exteriorPower

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Functoriality packages the `n`th exterior-power map as a monoid
homomorphism on module endomorphisms. -/
noncomputable def mapEndomorphismMonoidHom (n : ℕ) :
    Module.End R M →* Module.End R (⋀[R]^n M) where
  toFun := map n
  map_one' := by
    change map n (LinearMap.id (R := R) (M := M)) = LinearMap.id
    exact map_id
  map_mul' f g := by
    simp only [Module.End.mul_eq_comp]
    exact map_comp g f

/-- The determinant scalar obtained from the induced action on an invertible
exterior power. -/
noncomputable def determinant (n : ℕ) [Module.Invertible R (⋀[R]^n M)] :
    Module.End R M →* R :=
  (Module.Invertible.toModuleEndRingEquiv R (⋀[R]^n M)).symm.toMonoidHom.comp
    (mapEndomorphismMonoidHom R M n)

/-- The determinant is the scalar corresponding to the induced exterior-power
endomorphism. -/
theorem determinant_apply (n : ℕ) [Module.Invertible R (⋀[R]^n M)]
    (f : Module.End R M) :
    determinant R M n f =
      (Module.Invertible.toModuleEndRingEquiv R (⋀[R]^n M)).symm (map n f) :=
  rfl

/-- The induced exterior-power endomorphism is scalar multiplication by its
determinant. -/
theorem map_eq_smul_determinant (n : ℕ) [Module.Invertible R (⋀[R]^n M)]
    (f : Module.End R M) (x : ⋀[R]^n M) :
    map n f x = determinant R M n f • x := by
  let e := Module.Invertible.toModuleEndRingEquiv R (⋀[R]^n M)
  change map n f x = e (e.symm (map n f)) x
  exact DFunLike.congr_fun (e.apply_symm_apply (map n f)).symm x

/-- A scalar is the determinant exactly when it induces the exterior-power
map. -/
theorem determinant_eq_iff_map_eq_smul (n : ℕ)
    [Module.Invertible R (⋀[R]^n M)] (f : Module.End R M) (r : R) :
    determinant R M n f = r ↔ ∀ x : ⋀[R]^n M, map n f x = r • x := by
  constructor
  · rintro rfl x
    exact map_eq_smul_determinant R M n f x
  · intro h
    let e := Module.Invertible.toModuleEndRingEquiv R (⋀[R]^n M)
    apply e.injective
    change e (e.symm (map n f)) = e r
    rw [e.apply_symm_apply]
    apply LinearMap.ext
    intro x
    exact h x

/-- The determinant of the identity endomorphism is one. -/
@[simp] theorem determinant_id (n : ℕ) [Module.Invertible R (⋀[R]^n M)] :
    determinant R M n LinearMap.id = 1 := by
  exact (determinant R M n).map_one

/-- Determinants multiply under composition. -/
theorem determinant_comp (n : ℕ) [Module.Invertible R (⋀[R]^n M)]
    (f g : Module.End R M) :
    determinant R M n (f.comp g) =
      determinant R M n f * determinant R M n g := by
  simpa only [Module.End.mul_eq_comp] using (determinant R M n).map_mul f g

end exteriorPower
