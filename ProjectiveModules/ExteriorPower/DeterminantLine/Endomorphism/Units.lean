/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine.Stabilization
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Finiteness.Projective

/-!
# Units and scalar determinants

An endomorphism of a finite projective module is a unit exactly when its scalar
determinant is a unit. The module need not have constant stalk rank or be faithful.

The converse extends the endomorphism by the identity along a split finite-free
presentation. It uses `Module.determinant_eq_det_stabilization`, Mathlib's
`LinearMap.isUnit_iff_isUnit_det`, and `Module.End.isUnit_iff`.

## References

For determinants of finite projective modules, see C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*.
-/

@[expose] public section

universe u v

namespace Module

/-- An endomorphism of a finite projective module is a unit if and only if its
scalar determinant is a unit.

This extends `LinearMap.isUnit_iff_isUnit_det` using finite-free stabilization.
For the finite projective determinant, see C. A. Weibel, *The K-book*. -/
theorem isUnit_iff_isUnit_determinant
    (R : Type u) (P : Type v) [CommRing R]
    [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P) :
    IsUnit f ↔ IsUnit (Module.determinant R P f) := by
  constructor
  · intro hf
    exact IsUnit.map (determinant R P) hf
  · intro hf
    obtain ⟨n, p, j, hp, hj, hpj⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective R P
    let γ : Module.End R (Fin n → R) :=
      j.comp (f.comp p) + (LinearMap.id - j.comp p)
    have hγ : IsUnit γ := by
      apply (LinearMap.isUnit_iff_isUnit_det γ).2
      change IsUnit (LinearMap.det (j.comp (f.comp p) + (LinearMap.id - j.comp p)))
      rw [← determinant_eq_det_stabilization R P (Fin n → R) f p j hpj]
      exact hf
    have hγbij := (Module.End.isUnit_iff γ).1 hγ
    have hγj : γ.comp j = j.comp f := by
      dsimp only [γ]
      simp only [LinearMap.add_comp, LinearMap.sub_comp, LinearMap.comp_assoc,
        hpj, LinearMap.id_comp, LinearMap.comp_id, sub_self, add_zero]
    have hpγ : p.comp γ = f.comp p := by
      dsimp only [γ]
      simp only [LinearMap.comp_add, LinearMap.comp_sub, ← LinearMap.comp_assoc,
        hpj, LinearMap.id_comp, LinearMap.comp_id, sub_self, add_zero]
    apply (Module.End.isUnit_iff f).2
    constructor
    · intro x y hxy
      apply hj
      apply hγbij.1
      calc
        γ (j x) = j (f x) := LinearMap.congr_fun hγj x
        _ = j (f y) := congrArg j hxy
        _ = γ (j y) := (LinearMap.congr_fun hγj y).symm
    · intro y
      obtain ⟨x, hx⟩ := hp y
      obtain ⟨z, hz⟩ := hγbij.2 x
      refine ⟨p z, ?_⟩
      calc
        f (p z) = p (γ z) := (LinearMap.congr_fun hpγ z).symm
        _ = p x := congrArg p hz
        _ = y := hx

end Module
