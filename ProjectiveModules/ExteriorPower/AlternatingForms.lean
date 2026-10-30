/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.Duality

/-!
# Exterior powers of the dual and alternating forms

For a finite projective module, `exteriorPower.dualAlternatingEquiv` identifies the exterior
power of its dual with alternating scalar-valued forms. It is the composition of the
canonical determinant-pairing equivalence with Mathlib's universal property of the exterior
power. Evaluation and pullback therefore use the existing exterior power and alternating-map
constructions.

The determinant formula with functionals indexing rows holds for arbitrary modules, without
finiteness or projectivity assumptions. It follows from Mathlib's pairing formula by
invariance of the determinant under transpose.

## References

The determinant pairing and the exterior-power universal property are provided by Mathlib's
`Mathlib.LinearAlgebra.ExteriorPower.Pairing` and
`Mathlib.LinearAlgebra.ExteriorPower.Basic`.
-/

@[expose] public section

universe u v w

namespace exteriorPower

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The determinant pairing on pure wedges, with the functionals indexing rows.
This is Mathlib's determinant formula followed by `Matrix.det_transpose`. -/
theorem pairingDual_ιMulti_ιMulti_eq_det {n : ℕ}
    (φ : Fin n → Module.Dual R M) (x : Fin n → M) :
    pairingDual R M n (ιMulti R n φ) (ιMulti R n x) =
      Matrix.det (Matrix.of (fun i j ↦ φ i (x j))) := by
  rw [pairingDual_ιMulti_ιMulti]
  exact Matrix.det_transpose (Matrix.of (fun i j ↦ φ i (x j)))

/-- The canonical identification of exterior powers of the dual with alternating forms on a
finite projective module, using the determinant pairing and Mathlib's universal property. -/
noncomputable def dualAlternatingEquiv (n : ℕ) [Module.Finite R M] [Module.Projective R M] :
    (⋀[R]^n (Module.Dual R M)) ≃ₗ[R] AlternatingMap R M R (Fin n) :=
  (pairingDualEquiv R M n).trans
    (alternatingMapLinearEquiv (R := R) (M := M) (N := R) (n := n)).symm

variable {R M}

/-- Evaluation of the canonical alternating form is the determinant pairing with a pure wedge. -/
@[simp]
theorem dualAlternatingEquiv_apply [Module.Finite R M] [Module.Projective R M]
    {n : ℕ} (a : ⋀[R]^n (Module.Dual R M)) (x : Fin n → M) :
    dualAlternatingEquiv R M n a x = pairingDual R M n a (ιMulti R n x) := by
  simp only [dualAlternatingEquiv, LinearEquiv.trans_apply,
    alternatingMapLinearEquiv_symm_apply, LinearMap.compAlternatingMap_apply,
    pairingDualEquiv_apply]

/-- A pure wedge of functionals gives the alternating form with the usual row-indexed
determinant formula. -/
theorem dualAlternatingEquiv_ιMulti_apply [Module.Finite R M] [Module.Projective R M]
    {n : ℕ} (φ : Fin n → Module.Dual R M) (x : Fin n → M) :
    dualAlternatingEquiv R M n (ιMulti R n φ) x =
      Matrix.det (Matrix.of (fun i j ↦ φ i (x j))) := by
  rw [dualAlternatingEquiv_apply, pairingDual_ιMulti_ιMulti_eq_det]

/-- The exterior tensor representing an alternating form recovers the form under the
determinant pairing. -/
@[simp]
theorem pairingDual_dualAlternatingEquiv_symm_apply
    [Module.Finite R M] [Module.Projective R M] {n : ℕ}
    (form : AlternatingMap R M R (Fin n)) (x : Fin n → M) :
    pairingDual R M n ((dualAlternatingEquiv R M n).symm form) (ιMulti R n x) = form x := by
  have h := congrArg (fun ω : AlternatingMap R M R (Fin n) ↦ ω x)
    ((dualAlternatingEquiv R M n).apply_symm_apply form)
  simpa only [dualAlternatingEquiv_apply] using h

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Pullback of alternating forms corresponds to the exterior power of the ordinary dual
map. No invertibility assumption is needed on the underlying linear map. -/
theorem dualAlternatingEquiv_naturality
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    {n : ℕ} (f : M →ₗ[R] N) (a : ⋀[R]^n (Module.Dual R N)) :
    dualAlternatingEquiv R M n (map n f.dualMap a) =
      (dualAlternatingEquiv R N n a).compLinearMap f := by
  refine AlternatingMap.ext fun x ↦ ?_
  simp only [dualAlternatingEquiv_apply, AlternatingMap.compLinearMap_apply]
  have h := congrArg
    (fun g : (⋀[R]^n (Module.Dual R N)) →ₗ[R] Module.Dual R (⋀[R]^n M) ↦
      g a (ιMulti R n x))
    (pairingDual_naturality (R := R) (M := M) (N := N) (n := n) (f := f))
  simpa only [LinearMap.comp_apply, LinearMap.dualMap_apply, map_apply_ιMulti,
    Function.comp_def] using h

/-- The exterior tensor representing a pulled-back alternating form is obtained by applying
the exterior power of the ordinary dual map to its representing tensor. -/
theorem dualAlternatingEquiv_symm_compLinearMap
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    {n : ℕ} (f : M →ₗ[R] N) (form : AlternatingMap R N R (Fin n)) :
    map n f.dualMap ((dualAlternatingEquiv R N n).symm form) =
      (dualAlternatingEquiv R M n).symm (form.compLinearMap f) := by
  apply (dualAlternatingEquiv R M n).injective
  simpa only [LinearEquiv.apply_symm_apply] using
    (dualAlternatingEquiv_naturality f ((dualAlternatingEquiv R N n).symm form))

end exteriorPower
