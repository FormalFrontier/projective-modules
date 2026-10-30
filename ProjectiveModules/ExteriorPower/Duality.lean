/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Duality for exterior powers of finite projective modules

Mathlib's `exteriorPower.pairingDual` sends an exterior product of linear forms to
its determinant evaluation on exterior products of vectors. We prove its
contravariant naturality for arbitrary modules and bundle it as
`exteriorPower.pairingDualEquiv` for finite projective modules.

The proof of bijectivity splits a finite projective module off a finite free
module. Naturality transports the inverse of the finite-free determinant pairing
along this retraction. The inverse formula is also available for any supplied
retraction and compatible pairing equivalences; it does not require the retract
to have a chosen basis.

## References

The determinant pairing and its finite-free bijectivity theorem are reused from
Mathlib's `Mathlib.LinearAlgebra.ExteriorPower.Pairing` and
`Mathlib.LinearAlgebra.ExteriorPower.Basis`. The finite-free retraction is
`Module.Finite.exists_comp_eq_id_of_projective` from
`Mathlib.RingTheory.Finiteness.Projective`.
-/

@[expose] public section

universe u v w

namespace exteriorPower

section Naturality

variable (R : Type u) [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The determinant pairing is contravariantly natural in the module. -/
theorem pairingDual_naturality (n : ℕ) (f : M →ₗ[R] N) :
    (pairingDual R M n).comp (map n f.dualMap) =
      (map n f).dualMap.comp (pairingDual R N n) := by
  apply linearMap_ext
  apply AlternatingMap.ext
  intro φ
  apply linearMap_ext
  apply AlternatingMap.ext
  intro x
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    map_apply_ιMulti, pairingDual_ιMulti_ιMulti, LinearMap.dualMap_apply,
    Function.comp_apply]

/-- Naturality of the determinant pairing, evaluated on an exterior element of the dual. -/
theorem pairingDual_naturality_apply (n : ℕ) (f : M →ₗ[R] N)
    (a : ⋀[R]^n (Module.Dual R N)) :
    pairingDual R M n (map n f.dualMap a) =
      (map n f).dualMap (pairingDual R N n a) :=
  LinearMap.congr_fun (pairingDual_naturality R n f) a

end Naturality

section Retract

variable (R : Type u) [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {F : Type w} [AddCommGroup F] [Module R F]

/-- A retraction transports the inverse determinant pairing from the ambient module.
Both inverse identities use only naturality, the retraction identity, and the
supplied identification of the ambient pairing equivalence. -/
theorem pairingDual_inverse_of_retract (n : ℕ) (p : F →ₗ[R] M) (i : M →ₗ[R] F)
    (h : p.comp i = LinearMap.id)
    (eF : (⋀[R]^n (Module.Dual R F)) ≃ₗ[R] Module.Dual R (⋀[R]^n F))
    (heF : eF.toLinearMap = pairingDual R F n) :
    Function.LeftInverse
        ((map n i.dualMap).comp (eF.symm.toLinearMap.comp (map n p).dualMap))
        (pairingDual R M n) ∧
      Function.RightInverse
        ((map n i.dualMap).comp (eF.symm.toLinearMap.comp (map n p).dualMap))
        (pairingDual R M n) := by
  constructor
  · intro a
    change map n i.dualMap
      (eF.symm ((map n p).dualMap (pairingDual R M n a))) = a
    rw [← pairingDual_naturality_apply R n p, ← heF]
    change map n i.dualMap (eF.symm (eF (map n p.dualMap a))) = a
    rw [eF.symm_apply_apply]
    change ((map n i.dualMap).comp (map n p.dualMap)) a = a
    rw [← map_comp, LinearMap.dualMap_comp_dualMap, h,
      LinearMap.dualMap_id, map_id, LinearMap.id_apply]
  · intro b
    change pairingDual R M n
      (map n i.dualMap (eF.symm ((map n p).dualMap b))) = b
    rw [pairingDual_naturality_apply R n i, ← heF]
    change (map n i).dualMap (eF (eF.symm ((map n p).dualMap b))) = b
    rw [eF.apply_symm_apply]
    change ((map n i).dualMap.comp (map n p).dualMap) b = b
    rw [LinearMap.dualMap_comp_dualMap, ← map_comp, h, map_id,
      LinearMap.dualMap_id, LinearMap.id_apply]

/-- Bijectivity of the determinant pairing descends along a supplied module retraction. -/
theorem bijective_pairingDual_of_retract (n : ℕ) (p : F →ₗ[R] M) (i : M →ₗ[R] F)
    (h : p.comp i = LinearMap.id) (hF : Function.Bijective (pairingDual R F n)) :
    Function.Bijective (pairingDual R M n) := by
  let eF := LinearEquiv.ofBijective (pairingDual R F n) hF
  have hinv := pairingDual_inverse_of_retract R n p i h eF rfl
  exact ⟨hinv.1.injective, hinv.2.surjective⟩

/-- The inverse of any equivalence given by the determinant pairing is computed by
any supplied retraction and a compatible ambient pairing equivalence. -/
theorem pairingDual_symm_toLinearMap_of_retract (n : ℕ)
    (p : F →ₗ[R] M) (i : M →ₗ[R] F) (h : p.comp i = LinearMap.id)
    (eM : (⋀[R]^n (Module.Dual R M)) ≃ₗ[R] Module.Dual R (⋀[R]^n M))
    (heM : eM.toLinearMap = pairingDual R M n)
    (eF : (⋀[R]^n (Module.Dual R F)) ≃ₗ[R] Module.Dual R (⋀[R]^n F))
    (heF : eF.toLinearMap = pairingDual R F n) :
    eM.symm.toLinearMap =
      (map n i.dualMap).comp (eF.symm.toLinearMap.comp (map n p).dualMap) := by
  have hright := (pairingDual_inverse_of_retract R n p i h eF heF).2
  apply LinearMap.ext
  intro b
  apply eM.injective
  change eM (eM.symm b) =
    eM.toLinearMap (map n i.dualMap (eF.symm ((map n p).dualMap b)))
  rw [eM.apply_symm_apply, heM]
  exact (hright b).symm

end Retract

section FiniteProjective

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]

/-- The determinant pairing for a finite projective module is bijective over any
commutative ring. The proof uses Mathlib's finite-free splitting theorem and its
finite-free bijectivity theorem for the same determinant pairing. -/
theorem bijective_pairingDual_of_projective (n : ℕ) :
    Function.Bijective (pairingDual R M n) := by
  obtain ⟨r, p, i, _, _, h⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact bijective_pairingDual_of_retract R n p i h
    (bijective_pairingDual R (Fin r → R) n)

/-- The canonical determinant-pairing equivalence for a finite projective module. -/
noncomputable def pairingDualEquiv (n : ℕ) :
    (⋀[R]^n (Module.Dual R M)) ≃ₗ[R] Module.Dual R (⋀[R]^n M) :=
  LinearEquiv.ofBijective (pairingDual R M n) (bijective_pairingDual_of_projective R M n)

/-- The underlying map of `pairingDualEquiv` is Mathlib's determinant pairing. -/
@[simp]
theorem pairingDualEquiv_toLinearMap (n : ℕ) :
    (pairingDualEquiv R M n).toLinearMap = pairingDual R M n :=
  rfl

/-- Evaluation of the canonical equivalence agrees with Mathlib's determinant pairing. -/
@[simp]
theorem pairingDualEquiv_apply (n : ℕ) (a : ⋀[R]^n (Module.Dual R M)) :
    pairingDualEquiv R M n a = pairingDual R M n a :=
  rfl

/-- A supplied retraction computes the inverse of the canonical determinant-pairing
equivalence without choosing a basis of the finite projective module. -/
theorem pairingDualEquiv_symm_toLinearMap_of_retract
    {F : Type w} [AddCommGroup F] [Module R F] (n : ℕ)
    (p : F →ₗ[R] M) (i : M →ₗ[R] F) (h : p.comp i = LinearMap.id)
    (eF : (⋀[R]^n (Module.Dual R F)) ≃ₗ[R] Module.Dual R (⋀[R]^n F))
    (heF : eF.toLinearMap = pairingDual R F n) :
    (pairingDualEquiv R M n).symm.toLinearMap =
      (map n i.dualMap).comp (eF.symm.toLinearMap.comp (map n p).dualMap) :=
  pairingDual_symm_toLinearMap_of_retract R n p i h
    (pairingDualEquiv R M n) (pairingDualEquiv_toLinearMap R M n) eF heF

end FiniteProjective

end exteriorPower
