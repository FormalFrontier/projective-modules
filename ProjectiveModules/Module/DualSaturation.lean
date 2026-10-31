/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.FiniteFactorization
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Saturation by dual evaluations

For a projective module, nonzero tensor fibers at every maximal ideal force any ideal
containing all global dual evaluations to be the unit ideal. Neither finite generation
nor a rank-one hypothesis is required.

The proof uses elementwise finite-free factorization. A finite coordinate expansion
shows that every pure tensor over an ideal quotient vanishes if all dual evaluations
lie in that ideal. Maximal containment then gives the saturation theorem.

This is the saturation step in the projective rank-one finiteness argument associated
with Exercise I.2.13 of Weibel's *The K-book*. Finite-free factorization and the linear
and tensor coordinate identities are supplied by the existing projective-module and
Mathlib APIs.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter I, §2.
-/

@[expose] public section

universe u v

open scoped BigOperators TensorProduct

namespace Module.Projective

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommMonoid P] [Module R P] [Module.Projective R P]

private theorem quotient_tmul_eq_zero_of_forall_dual_apply_mem
    (J : Ideal R) (hJ : ∀ (φ : P →ₗ[R] R) (x : P), φ x ∈ J)
    (a : R ⧸ J) (x : P) : a ⊗ₜ[R] x = 0 := by
  classical
  obtain ⟨n, A, B, hAB⟩ := exists_finite_free_factorization_at (R := R) (P := P) x
  have hsum : (∑ i : Fin n, Pi.single i ((B x) i)) = B x :=
    LinearMap.sum_single_apply (fun _ : Fin n => R) (B x)
  calc
    a ⊗ₜ[R] x = a ⊗ₜ[R] A (B x) := by rw [hAB]
    _ = a ⊗ₜ[R] A (∑ i : Fin n, Pi.single i ((B x) i)) := by rw [hsum]
    _ = ∑ i : Fin n, a ⊗ₜ[R] A (Pi.single i ((B x) i)) := by
      rw [map_sum, TensorProduct.tmul_sum]
    _ = 0 := Finset.sum_eq_zero fun i _ => by
      have hcoeff : (B x) i ∈ J := by
        simpa only [LinearMap.comp_apply, LinearMap.proj_apply] using
          hJ ((LinearMap.proj i : (Fin n → R) →ₗ[R] R).comp B) x
      have hquot : Ideal.Quotient.mk J ((B x) i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hcoeff
      have hscale : (B x) i • a = 0 := by
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, hquot, zero_mul]
      have hsingle : Pi.single i ((B x) i) = (B x) i • Pi.single i (1 : R) := by
        simpa only [LinearMap.single_apply, smul_eq_mul, mul_one] using
          (LinearMap.single R (fun _ : Fin n => R) i).map_smul ((B x) i) (1 : R)
      rw [hsingle, map_smul, ← TensorProduct.smul_tmul, hscale, TensorProduct.zero_tmul]

/-- If every maximal residue tensor fiber of a projective module is nonzero, any ideal
containing all values of all global dual functionals is the unit ideal.

This statement does not require finite generation or a rank-one hypothesis, and also
applies over the zero ring. -/
theorem ideal_eq_top_of_forall_dual_apply_mem
    (hfib : ∀ (m : Ideal R) [m.IsMaximal], Nontrivial ((R ⧸ m) ⊗[R] P))
    (J : Ideal R) (hJ : ∀ (φ : P →ₗ[R] R) (x : P), φ x ∈ J) : J = ⊤ := by
  classical
  by_contra hproper
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hproper
  let : m.IsMaximal := hm
  have hpure (a : R ⧸ m) (x : P) : a ⊗ₜ[R] x = 0 :=
    quotient_tmul_eq_zero_of_forall_dual_apply_mem m (fun φ y => hJm (hJ φ y)) a x
  have hzero (z : (R ⧸ m) ⊗[R] P) : z = 0 := by
    refine TensorProduct.inductionOn z hpure ?_
    intro a b ha hb
    rw [ha, hb, add_zero]
  obtain ⟨a, b, hab⟩ := (hfib m).exists_pair_ne
  exact hab ((hzero a).trans (hzero b).symm)

end Module.Projective
