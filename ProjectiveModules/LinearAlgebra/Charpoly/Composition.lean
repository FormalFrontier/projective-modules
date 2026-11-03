/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Nontriviality

/-!
# Characteristic polynomials of rectangular compositions

For maps `f : P →ₗ[R] Q` and `g : Q →ₗ[R] P` between finite projective modules,
`Module.charpoly_comp_mul_charpoly_zero` relates the characteristic polynomials
of `g.comp f` and `f.comp g`, retaining the characteristic polynomials of the zero
endomorphisms as stabilizing factors. Thus no constant-rank or freeness assumption
is needed. Its rank-one consequence is `Module.charpoly_smulRight_mul_X`.

The proof compares two triangular endomorphisms of `P × Q` by Mathlib's
`LinearEquiv.skewProd`. Their characteristic polynomials are computed using
`Module.charpoly_eq_mul_of_exact` for the standard split sequence, and the
comparison uses `Module.charpoly_eq_of_intertwining`.

## References

* Mathlib's `Matrix.charpoly_mul_comm'` and `Matrix.charpoly_vecMulVec` in
  `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`, for the matrix statements and
  the block-triangular formalization approach.
* The block-matrix argument at https://math.stackexchange.com/a/311362/315369,
  credited in Mathlib's proof of `Matrix.charpoly_mul_comm'`.
* The intrinsic characteristic polynomial, intertwining invariance, and
  short-exact multiplicativity in `ProjectiveModules.LinearAlgebra.Charpoly`.
-/

@[expose] public section

universe u v w

namespace Module

/-- The characteristic polynomials of the two rectangular compositions agree
with stabilizing factors given by the zero endomorphisms. This is the intrinsic
finite-projective form of Mathlib's `Matrix.charpoly_mul_comm'`. -/
theorem charpoly_comp_mul_charpoly_zero
    (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q]
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] P) :
    Module.charpoly R P (g.comp f) *
        Module.charpoly R Q (0 : Module.End R Q) =
      Module.charpoly R P (0 : Module.End R P) *
        Module.charpoly R Q (f.comp g) := by
  let A : Module.End R (P × Q) := ((g.comp f).coprod g).prod 0
  let B : Module.End R (P × Q) :=
    (g.prod (f.comp g)).comp (LinearMap.snd R P Q)
  have hA : Module.charpoly R (P × Q) A =
      Module.charpoly R P (g.comp f) * Module.charpoly R Q (0 : Module.End R Q) :=
    charpoly_eq_mul_of_exact R P (P × Q) Q
      (LinearMap.inl R P Q) (LinearMap.snd R P Q)
      LinearMap.inl_injective LinearMap.snd_surjective (LinearMap.range_inl R P Q)
      (g.comp f) A 0
      (by ext p <;> simp [A]) (by ext x <;> simp [A])
  have hB : Module.charpoly R (P × Q) B =
      Module.charpoly R P (0 : Module.End R P) * Module.charpoly R Q (f.comp g) :=
    charpoly_eq_mul_of_exact R P (P × Q) Q
      (LinearMap.inl R P Q) (LinearMap.snd R P Q)
      LinearMap.inl_injective LinearMap.snd_surjective (LinearMap.range_inl R P Q)
      0 B (f.comp g)
      (by ext p <;> simp [B]) (by ext x <;> simp [B])
  have hAB : Module.charpoly R (P × Q) A = Module.charpoly R (P × Q) B := by
    apply charpoly_eq_of_intertwining R (P × Q) (P × Q) A B
      ((LinearEquiv.refl R P).skewProd (LinearEquiv.refl R Q) f)
    ext x <;> simp [A, B, add_comm]
  exact hA.symm.trans (hAB.trans hB)

/-- The characteristic polynomial of a rank-one endomorphism, stabilized by
`X`, is the characteristic polynomial of the zero endomorphism times
`X - C (φ v)`. This is the intrinsic stable form of Mathlib's
`Matrix.charpoly_vecMulVec`, without a freeness or constant-rank assumption. -/
theorem charpoly_smulRight_mul_X
    (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (φ : Module.Dual R P) (v : P) :
    Module.charpoly R P (φ.smulRight v) * (Polynomial.X : Polynomial R) =
      Module.charpoly R P (0 : Module.End R P) *
        (Polynomial.X - Polynomial.C (φ v)) := by
  nontriviality R
  let ι : R →ₗ[R] P := LinearMap.toSpanSingleton R P v
  have hcomp : ι.comp φ = φ.smulRight v := by
    ext p
    simp [ι, LinearMap.smulRight_apply]
  have hscalarcomp : φ.comp ι = (φ v) • (1 : Module.End R R) := by
    ext
    simp [ι, mul_comm]
  have hzero : Module.charpoly R R (0 : Module.End R R) =
      (Polynomial.X : Polynomial R) := by
    rw [charpoly_eq_charpoly, LinearMap.charpoly_zero, Module.finrank_self, pow_one]
  have hscalar : Module.charpoly R R ((φ v) • (1 : Module.End R R)) =
      Polynomial.X - Polynomial.C (φ v) := by
    have h := charpoly_sub_smul R R (0 : Module.End R R) (-(φ v))
    have hneg : (0 : Module.End R R) - (-(φ v)) • 1 = (φ v) • 1 := by
      ext
      simp
    rw [hneg] at h
    simpa [hzero, sub_eq_add_neg] using h
  simpa only [hcomp, hscalarcomp, hzero, hscalar] using
    (charpoly_comp_mul_charpoly_zero R P R φ ι)

end Module
