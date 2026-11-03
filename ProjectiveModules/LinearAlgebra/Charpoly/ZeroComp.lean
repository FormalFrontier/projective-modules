/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly
import Mathlib.Tactic.Abel

/-!
# Characteristic polynomials of zero compositions

For endomorphisms `f` and `g` of a finite projective module over a commutative ring,
`f.comp g = 0` implies `charpoly(f) * charpoly(g) = charpoly(f + g) * charpoly(0)`.
Neither the reverse composition nor commutation of `f` and `g` is required.

The proof factors the ordered product of the two universal scalar pencils and applies
multiplicativity of the intrinsic determinant. It does not require a basis, a constant
rank, or cancellation of a characteristic polynomial.
-/

@[expose] public section

universe u v

open scoped TensorProduct
open Polynomial

namespace Module

/-- If the composition of two endomorphisms of a finite projective module is zero,
the product of their characteristic polynomials equals the characteristic polynomial
of their sum times that of zero, all on the original module. Only the displayed order
of composition is assumed. -/
theorem charpoly_mul_charpoly_of_comp_eq_zero (R : Type u) (P : Type v)
    [CommRing R] [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (f g : Module.End R P) (hfg : f.comp g = 0) :
    Module.charpoly R P f * Module.charpoly R P g =
      Module.charpoly R P (f + g) *
        Module.charpoly R P (0 : Module.End R P) := by
  let Q := R[X] ⊗[R] P
  let F : Module.End R[X] Q := f.baseChange R[X]
  let G : Module.End R[X] Q := g.baseChange R[X]
  let x : Module.End R[X] Q := (X : R[X]) • LinearMap.id
  have hFG : F * G = 0 := by
    have hfg_apply (p : P) : f (g p) = 0 :=
      congrArg (fun k : Module.End R P => k p) hfg
    change f.baseChange R[X] * g.baseChange R[X] = 0
    ext p
    simpa using congrArg (fun q : P => (1 : R[X]) ⊗ₜ[R] q) (hfg_apply p)
  have hsum : (f + g).baseChange R[X] = F + G := by
    change (f + g).baseChange R[X] = f.baseChange R[X] + g.baseChange R[X]
    ext p
    simp
  have hzero : (0 : Module.End R P).baseChange R[X] = 0 := by
    ext p
    simp
  have hxzero : x - (0 : Module.End R[X] Q) = x := by
    ext p
    simp
  have hpencil : (x - F) * (x - G) = x * (x - (F + G)) := by
    apply LinearMap.ext
    intro q
    have hFG_apply : F (G q) = 0 :=
      congrArg (fun k : Module.End R[X] Q => k q) hFG
    simp only [x, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.id_apply, _root_.map_sub, _root_.map_smul,
      _root_.smul_sub, _root_.smul_add, hFG_apply, _root_.sub_zero]
    abel
  calc
    Module.charpoly R P f * Module.charpoly R P g =
        Module.determinant R[X] Q (x - F) *
          Module.determinant R[X] Q (x - G) := by
      simp only [Module.charpoly_def, Q, F, G, x]
    _ = Module.determinant R[X] Q ((x - F) * (x - G)) :=
      (map_mul (Module.determinant R[X] Q) (x - F) (x - G)).symm
    _ = Module.determinant R[X] Q (x * (x - (F + G))) :=
      congrArg (Module.determinant R[X] Q) hpencil
    _ = Module.determinant R[X] Q x *
        Module.determinant R[X] Q (x - (F + G)) :=
      map_mul (Module.determinant R[X] Q) x (x - (F + G))
    _ = Module.charpoly R P (0 : Module.End R P) *
        Module.charpoly R P (f + g) := by
      simp only [Module.charpoly_def, hzero, hsum, hxzero, Q, x]
    _ = Module.charpoly R P (f + g) *
        Module.charpoly R P (0 : Module.End R P) := mul_comm _ _

end Module
