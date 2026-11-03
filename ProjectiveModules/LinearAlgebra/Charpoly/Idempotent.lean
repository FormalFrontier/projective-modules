/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly.ZeroComp

/-!
# Characteristic polynomials of complementary idempotents

For an idempotent endomorphism of a finite projective module, the product of the
characteristic polynomials of the two complementary idempotents equals the product of
the intrinsic characteristic polynomials of zero and the identity on the same module.

This is the zero-composition characteristic-polynomial identity applied to `f` and
`1 - f`. No choice of a basis or a constant rank is required.
-/

@[expose] public section

universe u v

namespace Module

/-- The characteristic polynomials of complementary idempotent endomorphisms of a finite
projective module multiply to the product of the intrinsic characteristic polynomials of
zero and the identity on that module. -/
theorem charpoly_mul_charpoly_one_sub (R : Type u) (P : Type v)
    [CommRing R] [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P) (hf : IsIdempotentElem f) :
    Module.charpoly R P f * Module.charpoly R P (1 - f) =
      Module.charpoly R P (0 : Module.End R P) *
        Module.charpoly R P (1 : Module.End R P) := by
  have hfg : f.comp (1 - f) = 0 := by
    have hff (p : P) : f (f p) = f p :=
      congrArg (fun k : Module.End R P => k p) hf
    ext p
    simp [map_sub, hff]
  have hsum : f + (1 - f) = 1 := by
    simp [sub_eq_add_neg, add_comm]
  calc
    Module.charpoly R P f * Module.charpoly R P (1 - f) =
        Module.charpoly R P (f + (1 - f)) *
          Module.charpoly R P (0 : Module.End R P) :=
      Module.charpoly_mul_charpoly_of_comp_eq_zero R P f (1 - f) hfg
    _ = Module.charpoly R P (0 : Module.End R P) *
        Module.charpoly R P (1 : Module.End R P) := by rw [hsum, mul_comm]

end Module
