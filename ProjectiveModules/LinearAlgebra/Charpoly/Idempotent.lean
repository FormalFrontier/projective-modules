/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.LinearAlgebra.Prod

/-!
# Characteristic polynomials of complementary idempotents

For an idempotent endomorphism of a finite projective module, the product of the
characteristic polynomials of the two complementary idempotents equals the product of
the intrinsic characteristic polynomials of zero and the identity on the same module.

The proof intertwines the two block endomorphisms on the square of the module using an
involutive linear map, then applies characteristic-polynomial invariance and the product
formula. No choice of a basis or a constant rank is required.
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
  let g : Module.End R P := 1 - f
  have hff (p : P) : f (f p) = f p :=
    congrArg (fun k : Module.End R P => k p) hf
  have hfg (p : P) : f (g p) = 0 := by
    simp [g, map_sub, hff]
  have hgf (p : P) : g (f p) = 0 := by
    simp [g, hff]
  have hgg (p : P) : g (g p) = g p := by
    simp [g, map_sub, hff]
  have hsum (p : P) : f p + g p = p := by
    simp [g, sub_eq_add_neg, add_comm, add_left_comm]
  let E : Module.End R (P × P) :=
    (f.comp (LinearMap.fst R P P) + g.comp (LinearMap.snd R P P)).prod
      (g.comp (LinearMap.fst R P P) + f.comp (LinearMap.snd R P P))
  have hE (p : P × P) : E p = (f p.1 + g p.2, g p.1 + f p.2) := by
    rfl
  have hinv : Function.Involutive E := by
    rintro ⟨p, q⟩
    simp only [hE, map_add, hff, hfg, hgf, hgg,
      add_zero, zero_add]
    exact Prod.ext (hsum p) (by simpa only [add_comm] using hsum q)
  let e : (P × P) ≃ₗ[R] (P × P) :=
    LinearEquiv.ofInvolutive (σ := RingHom.id R) (σ' := RingHom.id R) E hinv
  have he (p : P × P) : e p = E p :=
    congrFun (LinearEquiv.coe_ofInvolutive
      (σ := RingHom.id R) (σ' := RingHom.id R) E hinv) p
  have hintertwine :
      e.toLinearMap.comp (f.prodMap g) =
        ((1 : Module.End R P).prodMap (0 : Module.End R P)).comp e.toLinearMap := by
    apply LinearMap.ext
    intro p
    change e ((f.prodMap g) p) =
      ((1 : Module.End R P).prodMap (0 : Module.End R P)) (e p)
    simp [LinearMap.prodMap_apply, he, hE, hff, hfg, hgf, hgg]
  calc
    Module.charpoly R P f * Module.charpoly R P (1 - f) =
        Module.charpoly R (P × P) (f.prodMap g) :=
      (Module.charpoly_prodMap R P P f g).symm
    _ = Module.charpoly R (P × P)
        ((1 : Module.End R P).prodMap (0 : Module.End R P)) :=
      Module.charpoly_eq_of_intertwining R (P × P) (P × P) (f.prodMap g)
        ((1 : Module.End R P).prodMap (0 : Module.End R P)) e hintertwine
    _ = Module.charpoly R P (1 : Module.End R P) *
        Module.charpoly R P (0 : Module.End R P) :=
      Module.charpoly_prodMap R P P (1 : Module.End R P) (0 : Module.End R P)
    _ = Module.charpoly R P (0 : Module.End R P) *
        Module.charpoly R P (1 : Module.End R P) := mul_comm _ _

end Module
