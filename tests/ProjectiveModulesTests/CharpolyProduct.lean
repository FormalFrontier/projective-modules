/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.ExteriorPower.DeterminantLine.Endomorphism.Pi
import ProjectiveModules.LinearAlgebra.Charpoly.CayleyHamilton

/-!
# Characteristic polynomial products and Cayley–Hamilton

The product characteristic polynomial annihilates the product endomorphism,
using the public binary and finite dependent product formulas and Cayley–Hamilton.
For constant finite free families, the determinant formula recovers
`LinearMap.det_pi`.
-/

@[expose] public section

open scoped BigOperators

universe u v w

example
    (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q]
    (f : Module.End R P) (g : Module.End R Q) :
    Polynomial.aeval (f.prodMap g) (Module.charpoly R P f * Module.charpoly R Q g) =
      (0 : Module.End R (P × Q)) := by
  rw [← Module.charpoly_prodMap R P Q f g]
  exact Module.aeval_self_charpoly R (P × Q) (f.prodMap g)

private theorem det_pi_of_determinant_piMap
    (R : Type u) [CommRing R]
    {I : Type w} [Fintype I]
    (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (f : I → Module.End R M) :
    LinearMap.det (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))) =
      ∏ i, LinearMap.det (f i) := by
  change LinearMap.det (LinearMap.piMap f) = _
  simpa only [Module.determinant_eq_det, finprod_eq_prod_of_fintype] using
    Module.determinant_piMap R (fun _ : I => M) f

example
    (R : Type u) [CommRing R]
    {I : Type w} [_root_.Finite I]
    (P : I → Type v) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
    [∀ i, Module.Finite R (P i)] [∀ i, Module.Projective R (P i)]
    (f : ∀ i, Module.End R (P i)) :
    Polynomial.aeval (LinearMap.piMap f) (∏ᶠ i, Module.charpoly R (P i) (f i)) =
      (0 : Module.End R (∀ i, P i)) := by
  rw [← Module.charpoly_piMap R P f]
  exact Module.aeval_self_charpoly R (∀ i, P i) (LinearMap.piMap f)
