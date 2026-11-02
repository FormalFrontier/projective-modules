/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.LinearAlgebra.Charpoly.CayleyHamilton

/-!
# Characteristic polynomial products and Cayley–Hamilton

The product characteristic polynomial annihilates the product endomorphism,
using the public product formula and Cayley–Hamilton theorem.
-/

@[expose] public section

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
