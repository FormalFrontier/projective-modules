/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.Koszul.Basic

/-!
# Symmetric insertion and bigraded Koszul maps

These callers use the canonical carriers with independent scalar and module universes.
-/

noncomputable section

open scoped TensorProduct

universe u v

example (S : Type u) [CommSemiring S] (P : Type v) [AddCommMonoid P] [Module S P]
    (d : ℕ) :
    P ⊗[S] Module.Koszul.SymmetricDegree S P d →ₗ[S]
      Module.Koszul.SymmetricDegree S P (d + 1) :=
  Module.Koszul.insert S P d

example (S : Type u) [CommRing S] (P : Type v) [AddCommGroup P] [Module S P]
    (i d : ℕ) :
    Module.Koszul.Term S P (i + 1) d →ₗ[S] Module.Koszul.Term S P i (d + 1) :=
  Module.Koszul.delta S P i d
