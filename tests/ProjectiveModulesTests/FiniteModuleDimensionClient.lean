/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.FiniteModuleDimension
public import ProjectiveModules.Category.FiniteProjectiveSmallness
public import Mathlib.Algebra.Field.Opposite
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite-module dimension clients

The categorical classification distinguishes coordinate modules of different
finite dimensions over division rings and over the integers. Both the ambient
module category and the finitely generated module category are exercised.
Mathlib's existing constructors give a categorical isomorphism from a product
of coordinate spaces to the coordinate space of the sum of their dimensions.

Finite-projective representative dimensions normalize through the generic
finite-module API, for independent carrier universes, products, lifts and zero
modules. The normalization also preserves Mathlib's finrank-one convention for
modules over a subsingleton scalar ring.

## References and credits

These examples use Mathlib's finite-rank classification, categorical
isomorphism constructors and product/lift dimensions, together with the finite
projective representative API in this library.
-/

@[expose] public section

universe u v w

open CategoryTheory ModuleCat

namespace ProjectiveModulesTests.FiniteModuleDimensionClient

-- Division-ring freeness is inferred, without a projectivity premise.
example (K : Type u) [DivisionRing K] (n m : ℕ) :
    Nonempty (ModuleCat.of Kᵐᵒᵖ (Fin n → Kᵐᵒᵖ) ≅
      ModuleCat.of Kᵐᵒᵖ (Fin m → Kᵐᵒᵖ)) ↔ n = m := by
  rw [ModuleCat.nonempty_iso_iff_finrank_eq]
  simp only [Module.finrank_fin_fun]

example (K : Type u) [DivisionRing K] (n m : ℕ) :
    Nonempty (FGModuleCat.of Kᵐᵒᵖ (Fin n → Kᵐᵒᵖ) ≅
      FGModuleCat.of Kᵐᵒᵖ (Fin m → Kᵐᵒᵖ)) ↔ n = m := by
  rw [FGModuleCat.nonempty_iso_iff_finrank_eq]
  change Module.finrank Kᵐᵒᵖ (Fin n → Kᵐᵒᵖ) =
    Module.finrank Kᵐᵒᵖ (Fin m → Kᵐᵒᵖ) ↔ n = m
  simp only [Module.finrank_fin_fun]

-- The generic category statement is not restricted to division rings.
example (n m : ℕ) :
    Nonempty (ModuleCat.of ℤ (Fin n → ℤ) ≅ ModuleCat.of ℤ (Fin m → ℤ)) ↔ n = m := by
  rw [ModuleCat.nonempty_iso_iff_finrank_eq]
  simp only [Module.finrank_fin_fun]

noncomputable example (K : Type u) [DivisionRing K] (n m : ℕ) :
    FGModuleCat.of Kᵐᵒᵖ ((Fin n → Kᵐᵒᵖ) × (Fin m → Kᵐᵒᵖ)) ≅
      FGModuleCat.of Kᵐᵒᵖ (Fin (n + m) → Kᵐᵒᵖ) :=
  (LinearEquiv.ofFinrankEq (R := Kᵐᵒᵖ)
    ((Fin n → Kᵐᵒᵖ) × (Fin m → Kᵐᵒᵖ)) (Fin (n + m) → Kᵐᵒᵖ)
    (by simp only [Module.finrank_prod, Module.finrank_fin_fun])).toFGModuleCatIso

example (K : Type u) [DivisionRing K]
    (M : Type v) [AddCommGroup M] [Module Kᵐᵒᵖ M] [Module.Finite Kᵐᵒᵖ M]
    (N : Type w) [AddCommGroup N] [Module Kᵐᵒᵖ N] [Module.Finite Kᵐᵒᵖ N] :
    Module.finrank Kᵐᵒᵖ (FiniteProjective.repr Kᵐᵒᵖ (M × N)) =
      Module.finrank Kᵐᵒᵖ M + Module.finrank Kᵐᵒᵖ N := by
  exact (FiniteProjective.reprEquiv Kᵐᵒᵖ (M × N)).finrank_eq.trans
    (Module.finrank_prod (R := Kᵐᵒᵖ) (M := M) (M' := N))

-- Normalization needs no freeness or strong-rank-condition premise.
example (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.finrank R (Module.Finite.repr R (ULift.{w} M)) = Module.finrank R M := by
  simp only [Module.Finite.finrank_repr, finrank_ulift]

example (K : Type u) [DivisionRing K] (Z : Type v) [AddCommGroup Z]
    [Module Kᵐᵒᵖ Z] [Subsingleton Z] :
    Module.finrank Kᵐᵒᵖ (FiniteProjective.repr Kᵐᵒᵖ Z) = 0 := by
  exact (FiniteProjective.reprEquiv Kᵐᵒᵖ Z).finrank_eq.trans
    (Module.finrank_zero_of_subsingleton (R := Kᵐᵒᵖ) (M := Z))

example (R : Type u) [Ring R] [Subsingleton R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.finrank R (Module.Finite.repr R M) = 1 := by
  simp

end ProjectiveModulesTests.FiniteModuleDimensionClient
