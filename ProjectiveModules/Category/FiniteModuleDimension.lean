/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Dimension and isomorphisms of finitely generated modules

Finitely generated free modules over a ring satisfying the strong rank condition
are isomorphic in `ModuleCat` exactly when their finite ranks agree. This uses
Mathlib's linear-equivalence classification, without a commutativity assumption
on the scalar ring. In particular, every finitely generated module over a division
ring is free, so the classification applies without extra freeness or projectivity
hypotheses on the caller.

The finite rank of Mathlib's chosen ring-universe representative of a finite
module is the finite rank of the original module, with independent scalar and
carrier universes. The ambient category classification also yields the
corresponding isomorphism criterion in `FGModuleCat`.

## References and credits

This file reuses Mathlib's `FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq`,
`LinearEquiv.finrank_eq`, the isomorphism bridges for `ModuleCat`, and
`Module.Finite.reprEquiv`. No dimension theorem or representative construction
is reproved here.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace Module.Finite

/-- The chosen ring-universe representative preserves the finite rank of a
finite module, even when its carrier universe differs from the ring universe. -/
@[simp]
theorem finrank_repr (R : Type u) [Ring R] (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Finite R M] :
    Module.finrank R (Module.Finite.repr R M) = Module.finrank R M :=
  (Module.Finite.reprEquiv R M).finrank_eq

end Module.Finite

namespace ModuleCat

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R}

/-- Finitely generated free objects over a ring satisfying the strong rank
condition are isomorphic exactly when their finite ranks agree. This is the
categorical form of Mathlib's finite-rank linear-equivalence classification. -/
theorem nonempty_iso_iff_finrank_eq [StrongRankCondition R]
    [Module.Finite R X] [Module.Finite R Y] [Module.Free R X] [Module.Free R Y] :
    Nonempty (X ≅ Y) ↔ Module.finrank R X = Module.finrank R Y := by
  constructor
  · rintro ⟨e⟩
    exact e.toLinearEquiv.finrank_eq
  · intro h
    obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq h
    exact ⟨e.toModuleIso⟩

end ModuleCat

namespace FGModuleCat

variable {R : Type u} [Ring R] {X Y : FGModuleCat.{v} R}

/-- Finitely generated free objects are isomorphic exactly when their finite
ranks agree, over any ring satisfying the strong rank condition. -/
theorem nonempty_iso_iff_finrank_eq [StrongRankCondition R]
    [Module.Free R X] [Module.Free R Y] :
    Nonempty (X ≅ Y) ↔ Module.finrank R X = Module.finrank R Y := by
  constructor
  · rintro ⟨e⟩
    exact (ModuleCat.nonempty_iso_iff_finrank_eq (X := X.obj) (Y := Y.obj)).1
      ⟨(ModuleCat.isFG R).ι.mapIso e⟩
  · intro h
    obtain ⟨e⟩ := (ModuleCat.nonempty_iso_iff_finrank_eq (X := X.obj) (Y := Y.obj)).2 h
    exact ⟨(ModuleCat.isFG R).isoMk e⟩

end FGModuleCat
