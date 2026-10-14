/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective

import Mathlib.LinearAlgebra.DFinsupp

/-!
# Projectivity of finite dependent products

A finite dependent product of projective modules is projective over any semiring,
with the canonical pointwise addition and scalar action. The factors need not be
finitely generated. The resulting projectivity can be used through
`Module.projective_lifting_property`.

## Implementation notes

The proof transports Mathlib's projectivity instance for dependent finitely
supported functions along `DFinsupp.linearEquivFunOnFintype`, using
`Module.Projective.of_equiv'`. A `Fintype` is chosen only inside the proof;
scalar, index and carrier universes remain independent.

## References

The projectivity and lifting APIs are from Kevin Buzzard and Antoine Labelle's
Mathlib formalization. The dependent finitely supported linear equivalence is
from Johannes Hölzl and Kenny Lau's Mathlib formalization.
-/

@[expose] public section

universe uR uι uM

namespace Module.Projective

/-- A finite dependent product of projective modules over a semiring is projective. -/
instance pi {R : Type uR} [Semiring R] {ι : Type uι} [_root_.Finite ι]
    (M : ι → Type uM) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Projective R (M i)] : Module.Projective R (∀ i, M i) := by
  classical
  let := Fintype.ofFinite ι
  exact Module.Projective.of_equiv'
    (DFinsupp.linearEquivFunOnFintype (R := R) (M := M))

end Module.Projective
