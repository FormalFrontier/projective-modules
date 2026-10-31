/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearMap.ChangeOfScalars
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Categorical comparison for semilinear scalar restriction

The additive part of `LinearMap.semilinearCompHomEquiv` agrees with
`ModuleCat.semilinearMapAddEquiv` after the usual identification of categorical
morphisms with linear maps. This comparison applies to arbitrary rings and
modules in a common carrier universe, as does the categorical equivalence.

## References

The categorical equivalence is Jujian Zhang's change-of-rings formalization in
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`. The comparison uses
Mathlib's `ModuleCat.homAddEquiv`.
-/

@[expose] public section

universe uR uS uM

namespace ModuleCat

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The additive scalar-restriction identification agrees with the categorical
semilinear-map identification. Natural-number auxiliary scalars recover the
additive equivalence without any commutativity assumption on the rings. -/
theorem semilinearMapAddEquiv_trans_homAddEquiv (σ : R →+* S)
    (L : ModuleCat.{uM} R) (M : ModuleCat.{uM} S) :
    (semilinearMapAddEquiv σ L M).trans
        (homAddEquiv (M := L) (N := (restrictScalars σ).obj M)) =
      (LinearMap.semilinearCompHomEquiv (L := L) (M := M) ℕ σ).toAddEquiv := by
  ext f l
  rfl

end ModuleCat
