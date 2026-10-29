/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.NilpotentEndomorphism
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Bijectivity from a nilradical bound on a finite image

The finite-image nilradical criterion gives a unit endomorphism without assuming
finite generation of the ambient module. Mathlib's `Module.End.isUnit_iff`, from
`Mathlib.Algebra.Module.Equiv.Basic`, then gives bijectivity of the underlying function.
-/

universe u v

variable {A : Type u} {M : Type v}
  [CommSemiring A] [AddCommGroup M] [Module A M]

example (δ : Module.End A M) (I : Ideal A) (hfg : (LinearMap.range δ).FG)
    (hδ : LinearMap.range δ ≤ I • (⊤ : Submodule A M))
    (hI : I ≤ nilradical A) : Function.Bijective (1 + δ : Module.End A M) := by
  exact (Module.End.isUnit_iff (1 + δ)).mp
    (Module.End.isUnit_one_add_of_fg_range_le_ideal_smul δ I hfg hδ hI)
