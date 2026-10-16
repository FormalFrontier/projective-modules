/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.Product
import Mathlib.LinearAlgebra.StdBasis

/-!
# Clients of finite and projective closure over a coefficient product

The nonempty family has two integer coefficient rings and factors of ranks one
and two. All actions are Mathlib's canonical left actions, including `Pi.module'`
over the coefficient product. The factor instances come from `Pi.basisFun`.
The empty-index examples check the same two public contracts at the boundary.
-/

namespace ProjectiveModulesTests.LeftProductClient

private abbrev Factor (i : Fin 2) := Fin (i.val + 1) → ℤ

private instance factorFinite (i : Fin 2) : Module.Finite ℤ (Factor i) :=
  Module.Finite.pi (R := ℤ) (M := fun _ : Fin (i.val + 1) ↦ ℤ)

private instance factorProjective (i : Fin 2) : Module.Projective ℤ (Factor i) :=
  Module.Projective.of_basis (Pi.basisFun ℤ (Fin (i.val + 1)))

example : Module.Finite (Fin 2 → ℤ) (∀ i : Fin 2, Factor i) :=
  Module.finite_pi (fun _ : Fin 2 ↦ ℤ) Factor

example : Module.Projective (Fin 2 → ℤ) (∀ i : Fin 2, Factor i) :=
  Module.projective_pi (fun _ : Fin 2 ↦ ℤ) Factor

-- This is the actual coordinate action on the module in both conclusions.
example (r : Fin 2 → ℤ) (m : ∀ i : Fin 2, Factor i)
    (i : Fin 2) (j : Fin (i.val + 1)) :
    (r • m) i j = r i * m i j := rfl

example : Module.Finite (Fin 0 → ℤ) (Fin 0 → ℤ) :=
  Module.finite_pi (fun _ : Fin 0 ↦ ℤ) (fun _ ↦ ℤ)

example : Module.Projective (Fin 0 → ℤ) (Fin 0 → ℤ) :=
  Module.projective_pi (fun _ : Fin 0 ↦ ℤ) (fun _ ↦ ℤ)

end ProjectiveModulesTests.LeftProductClient
