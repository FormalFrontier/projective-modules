/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.ExteriorPower.AlternatingForms

/-!
# Orientation of determinant duality on the integral plane

The ordered coordinate functionals give the positive unit alternating form on the ordered
coordinate vectors of `ℤ × ℤ`. The calculation uses the alternating-form equivalence and
its public determinant formula, then recovers the same normalization for the determinant pairing.
-/

@[expose] public section

example :
    let φ : Fin 2 → Module.Dual ℤ (ℤ × ℤ) :=
      fun j ↦ if j = 0 then LinearMap.fst ℤ ℤ ℤ else LinearMap.snd ℤ ℤ ℤ
    let x : Fin 2 → ℤ × ℤ := fun j ↦ if j = 0 then (1, 0) else (0, 1)
    exteriorPower.pairingDual ℤ (ℤ × ℤ) 2
      (exteriorPower.ιMulti ℤ 2 φ) (exteriorPower.ιMulti ℤ 2 x) = 1 := by
  let φ : Fin 2 → Module.Dual ℤ (ℤ × ℤ) :=
    fun j ↦ if j = 0 then LinearMap.fst ℤ ℤ ℤ else LinearMap.snd ℤ ℤ ℤ
  let x : Fin 2 → ℤ × ℤ := fun j ↦ if j = 0 then (1, 0) else (0, 1)
  have h : exteriorPower.dualAlternatingEquiv ℤ (ℤ × ℤ) 2
      (exteriorPower.ιMulti ℤ 2 φ) x = 1 := by
    rw [exteriorPower.dualAlternatingEquiv_ιMulti_apply]
    simp [φ, x, Matrix.det_fin_two]
  change exteriorPower.pairingDual ℤ (ℤ × ℤ) 2
    (exteriorPower.ιMulti ℤ 2 φ) (exteriorPower.ιMulti ℤ 2 x) = 1
  simpa only [exteriorPower.dualAlternatingEquiv_apply] using h
