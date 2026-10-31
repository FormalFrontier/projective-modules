/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Naturality of the localization–tensor equivalence

The canonical equivalence from a localized module to its tensor-product model
intertwines localized linear maps with extension of scalars.
-/

public section

universe uR uM uN

namespace LocalizedModule

variable {R : Type uR} [CommSemiring R] (S : Submonoid R)
  {M : Type uM} [AddCommMonoid M] [Module R M]
  {N : Type uN} [AddCommMonoid N] [Module R N]

/-- The canonical localization–tensor equivalence commutes with linear maps. -/
theorem equivTensorProduct_map (f : M →ₗ[R] N) (z : LocalizedModule S M) :
    equivTensorProduct S N (map S f z) =
      LinearMap.baseChange (Localization S) f (equivTensorProduct S M z) := by
  induction z using LocalizedModule.induction_on with
  | h x s =>
    rw [map_mk, equivTensorProduct_apply_mk, equivTensorProduct_apply_mk,
      LinearMap.baseChange_tmul]

end LocalizedModule
