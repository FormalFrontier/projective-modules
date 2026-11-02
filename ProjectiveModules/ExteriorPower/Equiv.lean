/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Exterior powers of linear equivalences

`exteriorPower.congr` is the linear equivalence on exterior powers induced by a
linear equivalence of modules. Its forward and inverse maps are the exterior-power
maps of the given equivalence and its inverse. The generator formulas apply in every
degree, including zero, over an arbitrary commutative ring and with independent
scalar and module universes.

The construction uses Mathlib's exterior-power functoriality and
`LinearEquiv.ofLinearMap`.
-/

@[expose] public section

universe uR uM uN

namespace exteriorPower

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]

/-- A linear equivalence of modules induces a linear equivalence on every exterior
power. The forward map is `exteriorPower.map` of the equivalence, and the inverse
is `exteriorPower.map` of its inverse. -/
noncomputable def congr (n : ℕ) (e : M ≃ₗ[R] N) :
    (⋀[R]^n M) ≃ₗ[R] ⋀[R]^n N :=
  LinearEquiv.ofLinearMap (map n e.toLinearMap) (map n e.symm.toLinearMap)
    (by
      have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id (R := R) := by
        apply LinearMap.ext
        intro x
        exact e.apply_symm_apply x
      calc
        _ = map n (e.toLinearMap.comp e.symm.toLinearMap) :=
          (map_comp (n := n) e.symm.toLinearMap e.toLinearMap).symm
        _ = LinearMap.id := (congrArg (map n) h).trans (map_id (n := n)))
    (by
      have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id (R := R) := by
        apply LinearMap.ext
        intro x
        exact e.symm_apply_apply x
      calc
        _ = map n (e.symm.toLinearMap.comp e.toLinearMap) :=
          (map_comp (n := n) e.toLinearMap e.symm.toLinearMap).symm
        _ = LinearMap.id := (congrArg (map n) h).trans (map_id (n := n)))

/-- The linear map underlying the exterior-power equivalence is the exterior-power
map of the original equivalence. -/
@[simp] theorem congr_toLinearMap (n : ℕ) (e : M ≃ₗ[R] N) :
    (congr n e).toLinearMap = map n e.toLinearMap := rfl

/-- The inverse exterior-power equivalence is induced by the inverse linear map. -/
@[simp] theorem congr_symm_toLinearMap (n : ℕ) (e : M ≃ₗ[R] N) :
    (congr n e).symm.toLinearMap = map n e.symm.toLinearMap := rfl

/-- The induced equivalence sends a pure wedge to the wedge of the images. -/
@[simp] theorem congr_ιMulti (n : ℕ) (e : M ≃ₗ[R] N) (m : Fin n → M) :
    congr n e (ιMulti R n m) = ιMulti R n (fun i => e (m i)) :=
  map_apply_ιMulti e.toLinearMap m

/-- The inverse induced equivalence applies the inverse to every wedge entry. -/
@[simp] theorem congr_symm_ιMulti (n : ℕ) (e : M ≃ₗ[R] N) (m : Fin n → N) :
    (congr n e).symm (ιMulti R n m) = ιMulti R n (fun i => e.symm (m i)) :=
  map_apply_ιMulti e.symm.toLinearMap m

end exteriorPower
