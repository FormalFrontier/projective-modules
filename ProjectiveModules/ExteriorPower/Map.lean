/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Scalars and induced maps on exterior powers

The map induced on the `n`th exterior power is homogeneous of degree `n` in the
underlying linear map. The proof uses Mathlib's exterior-power universal property
and its simultaneous scalar law for alternating maps.

## References

* Mathlib's formalizations of exterior powers and alternating maps in
  `Mathlib.LinearAlgebra.ExteriorPower.Basic` and
  `Mathlib.LinearAlgebra.Alternating.Basic`.
-/

@[expose] public section

universe u v w

namespace exteriorPower

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Scaling a linear map by `r` scales its induced map on the `n`th exterior power
by `r ^ n`. -/
@[simp] theorem map_smul (n : ℕ) (r : R) (f : M →ₗ[R] N) :
    map n (r • f) = r ^ n • map n f := by
  refine linearMap_ext (AlternatingMap.ext fun m ↦ ?_)
  change map n (r • f) (ιMulti R n m) = r ^ n • map n f (ιMulti R n m)
  simp only [map_apply_ιMulti, LinearMap.smul_apply, Function.comp_def]
  simpa using (ιMulti R n (M := N)).map_smul_univ
    (fun _ : Fin n ↦ r) (fun i ↦ f (m i))

end exteriorPower
