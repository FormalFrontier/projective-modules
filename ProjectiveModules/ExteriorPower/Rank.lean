/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import ProjectiveModules.ExteriorPower.TensorProduct

/-!
# Rank of the top exterior power after scalar extension

If scalar extension to a field has finite cardinal rank `r`, then scalar extension of
the `r`th exterior power has rank one. No finiteness assumption on the original
module is needed.
-/

@[expose] public section

open scoped TensorProduct

universe uR uK uM

namespace exteriorPower

variable {R : Type uR} [CommRing R]
variable {K : Type uK} [Field K] [Algebra R K]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- If extension to a field has cardinal rank `r`, then extension of the `r`th
exterior power has rank one, including when `r = 0`. The original module need
not be finitely generated, free, projective, or flat. -/
theorem rank_baseChange_eq_one_of_rank_eq_nat (r : ℕ)
    (h : Module.rank K (K ⊗[R] M) = (r : Cardinal)) :
    Module.rank K (K ⊗[R] (⋀[R]^r M)) = 1 := by
  -- Only the field-valued scalar extension is finite dimensional.
  let : Module.Finite K (K ⊗[R] M) := Module.finite_of_rank_eq_nat h
  have hfin : Module.finrank K (K ⊗[R] M) = r := Module.finrank_eq_of_rank_eq h
  have htop : Module.rank K (⋀[K]^r (K ⊗[R] M)) = 1 := by
    calc
      Module.rank K (⋀[K]^r (K ⊗[R] M)) =
          (Module.finrank K (⋀[K]^r (K ⊗[R] M)) : Cardinal) :=
        (Module.finrank_eq_rank K (⋀[K]^r (K ⊗[R] M))).symm
      _ = 1 := by simp [finrank_eq, hfin]
  -- The two modules can live in different universes, so compare lifted ranks.
  simpa only [htop, Cardinal.lift_one, Cardinal.lift_eq_one] using
    (baseChangeEquiv (R := R) (S := K) (M := M) r).lift_rank_eq

end exteriorPower
