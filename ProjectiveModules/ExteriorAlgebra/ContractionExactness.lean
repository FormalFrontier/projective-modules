/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorAlgebra.Contraction
public import Mathlib.Algebra.Module.Submodule.Range

/-!
# Exactness of left contraction by a surjective covector

The operators are the existing `CliffordAlgebra.contractLeft` and ordinary left
multiplication by `CliffordAlgebra.ι Q m`. Left multiplication squares to the scalar
`Q m`, so it need not be square-zero for a general quadratic form. Nevertheless, a
surjective covector makes contraction exact on the original Clifford algebra: a preimage
of one supplies a contraction–creation identity, which lifts every cycle to a boundary.
No condition on `Q m` is needed.

## References

Mathlib's `CliffordAlgebra.Basic` and `CliffordAlgebra.Contraction`, by Eric Wieser and
contributors, provide the Clifford relation, contraction, and its square-zero theorem.
The proofs below use those constructions and the contraction–creation identity from
`ProjectiveModules.ExteriorAlgebra.Contraction`, together with Mathlib's linear-map range
and kernel API. Exactness is conditional on surjectivity; no unconditional claim is made
for the zero covector.
-/

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace CliffordAlgebra

variable {Q : QuadraticForm R M}

/-- The square of left multiplication by a vector is scalar multiplication by its quadratic
value. In particular, creation is not assumed to be square-zero. -/
theorem mulLeft_ι_comp_self (m : M) :
    (LinearMap.mulLeft R (ι Q m)).comp (LinearMap.mulLeft R (ι Q m)) =
      Q m • (LinearMap.id : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) := by
  rw [← LinearMap.mulLeft_mul, ι_sq_scalar]
  apply LinearMap.ext
  intro x
  change algebraMap R (CliffordAlgebra Q) (Q m) * x = Q m • x
  exact (Algebra.smul_def (Q m) x).symm

/-- Left contraction by a surjective covector has range equal to its kernel, for every
quadratic form. A preimage of one gives the lift of each cycle by left multiplication. -/
theorem range_contractLeft_eq_ker_of_surjective (μ : Module.Dual R M)
    (hμ : Function.Surjective μ) :
    LinearMap.range (contractLeft (Q := Q) μ) =
      LinearMap.ker (contractLeft (Q := Q) μ) := by
  obtain ⟨m, hm⟩ := hμ 1
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact LinearMap.mem_ker.mpr (contractLeft_contractLeft μ y)
  · intro x hx
    refine LinearMap.mem_range.mpr ⟨LinearMap.mulLeft R (ι Q m) x, ?_⟩
    have hx' : contractLeft μ x = 0 := LinearMap.mem_ker.mp hx
    have h := LinearMap.ext_iff.mp
      (contractLeft_comp_mulLeft_add_mulLeft_comp_of_eq_one (Q := Q) μ m hm) x
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.id_apply, hx', mul_zero, add_zero] using h

end CliffordAlgebra
