/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.ShortExact
public import ProjectiveModules.Module.QuotientIntersectionSplitting
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Quotient inclusion–exclusion in K₀

`KTheory.K0.of_quotientInf_add_quotientSup` proves inclusion–exclusion for the original
right-module quotients by two submodules. Its five premises are finite generation and
projectivity of each individual quotient and projectivity of the sum quotient.
It derives finite generation and projectivity of the intersection quotient and finite
generation of the sum quotient, together with
`[M ⧸ (U ⊓ V)] + [M ⧸ (U ⊔ V)] = [M ⧸ U] + [M ⧸ V]`.

The proof applies short-exact additivity to the canonical diagonal–difference sequence
and to the split product sequence. The witnesses supply the existing `K0.of` arguments;
every quotient retains its original module structure. No finite-generation or projectivity
hypothesis on `M` is imposed. Noncommutative and zero rings are allowed, and the ring
and module universes are independent.

## References

* The quotient factor maps and difference map in
  `ProjectiveModules.Module.QuotientIntersection`.
* The finite-generation and projectivity criteria in
  `ProjectiveModules.Module.QuotientIntersectionSplitting`.
* Right-module short-exact additivity in `ProjectiveModules.KTheory.ShortExact`.
-/

@[expose] public section

universe uR uM

namespace KTheory.K0

variable (R : Type uR) [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- Inclusion–exclusion for the original right-module quotients, including the derived
finite-generation and projectivity witnesses needed by the existing `K0.of` terms.
Only the two individual quotients are assumed finitely generated and projective;
the sum quotient is assumed projective. -/
theorem of_quotientInf_add_quotientSup (U V : Submodule Rᵐᵒᵖ M)
    [Module.Finite Rᵐᵒᵖ (M ⧸ U)] [Module.Projective Rᵐᵒᵖ (M ⧸ U)]
    [Module.Finite Rᵐᵒᵖ (M ⧸ V)] [Module.Projective Rᵐᵒᵖ (M ⧸ V)]
    [Module.Projective Rᵐᵒᵖ (M ⧸ (U ⊔ V))] :
  ∃ hfiniteI : Module.Finite Rᵐᵒᵖ (M ⧸ (U ⊓ V)),
    ∃ hprojectiveI : Module.Projective Rᵐᵒᵖ (M ⧸ (U ⊓ V)),
      ∃ hfiniteC : Module.Finite Rᵐᵒᵖ (M ⧸ (U ⊔ V)),
        @of R _ (M ⧸ (U ⊓ V)) _ _ hfiniteI hprojectiveI +
          @of R _ (M ⧸ (U ⊔ V)) _ _ hfiniteC inferInstance =
        of R (M ⧸ U) + of R (M ⧸ V) := by
  let : Module.Finite Rᵐᵒᵖ (M ⧸ (U ⊓ V)) :=
    (Submodule.QuotientIntersection.finite_iff U V).2 ⟨inferInstance, inferInstance⟩
  let : Module.Projective Rᵐᵒᵖ (M ⧸ (U ⊓ V)) :=
    (Submodule.QuotientIntersection.projective_iff U V).2 ⟨inferInstance, inferInstance⟩
  let : Module.Finite Rᵐᵒᵖ (M ⧸ (U ⊔ V)) :=
    Module.Finite.of_surjective
      (Submodule.factor (show U ≤ U ⊔ V from le_sup_left))
      (Submodule.factor_surjective _)
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  calc
    of R (M ⧸ (U ⊓ V)) + of R (M ⧸ (U ⊔ V)) =
        of R ((M ⧸ U) × (M ⧸ V)) :=
      (of_eq_add_of_exact R (M ⧸ (U ⊓ V)) ((M ⧸ U) × (M ⧸ V)) (M ⧸ (U ⊔ V))
        (Submodule.QuotientIntersection.diagonal U V)
        (Submodule.QuotientIntersection.difference U V)
        (Submodule.QuotientIntersection.diagonal_injective U V)
        (Submodule.QuotientIntersection.difference_surjective U V)
        (Submodule.QuotientIntersection.exact_diagonal_difference U V).linearMap_ker_eq.symm).symm
    _ = of R (M ⧸ U) + of R (M ⧸ V) :=
      of_eq_add_of_exact R (M ⧸ U) ((M ⧸ U) × (M ⧸ V)) (M ⧸ V)
        (LinearMap.inl Rᵐᵒᵖ (M ⧸ U) (M ⧸ V))
        (LinearMap.snd Rᵐᵒᵖ (M ⧸ U) (M ⧸ V))
        LinearMap.inl_injective LinearMap.snd_surjective
        (LinearMap.range_inl Rᵐᵒᵖ (M ⧸ U) (M ⧸ V))

end KTheory.K0
