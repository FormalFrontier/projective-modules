/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective

/-!
# Projectivity in a scalar tower

Projectivity descends through a scalar tower when the intermediate semiring is
projective over the base. The module need not be finitely generated. Both tower
conditions refer to the given actions: compatibility with multiplication on the
intermediate semiring, and compatibility with its action on the module.

## References

The statement uses Mathlib's semiring-level projective-module and scalar-tower
interfaces.
-/

@[expose] public section

universe uR uS uM

namespace Module

/-- In a scalar tower, a projective `S`-module is projective over `R` if `S` is
projective over `R`. No finite-generation assumption on the module is needed. -/
theorem Projective.trans
    {R : Type uR} {S : Type uS} {M : Type uM}
    [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R S] [Module R M] [Module S M]
    [IsScalarTower R S S] [IsScalarTower R S M]
    [Module.Projective R S] [Module.Projective S M] :
    Module.Projective R M := by
  classical
  -- The free `S`-module is a direct sum of the `R`-projective coefficient module.
  let : Module.Projective R (M →₀ S) :=
    Module.Projective.of_equiv' (finsuppLEquivDirectSum R S M).symm
  obtain ⟨i, hi⟩ := Module.Projective.out (R := S) (P := M)
  -- Both scalar towers make the splitting maps `R`-linear for the given actions.
  refine Module.Projective.of_split (i.restrictScalars R)
    ((Finsupp.linearCombination S (id : M → M)).restrictScalars R) ?_
  ext m
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.id_apply] using hi m

end Module
