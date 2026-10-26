/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
public import ProjectiveModules.Module.RankLocallyConstant

/-!
# Locally constant rank of projective module classes

`KTheory.ProjectiveClass.rankLocallyConstant R` assigns a natural-valued locally
constant function on `PrimeSpectrum R` to an isomorphism class of finite
projective right `R`-modules. The right module keeps its original left
`Rᵐᵒᵖ`-module structure: its existing locally constant rank is pulled back by the
spectrum homeomorphism associated to `RingEquiv.toOpposite R`.

The construction uses `ProjectiveClass.liftFunction`, so it is independent of
the chosen ring-universe representative. The evaluation API accepts module
carriers in universes independent of the ring. No nontriviality assumption is
needed; the prime spectrum of the zero ring is empty.

## Implementation notes

This file supplies a function and its characteristic API, not an additive or
multiplicative map on classes or a map from K₀.

## References

The construction reuses this library's finite-projective representatives and
class-function descent, Mathlib's opposite-ring spectrum homeomorphism, and
the locally constant rank and equivalence laws in
`ProjectiveModules.Module.RankLocallyConstant`, based on Andrew Yang's
Mathlib stalk-rank formalization.
-/

@[expose] public section

universe uR uM

namespace KTheory.ProjectiveClass

variable (R : Type uR) [CommRing R]

/-- The locally constant natural-valued rank of a finite projective right-module
class, obtained from the original opposite-ring module without changing its action. -/
noncomputable def rankLocallyConstant :
    ProjectiveClass R → LocallyConstant (PrimeSpectrum R) ℕ :=
  liftFunction R
    (fun X : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ ↦
      LocallyConstant.comap
        (toContinuousMap (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.toOpposite R)))
        (Module.rankLocallyConstant Rᵐᵒᵖ X))
    (fun {X Y} e ↦ congrArg
      (LocallyConstant.comap
        (toContinuousMap (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.toOpposite R))))
      (Module.rankLocallyConstant_eq_of_equiv Rᵐᵒᵖ X Y
        (ModuleCat.FiniteProjective.isoToLinearEquiv e)))

/-- On a reference-category module, class rank is the pullback of its existing
opposite-ring locally constant rank. -/
theorem rankLocallyConstant_of
    (X : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ) :
    rankLocallyConstant R (of R X) =
      LocallyConstant.comap
        (toContinuousMap (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.toOpposite R)))
        (Module.rankLocallyConstant Rᵐᵒᵖ X) :=
  liftFunction_of R _ (fun {X Y} e ↦ congrArg
      (LocallyConstant.comap
        (toContinuousMap (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.toOpposite R))))
      (Module.rankLocallyConstant_eq_of_equiv Rᵐᵒᵖ X Y
        (ModuleCat.FiniteProjective.isoToLinearEquiv e))) X

/-- Class rank evaluates on any carrier universe using the original module
structure, rather than the chosen representative's carrier. -/
@[simp]
theorem rankLocallyConstant_of_module
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    rankLocallyConstant R (of R M) =
      LocallyConstant.comap
        (toContinuousMap (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.toOpposite R)))
        (Module.rankLocallyConstant Rᵐᵒᵖ M) := by
  rw [← of_repr R M, rankLocallyConstant_of]
  exact congrArg
    (LocallyConstant.comap
      (toContinuousMap (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.toOpposite R))))
    (Module.rankLocallyConstant_eq_of_equiv Rᵐᵒᵖ _ M
      (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ M))

/-- At a prime of `R`, class rank is the stalk rank of the original right
module at the corresponding prime of `Rᵐᵒᵖ`. -/
theorem rankLocallyConstant_of_module_apply
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (p : PrimeSpectrum R) :
    rankLocallyConstant R (of R M) p =
      Module.rankAtStalk (R := Rᵐᵒᵖ) M
        (PrimeSpectrum.comap (RingEquiv.toOpposite R).symm.toRingHom p) := by
  rw [rankLocallyConstant_of_module]
  exact Module.rankLocallyConstant_apply Rᵐᵒᵖ M _

/-- The values on reference-module classes characterize the class-rank function. -/
theorem rankLocallyConstant_unique
    (F : ProjectiveClass R → LocallyConstant (PrimeSpectrum R) ℕ)
    (h : ∀ X : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ,
      F (of R X) =
        LocallyConstant.comap
          (toContinuousMap (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.toOpposite R)))
          (Module.rankLocallyConstant Rᵐᵒᵖ X)) :
    F = rankLocallyConstant R :=
  liftFunction_unique R _ (fun {X Y} e ↦ congrArg
      (LocallyConstant.comap
        (toContinuousMap (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.toOpposite R))))
      (Module.rankLocallyConstant_eq_of_equiv Rᵐᵒᵖ X Y
        (ModuleCat.FiniteProjective.isoToLinearEquiv e))) F h

end KTheory.ProjectiveClass
