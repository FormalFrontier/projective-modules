/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
public import ProjectiveModules.Module.Trace.CommutatorQuotient

/-!
# Hattori–Stallings trace on projective classes and K₀

The endomorphism trace of the identity of a finite projective right `R`-module
is invariant under right-linear isomorphism and additive under binary direct
sum. `KTheory.ProjectiveClass.traceModCommutators R` descends this invariant
through `ProjectiveClass.lift`. Its extension through `K0.lift` is
`KTheory.K0.traceModCommutators R`.

Both maps take values in the additive-group quotient
`R ⧸ Ring.additiveCommutators R`, not an ideal quotient or an `R`-module target.
Here `ProjectiveClass R` and `K0 R` already use right `R`-modules, represented
by left `Rᵐᵒᵖ`-modules. Thus their scalar parameter is `R`, not `Rᵐᵒᵖ`.
Module carriers may lie in universes independent of the ring universe. No
commutativity, nontriviality, freeness or cancellation assumption is made.

The characteristic laws evaluate the class map on any finite projective
module and the K₀ map on the completion of any projective class. Together they
evaluate the K₀ map on module generators without unfolding either definition.
The ordinary right regular module has value the additive quotient class of `1`.
The extensionality and uniqueness principles are those of `ProjectiveClass.lift`
and `K0.lift`.

## References

* Charles A. Weibel, *The K-book*, §II.2, “Hattori–Stallings trace map”,
  for the finite-complement endomorphism trace, its value on the identity,
  direct-sum additivity and extension by group completion.
* Projective Modules' finite-projective category, ring-universe representatives,
  projective-class descent and right-module K₀ APIs, contributed by Formal
  Frontier Agents including Prism and Lens; and its endomorphism trace and
  complement construction, with contributions by Iris and Prism.
* Mathlib's skeleton, algebraic transport and additive Grothendieck group,
  including the group-completion formalization by Alex J. Best and Yaël Dillies;
  and its opposite, linear-map and additive-quotient APIs.
* General Linear Groups' additive-commutator subgroup and matrix trace
  formalization by Formal Frontier Agents. No source excerpt is reproduced.
-/

@[expose] public section

universe uR uM

namespace KTheory

variable (R : Type uR) [Ring R]

namespace ProjectiveClass

private theorem identityTrace_equiv
    {M : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    {N : Type*} [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N]
    (e : M ≃ₗ[Rᵐᵒᵖ] N) :
    LinearMap.traceModCommutators R M (LinearMap.id (R := Rᵐᵒᵖ) (M := M)) =
      LinearMap.traceModCommutators R N (LinearMap.id (R := Rᵐᵒᵖ) (M := N)) := by
  simpa only [LinearEquiv.symm_comp, LinearEquiv.comp_symm] using
    LinearMap.traceModCommutators_comp_comm R M e.toLinearMap e.symm.toLinearMap

private theorem identityTrace_prod
    (M : Type*) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (N : Type*) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    LinearMap.traceModCommutators R (M × N)
        (LinearMap.id (R := Rᵐᵒᵖ) (M := M × N)) =
      LinearMap.traceModCommutators R M (LinearMap.id (R := Rᵐᵒᵖ) (M := M)) +
        LinearMap.traceModCommutators R N (LinearMap.id (R := Rᵐᵒᵖ) (M := N)) := by
  have hid :
      LinearMap.id (R := Rᵐᵒᵖ) (M := M × N) =
        (LinearMap.inl Rᵐᵒᵖ M N).comp (LinearMap.fst Rᵐᵒᵖ M N) +
          (LinearMap.inr Rᵐᵒᵖ M N).comp (LinearMap.snd Rᵐᵒᵖ M N) :=
    (LinearMap.coprod_inl_inr (R := Rᵐᵒᵖ) (M := M) (M₂ := N)).symm
  rw [hid, map_add,
    LinearMap.traceModCommutators_comp_comm R (M × N)
      (LinearMap.fst Rᵐᵒᵖ M N) (LinearMap.inl Rᵐᵒᵖ M N),
    LinearMap.traceModCommutators_comp_comm R (M × N)
      (LinearMap.snd Rᵐᵒᵖ M N) (LinearMap.inr Rᵐᵒᵖ M N),
    LinearMap.fst_comp_inl, LinearMap.snd_comp_inr]

/-- The Hattori–Stallings identity trace on finite-projective right-module
classes, descending the endomorphism trace through direct-sum classes.
See Weibel, *The K-book*, §II.2, “Hattori–Stallings trace map”. -/
noncomputable def traceModCommutators :
    ProjectiveClass R →+ (R ⧸ Ring.additiveCommutators R) :=
  lift R
    (fun X : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ ↦
      LinearMap.traceModCommutators R X (LinearMap.id (R := Rᵐᵒᵖ) (M := X)))
    (by
      intro X Y e
      exact identityTrace_equiv R (ModuleCat.FiniteProjective.isoToLinearEquiv e))
    (by
      rw [LinearMap.identityMapOfZeroModuleIsZero, map_zero])
    (by
      intro X Y
      exact identityTrace_prod R X Y)

/-- On a module class in any carrier universe, the class trace is the
endomorphism trace of the identity. This is the module trace of Weibel,
*The K-book*, §II.2, “Hattori–Stallings trace map”. -/
@[simp]
theorem traceModCommutators_of_module (M : Type uM) [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    traceModCommutators R (of R M) =
      LinearMap.traceModCommutators R M (LinearMap.id (R := Rᵐᵒᵖ) (M := M)) := by
  rw [traceModCommutators, lift_of_module]
  · exact identityTrace_equiv R (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ M)
  · intro X Y e
    exact identityTrace_equiv R (ModuleCat.FiniteProjective.isoToLinearEquiv e)

/-- The ordinary right regular module has identity trace the class of `1`.
See Weibel, *The K-book*, §II.2, “Hattori–Stallings trace map”. -/
@[simp]
theorem traceModCommutators_of_self :
    traceModCommutators R (of R R) =
      QuotientAddGroup.mk' (Ring.additiveCommutators R) 1 := by
  rw [traceModCommutators_of_module]
  simpa only [map_one, Module.End.one_eq_id] using
    LinearMap.traceModCommutators_moduleEndSelfOp R (1 : R)

end ProjectiveClass

namespace K0

/-- The Hattori–Stallings trace on right-module K₀, extending the identity
trace on projective classes by the group-completion universal property.
See Weibel, *The K-book*, §II.2, “Hattori–Stallings trace map”. -/
noncomputable def traceModCommutators :
    K0 R →+ (R ⧸ Ring.additiveCommutators R) :=
  lift R (ProjectiveClass.traceModCommutators R)

/-- On a completed projective class, the K₀ trace equals the class trace.
This is the universal extension described in Weibel, *The K-book*, §II.2,
“Hattori–Stallings trace map”. -/
@[simp]
theorem traceModCommutators_ofClass (a : ProjectiveClass R) :
    traceModCommutators R (ofClass R a) =
      ProjectiveClass.traceModCommutators R a := by
  exact lift_ofClass R (ProjectiveClass.traceModCommutators R) a

end K0

end KTheory
