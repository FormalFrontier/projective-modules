/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.RankLocallyConstant
public import ProjectiveModules.KTheory.Ring

/-!
# Rank homomorphisms on projective classes and K₀

The locally constant rank of a finite projective right module is additive for
products and multiplicative for tensor products. Public representative induction
therefore bundles the existing class-rank function as
`KTheory.ProjectiveClass.rankLocallyConstantRingHom`. Its entire underlying
function is the original rank function, with the original opposite-ring action.

`KTheory.K0.rankLocallyConstantRingHom` is the Grothendieck additive group's
ring lift after the canonical natural-to-integer cast. Its additive
projection is definitionally the original `K0.lift`, not a second completion.
Neither construction assumes a nonempty spectrum or constant rank.

The proofs use this library's representative and tensor-product APIs, the module
rank laws following Andrew Yang's Mathlib stalk-rank formalization, and the
`Algebra.GrothendieckAddGroup.liftRingHom` universal property.
-/

@[expose] public section

universe uR uM

open scoped TensorProduct

namespace KTheory.ProjectiveClass

variable (R : Type uR) [CommRing R]

/-- The rank of the zero projective class is zero, including over the zero ring. -/
@[simp]
theorem rankLocallyConstant_zero : rankLocallyConstant R 0 = 0 := by
  rw [← of_zero R (Fin 0 → Rᵐᵒᵖ), rankLocallyConstant_of_module,
    Module.rankLocallyConstant_eq_zero_of_subsingleton]
  rfl

/-- The unit class is the original regular right module and has rank one. -/
@[simp]
theorem rankLocallyConstant_one : rankLocallyConstant R 1 = 1 := by
  rw [one_eq_of, rankLocallyConstant_of_module, Module.rankLocallyConstant_self]
  rfl

/-- Class rank is additive because a product of modules represents addition. -/
@[simp]
theorem rankLocallyConstant_add (a b : ProjectiveClass R) :
    rankLocallyConstant R (a + b) =
      rankLocallyConstant R a + rankLocallyConstant R b := by
  refine induction_on R a ?_
  intro X
  refine induction_on R b ?_
  intro Y
  rw [← of_prod R X Y]
  simp only [rankLocallyConstant_of_module, Module.rankLocallyConstant_prod]
  rfl

/-- Class rank is multiplicative for the tensor product of the original right modules. -/
@[simp]
theorem rankLocallyConstant_mul (a b : ProjectiveClass R) :
    rankLocallyConstant R (a * b) =
      rankLocallyConstant R a * rankLocallyConstant R b := by
  refine induction_on R a ?_
  intro X
  refine induction_on R b ?_
  intro Y
  rw [of_mul R X Y]
  simp only [rankLocallyConstant_of_module, Module.rankLocallyConstant_tensorProduct]
  rfl

/-- Natural-valued locally constant rank as a semiring homomorphism on projective classes. -/
noncomputable def rankLocallyConstantRingHom :
    ProjectiveClass R →+* LocallyConstant (PrimeSpectrum R) ℕ where
  toFun := rankLocallyConstant R
  map_zero' := rankLocallyConstant_zero R
  map_one' := rankLocallyConstant_one R
  map_add' := rankLocallyConstant_add R
  map_mul' := rankLocallyConstant_mul R

/-- The entire underlying function is the original class-rank function. -/
@[simp]
theorem rankLocallyConstantRingHom_toFun :
    (rankLocallyConstantRingHom R : ProjectiveClass R →
      LocallyConstant (PrimeSpectrum R) ℕ) = rankLocallyConstant R := rfl

/-- Evaluation of the bundled homomorphism uses the original rank function. -/
@[simp]
theorem rankLocallyConstantRingHom_apply (a : ProjectiveClass R) :
    rankLocallyConstantRingHom R a = rankLocallyConstant R a := rfl

/-- The class-rank homomorphism on a module in any carrier universe. -/
@[simp]
theorem rankLocallyConstantRingHom_of_module
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    rankLocallyConstantRingHom R (of R M) =
      LocallyConstant.comap
        (toContinuousMap (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.toOpposite R)))
        (Module.rankLocallyConstant Rᵐᵒᵖ M) :=
  rankLocallyConstant_of_module R M

/-- At a prime, the class-rank homomorphism is the original opposite-module stalk rank. -/
@[simp]
theorem rankLocallyConstantRingHom_of_module_apply
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] (p : PrimeSpectrum R) :
    rankLocallyConstantRingHom R (of R M) p =
      Module.rankAtStalk (R := Rᵐᵒᵖ) M
        (PrimeSpectrum.comap (RingEquiv.toOpposite R).symm.toRingHom p) :=
  rankLocallyConstant_of_module_apply R M p

/-- The original reference-module values uniquely determine the class-rank homomorphism. -/
theorem rankLocallyConstantRingHom_unique
    (F : ProjectiveClass R →+* LocallyConstant (PrimeSpectrum R) ℕ)
    (h : ∀ X : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ,
      F (of R X) =
        LocallyConstant.comap
          (toContinuousMap (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.toOpposite R)))
          (Module.rankLocallyConstant Rᵐᵒᵖ X)) :
    F = rankLocallyConstantRingHom R := by
  apply RingHom.ext
  intro a
  exact congrFun (rankLocallyConstant_unique R (fun a ↦ F a) h) a

/-- Equality with class rank can be checked on reference finite-projective modules. -/
theorem rankLocallyConstantRingHom_ext
    (F : ProjectiveClass R →+* LocallyConstant (PrimeSpectrum R) ℕ)
    (h : ∀ X : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ,
      F (of R X) = rankLocallyConstantRingHom R (of R X)) :
    F = rankLocallyConstantRingHom R := by
  apply rankLocallyConstantRingHom_unique R F
  intro X
  exact (h X).trans (rankLocallyConstantRingHom_of_module R X)

end KTheory.ProjectiveClass

namespace KTheory.K0

variable (R : Type uR) [CommRing R]

/-- Integer-valued locally constant rank on the existing Grothendieck group K₀. -/
noncomputable def rankLocallyConstantRingHom :
    K0 R →+* LocallyConstant (PrimeSpectrum R) ℤ :=
  Algebra.GrothendieckAddGroup.liftRingHom
    ((LocallyConstant.mapRingHom (Nat.castRingHom ℤ)).comp
      (ProjectiveClass.rankLocallyConstantRingHom R))

/-- The whole additive projection is definitionally the additive universal lift. -/
@[simp]
theorem rankLocallyConstantRingHom_toAddMonoidHom :
    (rankLocallyConstantRingHom R).toAddMonoidHom =
      K0.lift R
        (((LocallyConstant.mapRingHom (Nat.castRingHom ℤ)).comp
          (ProjectiveClass.rankLocallyConstantRingHom R)).toAddMonoidHom) := rfl

/-- On a class generator, K₀ rank is the canonical cast of its natural-valued rank. -/
@[simp]
theorem rankLocallyConstantRingHom_ofClass (a : ProjectiveClass R) :
    rankLocallyConstantRingHom R (ofClass R a) =
      LocallyConstant.mapRingHom (Nat.castRingHom ℤ)
        (ProjectiveClass.rankLocallyConstantRingHom R a) :=
  Algebra.GrothendieckAddGroup.liftRingHom_of _ a

/-- Bundled compatibility with the original class inclusion. -/
@[simp]
theorem rankLocallyConstantRingHom_comp_ofClassRingHom :
    (rankLocallyConstantRingHom R).comp (ofClassRingHom R) =
      (LocallyConstant.mapRingHom (Nat.castRingHom ℤ)).comp
        (ProjectiveClass.rankLocallyConstantRingHom R) := by
  apply RingHom.ext
  intro a
  exact rankLocallyConstantRingHom_ofClass R a

/-- K₀ rank on an arbitrary finite-projective right module, retaining its action. -/
@[simp]
theorem rankLocallyConstantRingHom_of
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    rankLocallyConstantRingHom R (of R M) =
      LocallyConstant.mapRingHom (Nat.castRingHom ℤ)
        (LocallyConstant.comap
          (toContinuousMap (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.toOpposite R)))
          (Module.rankLocallyConstant Rᵐᵒᵖ M)) := by
  rw [← ofClass_of, rankLocallyConstantRingHom_ofClass,
    ProjectiveClass.rankLocallyConstantRingHom_of_module]

/-- Prime evaluation of K₀ rank is the canonical integer cast of the original stalk rank. -/
@[simp]
theorem rankLocallyConstantRingHom_of_apply
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] (p : PrimeSpectrum R) :
    rankLocallyConstantRingHom R (of R M) p =
      ((Module.rankAtStalk (R := Rᵐᵒᵖ) M
        (PrimeSpectrum.comap (RingEquiv.toOpposite R).symm.toRingHom p) : ℕ) : ℤ) := by
  rw [← ofClass_of, rankLocallyConstantRingHom_ofClass]
  change ((ProjectiveClass.rankLocallyConstantRingHom R (ProjectiveClass.of R M) p : ℕ) : ℤ) = _
  rw [ProjectiveClass.rankLocallyConstantRingHom_of_module_apply]

/-- K₀ rank is uniquely determined by its values on the original class generators. -/
theorem rankLocallyConstantRingHom_unique
    (F : K0 R →+* LocallyConstant (PrimeSpectrum R) ℤ)
    (h : ∀ a : ProjectiveClass R,
      F (ofClass R a) =
        LocallyConstant.mapRingHom (Nat.castRingHom ℤ)
          (ProjectiveClass.rankLocallyConstantRingHom R a)) :
    F = rankLocallyConstantRingHom R := by
  exact (Algebra.GrothendieckAddGroup.liftRingHom_unique _ F h).symm

/-- The existing additive universal property checks equality with K₀ rank on modules. -/
theorem rankLocallyConstantRingHom_ext
    (F : K0 R →+* LocallyConstant (PrimeSpectrum R) ℤ)
    (h : ∀ X : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ,
      F (of R X) = rankLocallyConstantRingHom R (of R X)) :
    F = rankLocallyConstantRingHom R := by
  have heq : F.toAddMonoidHom = (rankLocallyConstantRingHom R).toAddMonoidHom :=
    K0.hom_ext R h
  apply RingHom.ext
  intro x
  exact DFunLike.congr_fun heq x

end KTheory.K0
