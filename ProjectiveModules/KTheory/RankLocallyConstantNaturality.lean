/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.RankLocallyConstantRing
public import ProjectiveModules.KTheory.RingScalarExtension
public import ProjectiveModules.Module.RightExtensionTensorProduct

/-!
# Naturality of locally constant rank

For any unital map of commutative rings, rank commutes with the original right
extension of scalars. The opposite-ring spectrum square identifies the original
rank pullback with the usual contravariant map on prime spectra.

The projective-class diagram is an equality of semiring homomorphisms. The K₀
diagram is an equality of additive homomorphisms through the existing `K0.map`;
no multiplicative structure on that map is introduced here.

The module comparison reuses `ModuleCat.RightExtension.oppositeScalarEquiv`
and the module-rank base-change law. The proofs retain the original
module actions, and use the canonical opposite-map algebra only locally.
-/

@[expose] public section

universe uR uS uM

open scoped TensorProduct

namespace KTheory.ProjectiveClass

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- The canonical maps from opposite commutative rings commute with every ring map. -/
theorem rankLocallyConstant_opposite_square (f : R →+* S) :
    (RingEquiv.toOpposite S).symm.toRingHom.comp f.op =
      f.comp (RingEquiv.toOpposite R).symm.toRingHom := by
  ext x
  rfl

/-- The contravariant spectrum square for the original opposite-ring rank pullback. -/
theorem rankLocallyConstant_spectrum_square (f : R →+* S) :
    (PrimeSpectrum.comap f.op) ∘
        (PrimeSpectrum.comap (RingEquiv.toOpposite S).symm.toRingHom) =
      (PrimeSpectrum.comap (RingEquiv.toOpposite R).symm.toRingHom) ∘
        (PrimeSpectrum.comap f) := by
  rw [← PrimeSpectrum.comap_comp, ← PrimeSpectrum.comap_comp,
    rankLocallyConstant_opposite_square]

end KTheory.ProjectiveClass

namespace Module

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- The rank of the original right extension is the opposite-map pullback of rank. -/
theorem rankLocallyConstant_rightExtension (f : R →+* S)
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    rankLocallyConstant Sᵐᵒᵖ (ModuleCat.RightExtension.Obj f M) =
      LocallyConstant.comapRingHom
        ⟨PrimeSpectrum.comap f.op, PrimeSpectrum.continuous_comap f.op⟩
        (rankLocallyConstant Rᵐᵒᵖ M) := by
  let : Algebra Rᵐᵒᵖ Sᵐᵒᵖ := f.op.toAlgebra
  let e : ModuleCat.RightExtension.Obj f M ≃ₗ[Sᵐᵒᵖ] Sᵐᵒᵖ ⊗[Rᵐᵒᵖ] M :=
    ModuleCat.RightExtension.oppositeScalarEquiv f (ModuleCat.of Rᵐᵒᵖ M)
  calc
    rankLocallyConstant Sᵐᵒᵖ (ModuleCat.RightExtension.Obj f M) =
        rankLocallyConstant Sᵐᵒᵖ (Sᵐᵒᵖ ⊗[Rᵐᵒᵖ] M) :=
      rankLocallyConstant_eq_of_equiv Sᵐᵒᵖ _ _ e
    _ = _ := rankLocallyConstant_baseChange Rᵐᵒᵖ M Sᵐᵒᵖ

end Module

namespace KTheory.ProjectiveClass

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- Raw class rank commutes with the existing projective-class scalar-extension map. -/
theorem rankLocallyConstant_mapRingHom (f : R →+* S) (a : ProjectiveClass R) :
    rankLocallyConstant S (mapRingHom f a) =
      LocallyConstant.comapRingHom
        ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩
        (rankLocallyConstant R a) := by
  refine induction_on R a ?_
  intro X
  rw [mapRingHom_of, rankLocallyConstant_of_module,
    Module.rankLocallyConstant_rightExtension, rankLocallyConstant_of_module]
  ext p
  change Module.rankLocallyConstant Rᵐᵒᵖ X
      (PrimeSpectrum.comap f.op
        (PrimeSpectrum.comap (RingEquiv.toOpposite S).symm.toRingHom p)) =
    Module.rankLocallyConstant Rᵐᵒᵖ X
      (PrimeSpectrum.comap (RingEquiv.toOpposite R).symm.toRingHom
        (PrimeSpectrum.comap f p))
  exact congrArg (Module.rankLocallyConstant Rᵐᵒᵖ X)
    (congrFun (rankLocallyConstant_spectrum_square f) p)

/-- Naturality of class rank as an equality of semiring homomorphisms. -/
theorem rankLocallyConstantRingHom_naturality (f : R →+* S) :
    (rankLocallyConstantRingHom S).comp (mapRingHom f) =
      (LocallyConstant.comapRingHom
        ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩).comp
        (rankLocallyConstantRingHom R) := by
  apply RingHom.ext
  intro a
  exact rankLocallyConstant_mapRingHom f a

end KTheory.ProjectiveClass

namespace KTheory.K0

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- Naturality of K₀ rank through the original additive scalar-extension map. -/
theorem rankLocallyConstantRingHom_naturality (f : R →+* S) :
    (rankLocallyConstantRingHom S).toAddMonoidHom.comp (K0.map f) =
      (LocallyConstant.comapRingHom
        ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩ :
          LocallyConstant (PrimeSpectrum R) ℤ →+*
            LocallyConstant (PrimeSpectrum S) ℤ).toAddMonoidHom.comp
        (rankLocallyConstantRingHom R).toAddMonoidHom := by
  apply K0.hom_ext_ofClass R
  intro a
  change rankLocallyConstantRingHom S (K0.map f (ofClass R a)) =
    LocallyConstant.comapRingHom
      ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩
      (rankLocallyConstantRingHom R (ofClass R a))
  rw [K0.map_ofClass, rankLocallyConstantRingHom_ofClass,
    rankLocallyConstantRingHom_ofClass]
  change LocallyConstant.mapRingHom (Nat.castRingHom ℤ)
      (ProjectiveClass.rankLocallyConstant S (ProjectiveClass.map f a)) =
    LocallyConstant.comapRingHom
      ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩
      (LocallyConstant.mapRingHom (Nat.castRingHom ℤ)
        (ProjectiveClass.rankLocallyConstant R a))
  rw [← ProjectiveClass.mapRingHom_apply,
    ProjectiveClass.rankLocallyConstant_mapRingHom]
  rfl

/-- The pointwise form of naturality, with the usual contravariant map on primes. -/
theorem rankLocallyConstantRingHom_map_apply (f : R →+* S)
    (x : K0 R) (p : PrimeSpectrum S) :
    rankLocallyConstantRingHom S (K0.map f x) p =
      rankLocallyConstantRingHom R x (PrimeSpectrum.comap f p) :=
  congrArg (fun F : K0 R →+ LocallyConstant (PrimeSpectrum S) ℤ ↦ F x p)
    (rankLocallyConstantRingHom_naturality f)

end KTheory.K0
