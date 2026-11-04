/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.FiniteFree
public import ProjectiveModules.Module.RightExtensionReflection

/-!
# Scalar extension with Jacobson-radical kernel

A surjective ring homomorphism whose kernel is contained in the Jacobson radical
induces an injective map on isomorphism classes of finitely generated projective
right modules, and consequently on `K₀`.

The ring-homomorphism formulation includes reduction modulo a two-sided ideal
contained in the Jacobson radical. No nontriviality or commutativity assumption
is needed.

## References

* C. A. Weibel, *The K-book*, Chapter II, Exercise 2.5 (reduction injectivity).
-/

@[expose] public section

universe uR uS

namespace KTheory

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

namespace ProjectiveClass

/-- Scalar extension along a surjective ring homomorphism with Jacobson-radical
kernel reflects equality of finitely generated projective isomorphism classes.
This is the ring-homomorphism form of Jacobson-radical reduction injectivity;
its quotient-map specialization underlies the reduction-injectivity statement in
Weibel, *The K-book*, Chapter II, Exercise 2.5. -/
theorem map_injective_of_surjective_of_ker_le_jacobson
    (f : R →+* S) (hf : Function.Surjective f)
    (hJac : RingHom.ker f ≤ Ideal.jacobson (⊥ : Ideal R)) :
    Function.Injective (map f) := by
  classical
  intro a b hab
  obtain ⟨P, rfl⟩ := of_surjective R a
  obtain ⟨Q, rfl⟩ := of_surjective R b
  simp only [map_of] at hab
  obtain ⟨e⟩ :=
    (of_eq_iff S (ModuleCat.RightExtension.Obj f P)
      (ModuleCat.RightExtension.Obj f Q)).mp hab
  obtain ⟨g, hg⟩ :=
    ModuleCat.RightExtension.map_surjective_of_surjective f hf e.toLinearMap
  have hmap : Function.Bijective (ModuleCat.RightExtension.map f g) := by
    rw [hg]
    exact e.bijective
  have hbij : Function.Bijective g :=
    ModuleCat.RightExtension.bijective_of_bijective_map_of_ker_le_jacobson_of_finite_source
      f hf hJac g hmap
  exact of_eq_of_equiv R P (LinearEquiv.ofBijective g hbij)

end ProjectiveClass

namespace K0

/-- A surjective ring homomorphism with Jacobson-radical kernel induces an
injective map on `K₀`. For quotient maps, this is reduction injectivity as in
Weibel, *The K-book*, Chapter II, Exercise 2.5. -/
theorem map_injective_of_surjective_of_ker_le_jacobson
    (f : R →+* S) (hf : Function.Surjective f)
    (hJac : RingHom.ker f ≤ Ideal.jacobson (⊥ : Ideal R)) :
    Function.Injective (map f) := by
  exact map_injective f
    (ProjectiveClass.map_injective_of_surjective_of_ker_le_jacobson f hf hJac)

end K0

end KTheory
