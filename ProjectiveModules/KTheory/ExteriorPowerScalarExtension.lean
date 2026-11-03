/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.Projective
public import ProjectiveModules.ExteriorPower.RightScalarExtension
public import ProjectiveModules.KTheory.RingScalarExtension

/-!
# Exterior-power classes and scalar extension

The class of an exterior power of a finite projective right module commutes
with extension of scalars. The coefficient-level linear equivalence is the
existing right exterior-power comparison; the map on K₀ is the existing
scalar-extension ring homomorphism.
-/

@[expose] public section

universe uR uS uP

namespace KTheory.K0

/-- Scalar extension sends the class of an exterior power of a finite projective
right module to the class of the exterior power of its scalar extension. -/
theorem mapRingHom_exteriorPower
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (P : Type uP)
    [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P] :
    mapRingHom f (of R (⋀[Rᵐᵒᵖ]^n P)) =
      of S (⋀[Sᵐᵒᵖ]^n (ModuleCat.RightExtension.Obj f P)) := by
  rw [mapRingHom_of]
  exact of_eq_of_equiv S _ (exteriorPower.rightExtensionEquiv f n P)

end KTheory.K0
