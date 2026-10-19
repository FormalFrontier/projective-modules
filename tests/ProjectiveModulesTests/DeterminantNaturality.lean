/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.DeterminantNaturality
import ProjectiveModules.Module.RightProduct

/-!
# Specializations of determinant naturality

Integer reduction, arbitrary invertible lines, a product with local ranks zero
and one, and the zero-ring boundary instantiate the bundled scalar-extension
comparison and its pointwise formula.
-/

open KTheory

universe u v

example :
    (K0.determinantHom (ZMod 4)).comp (K0.map (Int.castRingHom (ZMod 4))) =
      (MonoidHom.toAdditive (CommRing.Pic.mapRingHom (Int.castRingHom (ZMod 4)))).comp
        (K0.determinantHom ℤ) :=
  K0.determinantHom_comp_map (Int.castRingHom (ZMod 4))

example (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (f : R →+* S) (ℓ : CommRing.Pic Rᵐᵒᵖ) :
    K0.determinantHom S (K0.map f (K0.of R (CommRing.Pic.AsModule ℓ))) =
      MonoidHom.toAdditive (CommRing.Pic.mapRingHom f)
        (K0.determinantHom R (K0.of R (CommRing.Pic.AsModule ℓ))) :=
  K0.determinantHom_map f (K0.of R (CommRing.Pic.AsModule ℓ))

section

local instance :
    Module.Finite (Bool → ℤ)ᵐᵒᵖ
      (ModuleCat.piRight (fun _ : Bool => ℤ)
        (fun c => ModuleCat.of ℤᵐᵒᵖ (Fin (if c then 1 else 0) → ℤᵐᵒᵖ))) :=
  Module.finite_piRight (fun _ : Bool => ℤ)
    (fun c => ModuleCat.of ℤᵐᵒᵖ (Fin (if c then 1 else 0) → ℤᵐᵒᵖ))

local instance :
    Module.Projective (Bool → ℤ)ᵐᵒᵖ
      (ModuleCat.piRight (fun _ : Bool => ℤ)
        (fun c => ModuleCat.of ℤᵐᵒᵖ (Fin (if c then 1 else 0) → ℤᵐᵒᵖ))) :=
  Module.projective_piRight (fun _ : Bool => ℤ)
    (fun c => ModuleCat.of ℤᵐᵒᵖ (Fin (if c then 1 else 0) → ℤᵐᵒᵖ))

example (b : Bool) :
    K0.determinantHom ℤ
        (K0.map (Pi.evalRingHom (fun _ : Bool => ℤ) b)
          (K0.of (Bool → ℤ) (ModuleCat.piRight (fun _ : Bool => ℤ)
            (fun c => ModuleCat.of ℤᵐᵒᵖ (Fin (if c then 1 else 0) → ℤᵐᵒᵖ))))) =
      MonoidHom.toAdditive (CommRing.Pic.mapRingHom (Pi.evalRingHom (fun _ : Bool => ℤ) b))
        (K0.determinantHom (Bool → ℤ)
          (K0.of (Bool → ℤ) (ModuleCat.piRight (fun _ : Bool => ℤ)
            (fun c => ModuleCat.of ℤᵐᵒᵖ (Fin (if c then 1 else 0) → ℤᵐᵒᵖ))))) :=
  K0.determinantHom_map (Pi.evalRingHom (fun _ : Bool => ℤ) b)
    (K0.of (Bool → ℤ) (ModuleCat.piRight (fun _ : Bool => ℤ)
      (fun c => ModuleCat.of ℤᵐᵒᵖ (Fin (if c then 1 else 0) → ℤᵐᵒᵖ))))

end

example :
    (K0.determinantHom (ZMod 1)).comp (K0.map (Int.castRingHom (ZMod 1))) =
      (MonoidHom.toAdditive (CommRing.Pic.mapRingHom (Int.castRingHom (ZMod 1)))).comp
        (K0.determinantHom ℤ) :=
  K0.determinantHom_comp_map (Int.castRingHom (ZMod 1))
