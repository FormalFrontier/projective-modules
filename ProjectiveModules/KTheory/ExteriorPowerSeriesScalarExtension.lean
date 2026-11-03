/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.ExteriorPowerSeries
public import ProjectiveModules.KTheory.ExteriorPowerScalarExtension
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.Units.Hom

/-!
# Exterior series and extension of scalars

Extension of scalars commutes with the genuine total exterior series of every
virtual finite-projective class. The comparison is first proved on finite
projective right modules using exterior-power base change. The universal
property of K₀ then gives equality of the two unit-valued homomorphisms.
Coefficient naturality follows from this equality on the whole virtual group.

The coefficient map is the canonical scalar-extension ring homomorphism; its
underlying additive map is the existing scalar-extension map on K₀.

## References

C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §4,
for the exterior operations on K₀.
-/

public section

namespace KTheory.K0

universe uR uS uP

variable {R : Type uR} {S : Type uS}
variable [rR : CommRing R] [rS : CommRing S]

/-- Scalar extension commutes with the genuine exterior series of a finite
projective right module, with its given right-module structure. -/
theorem map_totalExteriorSeries_of
    (f : R →+* S) (P : Type uP)
    [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P] :
    PowerSeries.map (mapRingHom f)
        (totalExteriorSeries R (Multiplicative.ofAdd (of R P)) :
          PowerSeries (K0 R)) =
      (totalExteriorSeries S
        (Multiplicative.ofAdd
          (@map R S rR.toRing rS.toRing f (of R P))) :
        PowerSeries (K0 S)) := by
  rw [← mapRingHom_apply, mapRingHom_of]
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map, coeff_totalExteriorSeries_of,
    coeff_totalExteriorSeries_of, mapRingHom_exteriorPower]

/-- Scalar extension commutes with the genuine total exterior series as an
 equality of unit-valued homomorphisms on the whole virtual group. See C. A. Weibel,
 *The K-book*, Chapter II, §4, for the exterior operations on K₀. -/
theorem totalExteriorSeries_naturality (f : R →+* S) :
    (Units.map (PowerSeries.map (mapRingHom f)).toMonoidHom).comp
        (totalExteriorSeries R) =
      (totalExteriorSeries S).comp
        (AddMonoidHom.toMultiplicative (@map R S rR.toRing rS.toRing f)) := by
  let A : Multiplicative (K0 R) →* Units (PowerSeries (K0 S)) :=
    (Units.map (PowerSeries.map (mapRingHom f)).toMonoidHom).comp
      (totalExteriorSeries R)
  let B : Multiplicative (K0 R) →* Units (PowerSeries (K0 S)) :=
    (totalExteriorSeries S).comp
      (AddMonoidHom.toMultiplicative (@map R S rR.toRing rS.toRing f))
  have hgen (P : Type uR) [AddCommGroup P] [Module Rᵐᵒᵖ P]
      [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P] :
      A (Multiplicative.ofAdd (of R P)) =
        B (Multiplicative.ofAdd (of R P)) := by
    apply Units.ext
    simpa only [A, B, MonoidHom.comp_apply, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd] using
      map_totalExteriorSeries_of f P
  let A' : K0 R →+ Additive (Units (PowerSeries (K0 S))) :=
    MonoidHom.toAdditiveRight A
  let B' : K0 R →+ Additive (Units (PowerSeries (K0 S))) :=
    MonoidHom.toAdditiveRight B
  have hAdd : A' = B' := by
    refine @KTheory.K0.hom_ext R rR.toRing
      (Additive (Units (PowerSeries (K0 S)))) inferInstance A' B' ?_
    intro P
    simpa only [A', B', MonoidHom.coe_toAdditiveRight, Function.comp_apply] using
      congrArg Additive.ofMul (hgen P)
  have hhom : A = B := MonoidHom.toAdditiveRight.injective hAdd
  exact hhom

/-- Coefficientwise scalar extension of the genuine total exterior series is
 the genuine total exterior series of the scalar-extended virtual class. -/
theorem map_totalExteriorSeries (f : R →+* S) (x : K0 R) :
    PowerSeries.map (mapRingHom f)
        (totalExteriorSeries R (Multiplicative.ofAdd x) : PowerSeries (K0 R)) =
      (totalExteriorSeries S
        (Multiplicative.ofAdd (@map R S rR.toRing rS.toRing f x)) :
        PowerSeries (K0 S)) := by
  have hx := congrArg
    (fun F : Multiplicative (K0 R) →* Units (PowerSeries (K0 S)) =>
      (F (Multiplicative.ofAdd x) : PowerSeries (K0 S)))
    (totalExteriorSeries_naturality f)
  simpa only [MonoidHom.comp_apply, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd] using hx

/-- Every coefficient of the genuine exterior series commutes with the original
 additive scalar-extension map, including on negative virtual classes. -/
theorem map_coeff_totalExteriorSeries
    (f : R →+* S) (x : K0 R) (n : ℕ) :
    @map R S rR.toRing rS.toRing f
        (PowerSeries.coeff n
          (totalExteriorSeries R (Multiplicative.ofAdd x) : PowerSeries (K0 R))) =
      PowerSeries.coeff n
        (totalExteriorSeries S
          (Multiplicative.ofAdd (@map R S rR.toRing rS.toRing f x)) :
          PowerSeries (K0 S)) := by
  have hn := congrArg (PowerSeries.coeff n) (map_totalExteriorSeries f x)
  simpa only [PowerSeries.coeff_map, mapRingHom_apply] using hn

end KTheory.K0
