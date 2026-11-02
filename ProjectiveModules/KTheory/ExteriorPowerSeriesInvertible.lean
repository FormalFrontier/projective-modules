/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.InvertibleTwist
public import ProjectiveModules.KTheory.ExteriorPowerSeries
public import ProjectiveModules.KTheory.TensorPower
import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Exterior series under tensoring by an invertible module

Tensoring a virtual class by an invertible right module rescales its total
exterior series. The coefficient in degree n is multiplied by the n-th power of
the invertible module's class.

The module-level exterior-power equivalence proves the formula for finite
projective representatives. Equality of two additive homomorphisms into the
additive type tag of power-series units extends it to every virtual class.
Individual higher exterior coefficients need not be additive.

## References

* C. A. Weibel, *The K-book: an introduction to algebraic K-theory*, II.4.
-/

@[expose] public section

open scoped TensorProduct

universe uR uL uP

namespace KTheory.K0

private theorem totalExteriorSeries_of_mul_of
    (R : Type uR) [CommRing R]
    (L : Type uL) [AddCommGroup L] [Module Rᵐᵒᵖ L]
    [Module.Invertible Rᵐᵒᵖ L]
    (P : Type uP) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P] :
    (totalExteriorSeries R
        (Multiplicative.ofAdd (of R L * of R P)) : PowerSeries (K0 R)) =
      PowerSeries.rescale (of R L)
        (totalExteriorSeries R (Multiplicative.ofAdd (of R P)) :
          PowerSeries (K0 R)) := by
  rw [of_mul R L P]
  ext n
  rw [coeff_totalExteriorSeries_of, PowerSeries.coeff_rescale,
    coeff_totalExteriorSeries_of]
  calc
    of R (⋀[Rᵐᵒᵖ]^n (L ⊗[Rᵐᵒᵖ] P)) =
        of R (TensorPower Rᵐᵒᵖ n L ⊗[Rᵐᵒᵖ] (⋀[Rᵐᵒᵖ]^n P)) :=
      of_eq_of_equiv R _
        (exteriorPower.invertibleTwistEquiv Rᵐᵒᵖ L P n).symm
    _ = of R (TensorPower Rᵐᵒᵖ n L) * of R (⋀[Rᵐᵒᵖ]^n P) :=
      (of_mul R (TensorPower Rᵐᵒᵖ n L) (⋀[Rᵐᵒᵖ]^n P)).symm
    _ = of R L ^ n * of R (⋀[Rᵐᵒᵖ]^n P) := by
      -- This identity includes the scalar tensor power in degree zero.
      rw [of_tensorPower R L n]

variable (R : Type uR) [CommRing R]
variable (L : Type uL) [AddCommGroup L] [Module Rᵐᵒᵖ L]
variable [Module.Invertible Rᵐᵒᵖ L]

/-- Tensoring by an invertible right module rescales the total exterior series.
This is the line-module identity for exterior operations; see Weibel, *The K-book*, II.4. -/
theorem totalExteriorSeries_of_mul_invertible
    (x : K0 R) :
    (totalExteriorSeries R
        (Multiplicative.ofAdd (of R L * x)) : PowerSeries (K0 R)) =
      PowerSeries.rescale (of R L)
        (totalExteriorSeries R (Multiplicative.ofAdd x) :
          PowerSeries (K0 R)) := by
  let f : K0 R →+ Additive (Units (PowerSeries (K0 R))) :=
    MonoidHom.toAdditiveRight
      ((totalExteriorSeries R).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft (of R L))))
  let g : K0 R →+ Additive (Units (PowerSeries (K0 R))) :=
    MonoidHom.toAdditiveRight
      ((Units.map
          (PowerSeries.rescale (of R L) :
            PowerSeries (K0 R) →* PowerSeries (K0 R))).comp
        (totalExteriorSeries R))
  have hfg : f = g := by
    apply KTheory.K0.hom_ext R
      (G := Additive (Units (PowerSeries (K0 R))))
      (f := f) (g := g)
    intro P
    change
      totalExteriorSeries R
          (Multiplicative.ofAdd (of R L * of R P)) =
        Units.map
          (PowerSeries.rescale (of R L) :
            PowerSeries (K0 R) →* PowerSeries (K0 R))
          (totalExteriorSeries R (Multiplicative.ofAdd (of R P)))
    apply Units.ext
    change
      (totalExteriorSeries R
          (Multiplicative.ofAdd (of R L * of R P)) : PowerSeries (K0 R)) =
        PowerSeries.rescale (of R L)
          (totalExteriorSeries R (Multiplicative.ofAdd (of R P)) :
            PowerSeries (K0 R))
    exact totalExteriorSeries_of_mul_of R L P
  have hx := congrArg
    (fun h : K0 R →+ Additive (Units (PowerSeries (K0 R))) =>
      ((h x).toMul : PowerSeries (K0 R))) hfg
  change
    (totalExteriorSeries R
        (Multiplicative.ofAdd (of R L * x)) : PowerSeries (K0 R)) =
      PowerSeries.rescale (of R L)
        (totalExteriorSeries R (Multiplicative.ofAdd x) :
          PowerSeries (K0 R)) at hx
  exact hx

/-- The exterior coefficient of tensoring by an invertible module is multiplied
by the corresponding power of its class; see Weibel, *The K-book*, II.4. -/
theorem coeff_totalExteriorSeries_of_mul_invertible
    (x : K0 R) (n : ℕ) :
    PowerSeries.coeff n
        (totalExteriorSeries R
          (Multiplicative.ofAdd (of R L * x)) : PowerSeries (K0 R)) =
      of R L ^ n *
        PowerSeries.coeff n
          (totalExteriorSeries R (Multiplicative.ofAdd x) :
            PowerSeries (K0 R)) := by
  rw [totalExteriorSeries_of_mul_invertible R L x, PowerSeries.coeff_rescale]

end KTheory.K0
