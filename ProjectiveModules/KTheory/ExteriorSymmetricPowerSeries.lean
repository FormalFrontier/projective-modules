/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.ExteriorPowerSeries
public import ProjectiveModules.KTheory.SymmetricPowerSeries
public import Mathlib.RingTheory.PowerSeries.Basic
import ProjectiveModules.KTheory.KoszulEulerCharacteristic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.Units.Hom

@[expose] public section

/-!
# Exterior and symmetric power series on K0

The exterior series with the formal variable negated is inverse to the
symmetric series. For finite projective modules this follows coefficientwise
from the homogeneous Koszul Euler identity. The universal property of the
Grothendieck group extends the product formula to every virtual class.
Negating the formal variable again gives the complementary formula.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, 2013.
-/

noncomputable section

open scoped BigOperators TensorProduct

universe u v

namespace KTheory.K0

variable (R : Type u) [CommRing R]

section ProjectiveModule

variable (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
variable [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]

private theorem koszulTerm_class (i j : ℕ) :
    of R (Module.Koszul.Term (Rᵐᵒᵖ) P i j) =
      of R (⋀[Rᵐᵒᵖ]^i P) *
        of R (SymmetricPower Rᵐᵒᵖ (ULift.{u} (Fin j)) P) := by
  exact (of_mul R (⋀[Rᵐᵒᵖ]^i P)
    (SymmetricPower Rᵐᵒᵖ (ULift.{u} (Fin j)) P)).symm

private theorem neg_one_pow_mul_eq_zsmul (i : ℕ) (a : K0 R) :
    (-1 : K0 R) ^ i * a = ((-1 : ℤ) ^ i) • a := by
  induction i with
  | zero => simp
  | succ i hi =>
      have hm :
          (-1 : K0 R) ^ i * (-1 : K0 R) =
            -((-1 : K0 R) ^ i) :=
        _root_.mul_neg_one ((-1 : K0 R) ^ i)
      have hn :
          (-((-1 : K0 R) ^ i)) * a =
            -(((-1 : K0 R) ^ i) * a) :=
        _root_.neg_mul ((-1 : K0 R) ^ i) a
      rw [_root_.pow_succ, hm, hn, hi, _root_.pow_succ,
        _root_.mul_neg_one, _root_.neg_smul]

/-- The sign-rescaled exterior series of a finitely generated projective
module times its symmetric series is one, by the homogeneous Koszul Euler
identity from Weibel's *The K-book*. -/
theorem totalExteriorSeries_rescale_neg_one_mul_totalSymmetricSeries_of :
    PowerSeries.rescale (-1 : K0 R)
        (totalExteriorSeries R (Multiplicative.ofAdd (of R P)) :
          PowerSeries (K0 R)) *
      (totalSymmetricSeries R (Multiplicative.ofAdd (of R P)) :
        PowerSeries (K0 R)) =
      (1 : PowerSeries (K0 R)) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one]
  simp only [PowerSeries.coeff_rescale, coeff_totalExteriorSeries_of,
    coeff_totalSymmetricSeries_of]
  have hsum (f : ℕ → ℕ → K0 R) :
      (∑ ij ∈ Finset.antidiagonal n, f ij.1 ij.2) =
        ∑ i ∈ Finset.range (n + 1), f i (n - i) := by
    simpa only [toAdd_prod, toAdd_ofAdd, Nat.succ_eq_add_one] using
      congrArg Multiplicative.toAdd
        (Finset.Nat.prod_antidiagonal_eq_prod_range_succ
          (fun i j => Multiplicative.ofAdd (f i j)) n)
  rw [hsum (fun i j =>
    ((-1 : K0 R) ^ i * of R (⋀[Rᵐᵒᵖ]^i P)) *
      of R (SymmetricPower Rᵐᵒᵖ (ULift.{u} (Fin j)) P))]
  calc
    (∑ i ∈ Finset.range (n + 1),
        ((-1 : K0 R) ^ i * of R (⋀[Rᵐᵒᵖ]^i P)) *
          of R (SymmetricPower Rᵐᵒᵖ (ULift.{u} (Fin (n - i))) P)) =
        ∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) •
          of R (Module.Koszul.Term (Rᵐᵒᵖ) P i (n - i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc, ← koszulTerm_class R P i (n - i)]
      exact neg_one_pow_mul_eq_zsmul R i _
    _ = if n = 0 then (1 : K0 R) else 0 :=
      Module.Koszul.alternatingK0Euler R P n


end ProjectiveModule

/-- The sign-rescaled exterior series times the symmetric series is one,
as in Weibel's *The K-book*. -/
theorem totalExteriorSeries_rescale_neg_one_mul_totalSymmetricSeries
    (x : K0 R) :
    PowerSeries.rescale (-1 : K0 R)
        (totalExteriorSeries R (Multiplicative.ofAdd x) : PowerSeries (K0 R)) *
      (totalSymmetricSeries R (Multiplicative.ofAdd x) : PowerSeries (K0 R)) =
        (1 : PowerSeries (K0 R)) := by
  let F : Multiplicative (K0 R) →* Units (PowerSeries (K0 R)) :=
    @Mul.mul _
      (MonoidHom.mul
        (M := Multiplicative (K0 R))
        (N := Units (PowerSeries (K0 R))))
      ((Units.map
          (PowerSeries.rescale (-1 : K0 R) :
            PowerSeries (K0 R) →* PowerSeries (K0 R))).comp
          (totalExteriorSeries R))
      (totalSymmetricSeries R)
  have hF_apply (y : K0 R) :
      (F (Multiplicative.ofAdd y) : PowerSeries (K0 R)) =
        PowerSeries.rescale (-1 : K0 R)
            (totalExteriorSeries R (Multiplicative.ofAdd y) :
              PowerSeries (K0 R)) *
          (totalSymmetricSeries R (Multiplicative.ofAdd y) :
            PowerSeries (K0 R)) := by
    rfl
  have htag (f : Multiplicative (K0 R) →* Units (PowerSeries (K0 R)))
      (y : K0 R) :
      MonoidHom.toAdditiveRight f y =
        Additive.ofMul (f (Multiplicative.ofAdd y)) :=
    congrFun (MonoidHom.coe_toAdditiveRight f) y
  let f : K0 R →+ Additive (Units (PowerSeries (K0 R))) :=
    MonoidHom.toAdditiveRight F
  let g : K0 R →+ Additive (Units (PowerSeries (K0 R))) :=
    MonoidHom.toAdditiveRight
      (1 : Multiplicative (K0 R) →* Units (PowerSeries (K0 R)))
  have hfg : f = g := by
    apply KTheory.K0.hom_ext R
      (G := Additive (Units (PowerSeries (K0 R)))) (f := f) (g := g)
    intro P
    simp only [f, g, htag, MonoidHom.one_apply]
    apply congrArg Additive.ofMul
    apply Units.coeHom_injective
    simpa only [Units.coeHom_apply, hF_apply, Units.val_one] using
      totalExteriorSeries_rescale_neg_one_mul_totalSymmetricSeries_of R P
  have hF : F =
      (1 : Multiplicative (K0 R) →* Units (PowerSeries (K0 R))) :=
    MonoidHom.toAdditiveRight.injective hfg
  have hx := congrArg
    (fun h : Multiplicative (K0 R) →* Units (PowerSeries (K0 R)) =>
      (h (Multiplicative.ofAdd x) : PowerSeries (K0 R))) hF
  simpa only [hF_apply, MonoidHom.one_apply, Units.val_one] using hx

/-- The exterior series times the sign-rescaled symmetric series is one,
by the power-series identity in Weibel's *The K-book* after negating the variable. -/
theorem totalExteriorSeries_mul_totalSymmetricSeries_rescale_neg_one
    (x : K0 R) :
    (totalExteriorSeries R (Multiplicative.ofAdd x) : PowerSeries (K0 R)) *
      PowerSeries.rescale (-1 : K0 R)
        (totalSymmetricSeries R (Multiplicative.ofAdd x) : PowerSeries (K0 R)) =
          (1 : PowerSeries (K0 R)) := by
  have h := congrArg (PowerSeries.rescale (-1 : K0 R))
    (totalExteriorSeries_rescale_neg_one_mul_totalSymmetricSeries R x)
  rw [RingHom.map_mul, RingHom.map_one, PowerSeries.rescale_rescale] at h
  have hneg : (-1 : K0 R) * (-1 : K0 R) = 1 := by
    exact (_root_.mul_neg_one (-1 : K0 R)).trans (_root_.neg_neg (1 : K0 R))
  simpa only [hneg, PowerSeries.rescale_one, RingHom.id_apply] using h


end KTheory.K0
