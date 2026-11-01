/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Ring
public import ProjectiveModules.Module.SymmetricPower
import ProjectiveModules.KTheory.Product
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Total symmetric-power series on the Grothendieck group

For a commutative ring `R`, `KTheory.K0.totalSymmetricSeries` sends addition in `K0 R`
to multiplication of units of `PowerSeries (K0 R)`. On a finite projective right
`R`-module its coefficients are the classes of the symmetric powers over `Rᵐᵒᵖ`.
The construction first descends through projective isomorphism classes, then uses
the additive universal property of `K0 R`.

The constant coefficient is one and the linear coefficient recovers every virtual
class. In particular the negative regular-module class has series `1 - X`.
These are fixed-ring additive operations; no compatibility with tensor products
of virtual classes is asserted.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, 2013,
  for background on Grothendieck groups and symmetric-power operations.
* The construction uses the symmetric-power and Cauchy APIs of ProjectiveModules
  and Mathlib's power-series units and additive/multiplicative type tags.
-/

public section

noncomputable section

universe uR uM uN

namespace KTheory.K0

variable (R : Type uR) [CommRing R]

private def symmetricSeries
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    PowerSeries (K0 R) :=
  PowerSeries.mk (fun n =>
    of R (SymmetricPower Rᵐᵒᵖ (ULift.{uR} (Fin n)) M))

private theorem symmetricSeries_constantCoeff
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    PowerSeries.constantCoeff (symmetricSeries R M) = 1 := by
  rw [symmetricSeries, PowerSeries.constantCoeff_mk]
  exact (of_eq_of_equiv R _
    (SymmetricPower.isEmptyEquiv (R := Rᵐᵒᵖ)
      (ι := ULift.{uR} (Fin 0)) (M := M))).trans (of_self R)

private theorem symmetricSeries_isUnit
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    IsUnit (symmetricSeries R M) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [symmetricSeries_constantCoeff]
  exact isUnit_one

private def symmetricSeriesUnit
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    Units (PowerSeries (K0 R)) :=
  (symmetricSeries_isUnit R M).unit

private theorem coe_symmetricSeriesUnit
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    (symmetricSeriesUnit R M : PowerSeries (K0 R)) = symmetricSeries R M :=
  IsUnit.unit_spec (symmetricSeries_isUnit R M)

private theorem symmetricSeriesUnit_equiv
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (N : Type uN) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N]
    (e : M ≃ₗ[Rᵐᵒᵖ] N) :
    symmetricSeriesUnit R M = symmetricSeriesUnit R N := by
  apply Units.ext
  rw [coe_symmetricSeriesUnit, coe_symmetricSeriesUnit]
  apply PowerSeries.ext
  intro n
  rw [symmetricSeries, symmetricSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  exact of_eq_of_equiv R _ (LinearEquiv.ofLinearMap
    (SymmetricPower.map (ι := ULift.{uR} (Fin n)) e.toLinearMap)
    (SymmetricPower.map (ι := ULift.{uR} (Fin n)) e.symm.toLinearMap)
    (SymmetricPower.map_comp_eq_id e.comp_symm)
    (SymmetricPower.map_comp_eq_id e.symm_comp))

private theorem symmetricSeriesUnit_zero :
    symmetricSeriesUnit R PUnit.{uR + 1} = 1 := by
  apply Units.ext
  change (symmetricSeriesUnit R PUnit.{uR + 1} : PowerSeries (K0 R)) = 1
  rw [coe_symmetricSeriesUnit]
  apply PowerSeries.ext
  intro n
  rw [symmetricSeries, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  cases n with
  | zero =>
      change of R (SymmetricPower Rᵐᵒᵖ (ULift.{uR} (Fin 0)) PUnit.{uR + 1}) = 1
      exact (of_eq_of_equiv R _
        (SymmetricPower.isEmptyEquiv (R := Rᵐᵒᵖ)
          (ι := ULift.{uR} (Fin 0)) (M := PUnit.{uR + 1}))).trans (of_self R)
  | succ n =>
      change of R
        (SymmetricPower Rᵐᵒᵖ (ULift.{uR} (Fin (n + 1))) PUnit.{uR + 1}) = 0
      exact of_zero R _

private theorem of_addCommMonoidToAddCommGroup
    (P : Type uM) [hadd : AddCommGroup P] [hmodule : Module Rᵐᵒᵖ P]
    [hfinite : Module.Finite Rᵐᵒᵖ P] [hprojective : Module.Projective Rᵐᵒᵖ P] :
    @of R _ P (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
        hmodule hfinite hprojective = of R P := by
  exact
    @of_eq_of_equiv R _ P (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
      hmodule hfinite hprojective P hadd hmodule hfinite hprojective
      { toFun := id
        invFun := id
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }

open scoped TensorProduct BigOperators in
private theorem symmetricSeriesUnit_prod
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (N : Type uN) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    symmetricSeriesUnit R (M × N) =
      symmetricSeriesUnit R M * symmetricSeriesUnit R N := by
  classical
  apply Units.ext
  change (symmetricSeriesUnit R (M × N) : PowerSeries (K0 R)) =
    (symmetricSeriesUnit R M : PowerSeries (K0 R)) *
      (symmetricSeriesUnit R N : PowerSeries (K0 R))
  rw [coe_symmetricSeriesUnit, coe_symmetricSeriesUnit, coe_symmetricSeriesUnit]
  apply PowerSeries.ext
  intro n
  simp only [symmetricSeries, PowerSeries.coeff_mul, PowerSeries.coeff_mk]
  let f (i j : ℕ) : K0 R :=
    of R (SymmetricPower Rᵐᵒᵖ (ULift.{uR} (Fin i)) M) *
      of R (SymmetricPower Rᵐᵒᵖ (ULift.{uR} (Fin j)) N)
  let P (j : Fin (n + 1)) :=
    SymmetricPower Rᵐᵒᵖ (ULift.{uR} (Fin j.val)) M ⊗[Rᵐᵒᵖ]
      SymmetricPower Rᵐᵒᵖ (ULift.{uR} (Fin (n - j.val))) N
  obtain ⟨hfinitePi, hprojectivePi, hpi⟩ := of_pi R P
  have hpi' : of R (∀ j, P j) = ∑ j, of R (P j) := by
    have hleft :=
      of_addCommMonoidToAddCommGroup R (∀ j, P j)
        (hfinite := hfinitePi) (hprojective := hprojectivePi)
    have hright :=
      congrArg (fun g : Fin (n + 1) → K0 R => ∑ j, g j)
        (funext fun j : Fin (n + 1) =>
          of_addCommMonoidToAddCommGroup R (P j))
    exact hleft.symm.trans (hpi.trans hright)
  have hbin :
      of R (SymmetricPower Rᵐᵒᵖ (ULift.{uR} (Fin n)) (M × N)) =
        ∑ j : Fin (n + 1), f j.val (n - j.val) := by
    calc
      _ = of R (∀ j, P j) := by
        apply of_eq_of_equiv R
        exact
          (SymmetricPower.binomialEquiv
            (R := Rᵐᵒᵖ) (M := M) (N := N) n).trans
            (DirectSum.linearEquivFunOnFintype
              (R := Rᵐᵒᵖ) (ι := Fin (n + 1)) (M := P))
      _ = ∑ j, of R (P j) := hpi'
      _ = ∑ j : Fin (n + 1), f j.val (n - j.val) := by
        apply congrArg (fun g : Fin (n + 1) → K0 R => ∑ j, g j)
        funext j
        exact (of_mul R _ _).symm
  have hanti :
      (∑ p ∈ Finset.antidiagonal n, f p.1 p.2) =
        ∑ j : Fin (n + 1), f j.val (n - j.val) := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1), f k (n - k) := by
        simpa only [toAdd_prod, toAdd_ofAdd] using
          congrArg Multiplicative.toAdd
            (Finset.Nat.prod_antidiagonal_eq_prod_range_succ
              (M := Multiplicative (K0 R))
              (fun i j => Multiplicative.ofAdd (f i j)) n)
      _ = ∑ j : Fin (n + 1), f j.val (n - j.val) := by
        simpa only [toAdd_prod, toAdd_ofAdd] using
          congrArg Multiplicative.toAdd
            (Finset.prod_range (M := Multiplicative (K0 R)) (n := n + 1)
              (fun i => Multiplicative.ofAdd (f i (n - i))))
  exact hbin.trans hanti.symm

private def symmetricSeriesClass :
    ProjectiveClass R →+ Additive (Units (PowerSeries (K0 R))) :=
  ProjectiveClass.lift R
    (fun X : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ =>
      Additive.ofMul (symmetricSeriesUnit R X))
    (by
      intro X Y e
      change symmetricSeriesUnit R X = symmetricSeriesUnit R Y
      exact symmetricSeriesUnit_equiv R X Y
        (ModuleCat.FiniteProjective.isoToLinearEquiv e))
    (by
      change symmetricSeriesUnit R PUnit.{uR + 1} = 1
      exact symmetricSeriesUnit_zero R)
    (by
      intro X Y
      change symmetricSeriesUnit R (X × Y) =
        symmetricSeriesUnit R X * symmetricSeriesUnit R Y
      exact symmetricSeriesUnit_prod R X Y)

/-- The total symmetric-power series on `K0 R`, viewed multiplicatively on its
additive group. Its value on a finite projective right module is the series of
symmetric-power classes. -/
def totalSymmetricSeries :
    Multiplicative (K0 R) →* Units (PowerSeries (K0 R)) :=
  AddMonoidHom.toMultiplicativeLeft
    (lift R (G := Additive (Units (PowerSeries (K0 R)))) (symmetricSeriesClass R))

/-- On a finite projective right module, each coefficient is the class of the
corresponding symmetric power over the right scalar ring. -/
@[simp] theorem coeff_totalSymmetricSeries_of
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] (n : ℕ) :
    PowerSeries.coeff n
        (totalSymmetricSeries R (Multiplicative.ofAdd (of R M)) :
          PowerSeries (K0 R)) =
      of R (SymmetricPower Rᵐᵒᵖ (ULift.{uR} (Fin n)) M) := by
  have h : totalSymmetricSeries R (Multiplicative.ofAdd (of R M)) =
      symmetricSeriesUnit R M := by
    change Additive.toMul
      (lift R (G := Additive (Units (PowerSeries (K0 R))))
        (symmetricSeriesClass R) (of R M)) = symmetricSeriesUnit R M
    rw [lift_of]
    unfold symmetricSeriesClass
    rw [ProjectiveClass.lift_of_module
      (R := R) (M := M)
      (f := fun X : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ =>
        Additive.ofMul (symmetricSeriesUnit R X))
      (hiso := by
        intro X Y e
        change symmetricSeriesUnit R X = symmetricSeriesUnit R Y
        exact symmetricSeriesUnit_equiv R X Y
          (ModuleCat.FiniteProjective.isoToLinearEquiv e))]
    exact symmetricSeriesUnit_equiv R _ M
      (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ M)
  rw [h, coe_symmetricSeriesUnit, symmetricSeries, PowerSeries.coeff_mk]

/-- Every total symmetric-power series has constant coefficient one. -/
@[simp] theorem constantCoeff_totalSymmetricSeries (x : K0 R) :
    PowerSeries.constantCoeff
        (totalSymmetricSeries R (Multiplicative.ofAdd x) : PowerSeries (K0 R)) = 1 := by
  let f : K0 R →+ Additive (Units (K0 R)) :=
    MonoidHom.toAdditiveRight
      ((Units.map (PowerSeries.constantCoeff (R := K0 R)).toMonoidHom).comp
        (totalSymmetricSeries R))
  let g : K0 R →+ Additive (Units (K0 R)) :=
    { toFun := fun _ => Additive.ofMul 1
      map_zero' := rfl
      map_add' := fun _ _ => by
        change (1 : Units (K0 R)) = 1 * 1
        rw [one_mul] }
  have h : f = g := by
    refine KTheory.K0.hom_ext R
      (G := Additive (Units (K0 R))) (f := f) (g := g) ?_
    intro M
    change (Units.map (PowerSeries.constantCoeff (R := K0 R)).toMonoidHom)
        (totalSymmetricSeries R (Multiplicative.ofAdd (of R M))) = 1
    apply Units.ext
    rw [Units.coe_map, Units.val_one]
    change PowerSeries.constantCoeff
        (totalSymmetricSeries R (Multiplicative.ofAdd (of R M)) :
          PowerSeries (K0 R)) = 1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_totalSymmetricSeries_of]
    exact (of_eq_of_equiv R _
      (SymmetricPower.isEmptyEquiv
        (R := Rᵐᵒᵖ) (ι := ULift.{uR} (Fin 0)) (M := M))).trans
      (one_eq_of R).symm
  have hx := congrArg
    (fun h : K0 R →+ Additive (Units (K0 R)) =>
      ((Additive.toMul (h x) : Units (K0 R)) : K0 R)) h
  change PowerSeries.constantCoeff
      (totalSymmetricSeries R (Multiplicative.ofAdd x) :
        PowerSeries (K0 R)) = 1 at hx
  exact hx

/-- The first coefficient of the total symmetric-power series recovers any
virtual class, not only a class represented by a projective module. -/
@[simp] theorem coeff_one_totalSymmetricSeries (x : K0 R) :
    PowerSeries.coeff 1
        (totalSymmetricSeries R (Multiplicative.ofAdd x) : PowerSeries (K0 R)) = x := by
  let f : K0 R →+ K0 R :=
    { toFun := fun y => PowerSeries.coeff 1
        (totalSymmetricSeries R (Multiplicative.ofAdd y) : PowerSeries (K0 R))
      map_zero' := by
        rw [ofAdd_zero, map_one, Units.val_one, PowerSeries.coeff_one]
        simp
      map_add' := fun y z => by
        rw [ofAdd_add, map_mul, Units.val_mul, PowerSeries.coeff_one_mul,
          constantCoeff_totalSymmetricSeries, constantCoeff_totalSymmetricSeries]
        simp only [mul_one] }
  let g : K0 R →+ K0 R :=
    { toFun := fun y => y
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h : f = g := by
    apply hom_ext R
    intro M
    change PowerSeries.coeff 1
        (totalSymmetricSeries R (Multiplicative.ofAdd (of R M)) :
          PowerSeries (K0 R)) = of R M
    rw [coeff_totalSymmetricSeries_of]
    exact of_eq_of_equiv R _
      (SymmetricPower.subsingletonEquiv
        (R := Rᵐᵒᵖ) (ι := ULift.{uR} (Fin 1)) (M := M)
        (ULift.up (0 : Fin 1)))
  exact congrArg (fun h : K0 R →+ K0 R => h x) h

/-- Addition of virtual classes corresponds to multiplication of their total
symmetric-power series. -/
theorem totalSymmetricSeries_add (x y : K0 R) :
    totalSymmetricSeries R (Multiplicative.ofAdd (x + y)) =
      totalSymmetricSeries R (Multiplicative.ofAdd x) *
        totalSymmetricSeries R (Multiplicative.ofAdd y) := by
  rw [ofAdd_add, map_mul]

/-- A difference of virtual classes has the quotient of their unit-valued total
symmetric-power series. -/
theorem totalSymmetricSeries_sub (x y : K0 R) :
    totalSymmetricSeries R (Multiplicative.ofAdd (x - y)) =
      totalSymmetricSeries R (Multiplicative.ofAdd x) /
        totalSymmetricSeries R (Multiplicative.ofAdd y) := by
  rw [ofAdd_sub, map_div]

private theorem symmetricSeries_regular :
    symmetricSeries R Rᵐᵒᵖ = PowerSeries.mk (fun _ : ℕ => (1 : K0 R)) := by
  unfold symmetricSeries
  congr 1
  funext n
  exact (of_eq_of_equiv R _
    (SymmetricPower.baseRingEquiv Rᵐᵒᵖ (ULift.{uR} (Fin n)))).trans (of_self R)

/-- The total symmetric-power series of the negative regular-module class is
`1 - X`, with coefficients in `K0 R`. -/
theorem totalSymmetricSeries_neg_one :
    (totalSymmetricSeries R (Multiplicative.ofAdd (-1 : K0 R)) :
        PowerSeries (K0 R)) =
      1 - PowerSeries.X := by
  let a : PowerSeries (K0 R) :=
    (totalSymmetricSeries R (Multiplicative.ofAdd (-1 : K0 R)) :
      PowerSeries (K0 R))
  let b : PowerSeries (K0 R) :=
    (totalSymmetricSeries R (Multiplicative.ofAdd (1 : K0 R)) :
      PowerSeries (K0 R))
  have hb : b = PowerSeries.mk (fun _ : ℕ => (1 : K0 R)) := by
    dsimp only [b]
    conv_lhs => rw [one_eq_of R]
    rw [← symmetricSeries_regular R]
    apply PowerSeries.ext
    intro n
    simp only [coeff_totalSymmetricSeries_of, symmetricSeries, PowerSeries.coeff_mk]
  have hab : a * b = 1 := by
    simp [a, b]
  have hbc : b * (1 - PowerSeries.X) = 1 := by
    rw [hb]
    exact PowerSeries.mk_one_mul_one_sub_eq_one (K0 R)
  change a = 1 - PowerSeries.X
  calc
    a = a * 1 := (mul_one a).symm
    _ = a * (b * (1 - PowerSeries.X)) := by rw [hbc]
    _ = (a * b) * (1 - PowerSeries.X) := (mul_assoc _ _ _).symm
    _ = 1 - PowerSeries.X := by rw [hab, one_mul]

end KTheory.K0
