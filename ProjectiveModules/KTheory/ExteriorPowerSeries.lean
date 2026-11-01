/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Ring
public import ProjectiveModules.ExteriorPower.Projective
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Group.TypeTags.Hom
import ProjectiveModules.ExteriorPower.DirectSum
import ProjectiveModules.KTheory.Product
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Group.Units.Hom

/-!
# Total exterior-power series on K₀

For a finite projective right module, the degree `n` coefficient is the class of its
`n`th exterior power over the opposite ring. The constant coefficient is one, so this
series determines a unit. The direct-product compatibility descends this construction
through projective classes and then the existing Grothendieck-group universal property.

The construction uses exterior-power coefficients directly and does not require
a comparison with symmetric-power series.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory* (2013),
  for the exterior-power construction of λ-operations.
-/

public section

noncomputable section

open CategoryTheory

universe uR uM

namespace KTheory.K0

variable (R : Type uR) [CommRing R]

/-- The coefficient series of exterior-power classes of a finite projective right module. -/
private def exteriorSeries
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    PowerSeries (K0 R) :=
  PowerSeries.mk fun n => of R (⋀[Rᵐᵒᵖ]^n M)

private theorem exteriorSeries_constantCoeff
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    PowerSeries.constantCoeff (exteriorSeries R M) = 1 := by
  rw [exteriorSeries, PowerSeries.constantCoeff_mk]
  exact (of_eq_of_equiv R (⋀[Rᵐᵒᵖ]^0 M)
    (exteriorPower.zeroEquiv Rᵐᵒᵖ M)).trans (one_eq_of R).symm

private theorem exteriorSeries_isUnit
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    IsUnit (exteriorSeries R M) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [exteriorSeries_constantCoeff R M]
  exact isUnit_one

/-- The unit whose underlying series consists of exterior-power classes. -/
private def exteriorSeriesUnit
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    Units (PowerSeries (K0 R)) :=
  (exteriorSeries_isUnit R M).unit

universe uN

private theorem exteriorSeriesUnit_congr
    {M : Type uM} {N : Type uN}
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N]
    (e : M ≃ₗ[Rᵐᵒᵖ] N) :
    exteriorSeriesUnit R M = exteriorSeriesUnit R N := by
  apply Units.ext
  change ((exteriorSeries_isUnit R M).unit : PowerSeries (K0 R)) =
    ((exteriorSeries_isUnit R N).unit : PowerSeries (K0 R))
  rw [IsUnit.unit_spec, IsUnit.unit_spec]
  apply PowerSeries.ext
  intro n
  simp only [exteriorSeries, PowerSeries.coeff_mk]
  exact of_eq_of_equiv R (⋀[Rᵐᵒᵖ]^n M)
    (LinearEquiv.ofLinearMap (exteriorPower.map n e.toLinearMap)
      (exteriorPower.map n e.symm.toLinearMap)
      (by rw [← exteriorPower.map_comp, e.comp_symm, exteriorPower.map_id])
      (by rw [← exteriorPower.map_comp, e.symm_comp, exteriorPower.map_id]))

private theorem exteriorSeriesUnit_iso
    {X Y : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ} (e : X ≅ Y) :
    exteriorSeriesUnit R X = exteriorSeriesUnit R Y := by
  exact exteriorSeriesUnit_congr R
    (((ModuleCat.isFiniteProjective Rᵐᵒᵖ).ι.mapIso e).toLinearEquiv)

private theorem exteriorSeriesUnit_punit :
    exteriorSeriesUnit R PUnit.{uR + 1} = 1 := by
  apply Units.ext
  change ((exteriorSeries_isUnit R PUnit.{uR + 1}).unit : PowerSeries (K0 R)) = 1
  rw [IsUnit.unit_spec]
  apply PowerSeries.ext
  intro n
  rw [exteriorSeries, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  cases n with
  | zero =>
      simpa [exteriorSeries] using
        exteriorSeries_constantCoeff R PUnit.{uR + 1}
  | succ n =>
      have : Subsingleton (⋀[Rᵐᵒᵖ]^(n + 1) PUnit.{uR + 1}) :=
        exteriorPower.subsingleton_of_span_eq_top_of_card_lt
          (R := Rᵐᵒᵖ) (M := PUnit.{uR + 1})
          (fun _ : Fin 0 => 0)
          (Subsingleton.elim _ _) (n + 1) (by simp)
      simp

open scoped BigOperators in
/-- The finite-Pi class formula, with the supplied additive groups. -/
private theorem of_pi_addCommGroup
    (S : Type*) [Ring S] {ι : Type*} [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module Sᵐᵒᵖ (M i)]
    [∀ i, Module.Finite Sᵐᵒᵖ (M i)] [∀ i, Module.Projective Sᵐᵒᵖ (M i)] :
    ∃ hfinitePi : Module.Finite Sᵐᵒᵖ (∀ i, M i),
      ∃ hprojectivePi : Module.Projective Sᵐᵒᵖ (∀ i, M i),
        @of S _ (∀ i, M i) inferInstance inferInstance hfinitePi hprojectivePi =
          ∑ i, of S (M i) := by
  classical
  obtain ⟨hfinitePi, hprojectivePi, h⟩ := of_pi S M
  refine ⟨hfinitePi, hprojectivePi, ?_⟩
  calc
    @of S _ (∀ i, M i) inferInstance inferInstance hfinitePi hprojectivePi =
        @of S _ (∀ i, M i) (Module.addCommMonoidToAddCommGroup Sᵐᵒᵖ)
          inferInstance hfinitePi hprojectivePi :=
      @of_eq_of_equiv S _ (∀ i, M i) inferInstance inferInstance
        hfinitePi hprojectivePi (∀ i, M i)
        (Module.addCommMonoidToAddCommGroup Sᵐᵒᵖ) inferInstance
        hfinitePi hprojectivePi (LinearEquiv.refl Sᵐᵒᵖ (∀ i, M i))
    _ = ∑ i, @of S _ (M i) (Module.addCommMonoidToAddCommGroup Sᵐᵒᵖ)
          inferInstance inferInstance inferInstance := h
    _ = ∑ i, of S (M i) := by
      apply congrArg (fun f : ι → K0 S => ∑ i, f i)
      funext i
      exact @of_eq_of_equiv S _ (M i)
        (Module.addCommMonoidToAddCommGroup Sᵐᵒᵖ) inferInstance
        inferInstance inferInstance (M i) inferInstance inferInstance
        inferInstance inferInstance (LinearEquiv.refl Sᵐᵒᵖ (M i))

/-- The first coordinate of the finite-antidiagonal equivalence. -/
private theorem antidiagonalEquivFin_val (n : ℕ) (p : Finset.antidiagonal n) :
    ((Finset.Nat.antidiagonalEquivFin n) p : ℕ) = p.1.1 := by
  rfl

open scoped BigOperators TensorProduct in
/-- Exterior-power classes satisfy the direct-product Cauchy formula. -/
private theorem exteriorSeries_prod_coeff
    (X : Type*) [AddCommGroup X] [Module Rᵐᵒᵖ X]
    [Module.Finite Rᵐᵒᵖ X] [Module.Projective Rᵐᵒᵖ X]
    (Y : Type*) [AddCommGroup Y] [Module Rᵐᵒᵖ Y]
    [Module.Finite Rᵐᵒᵖ Y] [Module.Projective Rᵐᵒᵖ Y] (n : ℕ) :
    of R (⋀[Rᵐᵒᵖ]^n (X × Y)) =
      ∑ p ∈ Finset.antidiagonal n,
        of R (⋀[Rᵐᵒᵖ]^p.1 X) * of R (⋀[Rᵐᵒᵖ]^p.2 Y) := by
  classical
  let F : Fin (n + 1) → Type _ := fun i =>
    (⋀[Rᵐᵒᵖ]^i.1 X) ⊗[Rᵐᵒᵖ] (⋀[Rᵐᵒᵖ]^(n - i.1) Y)
  let G : Finset.antidiagonal n → Type _ := fun p =>
    F ((Finset.Nat.antidiagonalEquivFin n) p)
  obtain ⟨hfinitePi, hprojectivePi, hclass⟩ := of_pi_addCommGroup R G
  have : Module.Finite Rᵐᵒᵖ (∀ p, G p) := hfinitePi
  have : Module.Projective Rᵐᵒᵖ (∀ p, G p) := hprojectivePi
  have hprod : of R (⋀[Rᵐᵒᵖ]^n (X × Y)) =
      ∑ p : Finset.antidiagonal n, of R (G p) := by
    exact (of_eq_of_equiv R _
      (((exteriorPower.prodEquivDirectSum Rᵐᵒᵖ X Y n).trans
          (DirectSum.linearEquivFunOnFintype Rᵐᵒᵖ (Fin (n + 1)) F)).trans
        (LinearEquiv.piCongrLeft Rᵐᵒᵖ F
          (Finset.Nat.antidiagonalEquivFin n)).symm)).trans hclass
  have hterm : (fun p : Finset.antidiagonal n => of R (G p)) =
      (fun p => of R (⋀[Rᵐᵒᵖ]^p.1.1 X) * of R (⋀[Rᵐᵒᵖ]^p.1.2 Y)) := by
    funext p
    have hp : p.1.1 + p.1.2 = n := by
      exact Finset.mem_antidiagonal.mp p.2
    have hsub : n - p.1.1 = p.1.2 := by
      omega
    dsimp only [G, F]
    rw [antidiagonalEquivFin_val, hsub, ← of_mul R]
  calc
    of R (⋀[Rᵐᵒᵖ]^n (X × Y)) =
        ∑ p : Finset.antidiagonal n, of R (G p) := hprod
    _ = ∑ p : Finset.antidiagonal n,
        of R (⋀[Rᵐᵒᵖ]^p.1.1 X) * of R (⋀[Rᵐᵒᵖ]^p.1.2 Y) :=
      congrArg (fun f : Finset.antidiagonal n → K0 R => ∑ p, f p) hterm
    _ = ∑ p ∈ Finset.antidiagonal n,
        of R (⋀[Rᵐᵒᵖ]^p.1 X) * of R (⋀[Rᵐᵒᵖ]^p.2 Y) := by
      exact Finset.sum_coe_sort (Finset.antidiagonal n)
        (fun p : ℕ × ℕ => of R (⋀[Rᵐᵒᵖ]^p.1 X) * of R (⋀[Rᵐᵒᵖ]^p.2 Y))

private theorem exteriorSeriesUnit_prod
    (X Y : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ) :
    exteriorSeriesUnit R (X × Y) =
      exteriorSeriesUnit R X * exteriorSeriesUnit R Y := by
  apply Units.ext
  simp only [Units.val_mul, exteriorSeriesUnit, IsUnit.unit_spec]
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul]
  simp only [exteriorSeries, PowerSeries.coeff_mk]
  exact exteriorSeries_prod_coeff R X Y n

/-- The exterior-power series descended to projective isomorphism classes. -/
private def exteriorSeriesClass :
    ProjectiveClass R →+ Additive (Units (PowerSeries (K0 R))) :=
  ProjectiveClass.lift R
    (fun M => Additive.ofMul (exteriorSeriesUnit R M))
    (fun {X Y} e => congrArg Additive.ofMul (exteriorSeriesUnit_iso R e))
    (by
      simpa using congrArg Additive.ofMul (exteriorSeriesUnit_punit R))
    (fun X Y => by
      simpa using congrArg Additive.ofMul (exteriorSeriesUnit_prod R X Y))

/-- The total exterior-power series on `K₀ R`, valued in the full group of units of
formal power series. Its value on the class of a finite projective right module has
exterior-power classes as its coefficients. This is the exterior-power construction
of λ-operations; see Weibel, *The K-book* (2013). -/
def totalExteriorSeries :
    Multiplicative (K0 R) →* Units (PowerSeries (K0 R)) :=
  AddMonoidHom.toMultiplicativeLeft (α := K0 R)
    (β := Units (PowerSeries (K0 R)))
    (K0.lift R (G := Additive (Units (PowerSeries (K0 R)))) (exteriorSeriesClass R))

/-- On a finite projective right module, the total exterior-power series has the
class of its `n`th exterior power as coefficient `n`. -/
@[simp] theorem coeff_totalExteriorSeries_of
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] (n : ℕ) :
    PowerSeries.coeff n
        (totalExteriorSeries R (Multiplicative.ofAdd (of R M)) :
          PowerSeries (K0 R)) =
      of R (⋀[Rᵐᵒᵖ]^n M) := by
  have hunit :
      totalExteriorSeries R (Multiplicative.ofAdd (of R M)) =
        exteriorSeriesUnit R M := by
    change lift R (exteriorSeriesClass R) (of R M) =
      Additive.ofMul (exteriorSeriesUnit R M)
    rw [lift_of, exteriorSeriesClass, ProjectiveClass.lift_of_module]
    · exact congrArg Additive.ofMul
        (exteriorSeriesUnit_congr R
          (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ M))
    · intro X Y e
      exact congrArg Additive.ofMul (exteriorSeriesUnit_iso R e)
  rw [hunit]
  simp only [exteriorSeriesUnit, IsUnit.unit_spec, exteriorSeries,
    PowerSeries.coeff_mk]

/-- Every total exterior-power series has constant coefficient one, including at
virtual classes. -/
@[simp] theorem constantCoeff_totalExteriorSeries (x : K0 R) :
    PowerSeries.constantCoeff
        (totalExteriorSeries R (Multiplicative.ofAdd x) : PowerSeries (K0 R)) = 1 := by
  let c : K0 R →+ Additive (Units (K0 R)) :=
    MonoidHom.toAdditiveRight
      ((Units.map
        ((PowerSeries.constantCoeff : PowerSeries (K0 R) →+* K0 R) :
          PowerSeries (K0 R) →* K0 R)).comp
          (totalExteriorSeries R))
  have hc : c = 0 := by
    apply hom_ext R (G := Additive (Units (K0 R)))
      (f := c) (g := (0 : K0 R →+ Additive (Units (K0 R))))
    intro M
    change Units.map
      ((PowerSeries.constantCoeff : PowerSeries (K0 R) →+* K0 R) :
        PowerSeries (K0 R) →* K0 R)
        (totalExteriorSeries R (Multiplicative.ofAdd (of R M))) = 1
    apply Units.ext
    rw [Units.coe_map, Units.val_one, MonoidHom.coe_coe,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_totalExteriorSeries_of]
    exact (of_eq_of_equiv R (⋀[Rᵐᵒᵖ]^0 M)
      (exteriorPower.zeroEquiv Rᵐᵒᵖ M)).trans (one_eq_of R).symm
  have hx := congrArg
    (fun h : K0 R →+ Additive (Units (K0 R)) => h x) hc
  change Units.map
    ((PowerSeries.constantCoeff : PowerSeries (K0 R) →+* K0 R) :
      PowerSeries (K0 R) →* K0 R)
      (totalExteriorSeries R (Multiplicative.ofAdd x)) = 1 at hx
  have hv := congrArg (fun u : Units (K0 R) => (u : K0 R)) hx
  simpa only [Units.coe_map, Units.val_one, MonoidHom.coe_coe] using hv

/-- The coefficient of degree one recovers the virtual class. -/
@[simp] theorem coeff_one_totalExteriorSeries (x : K0 R) :
    PowerSeries.coeff 1
        (totalExteriorSeries R (Multiplicative.ofAdd x) : PowerSeries (K0 R)) = x := by
  -- Degree one is additive only after restricting to the image with constant term one.
  let f : K0 R →+ K0 R :=
    { toFun := fun y => PowerSeries.coeff 1
        (totalExteriorSeries R (Multiplicative.ofAdd y) : PowerSeries (K0 R))
      map_zero' := by
        change PowerSeries.coeff 1
          (totalExteriorSeries R (1 : Multiplicative (K0 R)) :
            PowerSeries (K0 R)) = 0
        simp
      map_add' := by
        intro y z
        change PowerSeries.coeff 1
            (totalExteriorSeries R
              (Multiplicative.ofAdd y * Multiplicative.ofAdd z) :
                PowerSeries (K0 R)) =
          PowerSeries.coeff 1
              (totalExteriorSeries R (Multiplicative.ofAdd y) :
                PowerSeries (K0 R)) +
            PowerSeries.coeff 1
              (totalExteriorSeries R (Multiplicative.ofAdd z) :
                PowerSeries (K0 R))
        simp only [map_mul, Units.val_mul, PowerSeries.coeff_one_mul,
          constantCoeff_totalExteriorSeries, mul_one] }
  let g : K0 R →+ K0 R :=
    { toFun := fun y => y
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : f = g := by
    apply hom_ext R
    intro M
    change PowerSeries.coeff 1
      (totalExteriorSeries R (Multiplicative.ofAdd (of R M)) :
        PowerSeries (K0 R)) = of R M
    rw [coeff_totalExteriorSeries_of]
    exact of_eq_of_equiv R (⋀[Rᵐᵒᵖ]^1 M) (exteriorPower.oneEquiv Rᵐᵒᵖ M)
  exact congrArg (fun h : K0 R →+ K0 R => h x) hf

/-- Addition of virtual classes corresponds to multiplication of total
exterior-power series. -/
theorem totalExteriorSeries_add (x y : K0 R) :
    totalExteriorSeries R (Multiplicative.ofAdd (x + y)) =
      totalExteriorSeries R (Multiplicative.ofAdd x) *
        totalExteriorSeries R (Multiplicative.ofAdd y) := by
  change totalExteriorSeries R
      (Multiplicative.ofAdd x * Multiplicative.ofAdd y) =
    totalExteriorSeries R (Multiplicative.ofAdd x) *
      totalExteriorSeries R (Multiplicative.ofAdd y)
  exact map_mul (totalExteriorSeries R) (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)

/-- Subtraction of virtual classes corresponds to division in the full unit group. -/
theorem totalExteriorSeries_sub (x y : K0 R) :
    totalExteriorSeries R (Multiplicative.ofAdd (x - y)) =
      totalExteriorSeries R (Multiplicative.ofAdd x) /
        totalExteriorSeries R (Multiplicative.ofAdd y) := by
  change totalExteriorSeries R
      (Multiplicative.ofAdd x / Multiplicative.ofAdd y) =
    totalExteriorSeries R (Multiplicative.ofAdd x) /
      totalExteriorSeries R (Multiplicative.ofAdd y)
  exact map_div (totalExteriorSeries R) (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)

end KTheory.K0
