/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
public import ProjectiveModules.ExteriorPower.DeterminantLine
public import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.ZMod.Basic

/-!
# Determinant homomorphisms on K₀

A finite projective right `R`-module has a determinant line over `Rᵐᵒᵖ`.
Transporting its Picard class along the inverse of `RingEquiv.toOpposite R`
gives a class in `CommRing.Pic R`. The homomorphism `KTheory.K0.determinantHom`
extends this assignment through the direct-sum class monoid and its additive
Grothendieck group. It is determined by its values on finite projective
modules, and every Picard class is the determinant of an invertible
representative.

The construction includes modules in independent carrier universes and the
zero ring. No constant-rank or nontriviality hypothesis is needed.

## References

For the determinant and Picard constructions, see C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*. The Picard-group and
invertible-module interfaces used here are Mathlib's formalization by Junyan Xu.
The determinant-line comparisons and the K₀ universal properties are the
formalizations by Formal Frontier Agents in this library.
-/

@[expose] public section

noncomputable section

universe u v w

namespace KTheory.K0

variable (R : Type u) [CommRing R]

private theorem determinantClass_congr
    (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]
    (Q : Type w) [AddCommGroup Q] [Module Rᵐᵒᵖ Q]
    [Module.Finite Rᵐᵒᵖ Q] [Module.Projective Rᵐᵒᵖ Q]
    (e : P ≃ₗ[Rᵐᵒᵖ] Q) :
    Additive.ofMul
      (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).symm.toRingHom
        (@CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ P)
          _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ P))) =
      Additive.ofMul
        (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).symm.toRingHom
          (@CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ Q)
            _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ Q))) := by
  apply congrArg Additive.ofMul
  apply congrArg (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).symm.toRingHom)
  exact (@CommRing.Pic.mk_eq_mk_iff Rᵐᵒᵖ
    (Module.DeterminantLine Rᵐᵒᵖ P) (Module.DeterminantLine Rᵐᵒᵖ Q)
    _ _ _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ P)
      (Module.determinantLine_invertible Rᵐᵒᵖ Q)).mpr
        (Module.determinantLine_congr Rᵐᵒᵖ P Q e)

private theorem determinantClass_zero :
    Additive.ofMul
      (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).symm.toRingHom
        (@CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ PUnit.{u + 1})
          _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ PUnit.{u + 1}))) = 0 := by
  have hline :
      @CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ PUnit.{u + 1})
        _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ PUnit.{u + 1}) = 1 := by
    apply (@CommRing.Pic.mk_eq_one_iff Rᵐᵒᵖ
      (Module.DeterminantLine Rᵐᵒᵖ PUnit.{u + 1})
      _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ PUnit.{u + 1})).mpr
    obtain ⟨e⟩ := Module.determinantLine_congr Rᵐᵒᵖ PUnit.{u + 1}
      (Fin 0 → Rᵐᵒᵖ) (LinearEquiv.ofSubsingleton _ _)
    obtain ⟨e₀⟩ := Module.determinantLine_zero Rᵐᵒᵖ
    exact ⟨e.trans e₀⟩
  rw [hline, map_one]
  rfl

private theorem determinantClass_prod
    (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]
    (Q : Type w) [AddCommGroup Q] [Module Rᵐᵒᵖ Q]
    [Module.Finite Rᵐᵒᵖ Q] [Module.Projective Rᵐᵒᵖ Q] :
    Additive.ofMul
      (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).symm.toRingHom
        (@CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ (P × Q))
          _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ (P × Q)))) =
      Additive.ofMul
        (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).symm.toRingHom
          (@CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ P)
            _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ P))) +
      Additive.ofMul
        (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).symm.toRingHom
          (@CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ Q)
            _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ Q))) := by
  have hline :
      @CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ (P × Q))
        _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ (P × Q)) =
      @CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ P)
        _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ P) *
      @CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ Q)
        _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ Q) := by
    rw [← @CommRing.Pic.mk_tensor Rᵐᵒᵖ
      (Module.DeterminantLine Rᵐᵒᵖ P) (Module.DeterminantLine Rᵐᵒᵖ Q)
      _ _ _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ P)
        (Module.determinantLine_invertible Rᵐᵒᵖ Q)]
    letI := Module.determinantLine_invertible Rᵐᵒᵖ P
    letI := Module.determinantLine_invertible Rᵐᵒᵖ Q
    letI := Module.determinantLine_invertible Rᵐᵒᵖ (P × Q)
    apply (@CommRing.Pic.mk_eq_mk_iff _ _ _ _ _ _ _ _ _ _).mpr
    obtain ⟨e⟩ := Module.determinantLine_prod Rᵐᵒᵖ P Q
    exact ⟨e.symm⟩
  rw [hline, map_mul]
  rfl

/-- The determinant homomorphism from K₀ of finite projective right modules to
 the additively written Picard group, as in C. A. Weibel's *The K-book*.
It depends only on the commutative ring, not on a universe of module carriers. -/
noncomputable def determinantHom : KTheory.K0 R →+ Additive (CommRing.Pic R) :=
  KTheory.K0.lift R
    (KTheory.ProjectiveClass.lift R
      (fun X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ ↦
        Additive.ofMul
          (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).symm.toRingHom
            (@CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ X)
              _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ X))))
      (fun {X Y} e ↦ by
        exact determinantClass_congr R X Y
          (ModuleCat.FiniteProjective.isoToLinearEquiv e))
      (by exact determinantClass_zero R)
      (fun X Y ↦ by exact determinantClass_prod R X Y))

/-- The determinant homomorphism sends every finite projective right module,
in an arbitrary carrier universe, to its transported determinant-line class. -/
@[simp]
theorem determinantHom_of
    (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P] :
    determinantHom R (KTheory.K0.of R P) =
      Additive.ofMul
        (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).symm.toRingHom
          (@CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ P)
            _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ P))) := by
  simp only [determinantHom, KTheory.K0.lift_of,
    KTheory.ProjectiveClass.lift_of_module]
  exact determinantClass_congr R (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ P) P
    (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ P)

/-- Normalization on the ring-universe finite projective generators characterizes
 the determinant homomorphism. No surjectivity hypothesis is needed. -/
theorem determinantHom_normalization_iff
    (E : KTheory.K0 R →+ Additive (CommRing.Pic R)) :
    (∀ X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ,
      E (KTheory.K0.of R X) =
        Additive.ofMul
          (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).symm.toRingHom
            (@CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ X)
              _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ X)))) ↔
      E = determinantHom R := by
  constructor
  · intro h
    exact KTheory.K0.hom_ext R
      (fun X ↦ (h X).trans (determinantHom_of R X).symm)
  · rintro rfl
    intro X
    exact determinantHom_of R X

/-- Every Picard class is the transported determinant class of its
opposite-ring invertible representative. -/
theorem determinantLine_pic_representative (ℓ : CommRing.Pic R) :
    CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).symm.toRingHom
      (@CommRing.Pic.mk Rᵐᵒᵖ
        (Module.DeterminantLine Rᵐᵒᵖ
          (CommRing.Pic.AsModule
            (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).toRingHom ℓ)))
        _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ
          (CommRing.Pic.AsModule
            (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).toRingHom ℓ)))) = ℓ := by
  let L := CommRing.Pic.AsModule
    (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).toRingHom ℓ)
  letI : Module.Invertible Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ L) :=
    Module.determinantLine_invertible Rᵐᵒᵖ L
  have hline : CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ L) =
      CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).toRingHom ℓ :=
    CommRing.Pic.mk_eq_iff.mpr (Module.determinantLine_invertibleModule Rᵐᵒᵖ L)
  change CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).symm.toRingHom
    (CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ L)) = ℓ
  rw [hline, CommRing.Pic.mapRingHom_mapRingHom,
    RingEquiv.symm_toRingHom_comp_toRingHom, CommRing.Pic.mapRingHom_id_apply]

/-- An invertible representative of the forward opposite-ring Picard class maps
back to the given Picard class under the determinant homomorphism. -/
@[simp]
theorem determinantHom_pic_representative (ℓ : CommRing.Pic R) :
    determinantHom R (KTheory.K0.of R
      (CommRing.Pic.AsModule
        (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).toRingHom ℓ))) =
      Additive.ofMul ℓ := by
  exact (determinantHom_of R
    (CommRing.Pic.AsModule
      (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).toRingHom ℓ))).trans
        (congrArg Additive.ofMul (determinantLine_pic_representative R ℓ))

/-- Every Picard class is a determinant of a K₀ class, as in the
 determinant/Picard construction in C. A. Weibel's *The K-book*. -/
theorem determinantHom_surjective : Function.Surjective (determinantHom R) := by
  intro ℓ
  exact ⟨KTheory.K0.of R
    (CommRing.Pic.AsModule
      (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).toRingHom ℓ.toMul)),
    determinantHom_pic_representative R ℓ.toMul⟩

/-- The rational regular line gives the unit Picard class. -/
example :
    CommRing.Pic.mapRingHom (RingEquiv.toOpposite ℚ).symm.toRingHom
      (@CommRing.Pic.mk ℚᵐᵒᵖ (Module.DeterminantLine ℚᵐᵒᵖ ℚᵐᵒᵖ)
        _ _ _ (Module.determinantLine_invertible ℚᵐᵒᵖ ℚᵐᵒᵖ)) = 1 := by
  letI : Module.Invertible ℚᵐᵒᵖ (Module.DeterminantLine ℚᵐᵒᵖ ℚᵐᵒᵖ) :=
    Module.determinantLine_invertible ℚᵐᵒᵖ ℚᵐᵒᵖ
  have hline : CommRing.Pic.mk ℚᵐᵒᵖ (Module.DeterminantLine ℚᵐᵒᵖ ℚᵐᵒᵖ) = 1 :=
    CommRing.Pic.mk_eq_one_iff.mpr
      (Module.determinantLine_invertibleModule ℚᵐᵒᵖ ℚᵐᵒᵖ)
  change CommRing.Pic.mapRingHom (RingEquiv.toOpposite ℚ).symm.toRingHom
    (CommRing.Pic.mk ℚᵐᵒᵖ (Module.DeterminantLine ℚᵐᵒᵖ ℚᵐᵒᵖ)) = 1
  rw [hline, map_one]

/-- The zero ring permits the determinant comparison for the zero module. -/
example :
    Nonempty (Module.DeterminantLine (ZMod 1)ᵐᵒᵖ (Fin 0 → (ZMod 1)ᵐᵒᵖ)
      ≃ₗ[(ZMod 1)ᵐᵒᵖ] (ZMod 1)ᵐᵒᵖ) :=
  Module.determinantLine_zero (ZMod 1)ᵐᵒᵖ


/-- The rational regular line has zero additive determinant class. -/
example : determinantHom ℚ (KTheory.K0.of ℚ ℚᵐᵒᵖ) = 0 := by
  rw [determinantHom_of]
  exact Subsingleton.elim _ _

/-- The regular module over the zero ring is a zero K₀ class. -/
example : determinantHom (ZMod 1) (KTheory.K0.of (ZMod 1) (ZMod 1)ᵐᵒᵖ) = 0 := by
  rw [KTheory.K0.of_zero, map_zero]

end KTheory.K0
