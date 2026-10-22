/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Product
public import ProjectiveModules.KTheory.Rank
import ProjectiveModules.KTheory.Stabilization
import ProjectiveModules.Module.ProjectiveComplement

/-!
# Uniform rank bounds and infinite product comparisons

For a ring `R` and a family of homomorphisms `R →+* D i` to division rings,
the integer ranks of the images of any fixed K₀ element have a uniform absolute
bound. Ranks are dimensions of right modules, with scalars `(D i)ᵐᵒᵖ`.
The index type and the source and target ring universes are independent.

For a family of division rings, the canonical comparison from K₀ of the product
ring to the product of the factor K₀ groups is injective. Its image consists
exactly of the families whose integer ranks admit one uniform absolute bound.
The uniform bound also allows empty index types. For an infinite family, the
comparison is not surjective.

A finite projective and its finite projective complement form a finite free
module. Right scalar extension to each division ring bounds each summand's
dimension by that same finite free rank. Expressing a K₀ element as a difference
of projective classes gives one absolute integer-rank bound before choosing an
index. For product evaluation maps, an unbounded family of integer ranks
therefore cannot come from a K₀ element of the product.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  II.2.1.4.

## Formalization credits

The argument reuses Mathlib's projectivity, additive localization/Grothendieck
completion and dimension APIs, together with Projective Modules' finite-projective
complement linear equivalences, right scalar extension, and class and K₀ rank
maps. The class/group-completion and right-extension infrastructure follows the
formalization by Prism and Lens; the rank maps use Mathlib's dimensions of right
modules via opposite scalars.
-/

@[expose] public section

universe uR uI uD

namespace KTheory.K0

/-- Under any family of homomorphisms from a ring to division rings, the
integer ranks of the images of a fixed K₀ element are uniformly bounded
in absolute value. -/
theorem exists_uniform_abs_finrank_map_le
    {R : Type uR} [Ring R] {I : Type uI}
    (D : I → Type uD) [∀ i, DivisionRing (D i)]
    (φ : ∀ i, R →+* D i) (x : K0 R) :
    ∃ n : ℕ, ∀ i : I, |finrankEquiv (D i) (map (φ i) x)| ≤ (n : ℤ) := by
  classical
  have hclass (a : ProjectiveClass R) :
      ∃ m : ℕ, ∀ i : I,
        ProjectiveClass.finrankHom (D i) (ProjectiveClass.map (φ i) a) ≤ m := by
    obtain ⟨P, rfl⟩ := ProjectiveClass.of_surjective R a
    obtain ⟨m, C, hCadd, hCmodule, hCfinite, ⟨e⟩⟩ :=
      Module.Projective.exists_finite_complement_linearEquiv
        (R := Rᵐᵒᵖ) (P := P)
    letI : AddCommGroup C := hCadd
    letI : Module Rᵐᵒᵖ C := hCmodule
    letI : Module.Finite Rᵐᵒᵖ C := hCfinite
    letI : Module.Projective Rᵐᵒᵖ (P × C) :=
      Module.Projective.of_equiv' e.symm
    letI : Module.Projective Rᵐᵒᵖ C :=
      Module.Projective.of_split (LinearMap.inr Rᵐᵒᵖ P C)
        (LinearMap.snd Rᵐᵒᵖ P C) (LinearMap.snd_comp_inr Rᵐᵒᵖ P C)
    have heq : ProjectiveClass.of R P + ProjectiveClass.of R C =
        m • ProjectiveClass.of R Rᵐᵒᵖ := by
      calc
        _ = ProjectiveClass.of R (P × C) :=
          (ProjectiveClass.of_prod R P C).symm
        _ = ProjectiveClass.of R (Fin m → Rᵐᵒᵖ) :=
          ProjectiveClass.of_eq_of_equiv R _ e
        _ = _ := ProjectiveClass.of_fin_fun_eq_nsmul R m
    refine ⟨m, fun i ↦ ?_⟩
    have hsum := congrArg (fun b : ProjectiveClass R ↦
      ProjectiveClass.finrankHom (D i) (ProjectiveClass.map (φ i) b)) heq
    have hsum' :
        ProjectiveClass.finrankHom (D i)
            (ProjectiveClass.map (φ i) (ProjectiveClass.of R P)) +
          ProjectiveClass.finrankHom (D i)
            (ProjectiveClass.map (φ i) (ProjectiveClass.of R C)) = m := by
      simpa only [map_add, map_nsmul, ProjectiveClass.map_of_self,
        ProjectiveClass.finrankHom_of_self, Nat.nsmul_eq_mul, mul_one] using hsum
    calc
      _ ≤ ProjectiveClass.finrankHom (D i)
              (ProjectiveClass.map (φ i) (ProjectiveClass.of R P)) +
            ProjectiveClass.finrankHom (D i)
              (ProjectiveClass.map (φ i) (ProjectiveClass.of R C)) :=
        Nat.le_add_right _ _
      _ = m := hsum'
  have hx : ∃ a b : ProjectiveClass R, x = ofClass R a - ofClass R b := by
    obtain ⟨P, Q, hPQ⟩ := K0.exists_sub R x
    refine ⟨ProjectiveClass.of R P, ProjectiveClass.of R Q, ?_⟩
    simpa only [K0.ofClass_of] using hPQ
  obtain ⟨a, b, rfl⟩ := hx
  obtain ⟨m, hm⟩ := hclass a
  obtain ⟨n, hn⟩ := hclass b
  refine ⟨m + n, fun i ↦ ?_⟩
  simp only [map_sub, map_ofClass, finrankEquiv_ofClass,
    ProjectiveClass.finrankEquiv_apply]
  let A := ProjectiveClass.finrankHom (D i) (ProjectiveClass.map (φ i) a)
  let B := ProjectiveClass.finrankHom (D i) (ProjectiveClass.map (φ i) b)
  change |(A : ℤ) - (B : ℤ)| ≤ ((m + n : ℕ) : ℤ)
  have hA : (A : ℤ) ≤ (m : ℤ) := Int.ofNat_le.mpr (hm i)
  have hB : (B : ℤ) ≤ (n : ℤ) := Int.ofNat_le.mpr (hn i)
  rw [Nat.cast_add]
  apply abs_le.mpr
  constructor
  · calc
      -((m : ℤ) + (n : ℤ)) ≤ -(n : ℤ) :=
        neg_le_neg (le_add_of_nonneg_left (Int.natCast_nonneg m))
      _ = (0 : ℤ) - (n : ℤ) := (zero_sub _).symm
      _ ≤ (A : ℤ) - (B : ℤ) := sub_le_sub (Int.natCast_nonneg A) hB
  · calc
      (A : ℤ) - (B : ℤ) ≤ (m : ℤ) - (0 : ℤ) :=
        sub_le_sub hA (Int.natCast_nonneg B)
      _ = (m : ℤ) := sub_zero _
      _ ≤ (m : ℤ) + (n : ℤ) := le_add_of_nonneg_right (Int.natCast_nonneg n)

/-- The K₀ comparison for an infinite product of division rings is not
surjective onto the product of their K₀ groups.

Compare Weibel, *The K-book: An Introduction to Algebraic K-theory*, II.2.1.4.
Here the factors may be noncommutative division rings: the uniform absolute
integer-rank bound along product evaluations rules out a family of unbounded
ranks. -/
theorem not_surjective_piMap {I : Type uI} [Infinite I]
    (D : I → Type uD) [∀ i, DivisionRing (D i)] :
    ¬ Function.Surjective (piMap D) := by
  classical
  let e : ℕ ↪ I := Infinite.natEmbedding I
  let t : I → ℕ := Function.invFun e
  have ht (k : ℕ) : t (e k) = k :=
    Function.leftInverse_invFun e.injective k
  let y : ∀ i, K0 (D i) := fun i ↦ (finrankEquiv (D i)).symm (t i : ℤ)
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj y
  obtain ⟨N, hN⟩ :=
    exists_uniform_abs_finrank_map_le D (fun i ↦ Pi.evalRingHom D i) x
  have h := hN (e (N + 1))
  have hcoord : map (Pi.evalRingHom D (e (N + 1))) x = y (e (N + 1)) :=
    (piMap_apply D x (e (N + 1))).symm.trans (congrFun hx (e (N + 1)))
  rw [hcoord] at h
  change |finrankEquiv (D (e (N + 1)))
    ((finrankEquiv (D (e (N + 1)))).symm (t (e (N + 1)) : ℤ))| ≤ (N : ℤ) at h
  rw [AddEquiv.apply_symm_apply, ht,
    abs_of_nonneg (Int.natCast_nonneg (N + 1))] at h
  exact (Nat.not_succ_le_self N) (Int.ofNat_le.mp h)

/-- Coordinate scalar extension on K₀ is injective for an arbitrary family of division rings.
The factors need not be commutative. -/
theorem piMap_injective {I : Type uI} (D : I → Type uD) [∀ i, DivisionRing (D i)] :
    Function.Injective (piMap D) := by
  intro x y hxy
  have hzero : piMap D (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hrep : ∃ a b : ProjectiveClass (∀ i, D i),
      x - y = ofClass (∀ i, D i) a - ofClass (∀ i, D i) b := by
    obtain ⟨P, Q, hPQ⟩ := K0.exists_sub (∀ i, D i) (x - y)
    refine ⟨ProjectiveClass.of (∀ i, D i) P, ProjectiveClass.of (∀ i, D i) Q, ?_⟩
    simpa only [K0.ofClass_of] using hPQ
  obtain ⟨a, b, hab⟩ := hrep
  have hab' : a = b := by
    apply ProjectiveClass.piMap_injective D
    funext i
    apply (ProjectiveClass.finrankEquiv (D i)).injective
    apply Int.ofNat_inj.mp
    have hi : map (Pi.evalRingHom D i) (x - y) = 0 := congrFun hzero i
    rw [hab, map_sub, map_ofClass, map_ofClass] at hi
    simpa only [ProjectiveClass.piMap_apply, finrankEquiv_ofClass] using
      congrArg (finrankEquiv (D i)) (sub_eq_zero.mp hi)
  apply sub_eq_zero.mp
  rw [hab, hab', sub_self]

/-- A family of factor K₀ classes comes from the product exactly when its integer ranks
admit one uniform absolute bound. -/
theorem mem_range_piMap_iff {I : Type uI} (D : I → Type uD) [∀ i, DivisionRing (D i)]
    (z : ∀ i, K0 (D i)) :
    z ∈ Set.range (piMap D) ↔
      ∃ n : ℕ, ∀ i : I, |finrankEquiv (D i) (z i)| ≤ (n : ℤ) := by
  classical
  constructor
  · rintro ⟨x, rfl⟩
    simpa only [piMap_apply] using
      exists_uniform_abs_finrank_map_le D (fun i ↦ Pi.evalRingHom D i) x
  · rintro ⟨N, hN⟩
    have hshift : ∀ i, ∃ k : ℕ,
        -(N : ℤ) + (k : ℤ) = finrankEquiv (D i) (z i) ∧ k ≤ N + N := by
      intro i
      refine Int.le.elim (abs_le.mp (hN i)).1 ?_
      intro k hk
      refine ⟨k, hk, Int.ofNat_le.mp ?_⟩
      rw [Nat.cast_add]
      calc
        (k : ℤ) = (N : ℤ) + (-(N : ℤ) + (k : ℤ)) := by
          rw [← add_assoc, add_neg_cancel, zero_add]
        _ ≤ (N : ℤ) + (N : ℤ) :=
          add_le_add (le_refl (N : ℤ)) (hk.le.trans (abs_le.mp (hN i)).2)
    choose k hk using hshift
    let p : ∀ i, ProjectiveClass (D i) :=
      fun i ↦ k i • ProjectiveClass.of (D i) (D i)ᵐᵒᵖ
    have hp : p ∈ Set.range (ProjectiveClass.piMap D) := by
      apply (ProjectiveClass.mem_range_piMap_iff D p).2
      refine ⟨N + N, fun i ↦ ⟨(N + N - k i) •
        ProjectiveClass.of (D i) (D i)ᵐᵒᵖ, ?_⟩⟩
      change k i • ProjectiveClass.of (D i) (D i)ᵐᵒᵖ +
          (N + N - k i) • ProjectiveClass.of (D i) (D i)ᵐᵒᵖ =
        (N + N) • ProjectiveClass.of (D i) (D i)ᵐᵒᵖ
      rw [← add_nsmul, Nat.add_comm (k i) (N + N - k i),
        Nat.sub_add_cancel (hk i).2]
    obtain ⟨P, hP⟩ := hp
    refine ⟨ofClass (∀ i, D i) P - N • ofClass (∀ i, D i)
      (ProjectiveClass.of (∀ i, D i) (∀ i, D i)ᵐᵒᵖ), ?_⟩
    funext i
    apply (finrankEquiv (D i)).injective
    have hPi : ProjectiveClass.map (Pi.evalRingHom D i) P = p i :=
      (ProjectiveClass.piMap_apply D P i).symm.trans (congrFun hP i)
    calc
      _ = (k i : ℤ) - (N : ℤ) := by
        rw [piMap_apply, map_sub, map_nsmul, map_ofClass, map_ofClass,
          hPi, ProjectiveClass.map_of_self]
        simp only [map_sub, map_nsmul, finrankEquiv_ofClass, p,
          ProjectiveClass.finrankEquiv_apply,
          ProjectiveClass.finrankHom_of_self, Nat.cast_one, nsmul_eq_mul, mul_one]
      _ = -(N : ℤ) + (k i : ℤ) := by rw [sub_eq_add_neg, add_comm]
      _ = _ := (hk i).1

end KTheory.K0
