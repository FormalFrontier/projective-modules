/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Koszul.Acyclic
public import ProjectiveModules.KTheory.CochainEulerCharacteristic
public import ProjectiveModules.KTheory.Ring
public import ProjectiveModules.ExteriorPower.Projective
public import ProjectiveModules.Module.SymmetricPower
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Group.Int.Even

/-!
# The alternating class of a homogeneous Koszul complex

Extend the homogeneous Nat-chain complex by zero to an Int-cochain complex,
placing chain degree `i` at cochain degree `-i`. Transport exactness through
its canonical component isomorphisms, and apply the existing cochain Euler
characteristic theorem. The signed finite sum is reindexed without changing
its integer coefficients.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, 2013.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u v w

namespace Module.Koszul

section ModuleTransport

variable {S : Type u} [Ring S]

private theorem moduleIso_hom_inv_apply
    {X Y : ModuleCat.{w} S} (e : X ≅ Y) (x : X) :
    e.inv (e.hom x) = x := by
  exact congrArg (fun f : X ⟶ X => f x) e.hom_inv_id

private theorem moduleIso_inv_hom_apply
    {X Y : ModuleCat.{w} S} (e : X ≅ Y) (y : Y) :
    e.hom (e.inv y) = y := by
  exact congrArg (fun f : Y ⟶ Y => f y) e.inv_hom_id

private theorem moduleIsZero_of_iso
    {X Y : ModuleCat.{w} S} (e : X ≅ Y) (hY : IsZero Y) : IsZero X := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y => ?_⟩
  have h : e.hom x = e.hom y :=
    (ModuleCat.subsingleton_of_isZero hY).elim _ _
  have h' := congrArg (fun z => e.inv z) h
  simpa only [moduleIso_hom_inv_apply] using h'

private theorem moduleFinite_of_isZero
    {X : ModuleCat.{w} S} (hX : IsZero X) : Module.Finite S X := by
  apply Module.Finite.of_surjective (0 : S →ₗ[S] X)
  intro x
  exact ⟨0, (ModuleCat.subsingleton_of_isZero hX).elim _ _⟩

private theorem moduleProjective_of_isZero
    {X : ModuleCat.{w} S} (hX : IsZero X) : Module.Projective S X := by
  apply Module.projective_def.mpr
  refine ⟨0, ?_⟩
  intro x
  exact (ModuleCat.subsingleton_of_isZero hX).elim _ _

private theorem moduleFinite_of_iso
    {X Y : ModuleCat.{w} S} (e : X ≅ Y) [Module.Finite S Y] :
    Module.Finite S X :=
  Module.Finite.equiv e.toLinearEquiv.symm

private theorem moduleProjective_of_iso
    {X Y : ModuleCat.{w} S} (e : X ≅ Y) [Module.Projective S Y] :
    Module.Projective S X :=
  Module.Projective.of_equiv e.toLinearEquiv.symm

/-- Elementwise exactness transports along three module isomorphisms. -/
private theorem moduleExact_of_transport
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : ModuleCat.{w} S}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃)
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃)
    (f' : X₁ ⟶ X₂) (g' : X₂ ⟶ X₃)
    (h : ∀ x : Y₂, g x = 0 → ∃ y : Y₁, f y = x)
    (hf : f' = e₁.hom ≫ f ≫ e₂.inv)
    (hg : g' = e₂.hom ≫ g ≫ e₃.inv) :
    ∀ x : X₂, g' x = 0 → ∃ y : X₁, f' y = x := by
  intro x hx
  have hx' : g (e₂.hom x) = 0 := by
    have he := congrArg (fun z => e₃.hom z) hx
    rw [hg] at he
    change e₃.hom (e₃.inv (g (e₂.hom x))) = e₃.hom 0 at he
    simpa only [moduleIso_inv_hom_apply, map_zero] using he
  obtain ⟨y, hy⟩ := h (e₂.hom x) hx'
  refine ⟨e₁.inv y, ?_⟩
  rw [hf]
  change e₂.inv (f (e₁.hom (e₁.inv y))) = x
  rw [moduleIso_inv_hom_apply, hy]
  exact moduleIso_hom_inv_apply e₂ x

end ModuleTransport

variable (R : Type u) [CommRing R]
variable (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
variable [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]

/-- The bidegree `(0,0)` Koszul term represents the unit class. -/
private theorem k0_term_zero_zero :
    KTheory.K0.of R (Term (Rᵐᵒᵖ) P 0 0) = (1 : KTheory.K0 R) := by
  calc
    KTheory.K0.of R (Term (Rᵐᵒᵖ) P 0 0) = KTheory.K0.of R Rᵐᵒᵖ :=
      KTheory.K0.of_eq_of_equiv R (Term (Rᵐᵒᵖ) P 0 0)
        (termZeroZeroEquiv (Rᵐᵒᵖ) P)
    _ = 1 := KTheory.K0.of_self R

/-- The total-degree-zero alternating Koszul class sum is the scalar class. -/
private theorem alternatingK0Euler_zero :
    (∑ i ∈ Finset.range (0 + 1),
      ((-1 : ℤ) ^ i) •
        KTheory.K0.of R (Term (Rᵐᵒᵖ) P i (0 - i))) =
      if (0 : ℕ) = 0 then (1 : KTheory.K0 R) else 0 := by
  simpa using k0_term_zero_zero R P


/-- The index formula for the stock chain-to-cochain embedding. -/
private theorem downNat_embedding_index (i : ℕ) :
    ComplexShape.embeddingDownNat.f i = -(i : ℤ) := by
  rfl

/-- The canonical extension to integer cochain degrees. -/
private def homogeneousExtension (n : ℕ) :
    CochainComplex (ModuleCat.{max u v} Rᵐᵒᵖ) ℤ :=
  (homogeneousComplex (Rᵐᵒᵖ) P n).extend ComplexShape.embeddingDownNat

private def homogeneousEulerSupport (n : ℕ) : Finset ℤ :=
  (Finset.range (n + 1)).image (fun i : ℕ => -(i : ℤ))

omit [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P] in
private theorem homogeneousExtension_isZero_pos (n : ℕ) (j : ℤ) (hj : 0 < j) :
    IsZero ((homogeneousExtension R P n).X j) := by
  apply HomologicalComplex.isZero_extend_X
  intro i hi
  rw [downNat_embedding_index] at hi
  omega

private instance homogeneousComplex_finite (n i : ℕ) :
    Module.Finite Rᵐᵒᵖ ((homogeneousComplex (Rᵐᵒᵖ) P n).X i) := by
  by_cases hi : i ≤ n
  · rw [homogeneousComplex_X, homogeneousTerm_of_le (Rᵐᵒᵖ) P n i hi]
    infer_instance
  · exact moduleFinite_of_isZero
      (homogeneousComplex_isZero_X (Rᵐᵒᵖ) P n i (by omega))

private instance homogeneousComplex_projective (n i : ℕ) :
    Module.Projective Rᵐᵒᵖ ((homogeneousComplex (Rᵐᵒᵖ) P n).X i) := by
  by_cases hi : i ≤ n
  · rw [homogeneousComplex_X, homogeneousTerm_of_le (Rᵐᵒᵖ) P n i hi]
    infer_instance
  · exact moduleProjective_of_isZero
      (homogeneousComplex_isZero_X (Rᵐᵒᵖ) P n i (by omega))

private instance homogeneousExtension_finite (n : ℕ) :
    ∀ j, Module.Finite Rᵐᵒᵖ ((homogeneousExtension R P n).X j) := by
  intro j
  cases j with
  | ofNat k =>
      cases k with
      | zero =>
          exact moduleFinite_of_iso
            ((homogeneousComplex (Rᵐᵒᵖ) P n).extendXIso
              ComplexShape.embeddingDownNat (i := 0) (i' := 0)
              (by rw [downNat_embedding_index]; simp))
      | succ k =>
          exact moduleFinite_of_isZero
            (homogeneousExtension_isZero_pos R P n _ (by
              change (0 : ℤ) < (k : ℤ) + 1
              omega))
  | negSucc k =>
      exact moduleFinite_of_iso
        ((homogeneousComplex (Rᵐᵒᵖ) P n).extendXIso
          ComplexShape.embeddingDownNat (i := k + 1) (i' := Int.negSucc k)
          (by rw [downNat_embedding_index]; omega))

private instance homogeneousExtension_projective (n : ℕ) :
    ∀ j, Module.Projective Rᵐᵒᵖ ((homogeneousExtension R P n).X j) := by
  intro j
  cases j with
  | ofNat k =>
      cases k with
      | zero =>
          exact moduleProjective_of_iso
            ((homogeneousComplex (Rᵐᵒᵖ) P n).extendXIso
              ComplexShape.embeddingDownNat (i := 0) (i' := 0)
              (by rw [downNat_embedding_index]; simp))
      | succ k =>
          exact moduleProjective_of_isZero
            (homogeneousExtension_isZero_pos R P n _ (by
              change (0 : ℤ) < (k : ℤ) + 1
              omega))
  | negSucc k =>
      exact moduleProjective_of_iso
        ((homogeneousComplex (Rᵐᵒᵖ) P n).extendXIso
          ComplexShape.embeddingDownNat (i := k + 1) (i' := Int.negSucc k)
          (by rw [downNat_embedding_index]; omega))

omit [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P] in
private theorem homogeneousExtension_support (n : ℕ) (j : ℤ)
    (hj : j ∉ homogeneousEulerSupport n) :
    IsZero ((homogeneousExtension R P n).X j) := by
  cases j with
  | ofNat k =>
      cases k with
      | zero =>
          exfalso
          apply hj
          exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩
      | succ k =>
          exact homogeneousExtension_isZero_pos R P n _ (by
            change (0 : ℤ) < (k : ℤ) + 1
            omega)
  | negSucc k =>
      have hk : n < k + 1 := by
        by_contra h
        have hm : k + 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
        apply hj
        exact Finset.mem_image.mpr ⟨k + 1, hm, by omega⟩
      exact moduleIsZero_of_iso
        ((homogeneousComplex (Rᵐᵒᵖ) P n).extendXIso
          ComplexShape.embeddingDownNat (i := k + 1) (i' := Int.negSucc k)
          (by rw [downNat_embedding_index]; omega))
        (homogeneousComplex_isZero_X (Rᵐᵒᵖ) P n (k + 1) hk)

/-- Exactness of the extension, including its zero positive indices. -/
private theorem homogeneousExtension_acyclic (n : ℕ) (hn : 0 < n) :
    (homogeneousExtension R P n).Acyclic := by
  have hK := (HomologicalComplex.acyclic_iff
    (K := homogeneousComplex (Rᵐᵒᵖ) P n)).mp
      (homogeneousComplex_acyclic R P n hn)
  apply (HomologicalComplex.acyclic_iff
    (K := homogeneousExtension R P n)).mpr
  intro j
  cases j with
  | ofNat k =>
      cases k with
      | succ k =>
          exact HomologicalComplex.ExactAt.of_isZero
            (homogeneousExtension_isZero_pos R P n _ (by
              change (0 : ℤ) < (k : ℤ) + 1
              omega))
      | zero =>
          have hsc := (HomologicalComplex.exactAt_iff'
            (K := homogeneousComplex (Rᵐᵒᵖ) P n)
            (i := 1) (j := 0) (k := 0)
            (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero).mp (hK 0)
          have he := (CategoryTheory.ShortComplex.moduleCat_exact_iff _).mp hsc
          change ∀ x : (homogeneousComplex (Rᵐᵒᵖ) P n).X 0,
            (homogeneousComplex (Rᵐᵒᵖ) P n).d 0 0 x = 0 →
            ∃ y : (homogeneousComplex (Rᵐᵒᵖ) P n).X 1,
              (homogeneousComplex (Rᵐᵒᵖ) P n).d 1 0 y = x at he
          apply (HomologicalComplex.exactAt_iff'
            (K := homogeneousExtension R P n)
            (i := -1) (j := 0) (k := 1)
            (by simp)
            (by simp)).mpr
          apply (CategoryTheory.ShortComplex.moduleCat_exact_iff _).mpr
          change ∀ x : (homogeneousExtension R P n).X 0,
            (homogeneousExtension R P n).d 0 1 x = 0 →
            ∃ y : (homogeneousExtension R P n).X (-1),
              (homogeneousExtension R P n).d (-1) 0 y = x
          intro x _
          have h₀ : ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) := by
            rw [downNat_embedding_index]; simp
          have h₁ : ComplexShape.embeddingDownNat.f 1 = (-1 : ℤ) := by
            rw [downNat_embedding_index]; simp
          let e₀ : (homogeneousExtension R P n).X 0 ≅
              (homogeneousComplex (Rᵐᵒᵖ) P n).X 0 :=
            (homogeneousComplex (Rᵐᵒᵖ) P n).extendXIso
              ComplexShape.embeddingDownNat h₀
          let e₁ : (homogeneousExtension R P n).X (-1) ≅
              (homogeneousComplex (Rᵐᵒᵖ) P n).X 1 :=
            (homogeneousComplex (Rᵐᵒᵖ) P n).extendXIso
              ComplexShape.embeddingDownNat h₁
          obtain ⟨y, hy⟩ := he (e₀.hom x) (by simp)
          refine ⟨e₁.inv y, ?_⟩
          have hd : (homogeneousExtension R P n).d (-1) 0 =
              e₁.hom ≫ (homogeneousComplex (Rᵐᵒᵖ) P n).d 1 0 ≫ e₀.inv :=
            HomologicalComplex.extend_d_eq _ ComplexShape.embeddingDownNat h₁ h₀
          have heval := congrArg
            (fun f : (homogeneousExtension R P n).X (-1) ⟶
                (homogeneousExtension R P n).X 0 => f (e₁.inv y)) hd
          change (homogeneousExtension R P n).d (-1) 0 (e₁.inv y) =
            e₀.inv ((homogeneousComplex (Rᵐᵒᵖ) P n).d 1 0
              (e₁.hom (e₁.inv y))) at heval
          simpa only [moduleIso_inv_hom_apply, hy, moduleIso_hom_inv_apply] using heval
  | negSucc k =>
      have hsc := (HomologicalComplex.exactAt_iff'
        (K := homogeneousComplex (Rᵐᵒᵖ) P n)
        (i := k + 2) (j := k + 1) (k := k)
        (ChainComplex.prev ℕ (k + 1)) (ChainComplex.next_nat_succ k)).mp (hK (k + 1))
      have he := (CategoryTheory.ShortComplex.moduleCat_exact_iff _).mp hsc
      change ∀ x : (homogeneousComplex (Rᵐᵒᵖ) P n).X (k + 1),
        (homogeneousComplex (Rᵐᵒᵖ) P n).d (k + 1) k x = 0 →
        ∃ y : (homogeneousComplex (Rᵐᵒᵖ) P n).X (k + 2),
          (homogeneousComplex (Rᵐᵒᵖ) P n).d (k + 2) (k + 1) y = x at he
      apply (HomologicalComplex.exactAt_iff'
        (K := homogeneousExtension R P n)
        (i := Int.negSucc k - 1) (j := Int.negSucc k) (k := Int.negSucc k + 1)
        (CochainComplex.prev ℤ (Int.negSucc k))
        (CochainComplex.next ℤ (Int.negSucc k))).mpr
      apply (CategoryTheory.ShortComplex.moduleCat_exact_iff _).mpr
      change ∀ x : (homogeneousExtension R P n).X (Int.negSucc k),
        (homogeneousExtension R P n).d (Int.negSucc k) (Int.negSucc k + 1) x = 0 →
        ∃ y : (homogeneousExtension R P n).X (Int.negSucc k - 1),
          (homogeneousExtension R P n).d (Int.negSucc k - 1) (Int.negSucc k) y = x
      have h₁ : ComplexShape.embeddingDownNat.f (k + 2) = Int.negSucc k - 1 := by
        rw [downNat_embedding_index]; omega
      have h₂ : ComplexShape.embeddingDownNat.f (k + 1) = Int.negSucc k := by
        rw [downNat_embedding_index]; omega
      have h₃ : ComplexShape.embeddingDownNat.f k = Int.negSucc k + 1 := by
        rw [downNat_embedding_index]; omega
      exact moduleExact_of_transport
        ((homogeneousComplex (Rᵐᵒᵖ) P n).extendXIso ComplexShape.embeddingDownNat h₁)
        ((homogeneousComplex (Rᵐᵒᵖ) P n).extendXIso ComplexShape.embeddingDownNat h₂)
        ((homogeneousComplex (Rᵐᵒᵖ) P n).extendXIso ComplexShape.embeddingDownNat h₃)
        _ _ _ _ he
        (HomologicalComplex.extend_d_eq _ ComplexShape.embeddingDownNat h₁ h₂)
        (HomologicalComplex.extend_d_eq _ ComplexShape.embeddingDownNat h₂ h₃)

private theorem homogeneousExtension_class (n i : ℕ) (hi : i ≤ n) :
    KTheory.K0.of R ((homogeneousExtension R P n).X (-(i : ℤ))) =
      KTheory.K0.of R (Term (Rᵐᵒᵖ) P i (n - i)) := by
  let e : (homogeneousExtension R P n).X (-(i : ℤ)) ≅
      (homogeneousComplex (Rᵐᵒᵖ) P n).X i :=
    (homogeneousComplex (Rᵐᵒᵖ) P n).extendXIso
      ComplexShape.embeddingDownNat (downNat_embedding_index i)
  calc
    _ = KTheory.K0.of R ((homogeneousComplex (Rᵐᵒᵖ) P n).X i) :=
      KTheory.K0.of_eq_of_equiv R
        ((homogeneousExtension R P n).X (-(i : ℤ))) e.toLinearEquiv
    _ = _ :=
      KTheory.K0.of_eq_of_equiv R
        ((homogeneousComplex (Rᵐᵒᵖ) P n).X i)
        (CategoryTheory.Iso.toLinearEquiv
          (eqToIso ((homogeneousComplex_X (Rᵐᵒᵖ) P n i).trans
            (homogeneousTerm_of_le (Rᵐᵒᵖ) P n i hi))))

private theorem homogeneousExtension_euler (n : ℕ) :
    KTheory.K0.eulerCharacteristic R
      (fun j => ((homogeneousExtension R P n).X j : Type (max u v)))
      (homogeneousEulerSupport n) =
      ∑ i ∈ Finset.range (n + 1),
        ((-1 : ℤ) ^ i) • KTheory.K0.of R (Term (Rᵐᵒᵖ) P i (n - i)) := by
  classical
  rw [KTheory.K0.eulerCharacteristic_eq_sum]
  change (∑ j ∈ (Finset.range (n + 1)).image (fun i : ℕ => -(i : ℤ)),
      if Even j then KTheory.K0.of R ((homogeneousExtension R P n).X j)
      else -KTheory.K0.of R ((homogeneousExtension R P n).X j)) = _
  rw [Finset.sum_image (by
    intro a ha b hb hab
    have hab' : (a : ℤ) = (b : ℤ) := by
      simpa using congrArg (fun z : ℤ => -z) hab
    omega)]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
  rw [homogeneousExtension_class R P n i hin]
  have hpar : Even (-(i : ℤ)) ↔ Even i := by
    constructor
    · rintro ⟨a, ha⟩
      apply (Int.even_coe_nat i).mp
      exact ⟨-a, by omega⟩
    · intro h
      obtain ⟨a, ha⟩ := (Int.even_coe_nat i).mpr h
      exact ⟨-a, by omega⟩
  by_cases h : Even i <;> simp [hpar, neg_one_pow_eq_ite, h]

/-- The homogeneous alternating Koszul class is the scalar class only in degree zero,
as in the Koszul class identity of Weibel's *The K-book*. -/
theorem alternatingK0Euler (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), ((-1 : ℤ) ^ i) •
      KTheory.K0.of R (Term (Rᵐᵒᵖ) P i (n - i))) =
      if n = 0 then (1 : KTheory.K0 R) else 0 := by
  by_cases hn : n = 0
  · subst n
    exact alternatingK0Euler_zero R P
  · rw [ite_eq_right hn]
    calc
      _ = KTheory.K0.eulerCharacteristic R
          (fun j => ((homogeneousExtension R P n).X j : Type (max u v)))
          (homogeneousEulerSupport n) := (homogeneousExtension_euler R P n).symm
      _ = 0 := KTheory.K0.eulerCharacteristic_eq_zero_of_acyclic R
        (homogeneousExtension R P n) (homogeneousEulerSupport n)
        (homogeneousExtension_support R P n)
        (homogeneousExtension_acyclic R P n (by omega))

end Module.Koszul
