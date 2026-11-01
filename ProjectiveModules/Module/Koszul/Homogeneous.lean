/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Koszul.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Homogeneous Koszul complexes

For a commutative ring `S`, an `S`-module `P`, and a total degree `n`, the
homogeneous Koszul complex has term `Λ^i P ⊗ Sym^(n-i) P` in degrees `i ≤ n`
and the zero object in higher degrees. Its adjacent differential is the
bigraded signed Koszul differential, with only its symmetric degree reindexed.

The scalar ring and the module have independent universes. No finiteness,
projectivity, freeness, rank, or nontriviality assumption is imposed. The
construction uses the canonical module structures and the category of modules
in their natural maximum universe.

The degree-zero and degree-one identifications below describe the scalar
complex in total degree zero and the identity of `P` in total degree one.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ZeroObject

universe u v

namespace Module.Koszul

variable (S : Type u) [CommRing S]
variable (P : Type v) [AddCommGroup P] [Module S P]

/-- The symmetric degree increases by one along an interior homogeneous differential. -/
theorem homogeneousDegree_succ (n i : ℕ) (h : i < n) :
    n - (i + 1) + 1 = n - i := by
  omega

/-- The Koszul differential between the two bigraded terms of total degree `n`. -/
def homogeneousDelta (n i : ℕ) (h : i < n) :
    Term S P (i + 1) (n - (i + 1)) →ₗ[S] Term S P i (n - i) :=
  cast
    (congrArg
      (fun d => Term S P (i + 1) (n - (i + 1)) →ₗ[S] Term S P i d)
      (homogeneousDegree_succ n i h))
    (delta S P i (n - (i + 1)))

/-- The term of total degree `n` in chain degree `i`, zero above degree `n`. -/
def homogeneousTerm (n i : ℕ) : ModuleCat.{max u v} S :=
  if i ≤ n then ModuleCat.of S (Term S P i (n - i))
  else 0

/-- Inside its finite range, a homogeneous term is the exterior-symmetric term. -/
@[simp]
theorem homogeneousTerm_of_le (n i : ℕ) (h : i ≤ n) :
    homogeneousTerm S P n i = ModuleCat.of S (Term S P i (n - i)) := by
  simp [homogeneousTerm, h]

/-- Above its total degree, a homogeneous term is the categorical zero object. -/
@[simp]
theorem homogeneousTerm_eq_zero (n i : ℕ) (h : n < i) :
    homogeneousTerm S P n i = 0 := by
  have h' : ¬ i ≤ n := by omega
  simp [homogeneousTerm, h']

/-- In the finite range, the bigraded and homogeneous differential hom types agree. -/
theorem homogeneousTerm_hom_eq (n i : ℕ) (h : i < n) :
    (ModuleCat.of S (Term S P (i + 1) (n - (i + 1))) ⟶
      ModuleCat.of S (Term S P i (n - i))) =
    (homogeneousTerm S P n (i + 1) ⟶ homogeneousTerm S P n i) := by
  have hs : i + 1 ≤ n := by omega
  have ht : i ≤ n := by omega
  rw [homogeneousTerm_of_le S P n (i + 1) hs,
    homogeneousTerm_of_le S P n i ht]

/-- The adjacent homogeneous differential, zero when its source is above the finite range. -/
def homogeneousDifferential (n i : ℕ) :
    homogeneousTerm S P n (i + 1) ⟶ homogeneousTerm S P n i :=
  if h : i < n then
    cast (homogeneousTerm_hom_eq S P n i h)
      (ModuleCat.ofHom (R := S)
        (X := Term S P (i + 1) (n - (i + 1)))
        (Y := Term S P i (n - i)) (homogeneousDelta S P n i h))
  else 0

private theorem homogeneousDelta_comp (n i : ℕ) (hi : i < n) (h : i + 1 < n) :
    (homogeneousDelta S P n i hi).comp
      (homogeneousDelta S P n (i + 1) h) = 0 := by
  have aux (a b c : ℕ) (h₁ : a + 1 = b) (h₂ : b + 1 = c) :
      (cast (congrArg
          (fun t => Term S P (i + 1) b →ₗ[S] Term S P i t) h₂)
        (delta S P i b)).comp
      (cast (congrArg
          (fun t => Term S P (i + 2) a →ₗ[S] Term S P (i + 1) t) h₁)
        (delta S P (i + 1) a)) = 0 := by
    subst b
    subst c
    exact delta_comp_delta S P i a
  exact aux (n - (i + 2)) (n - (i + 1)) (n - i)
    (homogeneousDegree_succ n (i + 1) h)
    (homogeneousDegree_succ n i hi)

private theorem castHom_comp_eq_zero
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : ModuleCat.{max u v} S}
    (h₀ : X₀ = Y₀) (h₁ : X₁ = Y₁) (h₂ : X₂ = Y₂)
    (e₁ : (X₂ ⟶ X₁) = (Y₂ ⟶ Y₁))
    (e₀ : (X₁ ⟶ X₀) = (Y₁ ⟶ Y₀))
    (f : X₂ ⟶ X₁) (g : X₁ ⟶ X₀) (hfg : f ≫ g = 0) :
    cast e₁ f ≫ cast e₀ g = 0 := by
  subst Y₀
  subst Y₁
  subst Y₂
  exact hfg

/-- Two successive homogeneous differentials compose to zero. -/
theorem homogeneousDifferential_comp (n i : ℕ) :
    homogeneousDifferential S P n (i + 1) ≫ homogeneousDifferential S P n i = 0 := by
  by_cases h : i + 1 < n
  · have hi : i < n := by omega
    have hs : i + 2 ≤ n := by omega
    have hm : i + 1 ≤ n := by omega
    have ht : i ≤ n := by omega
    have hd :
        ModuleCat.ofHom (R := S)
          (X := Term S P (i + 1 + 1) (n - (i + 1 + 1)))
          (Y := Term S P (i + 1) (n - (i + 1)))
          (homogeneousDelta S P n (i + 1) h) ≫
          ModuleCat.ofHom (R := S)
            (X := Term S P (i + 1) (n - (i + 1)))
            (Y := Term S P i (n - i))
            (homogeneousDelta S P n i hi) = 0 := by
      rw [← ModuleCat.ofHom_comp, homogeneousDelta_comp S P n i hi h,
        ModuleCat.ofHom_zero]
    simpa only [homogeneousDifferential, dite_eq_left h, dite_eq_left hi] using
      (castHom_comp_eq_zero (S := S)
        (homogeneousTerm_of_le S P n i ht).symm
        (homogeneousTerm_of_le S P n (i + 1) hm).symm
        (homogeneousTerm_of_le S P n (i + 1 + 1) hs).symm
        (homogeneousTerm_hom_eq S P n (i + 1) h)
        (homogeneousTerm_hom_eq S P n i hi)
        (ModuleCat.ofHom (R := S)
          (X := Term S P (i + 1 + 1) (n - (i + 1 + 1)))
          (Y := Term S P (i + 1) (n - (i + 1)))
          (homogeneousDelta S P n (i + 1) h))
        (ModuleCat.ofHom (R := S)
            (X := Term S P (i + 1) (n - (i + 1)))
            (Y := Term S P i (n - i))
            (homogeneousDelta S P n i hi)) hd)
  · simp only [homogeneousDifferential, dite_eq_right h, zero_comp]

/-- The Nat-indexed homogeneous Koszul chain complex of total degree `n`. -/
def homogeneousComplex (n : ℕ) : ChainComplex (ModuleCat.{max u v} S) ℕ :=
  ChainComplex.of (homogeneousTerm S P n) (homogeneousDifferential S P n)
    (homogeneousDifferential_comp S P n)

/-- Applying the homogeneous differential is applying `delta` and reindexing its degree. -/
theorem homogeneousDelta_apply (n i : ℕ) (h : i < n)
    (x : Term S P (i + 1) (n - (i + 1))) :
    homogeneousDelta S P n i h x =
      cast (congrArg (Term S P i) (homogeneousDegree_succ n i h))
        (delta S P i (n - (i + 1)) x) := by
  have cast_apply (a b : ℕ) (e : a = b)
      (f : Term S P (i + 1) (n - (i + 1)) →ₗ[S] Term S P i a) :
      (cast (congrArg
          (fun d => Term S P (i + 1) (n - (i + 1)) →ₗ[S] Term S P i d) e)
        f) x = cast (congrArg (Term S P i) e) (f x) := by
    subst b
    rfl
  exact cast_apply _ _ (homogeneousDegree_succ n i h)
    (delta S P i (n - (i + 1)))

/-- In the interior, the categorical differential is the specified homogeneous linear map. -/
theorem homogeneousDifferential_heq_of_lt (n i : ℕ) (h : i < n) :
    HEq (homogeneousDifferential S P n i)
      (ModuleCat.ofHom (R := S)
        (X := Term S P (i + 1) (n - (i + 1)))
        (Y := Term S P i (n - i)) (homogeneousDelta S P n i h)) := by
  have hcast {α β : Sort _} (e : α = β) (y : α) : HEq (cast e y) y := by
    cases e
    rfl
  simpa only [homogeneousDifferential, dite_eq_left h] using
    (hcast (homogeneousTerm_hom_eq S P n i h)
      (ModuleCat.ofHom (R := S)
        (X := Term S P (i + 1) (n - (i + 1)))
        (Y := Term S P i (n - i)) (homogeneousDelta S P n i h)))

/-- If the adjacent source is outside the finite range, its differential is zero. -/
@[simp]
theorem homogeneousDifferential_eq_zero (n i : ℕ) (h : n ≤ i) :
    homogeneousDifferential S P n i = 0 := by
  have h' : ¬ i < n := by omega
  simp [homogeneousDifferential, h']

/-- The objects of the homogeneous complex are its prescribed homogeneous terms. -/
@[simp]
theorem homogeneousComplex_X (n i : ℕ) :
    (homogeneousComplex S P n).X i = homogeneousTerm S P n i := by
  rfl

/-- The adjacent maps of the homogeneous complex are its prescribed differentials. -/
theorem homogeneousComplex_d (n i : ℕ) :
    (homogeneousComplex S P n).d (i + 1) i = homogeneousDifferential S P n i := by
  exact ChainComplex.of_d (homogeneousTerm S P n)
    (homogeneousDifferential S P n) i

/-- The homogeneous complex is supported in the finite interval from zero to `n`. -/
theorem homogeneousComplex_isZero_X (n i : ℕ) (h : n < i) :
    IsZero ((homogeneousComplex S P n).X i) := by
  simpa only [homogeneousComplex_X, homogeneousTerm_eq_zero S P n i h] using
    (isZero_zero (C := ModuleCat.{max u v} S))

/-- Every map whose source degree is above the total degree is zero. -/
theorem homogeneousComplex_d_eq_zero_of_source (n i j : ℕ) (h : n < i) :
    (homogeneousComplex S P n).d i j = 0 := by
  exact (homogeneousComplex_isZero_X S P n i h).eq_of_src _ _

/-- The exterior-symmetric term in bidegree `(0,0)` is canonically the scalar module. -/
def termZeroZeroEquiv : Term S P 0 0 ≃ₗ[S] S :=
  (TensorProduct.congr
    (exteriorPower.zeroEquiv (R := S) (M := P))
    (SymmetricPower.isEmptyEquiv (R := S) (ι := SymmetricIndex.{u} 0) (M := P))).trans
    (TensorProduct.lid S S)

/-- The exterior-symmetric term in bidegree `(1,0)` is canonically `P`. -/
def termOneZeroEquiv : Term S P 1 0 ≃ₗ[S] P :=
  (TensorProduct.congr
    (exteriorPower.oneEquiv (R := S) (M := P))
    (SymmetricPower.isEmptyEquiv (R := S) (ι := SymmetricIndex.{u} 0) (M := P))).trans
    (TensorProduct.rid S P)

/-- The exterior-symmetric term in bidegree `(0,1)` is canonically `P`. -/
def termZeroOneEquiv : Term S P 0 1 ≃ₗ[S] P :=
  (TensorProduct.congr
    (exteriorPower.zeroEquiv (R := S) (M := P))
    (SymmetricPower.subsingletonEquiv (R := S) (ι := SymmetricIndex.{u} 1)
      (M := P) ⟨0⟩)).trans
    (TensorProduct.lid S P)

/-- Under the canonical degree-one identifications, the Koszul differential is the identity. -/
theorem delta_zero_zero (x : Term S P 1 0) :
    termZeroOneEquiv S P (delta S P 0 0 x) = termOneZeroEquiv S P x := by
  have heq :
      (termZeroOneEquiv S P).toLinearMap.comp (delta S P 0 0) =
        (termOneZeroEquiv S P).toLinearMap := by
    apply TensorProduct.ext
    apply exteriorPower.linearMap_ext
    ext1 v
    apply SymmetricPower.hom_ext
    intro s
    simp [termZeroOneEquiv, termOneZeroEquiv, delta_ιMulti_tmul, insert_tprod,
      TensorProduct.congr_tmul, exteriorPower.zeroEquiv_ιMulti,
      exteriorPower.oneEquiv_ιMulti, SymmetricPower.isEmptyEquiv_tprod,
      SymmetricPower.subsingletonEquiv_tprod]
  exact congrArg (fun f : Term S P 1 0 →ₗ[S] P => f x) heq

end Module.Koszul
