/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.EulerCharacteristic
public import ProjectiveModules.KTheory.ParitySum
public import ProjectiveModules.Module.CochainCycles
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-!
# Euler characteristics of cochain complexes

Finite supports are expressed by vanishing of the module objects, rather than
vanishing of their classes. Bounded projective cochains use Mathlib's
K-projectivity criterion and its homotopy-to-zero construction. The cycle
splitting uses the right-split exact-sequence equivalence from Mathlib and its
application formula in `StableRange.Module.SplitSurjective`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Graduate Studies in Mathematics 145, American Mathematical Society, 2013.
* Mathlib's homotopy and K-projective cochain-complex APIs.
-/

@[expose] public section

universe u v

open CategoryTheory HomologicalComplex
open scoped BigOperators

namespace KTheory

private theorem classOfSubsingleton_eq_zero (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] [Subsingleton M] :
    ProjectiveClass.of R M = 0 := by
  simp

private noncomputable def cochainHomotopyZero (R : Type u) [Ring R]
    (C : CochainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    [∀ i, Module.Projective Rᵐᵒᵖ (C.X i)] (S : Finset ℤ)
    (hS : ∀ i, i ∉ S → CategoryTheory.Limits.IsZero (C.X i)) (hC : C.Acyclic) :
    Homotopy (𝟙 C) 0 := by
  classical
  have hb : ∃ b : ℤ, C.IsStrictlyLE b := by
    by_cases hne : S.Nonempty
    · refine ⟨S.max' hne, (CochainComplex.isStrictlyLE_iff C _).2 ?_⟩
      intro i hi
      exact hS i (fun his => (not_lt_of_ge (Finset.le_max' S i his)) hi)
    · refine ⟨0, (CochainComplex.isStrictlyLE_iff C _).2 ?_⟩
      intro i _
      exact hS i (by simp [Finset.not_nonempty_iff_eq_empty.mp hne])
  let b := Classical.choose hb
  letI : C.IsStrictlyLE b := Classical.choose_spec hb
  letI : C.IsKProjective := CochainComplex.isKProjective_of_projective C b
  exact CochainComplex.IsKProjective.homotopyZero (𝟙 C) hC

namespace ProjectiveClass

/-- The even and odd term-class sums of a finitely supported acyclic cochain
complex of finite-projective right modules agree in the projective-class monoid.
No cancellation or injectivity of the map to `K0 R` is used. This is the
projective-class form of acyclic Euler vanishing; see Weibel, *The K-book*. -/
theorem sum_even_eq_sum_odd_of_acyclic (R : Type u) [Ring R]
    (C : CochainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    [∀ i, Module.Finite Rᵐᵒᵖ (C.X i)] [∀ i, Module.Projective Rᵐᵒᵖ (C.X i)]
    (S : Finset ℤ) (hS : ∀ i, i ∉ S → Limits.IsZero (C.X i)) (hC : C.Acyclic) :
    (S.filter Even).sum (fun i => of R (C.X i)) =
      (S.filter Odd).sum (fun i => of R (C.X i)) := by
  classical
  let h := cochainHomotopyZero R C S hS hC
  let Z (i : ℤ) := LinearMap.ker ((C.d i (i + 1)).hom)
  have : ∀ i, Module.Finite Rᵐᵒᵖ (Z i) := fun i => C.moduleFinite_cycles h i
  have : ∀ i, Module.Projective Rᵐᵒᵖ (Z i) := fun i => C.moduleProjective_cycles h i
  let z (i : ℤ) : ProjectiveClass R := of R (Z i)
  have hterm (i : ℤ) : of R (C.X i) = z i + z (i + 1) := by
    calc
      of R (C.X i) = of R (Z i × Z (i + 1)) :=
        of_eq_of_equiv R (C.X i) (C.moduleCyclesEquiv h i).symm
      _ = z i + z (i + 1) := of_prod R (Z i) (Z (i + 1))
  have hzero (i : ℤ) (hi : i ∉ S) : of R (C.X i) = 0 := by
    have : Subsingleton (C.X i) := ModuleCat.subsingleton_of_isZero (hS i hi)
    exact classOfSubsingleton_eq_zero R (C.X i)
  have hz (i : ℤ) (hi : i ∉ S) : z i = 0 := by
    have : Subsingleton (C.X i) := ModuleCat.subsingleton_of_isZero (hS i hi)
    exact classOfSubsingleton_eq_zero R (Z i)
  by_cases hne : S.Nonempty
  · let a : ℤ := S.min' hne - 1
    let b : ℤ := S.max' hne
    let I := Finset.Icc a b
    have hSI : S ⊆ I := by
      intro i hi
      have hmin := Finset.min'_le S i hi
      have hmax := Finset.le_max' S i hi
      exact Finset.mem_Icc.mpr ⟨by dsimp [a]; omega, hmax⟩
    have ha : z a = 0 := by
      apply hz a
      intro hi
      have hmin := Finset.min'_le S a hi
      dsimp [a] at hmin
      omega
    have hb : z (b + 1) = 0 := by
      apply hz (b + 1)
      intro hi
      have hmax := Finset.le_max' S (b + 1) hi
      dsimp [b] at hmax
      omega
    have hsum (p : ℤ → Prop) [DecidablePred p] :
        (S.filter p).sum (fun i => of R (C.X i)) =
          (I.filter p).sum (fun i => of R (C.X i)) := by
      apply Finset.sum_subset
      · intro i hi
        obtain ⟨his, hip⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨hSI his, hip⟩
      · intro i hi hn
        apply hzero i
        intro his
        exact hn (Finset.mem_filter.mpr ⟨his, (Finset.mem_filter.mp hi).2⟩)
    calc
      (S.filter Even).sum (fun i => of R (C.X i)) =
          (I.filter Even).sum (fun i => of R (C.X i)) := hsum Even
      _ = (I.filter Even).sum (fun i => z i + z (i + 1)) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (I.filter Odd).sum (fun i => z i + z (i + 1)) :=
        Int.sum_Icc_even_add_eq_sum_Icc_odd_add z a b ha hb
      _ = (I.filter Odd).sum (fun i => of R (C.X i)) :=
        Finset.sum_congr rfl (fun i _ => (hterm i).symm)
      _ = (S.filter Odd).sum (fun i => of R (C.X i)) := (hsum Odd).symm
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

end ProjectiveClass

namespace K0

/-- A finitely supported acyclic cochain complex of finite-projective right
modules has zero Euler characteristic in `K0 R` (Weibel, *The K-book*).
This follows by applying the additive class map to the equality in
`ProjectiveClass R`, not by cancellation in that monoid. -/
theorem eulerCharacteristic_eq_zero_of_acyclic (R : Type u) [Ring R]
    (C : CochainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    [∀ i, Module.Finite Rᵐᵒᵖ (C.X i)] [∀ i, Module.Projective Rᵐᵒᵖ (C.X i)]
    (S : Finset ℤ) (hS : ∀ i, i ∉ S → Limits.IsZero (C.X i)) (hC : C.Acyclic) :
    eulerCharacteristic R (fun i => (C.X i : Type v)) S = 0 := by
  classical
  rw [eulerCharacteristic_eq_sum_sub_sum]
  apply sub_eq_zero.mpr
  simpa only [map_sum, ofClass_of] using
    congrArg (ofClass R) (ProjectiveClass.sum_even_eq_sum_odd_of_acyclic R C S hS hC)

end K0

end KTheory
