/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Iris; see docs/CREDITS.md
module

public import Mathlib.LinearAlgebra.Basis.Fin
public import ProjectiveModules.ExteriorPower.DirectSum
public import ProjectiveModules.ExteriorPower.StalkRank

/-!
# The ordered pairing for exterior powers of a product

The pairing is the ordered component of the existing exterior-power direct-sum
decomposition: the `M` factor is included before the `N` factor. For finite flat
modules of constant stalk ranks `i` and `j`, all other components vanish, so
this pairing is bijective. The construction and characteristic formula use
`exteriorPower.prodEquivDirectSum`; the vanishing argument uses
`exteriorPower.subsingleton_of_rankAtStalk_lt` and Mathlib's tensor-product and
direct-sum APIs. No chosen inverse or determinant-line product law is supplied.
-/

@[expose] public section

noncomputable section

open scoped DirectSum TensorProduct

namespace exteriorPower

universe u v w

/-- The ordered component of the existing exterior-power direct-sum decomposition.
The `M` block precedes the `N` block. Its data uses only the stock equivalence,
component inclusion, and the ambient-preserving transport of the right degree. -/
@[no_expose]
noncomputable def prodPairing
    (R : Type u) (M : Type v) (N : Type w)
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (i j : ℕ) :
    ((⋀[R]^i M) ⊗[R] (⋀[R]^j N)) →ₗ[R] ⋀[R]^(i + j) (M × N) :=
  let t : Fin (i + j + 1) :=
    ⟨i, Nat.lt_succ_iff.mpr (Nat.le_add_right i j)⟩
  let rightDegree : (⋀[R]^j N) ≃ₗ[R] ⋀[R]^((i + j) - i) N :=
    LinearEquiv.ofEq (ExteriorAlgebra.exteriorPower R j N)
      (ExteriorAlgebra.exteriorPower R ((i + j) - i) N)
      (congrArg (fun n : ℕ ↦ ExteriorAlgebra.exteriorPower R n N)
        (Nat.add_sub_cancel_left i j).symm)
  (prodEquivDirectSum R M N (i + j)).symm.toLinearMap ∘ₗ
    DirectSum.lof R (Fin (i + j + 1))
      (fun a ↦ (⋀[R]^a.1 M) ⊗[R] (⋀[R]^((i + j) - a.1) N)) t ∘ₗ
        (TensorProduct.congr (LinearEquiv.refl R (⋀[R]^i M)) rightDegree).toLinearMap

/-- The pairing is ambient exterior multiplication after the canonical inclusions,
with the `M` factor first. This is the characteristic formula of
`prodEquivDirectSum` on the selected summand. -/
theorem coe_prodPairing_tmul
    (R : Type u) (M : Type v) (N : Type w)
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (i j : ℕ) (a : ⋀[R]^i M) (b : ⋀[R]^j N) :
    (prodPairing R M N i j (a ⊗ₜ[R] b)).val =
      ExteriorAlgebra.map (LinearMap.inl R M N) a.val *
        ExteriorAlgebra.map (LinearMap.inr R M N) b.val := by
  exact coe_prodEquivDirectSum_symm_of_tmul R M N (i + j)
    ⟨i, Nat.lt_succ_iff.mpr (Nat.le_add_right i j)⟩ a
    (LinearEquiv.ofEq (ExteriorAlgebra.exteriorPower R j N)
      (ExteriorAlgebra.exteriorPower R ((i + j) - i) N)
      (congrArg (fun n : ℕ ↦ ExteriorAlgebra.exteriorPower R n N)
        (Nat.add_sub_cancel_left i j).symm) b)

/-- For finite flat modules of constant stalk ranks, the ordered top-degree pairing
is bijective. Every other direct-sum component has a factor above its stalk rank
and therefore vanishes. No global basis or projectivity is assumed. -/
theorem bijective_prodPairing_of_rankAtStalk_eq
    (R : Type u) (M : Type v) (N : Type w)
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Flat R M] [Module.Finite R N] [Module.Flat R N]
    (i j : ℕ)
    (hM : Module.rankAtStalk (R := R) M = (fun _ ↦ i))
    (hN : Module.rankAtStalk (R := R) N = (fun _ ↦ j)) :
    Function.Bijective (prodPairing R M N i j) := by
  classical
  let t : Fin (i + j + 1) :=
    ⟨i, Nat.lt_succ_iff.mpr (Nat.le_add_right i j)⟩
  let β := fun a : Fin (i + j + 1) ↦ (⋀[R]^a.1 M) ⊗[R] (⋀[R]^((i + j) - a.1) N)
  have hother (a : Fin (i + j + 1)) (ha : a ≠ t) : Subsingleton (β a) := by
    rcases lt_trichotomy a.1 i with hlt | heq | hgt
    · have hdegree : j < (i + j) - a.1 := by
        apply Nat.lt_sub_iff_add_lt.mpr
        calc
          j + a.1 = a.1 + j := Nat.add_comm _ _
          _ < i + j := Nat.add_lt_add_right hlt j
      haveI : Subsingleton (⋀[R]^((i + j) - a.1) N) :=
        subsingleton_of_rankAtStalk_lt (R := R) (M := N) _ (fun p ↦ by
          rw [hN]
          exact hdegree)
      exact inferInstance
    · exact (ha (Fin.ext heq)).elim
    · haveI : Subsingleton (⋀[R]^a.1 M) :=
        subsingleton_of_rankAtStalk_lt (R := R) (M := M) _ (fun p ↦ by
          rw [hM]
          exact hgt)
      exact inferInstance
  have hinc : Function.Bijective (DirectSum.lof R (Fin (i + j + 1)) β t) := by
    constructor
    · intro x y hxy
      simpa only [DirectSum.component.lof_self] using
        congrArg (DirectSum.component R (Fin (i + j + 1)) β t) hxy
    · intro x
      refine ⟨DirectSum.component R (Fin (i + j + 1)) β t x, ?_⟩
      apply DirectSum.ext_component R
      intro a
      by_cases ha : a = t
      · subst a
        exact DirectSum.component.lof_self R t _
      · haveI : Subsingleton (β a) := hother a ha
        exact Subsingleton.elim _ _
  let rightDegree : (⋀[R]^j N) ≃ₗ[R] ⋀[R]^((i + j) - i) N :=
    LinearEquiv.ofEq (ExteriorAlgebra.exteriorPower R j N)
      (ExteriorAlgebra.exteriorPower R ((i + j) - i) N)
      (congrArg (fun n : ℕ ↦ ExteriorAlgebra.exteriorPower R n N)
        (Nat.add_sub_cancel_left i j).symm)
  exact (prodEquivDirectSum R M N (i + j)).symm.bijective.comp
    (hinc.comp (TensorProduct.congr (LinearEquiv.refl R (⋀[R]^i M)) rightDegree).bijective)

/-! ## Private standard definition-contract model

The inputs and independent target below are stock exterior generators over `ℤ`.
The two coordinate facts identify the target's ordered family literally as
`(1, 0)`, then `(0, 1)`. The rank premise is supplied by stock free-rank results.
The last two applications use the public characteristic and bijectivity API,
without unfolding the pairing. The independent target `c` is not defined as an
image, and no identification of the output with `c` is asserted.
-/

namespace IntegerProductPairing

private def a : ⋀[ℤ]^1 ℤ :=
  exteriorPower.ιMulti ℤ 1 (fun _ ↦ (1 : ℤ))

private def b : ⋀[ℤ]^1 ℤ :=
  exteriorPower.ιMulti ℤ 1 (fun _ ↦ (1 : ℤ))

private def c : ⋀[ℤ]^2 (ℤ × ℤ) :=
  exteriorPower.ιMulti ℤ 2 (Module.Basis.finTwoProd ℤ)

private theorem target_first : Module.Basis.finTwoProd ℤ 0 = ((1, 0) : ℤ × ℤ) :=
  Module.Basis.finTwoProd_zero ℤ

private theorem target_second : Module.Basis.finTwoProd ℤ 1 = ((0, 1) : ℤ × ℤ) :=
  Module.Basis.finTwoProd_one ℤ

private theorem integer_rankAtStalk :
    Module.rankAtStalk (R := ℤ) ℤ = (fun _ ↦ 1) := by
  simpa only [Pi.one_def] using (Module.rankAtStalk_self (R := ℤ))

/-- The characteristic API applied to independent stock generators over `ℤ`. -/
private theorem characteristic :
    (prodPairing ℤ ℤ ℤ 1 1 (a ⊗ₜ[ℤ] b)).val =
      ExteriorAlgebra.map (LinearMap.inl ℤ ℤ ℤ) a.val *
        ExteriorAlgebra.map (LinearMap.inr ℤ ℤ ℤ) b.val :=
  coe_prodPairing_tmul ℤ ℤ ℤ 1 1 a b

/-- The bijectivity API applied over `ℤ`.
The finite and flat instances are the existing scalar-self instances. -/
private theorem bijective : Function.Bijective (prodPairing ℤ ℤ ℤ 1 1) :=
  bijective_prodPairing_of_rankAtStalk_eq ℤ ℤ ℤ 1 1
    integer_rankAtStalk integer_rankAtStalk

end IntegerProductPairing

end exteriorPower
