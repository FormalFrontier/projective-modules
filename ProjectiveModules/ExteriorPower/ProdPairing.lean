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
direct-sum APIs. The resulting `exteriorPower.prodPairingEquiv` has this ordered
pairing as its forward map. Both directions are natural for arbitrary linear maps
between factors of the same constant stalk ranks.
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

universe v' w'

/-- The ordered exterior-power pairing is natural for arbitrary linear maps of both
factors, without rank or finiteness assumptions. -/
theorem prodPairing_naturality
    (R : Type u) (M : Type v) (N : Type w)
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {M' : Type v'} {N' : Type w'}
    [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    (i j : ℕ) (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    (map (i + j) (f.prodMap g)).comp (prodPairing R M N i j) =
      (prodPairing R M' N' i j).comp
        (TensorProduct.map (map i f) (map j g)) := by
  apply TensorProduct.ext'
  intro a b
  apply Subtype.ext
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, coe_map,
    coe_prodPairing_tmul, map_mul]
  congr 1
  · rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    rw [show (f.prodMap g).comp (LinearMap.inl R M N) =
        (LinearMap.inl R M' N').comp f by
          apply LinearMap.ext
          intro x
          simp]
    rw [← ExteriorAlgebra.map_comp_map]
    rfl
  · rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    rw [show (f.prodMap g).comp (LinearMap.inr R M N) =
        (LinearMap.inr R M' N').comp g by
          apply LinearMap.ext
          intro x
          simp]
    rw [← ExteriorAlgebra.map_comp_map]
    rfl

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
      have : Subsingleton (⋀[R]^((i + j) - a.1) N) :=
        subsingleton_of_rankAtStalk_lt (R := R) (M := N) _ (fun p ↦ by
          rw [hN]
          exact hdegree)
      exact inferInstance
    · exact (ha (Fin.ext heq)).elim
    · have : Subsingleton (⋀[R]^a.1 M) :=
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
      · have : Subsingleton (β a) := hother a ha
        exact Subsingleton.elim _ _
  let rightDegree : (⋀[R]^j N) ≃ₗ[R] ⋀[R]^((i + j) - i) N :=
    LinearEquiv.ofEq (ExteriorAlgebra.exteriorPower R j N)
      (ExteriorAlgebra.exteriorPower R ((i + j) - i) N)
      (congrArg (fun n : ℕ ↦ ExteriorAlgebra.exteriorPower R n N)
        (Nat.add_sub_cancel_left i j).symm)
  exact (prodEquivDirectSum R M N (i + j)).symm.bijective.comp
    (hinc.comp (TensorProduct.congr (LinearEquiv.refl R (⋀[R]^i M)) rightDegree).bijective)

section Top

variable (R : Type u) (M : Type v) (N : Type w)
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [Module.Finite R M] [Module.Flat R M] [Module.Finite R N] [Module.Flat R N]
variable (i j : ℕ)
variable (hM : Module.rankAtStalk (R := R) M = fun _ ↦ i)
variable (hN : Module.rankAtStalk (R := R) N = fun _ ↦ j)

/-- The ordered top exterior-product equivalence for finite flat modules of constant
stalk ranks. Its forward map is `prodPairing`, with the `M` factor preceding the `N`
factor, including when either degree is zero. -/
def prodPairingEquiv :
    ((⋀[R]^i M) ⊗[R] (⋀[R]^j N)) ≃ₗ[R] ⋀[R]^(i + j) (M × N) :=
  LinearEquiv.ofBijective (prodPairing R M N i j)
    (bijective_prodPairing_of_rankAtStalk_eq R M N i j hM hN)

/-- The forward linear map is the ordered exterior-product pairing. -/
@[simp]
theorem prodPairingEquiv_toLinearMap :
    (prodPairingEquiv R M N i j hM hN).toLinearMap = prodPairing R M N i j :=
  rfl

/-- Evaluation of the top exterior-product equivalence is the ordered pairing. -/
@[simp]
theorem prodPairingEquiv_apply (x : (⋀[R]^i M) ⊗[R] (⋀[R]^j N)) :
    prodPairingEquiv R M N i j hM hN x = prodPairing R M N i j x :=
  rfl

/-- On pure tensors the equivalence is exterior multiplication after the canonical
inclusions, with the `M` factor first. -/
theorem coe_prodPairingEquiv_tmul (a : ⋀[R]^i M) (b : ⋀[R]^j N) :
    (prodPairingEquiv R M N i j hM hN (a ⊗ₜ[R] b)).val =
      ExteriorAlgebra.map (LinearMap.inl R M N) a.val *
        ExteriorAlgebra.map (LinearMap.inr R M N) b.val :=
  coe_prodPairing_tmul R M N i j a b

/-- Applying the inverse to an ordered pairing recovers the input tensor. -/
@[simp]
theorem prodPairingEquiv_symm_prodPairing (x : (⋀[R]^i M) ⊗[R] (⋀[R]^j N)) :
    (prodPairingEquiv R M N i j hM hN).symm (prodPairing R M N i j x) = x :=
  (prodPairingEquiv R M N i j hM hN).symm_apply_apply x

/-- Pairing the tensor recovered by the inverse recovers the top exterior form. -/
@[simp]
theorem prodPairing_prodPairingEquiv_symm (z : ⋀[R]^(i + j) (M × N)) :
    prodPairing R M N i j ((prodPairingEquiv R M N i j hM hN).symm z) = z :=
  (prodPairingEquiv R M N i j hM hN).apply_symm_apply z

/-- The inverse is a given pure tensor precisely when the ambient exterior form is
the ordered product of its factors. -/
theorem prodPairingEquiv_symm_apply_eq_tmul_iff
    (z : ⋀[R]^(i + j) (M × N)) (a : ⋀[R]^i M) (b : ⋀[R]^j N) :
    (prodPairingEquiv R M N i j hM hN).symm z = a ⊗ₜ[R] b ↔
      z.val = ExteriorAlgebra.map (LinearMap.inl R M N) a.val *
        ExteriorAlgebra.map (LinearMap.inr R M N) b.val := by
  rw [LinearEquiv.symm_apply_eq]
  constructor
  · intro h
    rw [h, coe_prodPairingEquiv_tmul]
  · intro h
    apply Subtype.ext
    rw [coe_prodPairingEquiv_tmul]
    exact h

variable {M' : Type v'} {N' : Type w'}
variable [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
variable [Module.Finite R M'] [Module.Flat R M'] [Module.Finite R N'] [Module.Flat R N']

/-- Naturality of the top exterior-product equivalence for arbitrary linear maps
between factors of the same constant stalk ranks, in independent universes. -/
theorem prodPairingEquiv_naturality
    (hM' : Module.rankAtStalk (R := R) M' = fun _ ↦ i)
    (hN' : Module.rankAtStalk (R := R) N' = fun _ ↦ j)
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    (map (i + j) (f.prodMap g)).comp
        (prodPairingEquiv R M N i j hM hN).toLinearMap =
      (prodPairingEquiv R M' N' i j hM' hN').toLinearMap.comp
        (TensorProduct.map (map i f) (map j g)) :=
  prodPairing_naturality R M N i j f g

/-- The inverse top exterior-product equivalences commute with arbitrary linear
maps between factors of the same constant stalk ranks. -/
theorem prodPairingEquiv_symm_naturality
    (hM' : Module.rankAtStalk (R := R) M' = fun _ ↦ i)
    (hN' : Module.rankAtStalk (R := R) N' = fun _ ↦ j)
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    (prodPairingEquiv R M' N' i j hM' hN').symm.toLinearMap.comp
        (map (i + j) (f.prodMap g)) =
      (TensorProduct.map (map i f) (map j g)).comp
        (prodPairingEquiv R M N i j hM hN).symm.toLinearMap := by
  apply LinearMap.ext
  intro z
  apply (prodPairingEquiv R M' N' i j hM' hN').injective
  have h := LinearMap.congr_fun
    (prodPairingEquiv_naturality R M N i j hM hN hM' hN' f g)
    ((prodPairingEquiv R M N i j hM hN).symm z)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply] using h

end Top

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
