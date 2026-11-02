/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md
module

public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Exterior powers of a direct sum

This file gives the fixed-degree decomposition of the exterior power of a binary direct sum.
It is valid for arbitrary modules over an arbitrary commutative ring, including degree zero.
The component formula on generating wedges uses Eric Wieser's formalization of the exterior
product of alternating maps, `AlternatingMap.domCoprod`.
The homogeneous components are natural in both module arguments and respect graded
commutation and association. These identities follow from the ordered multiplication
formula for the inverse binary decomposition.
-/

@[expose] public section

noncomputable section

open scoped DirectSum TensorProduct

namespace exteriorPower

universe u v w

variable (R : Type u) [CommRing R]
variable (P : Type v) (Q : Type w)
variable [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

private abbrev Bidegree (ij : ℕ × ℕ) :=
  (⋀[R]^ij.1 P) ⊗[R] (⋀[R]^ij.2 Q)

/-- The ambient decomposition of the full exterior algebra into all pairs of degrees. -/
private noncomputable def ambientDirectSumEquiv :
    ExteriorAlgebra R (P × Q) ≃ₗ[R] ⨁ ij : ℕ × ℕ, Bidegree R P Q ij :=
  (ExteriorAlgebra.prodEquivTensor R P Q).toLinearEquiv ≪≫ₗ
    GradedTensorProduct.auxEquiv R
      (fun i : ℕ ↦ ⋀[R]^i P) (fun j : ℕ ↦ ⋀[R]^j Q) ≪≫ₗ
    TensorProduct.directSum R R
      (fun i : ℕ ↦ ⋀[R]^i P) (fun j : ℕ ↦ ⋀[R]^j Q)

private theorem ambientDirectSumEquiv_symm_of_tmul (i j : ℕ)
    (p : Fin i → P) (q : Fin j → Q) :
    (ambientDirectSumEquiv R P Q).symm
        (DirectSum.of (Bidegree R P Q) (i, j)
          (exteriorPower.ιMulti R i p ⊗ₜ[R] exteriorPower.ιMulti R j q)) =
      ExteriorAlgebra.ιMulti R (i + j)
        (Fin.append (LinearMap.inl R P Q ∘ p) (LinearMap.inr R P Q ∘ q)) := by
  rw [ambientDirectSumEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_symm]
  simp only [LinearEquiv.trans_apply]
  rw [← DirectSum.lof_eq_of R]
  rw [TensorProduct.directSum_symm_lof_tmul]
  have haux :
      (GradedTensorProduct.auxEquiv R
        (fun a : ℕ ↦ ⋀[R]^a P) (fun b : ℕ ↦ ⋀[R]^b Q)).symm
          (DirectSum.lof R ℕ (fun a : ℕ ↦ ⋀[R]^a P) i
              (exteriorPower.ιMulti R i p) ⊗ₜ[R]
            DirectSum.lof R ℕ (fun b : ℕ ↦ ⋀[R]^b Q) j
              (exteriorPower.ιMulti R j q)) =
        ((exteriorPower.ιMulti R i p : ExteriorAlgebra R P) ᵍ⊗ₜ[R]
          (exteriorPower.ιMulti R j q : ExteriorAlgebra R Q)) := by
    rw [LinearEquiv.symm_apply_eq, GradedTensorProduct.auxEquiv_tmul]
    simp only [DirectSum.decompose_coe, DirectSum.lof_eq_of]
  rw [haux]
  exact ExteriorAlgebra.prodEquivTensor_symm_apply_tmul_ιMulti R P Q i j p q

private theorem ambientDirectSumEquiv_symm_of_tmul' (i j : ℕ)
    (a : ⋀[R]^i P) (b : ⋀[R]^j Q) :
    (ambientDirectSumEquiv R P Q).symm
        (DirectSum.of (Bidegree R P Q) (i, j) (a ⊗ₜ[R] b)) =
      ExteriorAlgebra.map (LinearMap.inl R P Q) a.1 *
        ExteriorAlgebra.map (LinearMap.inr R P Q) b.1 := by
  rw [ambientDirectSumEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_symm]
  simp only [LinearEquiv.trans_apply]
  rw [← DirectSum.lof_eq_of R]
  rw [TensorProduct.directSum_symm_lof_tmul]
  have haux :
      (GradedTensorProduct.auxEquiv R
        (fun d : ℕ ↦ ⋀[R]^d P) (fun d : ℕ ↦ ⋀[R]^d Q)).symm
          (DirectSum.lof R ℕ (fun d : ℕ ↦ ⋀[R]^d P) i a ⊗ₜ[R]
            DirectSum.lof R ℕ (fun d : ℕ ↦ ⋀[R]^d Q) j b) =
        ((a.1 : ExteriorAlgebra R P) ᵍ⊗ₜ[R] (b.1 : ExteriorAlgebra R Q)) := by
    rw [LinearEquiv.symm_apply_eq, GradedTensorProduct.auxEquiv_tmul]
    simp only [DirectSum.decompose_coe, DirectSum.lof_eq_of]
  rw [haux]
  exact ExteriorAlgebra.prodEquivTensor_symm_tmul R P Q a.1 b.1

private theorem ambientDirectSumEquiv_symm_of_mem (i j : ℕ)
    (z : (⋀[R]^i P) ⊗[R] (⋀[R]^j Q)) :
    (ambientDirectSumEquiv R P Q).symm
        (DirectSum.of (Bidegree R P Q) (i, j) z) ∈ ⋀[R]^(i + j) (P × Q) := by
  let L : ((⋀[R]^i P) ⊗[R] (⋀[R]^j Q)) →ₗ[R] ExteriorAlgebra R (P × Q) :=
    (ambientDirectSumEquiv R P Q).symm.toLinearMap.comp
      (DirectSum.lof R (ℕ × ℕ) (Bidegree R P Q) (i, j))
  change L z ∈ ⋀[R]^(i + j) (P × Q)
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa using add_mem hx hy
  | tmul x y =>
      have hx : x ∈ (⊤ : Submodule R (⋀[R]^i P)) := Submodule.mem_top
      have hy : y ∈ (⊤ : Submodule R (⋀[R]^j Q)) := Submodule.mem_top
      rw [← exteriorPower.ιMulti_span R i P] at hx
      rw [← exteriorPower.ιMulti_span R j Q] at hy
      refine Submodule.span_induction₂
        (p := fun a b _ _ ↦ L (a ⊗ₜ[R] b) ∈ ⋀[R]^(i + j) (P × Q))
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
      · rintro a b ⟨p, rfl⟩ ⟨q, rfl⟩
        change (ambientDirectSumEquiv R P Q).symm
          (DirectSum.of (Bidegree R P Q) (i, j)
            (exteriorPower.ιMulti R i p ⊗ₜ[R] exteriorPower.ιMulti R j q)) ∈
              ⋀[R]^(i + j) (P × Q)
        rw [ambientDirectSumEquiv_symm_of_tmul]
        exact (exteriorPower.ιMulti R (i + j)
          (Fin.append (LinearMap.inl R P Q ∘ p) (LinearMap.inr R P Q ∘ q))).2
      · simp
      · simp
      · intro a a' b _ _ _ h h'
        rw [TensorProduct.add_tmul, map_add]
        exact add_mem h h'
      · intro a b b' _ _ _ h h'
        rw [TensorProduct.tmul_add, map_add]
        exact add_mem h h'
      · intro r a b _ _ h
        rw [← TensorProduct.smul_tmul', map_smul]
        exact Submodule.smul_mem _ _ h
      · intro r a b _ _ h
        rw [TensorProduct.tmul_smul, map_smul]
        exact Submodule.smul_mem _ _ h

/-- Keep only the bidegrees whose total degree is `n`. -/
private noncomputable def totalDegreeComponent (n : ℕ) :
    (⨁ ij : ℕ × ℕ, Bidegree R P Q ij) →ₗ[R]
      ⨁ ij : ℕ × ℕ, Bidegree R P Q ij :=
  DirectSum.lmap fun ij ↦
    if ij.1 + ij.2 = n then LinearMap.id else 0

private theorem totalDegreeComponent_of (n : ℕ) (ij : ℕ × ℕ)
    (z : Bidegree R P Q ij) :
    totalDegreeComponent R P Q n (DirectSum.of (Bidegree R P Q) ij z) =
      if ij.1 + ij.2 = n then DirectSum.of (Bidegree R P Q) ij z else 0 := by
  classical
  by_cases h : ij.1 + ij.2 = n <;> simp [totalDegreeComponent, h]

/-- Exterior homogeneous projection corresponds to retaining all bidegrees of the same total
degree in the ambient direct-sum decomposition. -/
private theorem proj_ambientDirectSumEquiv_symm (n : ℕ)
    (y : ⨁ ij : ℕ × ℕ, Bidegree R P Q ij) :
    GradedAlgebra.proj (fun d : ℕ ↦ ⋀[R]^d (P × Q)) n
        ((ambientDirectSumEquiv R P Q).symm y) =
      (ambientDirectSumEquiv R P Q).symm (totalDegreeComponent R P Q n y) := by
  classical
  induction y using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  | of ij z =>
      by_cases h : ij.1 + ij.2 = n
      · simp only [totalDegreeComponent_of, h]
        rw [GradedAlgebra.proj_apply]
        exact DirectSum.decompose_of_mem_same
          (fun d : ℕ ↦ ⋀[R]^d (P × Q))
          (h ▸ ambientDirectSumEquiv_symm_of_mem R P Q ij.1 ij.2 z)
      · simp only [totalDegreeComponent_of, h]
        rw [GradedAlgebra.proj_apply]
        exact DirectSum.decompose_of_mem_ne
          (fun d : ℕ ↦ ⋀[R]^d (P × Q))
          (ambientDirectSumEquiv_symm_of_mem R P Q ij.1 ij.2 z) h

/-- An element of exterior degree `k` has no ambient component in a bidegree of different total
degree. -/
private theorem ambientDirectSumEquiv_apply_eq_zero {k : ℕ}
    (x : ⋀[R]^k (P × Q)) (ij : ℕ × ℕ) (hij : ij.1 + ij.2 ≠ k) :
    ambientDirectSumEquiv R P Q x.1 ij = 0 := by
  classical
  let y := ambientDirectSumEquiv R P Q x.1
  have hproj :
      GradedAlgebra.proj (fun d : ℕ ↦ ⋀[R]^d (P × Q)) (ij.1 + ij.2) x.1 = 0 := by
    rw [GradedAlgebra.proj_apply]
    exact DirectSum.decompose_of_mem_ne
      (fun d : ℕ ↦ ⋀[R]^d (P × Q)) x.2 hij.symm
  have hcomponent : totalDegreeComponent R P Q (ij.1 + ij.2) y = 0 := by
    apply (ambientDirectSumEquiv R P Q).symm.injective
    rw [map_zero, ← proj_ambientDirectSumEquiv_symm]
    simpa [y] using hproj
  have hc := DFunLike.congr_fun hcomponent ij
  change (if ij.1 + ij.2 = ij.1 + ij.2 then LinearMap.id else 0) (y ij) = 0 at hc
  simpa [y] using hc

private abbrev Antidiagonal (k : ℕ) := {ij : ℕ × ℕ // ij.1 + ij.2 = k}

private abbrev AntidiagonalBidegree (k : ℕ) (a : Antidiagonal k) :=
  Bidegree R P Q a.1

/-- Include the direct sum over one antidiagonal into the ambient bidegree direct sum. -/
private noncomputable def antidiagonalIncl (k : ℕ) :
    (⨁ a : Antidiagonal k, AntidiagonalBidegree R P Q k a) →ₗ[R]
      ⨁ ij : ℕ × ℕ, Bidegree R P Q ij :=
  DirectSum.toModule R _ _ fun a ↦
    DirectSum.lof R (ℕ × ℕ) (Bidegree R P Q) a.1

/-- Restrict the ambient bidegree direct sum to one antidiagonal. -/
private noncomputable def antidiagonalProj (k : ℕ) :
    (⨁ ij : ℕ × ℕ, Bidegree R P Q ij) →ₗ[R]
      ⨁ a : Antidiagonal k, AntidiagonalBidegree R P Q k a :=
  DirectSum.toModule R _ _ fun ij ↦
    if h : ij.1 + ij.2 = k then
      DirectSum.lof R (Antidiagonal k) (AntidiagonalBidegree R P Q k) ⟨ij, h⟩
    else 0

private theorem antidiagonalProj_incl (k : ℕ) :
    (antidiagonalProj R P Q k).comp (antidiagonalIncl R P Q k) = LinearMap.id := by
  classical
  apply DirectSum.linearMap_ext
  intro a
  apply LinearMap.ext
  intro z
  simp [antidiagonalIncl, antidiagonalProj, a.2]

private theorem antidiagonalIncl_proj_component (k : ℕ)
    (y : ⨁ ij : ℕ × ℕ, Bidegree R P Q ij) (ij : ℕ × ℕ) :
    antidiagonalIncl R P Q k (antidiagonalProj R P Q k y) ij =
      if ij.1 + ij.2 = k then y ij else 0 := by
  classical
  let lhs : (⨁ ab : ℕ × ℕ, Bidegree R P Q ab) →ₗ[R] Bidegree R P Q ij :=
    (DirectSum.component R (ℕ × ℕ) (Bidegree R P Q) ij).comp
      ((antidiagonalIncl R P Q k).comp (antidiagonalProj R P Q k))
  let rhs : (⨁ ab : ℕ × ℕ, Bidegree R P Q ab) →ₗ[R] Bidegree R P Q ij :=
    if ij.1 + ij.2 = k then
      DirectSum.component R (ℕ × ℕ) (Bidegree R P Q) ij
    else 0
  have heq : lhs = rhs := by
    apply DirectSum.linearMap_ext
    intro ab
    apply LinearMap.ext
    intro z
    by_cases hab : ab.1 + ab.2 = k
    · by_cases h : ab = ij
      · subst ab
        simp [lhs, rhs, antidiagonalIncl, antidiagonalProj, hab]
      · by_cases hij : ij.1 + ij.2 = k <;>
          simp [lhs, rhs, antidiagonalIncl, antidiagonalProj, hab,
            DirectSum.component.of, h, hij]
    · by_cases h : ab = ij
      · subst ab
        simp [lhs, rhs, antidiagonalIncl, antidiagonalProj, hab]
      · by_cases hij : ij.1 + ij.2 = k <;>
          simp [lhs, rhs, antidiagonalIncl, antidiagonalProj, hab,
            DirectSum.component.of, h, hij]
  change (DirectSum.component R (ℕ × ℕ) (Bidegree R P Q) ij)
    (antidiagonalIncl R P Q k (antidiagonalProj R P Q k y)) =
      if ij.1 + ij.2 = k then
        DirectSum.component R (ℕ × ℕ) (Bidegree R P Q) ij y else 0
  have hfun := LinearMap.congr_fun heq y
  by_cases hij : ij.1 + ij.2 = k <;> simpa [lhs, rhs, hij] using hfun

private theorem antidiagonalIncl_proj_eq_of_support (k : ℕ)
    (y : ⨁ ij : ℕ × ℕ, Bidegree R P Q ij)
    (hy : ∀ ij, ij.1 + ij.2 ≠ k → y ij = 0) :
    antidiagonalIncl R P Q k (antidiagonalProj R P Q k y) = y := by
  classical
  apply DirectSum.ext
  intro ij
  rw [antidiagonalIncl_proj_component]
  by_cases h : ij.1 + ij.2 = k
  · simp [h]
  · simp [h, hy ij h]

private theorem ambientDirectSumEquiv_symm_antidiagonalIncl_mem (k : ℕ)
    (z : ⨁ a : Antidiagonal k, AntidiagonalBidegree R P Q k a) :
    (ambientDirectSumEquiv R P Q).symm (antidiagonalIncl R P Q k z) ∈
      ⋀[R]^k (P × Q) := by
  classical
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simpa using add_mem hx hy
  | of a z =>
      rw [← DirectSum.lof_eq_of R]
      simp only [antidiagonalIncl, DirectSum.toModule_lof]
      have hm := ambientDirectSumEquiv_symm_of_mem R P Q a.1.1 a.1.2 z
      rw [a.2] at hm
      exact hm

private noncomputable def fixedDegreeForward (k : ℕ) :
    (⋀[R]^k (P × Q)) →ₗ[R]
      ⨁ a : Antidiagonal k, AntidiagonalBidegree R P Q k a :=
  (antidiagonalProj R P Q k).comp
    ((ambientDirectSumEquiv R P Q).toLinearMap.comp (⋀[R]^k (P × Q)).subtype)

private noncomputable def fixedDegreeInverse (k : ℕ) :
    (⨁ a : Antidiagonal k, AntidiagonalBidegree R P Q k a) →ₗ[R]
      ⋀[R]^k (P × Q) :=
  ((ambientDirectSumEquiv R P Q).symm.toLinearMap.comp
    (antidiagonalIncl R P Q k)).codRestrict (⋀[R]^k (P × Q))
      (ambientDirectSumEquiv_symm_antidiagonalIncl_mem R P Q k)

/-- The fixed-degree part of the ambient exterior-algebra decomposition, indexed by pairs whose
sum is the chosen degree. -/
private noncomputable def fixedDegreeAntidiagonalEquiv (k : ℕ) :
    (⋀[R]^k (P × Q)) ≃ₗ[R]
      ⨁ a : Antidiagonal k, AntidiagonalBidegree R P Q k a :=
  LinearEquiv.ofLinearMap (fixedDegreeForward R P Q k) (fixedDegreeInverse R P Q k)
    (by
      apply LinearMap.ext
      intro z
      dsimp [fixedDegreeForward, fixedDegreeInverse]
      change antidiagonalProj R P Q k
        (ambientDirectSumEquiv R P Q
          ((ambientDirectSumEquiv R P Q).symm (antidiagonalIncl R P Q k z))) = z
      rw [LinearEquiv.apply_symm_apply]
      exact LinearMap.congr_fun (antidiagonalProj_incl R P Q k) z)
    (by
      apply LinearMap.ext
      intro x
      dsimp [fixedDegreeForward, fixedDegreeInverse]
      apply Subtype.ext
      change (ambientDirectSumEquiv R P Q).symm
        (antidiagonalIncl R P Q k
          (antidiagonalProj R P Q k (ambientDirectSumEquiv R P Q x.1))) = x.1
      rw [antidiagonalIncl_proj_eq_of_support R P Q k _
        (fun ij hij ↦ ambientDirectSumEquiv_apply_eq_zero R P Q x ij hij)]
      exact (ambientDirectSumEquiv R P Q).symm_apply_apply x.1)

private theorem coe_fixedDegreeAntidiagonalEquiv_symm_of (k : ℕ)
    (a : Antidiagonal k) (z : AntidiagonalBidegree R P Q k a) :
    ((fixedDegreeAntidiagonalEquiv R P Q k).symm
        (DirectSum.of (AntidiagonalBidegree R P Q k) a z) : ExteriorAlgebra R (P × Q)) =
      (ambientDirectSumEquiv R P Q).symm
        (DirectSum.of (Bidegree R P Q) a.1 z) := by
  rw [fixedDegreeAntidiagonalEquiv]
  change (ambientDirectSumEquiv R P Q).symm
    (antidiagonalIncl R P Q k (DirectSum.of (AntidiagonalBidegree R P Q k) a z)) = _
  congr 1
  change (DirectSum.toModule R (Antidiagonal k)
      (⨁ ij : ℕ × ℕ, Bidegree R P Q ij)
      (fun a ↦ DirectSum.lof R (ℕ × ℕ) (Bidegree R P Q) a.1))
        (DirectSum.lof R (Antidiagonal k) (AntidiagonalBidegree R P Q k) a z) =
      DirectSum.lof R (ℕ × ℕ) (Bidegree R P Q) a.1 z
  rw [DirectSum.toModule_lof]

/-- The natural bijection between `Fin (k + 1)` and pairs of natural numbers with sum `k`. -/
private abbrev finEquivAntidiagonal (k : ℕ) : Fin (k + 1) ≃ Antidiagonal k where
  toFun i := ⟨(i, k - i), Nat.add_sub_of_le (Nat.lt_succ_iff.mp i.2)⟩
  invFun a := ⟨a.1.1, by omega⟩
  left_inv i := Fin.ext rfl
  right_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change k - a.1.1 = a.1.2
      omega

private noncomputable def antidiagonalFinEquiv (k : ℕ) :
    (⨁ a : Antidiagonal k, AntidiagonalBidegree R P Q k a) ≃ₗ[R]
      ⨁ i : Fin (k + 1), (⋀[R]^i.1 P) ⊗[R] (⋀[R]^(k - i.1) Q) :=
  DirectSum.lequivCongrLeft R (finEquivAntidiagonal k).symm

private theorem antidiagonalFinEquiv_symm_of (k : ℕ) (i : Fin (k + 1))
    (z : (⋀[R]^i.1 P) ⊗[R] (⋀[R]^(k - i.1) Q)) :
    (antidiagonalFinEquiv R P Q k).symm
        (DirectSum.of
          (fun j : Fin (k + 1) ↦ (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(k - j.1) Q)) i z) =
      DirectSum.of (AntidiagonalBidegree R P Q k)
        ⟨(i.1, k - i.1), Nat.add_sub_of_le (Nat.lt_succ_iff.mp i.2)⟩ z := by
  rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R]
  rw [antidiagonalFinEquiv]
  convert (DirectSum.lequivCongrLeft_symm_lof
      (R := R) (M := AntidiagonalBidegree R P Q k)
      (h := (finEquivAntidiagonal k).symm) (k := i) (x := z)) using 1 <;>
    simp [finEquivAntidiagonal]

/-- The degree-`k` exterior power of a binary direct sum is the direct sum of the tensor products
of exterior powers whose degrees add to `k`.

The inverse uses the ordered convention: the `P` block is wedged before the `Q` block. No
finiteness, projectivity, flatness, or nontriviality assumption is needed. -/
@[no_expose]
noncomputable def prodEquivDirectSum (k : ℕ) :
    (⋀[R]^k (P × Q)) ≃ₗ[R]
      ⨁ i : Fin (k + 1), (⋀[R]^i.1 P) ⊗[R] (⋀[R]^(k - i.1) Q) :=
  fixedDegreeAntidiagonalEquiv R P Q k ≪≫ₗ antidiagonalFinEquiv R P Q k

/-- The inverse of `prodEquivDirectSum` sends a pure tensor in the `i`th summand to exterior
multiplication after the two canonical inclusions, with the `P` factor first. -/
@[simp]
theorem coe_prodEquivDirectSum_symm_of_tmul (k : ℕ) (i : Fin (k + 1))
    (a : ⋀[R]^i.1 P) (b : ⋀[R]^(k - i.1) Q) :
    ((prodEquivDirectSum R P Q k).symm
        (DirectSum.of
          (fun j : Fin (k + 1) ↦ (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(k - j.1) Q)) i
          (a ⊗ₜ[R] b)) : ExteriorAlgebra R (P × Q)) =
      ExteriorAlgebra.map (LinearMap.inl R P Q) a.1 *
        ExteriorAlgebra.map (LinearMap.inr R P Q) b.1 := by
  rw [prodEquivDirectSum, LinearEquiv.trans_symm]
  simp only [LinearEquiv.trans_apply]
  rw [antidiagonalFinEquiv_symm_of]
  rw [coe_fixedDegreeAntidiagonalEquiv_symm_of]
  exact ambientDirectSumEquiv_symm_of_tmul' R P Q i.1 (k - i.1) a b

/-- On pure exterior products, the inverse concatenates the `P` entries and then the `Q`
entries. The right side is written in the full exterior algebra, avoiding any index casts. -/
theorem coe_prodEquivDirectSum_symm_of_tmul_ιMulti (k : ℕ) (i : Fin (k + 1))
    (p : Fin i.1 → P) (q : Fin (k - i.1) → Q) :
    ((prodEquivDirectSum R P Q k).symm
        (DirectSum.of
          (fun j : Fin (k + 1) ↦ (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(k - j.1) Q)) i
          (exteriorPower.ιMulti R i.1 p ⊗ₜ[R]
            exteriorPower.ιMulti R (k - i.1) q)) : ExteriorAlgebra R (P × Q)) =
      ExteriorAlgebra.ιMulti R (i.1 + (k - i.1))
        (Fin.append (LinearMap.inl R P Q ∘ p) (LinearMap.inr R P Q ∘ q)) := by
  rw [coe_prodEquivDirectSum_symm_of_tmul]
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti]
  exact ExteriorAlgebra.ιMulti_mul_ιMulti _ _

universe v' w'

variable {P' : Type v'} {Q' : Type w'}
variable [AddCommGroup P'] [Module R P'] [AddCommGroup Q'] [Module R Q']

/-- The summandwise map on the direct-sum side induced by a pair of linear maps. -/
noncomputable def prodDirectSumMap (k : ℕ) (f : P →ₗ[R] P') (g : Q →ₗ[R] Q') :
    (⨁ i : Fin (k + 1), (⋀[R]^i.1 P) ⊗[R] (⋀[R]^(k - i.1) Q)) →ₗ[R]
      ⨁ i : Fin (k + 1), (⋀[R]^i.1 P') ⊗[R] (⋀[R]^(k - i.1) Q') :=
  DirectSum.lmap fun i ↦
    TensorProduct.map (exteriorPower.map i.1 f) (exteriorPower.map (k - i.1) g)

/-- Naturality of the inverse fixed-degree decomposition for arbitrary module maps over `R`. -/
theorem prodEquivDirectSum_symm_naturality (k : ℕ)
    (f : P →ₗ[R] P') (g : Q →ₗ[R] Q') :
    (exteriorPower.map k (f.prodMap g)).comp
        (prodEquivDirectSum R P Q k).symm.toLinearMap =
      (prodEquivDirectSum R P' Q' k).symm.toLinearMap.comp
        (prodDirectSumMap R P Q k f g) := by
  apply DirectSum.linearMap_ext
  intro i
  apply TensorProduct.ext'
  intro a b
  apply Subtype.ext
  simp only [LinearMap.comp_apply, exteriorPower.coe_map]
  rw [DirectSum.lof_eq_of]
  change ExteriorAlgebra.map (f.prodMap g)
      ((prodEquivDirectSum R P Q k).symm
        (DirectSum.of
          (fun j : Fin (k + 1) ↦ (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(k - j.1) Q)) i
          (a ⊗ₜ[R] b))).1 =
    ((prodEquivDirectSum R P' Q' k).symm
      (prodDirectSumMap R P Q k f g
        (DirectSum.of
          (fun j : Fin (k + 1) ↦ (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(k - j.1) Q)) i
          (a ⊗ₜ[R] b)))).1
  rw [coe_prodEquivDirectSum_symm_of_tmul]
  simp only [map_mul]
  rw [prodDirectSumMap, DirectSum.lmap_of, TensorProduct.map_tmul]
  rw [coe_prodEquivDirectSum_symm_of_tmul]
  simp only [exteriorPower.coe_map]
  congr 1
  · rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    rw [show (f.prodMap g).comp (LinearMap.inl R P Q) =
        (LinearMap.inl R P' Q').comp f by
          apply LinearMap.ext
          intro x
          simp]
    rw [← ExteriorAlgebra.map_comp_map]
    rfl
  · rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    rw [show (f.prodMap g).comp (LinearMap.inr R P Q) =
        (LinearMap.inr R P' Q').comp g by
          apply LinearMap.ext
          intro x
          simp]
    rw [← ExteriorAlgebra.map_comp_map]
    rfl

/-- Naturality of `prodEquivDirectSum` for arbitrary module maps over the fixed base ring. -/
theorem prodEquivDirectSum_naturality (k : ℕ)
    (f : P →ₗ[R] P') (g : Q →ₗ[R] Q') :
    (prodEquivDirectSum R P' Q' k).toLinearMap.comp
        (exteriorPower.map k (f.prodMap g)) =
      (prodDirectSumMap R P Q k f g).comp
        (prodEquivDirectSum R P Q k).toLinearMap := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (prodEquivDirectSum_symm_naturality R P Q k f g)
    (prodEquivDirectSum R P Q k x)
  have hinv :
      exteriorPower.map k (f.prodMap g) x =
        (prodEquivDirectSum R P' Q' k).symm
          (prodDirectSumMap R P Q k f g (prodEquivDirectSum R P Q k x)) := by
    simp only [LinearMap.comp_apply] at h
    change exteriorPower.map k (f.prodMap g)
        ((prodEquivDirectSum R P Q k).symm (prodEquivDirectSum R P Q k x)) =
      (prodEquivDirectSum R P' Q' k).symm
        (prodDirectSumMap R P Q k f g (prodEquivDirectSum R P Q k x)) at h
    rw [LinearEquiv.symm_apply_apply] at h
    exact h
  change prodEquivDirectSum R P' Q' k (exteriorPower.map k (f.prodMap g) x) =
    prodDirectSumMap R P Q k f g (prodEquivDirectSum R P Q k x)
  rw [hinv, LinearEquiv.apply_symm_apply]

/-- The bidegree `(p, q)` component of the exterior power of a binary product.
It is the homogeneous projection of `prodEquivDirectSum`, with the canonical
indexed cast from the right degree `(p + q) - p` to `q`. -/
noncomputable def prodComponent (p q : ℕ) :
    (⋀[R]^(p + q) (P × Q)) →ₗ[R] (⋀[R]^p P) ⊗[R] (⋀[R]^q Q) :=
  (LinearEquiv.cast (R := R)
      (M := fun d : ℕ ↦ (⋀[R]^p P) ⊗[R] (⋀[R]^d Q))
      (Nat.add_sub_cancel_left p q)).toLinearMap ∘ₗ
    DirectSum.component R (Fin (p + q + 1))
      (fun i ↦ (⋀[R]^i.1 P) ⊗[R] (⋀[R]^(p + q - i.1) Q))
      ⟨p, Nat.lt_succ_of_le (Nat.le_add_right p q)⟩ ∘ₗ
    (prodEquivDirectSum R P Q (p + q)).toLinearMap

private theorem sumEquiv_eq_sum_map {α β γ δ : Type*} (e : α ⊕ β ≃ γ ⊕ δ)
    (hl : ∀ x, ∃ y, e (Sum.inl x) = Sum.inl y)
    (hr : ∀ x, ∃ y, e (Sum.inr x) = Sum.inr y) :
    ∃ (f : α → γ) (g : β → δ), Function.Bijective f ∧ Function.Bijective g ∧
      (e : α ⊕ β → γ ⊕ δ) = Sum.map f g := by
  classical
  choose f hf using hl
  choose g hg using hr
  have he : (e : α ⊕ β → γ ⊕ δ) = Sum.map f g := by
    funext z
    cases z with
    | inl x => exact hf x
    | inr x => exact hg x
  have hb : Function.Bijective (Sum.map f g) := by
    rw [← he]
    exact e.bijective
  exact ⟨f, g, (Sum.map_bijective.mp hb).1, (Sum.map_bijective.mp hb).2, he⟩

/-- A nonzero projected coshuffle summand cannot move an entry across the two pure blocks. -/
private theorem prodComponent_summand_ne_zero_blocks (p q a b : ℕ)
    (x : Fin a → P) (y : Fin b → Q)
    (e : Fin p ⊕ Fin q ≃ Fin a ⊕ Fin b)
    (σ : Equiv.Perm (Fin p ⊕ Fin q))
    (h : AlternatingMap.domCoprod.summand
      ((ιMulti R p).compLinearMap (LinearMap.fst R P Q))
      ((ιMulti R q).compLinearMap (LinearMap.snd R P Q)) (Quotient.mk'' σ)
      (Sum.elim (LinearMap.inl R P Q ∘ x) (LinearMap.inr R P Q ∘ y) ∘ e) ≠ 0) :
    (∀ k, ∃ l, e (σ (Sum.inl k)) = Sum.inl l) ∧
      (∀ k, ∃ l, e (σ (Sum.inr k)) = Sum.inr l) := by
  classical
  simp only [AlternatingMap.domCoprod.summand_mk'', _root_.smul_apply,
    MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    AlternatingMap.coe_multilinearMap, AlternatingMap.compLinearMap_apply,
    Function.comp_apply] at h
  constructor
  · intro k
    cases he : e (σ (Sum.inl k)) with
    | inl l => exact ⟨l, rfl⟩
    | inr l =>
        exfalso
        apply h
        have hz : ιMulti R p (fun j ↦ LinearMap.fst R P Q
            (Sum.elim (LinearMap.inl R P Q ∘ x) (LinearMap.inr R P Q ∘ y)
              (e (σ (Sum.inl j))))) = 0 :=
          (ιMulti R p).map_coord_zero k (by simp [he])
        simp only [hz, TensorProduct.zero_tmul, smul_zero]
  · intro k
    cases he : e (σ (Sum.inr k)) with
    | inr l => exact ⟨l, rfl⟩
    | inl l =>
        exfalso
        apply h
        have hz : ιMulti R q (fun j ↦ LinearMap.snd R P Q
            (Sum.elim (LinearMap.inl R P Q ∘ x) (LinearMap.inr R P Q ∘ y)
              (e (σ (Sum.inr j))))) = 0 :=
          (ιMulti R q).map_coord_zero k (by simp [he])
        simp only [hz, TensorProduct.tmul_zero, smul_zero]

/-- Every coshuffle summand vanishes when the size of the left pure block is wrong. -/
private theorem prodComponent_domCoprod_eq_zero (p q a b : ℕ) (ha : a ≠ p)
    (x : Fin a → P) (y : Fin b → Q)
    (e : Fin p ⊕ Fin q ≃ Fin a ⊕ Fin b) :
    (((ιMulti R p).compLinearMap (LinearMap.fst R P Q)).domCoprod
      ((ιMulti R q).compLinearMap (LinearMap.snd R P Q)))
      (Sum.elim (LinearMap.inl R P Q ∘ x) (LinearMap.inr R P Q ∘ y) ∘ e) = 0 := by
  classical
  simp only [AlternatingMap.domCoprod_apply, _root_.sum_apply]
  apply Finset.sum_eq_zero
  intro s _
  refine Quotient.inductionOn' s (fun σ ↦ ?_)
  by_contra hs
  have hb := prodComponent_summand_ne_zero_blocks R P Q p q a b x y e σ hs
  obtain ⟨f, _, hf, _, _⟩ := sumEquiv_eq_sum_map (σ.trans e) hb.1 hb.2
  have hc : p = a := by simpa using Fintype.card_of_bijective hf
  exact ha hc.symm

/-- For matching pure blocks, only the identity coset contributes, with coefficient one. -/
private theorem prodComponent_domCoprod_blocks (p q : ℕ)
    (x : Fin p → P) (y : Fin q → Q) :
    (((ιMulti R p).compLinearMap (LinearMap.fst R P Q)).domCoprod
      ((ιMulti R q).compLinearMap (LinearMap.snd R P Q)))
      (Sum.elim (LinearMap.inl R P Q ∘ x) (LinearMap.inr R P Q ∘ y)) =
      ιMulti R p x ⊗ₜ[R] ιMulti R q y := by
  classical
  let s₀ : Equiv.Perm.ModSumCongr (Fin p) (Fin q) :=
    Quotient.mk'' (1 : Equiv.Perm (Fin p ⊕ Fin q))
  have hzero : ∀ s : Equiv.Perm.ModSumCongr (Fin p) (Fin q), s ≠ s₀ →
      AlternatingMap.domCoprod.summand
        ((ιMulti R p).compLinearMap (LinearMap.fst R P Q))
        ((ιMulti R q).compLinearMap (LinearMap.snd R P Q)) s
        (Sum.elim (LinearMap.inl R P Q ∘ x) (LinearMap.inr R P Q ∘ y)) = 0 := by
    intro s
    refine Quotient.inductionOn' s (fun σ hσ ↦ ?_)
    by_contra hs
    have hb := prodComponent_summand_ne_zero_blocks R P Q p q p q x y
      (Equiv.refl _) σ hs
    obtain ⟨f, g, hf, hg, he⟩ := sumEquiv_eq_sum_map σ hb.1 hb.2
    have hm : σ ∈ (Equiv.Perm.sumCongrHom (Fin p) (Fin q)).range := by
      refine ⟨(Equiv.ofBijective f hf, Equiv.ofBijective g hg), ?_⟩
      apply Equiv.ext
      intro z
      exact (congrFun he z).symm
    have hc : (Quotient.mk'' (1 : Equiv.Perm (Fin p ⊕ Fin q)) :
        Equiv.Perm.ModSumCongr (Fin p) (Fin q)) = Quotient.mk'' σ :=
      QuotientGroup.eq.mpr (by simpa using hm)
    exact hσ hc.symm
  simp only [AlternatingMap.domCoprod_apply, _root_.sum_apply]
  rw [Finset.sum_eq_single s₀ (fun s _ hs ↦ hzero s hs) (by simp)]
  simp [s₀, AlternatingMap.domCoprod.summand_mk'',
    MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    AlternatingMap.compLinearMap_apply, Function.comp_def]

private theorem prodComponent_domCoprod_append_cast (p q b : ℕ) (h : b = q)
    (x : Fin p → P) (y : Fin b → Q) :
    (((ιMulti R p).compLinearMap (LinearMap.fst R P Q)).domCoprod
      ((ιMulti R q).compLinearMap (LinearMap.snd R P Q)))
      ((Fin.append (LinearMap.inl R P Q ∘ x) (LinearMap.inr R P Q ∘ y) ∘
        Equiv.cast (congrArg Fin (congrArg (fun d ↦ p + d) h).symm)) ∘
          finSumFinEquiv) =
      LinearEquiv.cast (R := R)
        (M := fun d : ℕ ↦ (⋀[R]^p P) ⊗[R] (⋀[R]^d Q)) h
        (ιMulti R p x ⊗ₜ[R] ιMulti R b y) := by
  subst b
  change (((ιMulti R p).compLinearMap (LinearMap.fst R P Q)).domCoprod
    ((ιMulti R q).compLinearMap (LinearMap.snd R P Q)))
      (Fin.append (LinearMap.inl R P Q ∘ x) (LinearMap.inr R P Q ∘ y) ∘
        finSumFinEquiv) = ιMulti R p x ⊗ₜ[R] ιMulti R q y
  have happend : Fin.append (LinearMap.inl R P Q ∘ x) (LinearMap.inr R P Q ∘ y) ∘
      (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)) =
      Sum.elim (LinearMap.inl R P Q ∘ x) (LinearMap.inr R P Q ∘ y) :=
    Fin.append_comp_sumElim
  rw [happend]
  exact prodComponent_domCoprod_blocks R P Q p q x y

private theorem prodComponent_ιMulti_coe_reindex {X : Type*}
    [AddCommGroup X] [Module R X] {a b : ℕ} (h : a = b) (x : Fin a → X) :
    (ιMulti R a x : ExteriorAlgebra R X) =
      (ιMulti R b (x ∘ Equiv.cast (congrArg Fin h.symm)) : ExteriorAlgebra R X) := by
  cases h
  rfl

/-- The Cauchy component of a generating wedge is the exterior product of the two projected
universal alternating maps. The signed sum is indexed by coshuffles, so each shuffle occurs
once, without factorial coefficients. -/
@[simp]
theorem prodComponent_ιMulti (p q : ℕ) (v : Fin (p + q) → P × Q) :
    prodComponent R P Q p q (ιMulti R (p + q) v) =
      (((ιMulti R p).compLinearMap (LinearMap.fst R P Q)).domCoprod
        ((ιMulti R q).compLinearMap (LinearMap.snd R P Q)))
        (v ∘ finSumFinEquiv) := by
  classical
  let e := prodEquivDirectSum R P Q (p + q)
  let A := ((ιMulti R p).compLinearMap (LinearMap.fst R P Q)).domCoprod
    ((ιMulti R q).compLinearMap (LinearMap.snd R P Q))
  let T : (⋀[R]^(p + q) (P × Q)) →ₗ[R] (⋀[R]^p P) ⊗[R] (⋀[R]^q Q) :=
    alternatingMapLinearEquiv (R := R) (M := P × Q) (n := p + q)
      (N := (⋀[R]^p P) ⊗[R] (⋀[R]^q Q))
      (AlternatingMap.domDomCongr finSumFinEquiv A)
  let c : (⨁ i : Fin (p + q + 1),
      (⋀[R]^i.1 P) ⊗[R] (⋀[R]^(p + q - i.1) Q)) →ₗ[R]
      (⋀[R]^p P) ⊗[R] (⋀[R]^q Q) :=
    (LinearEquiv.cast (R := R)
      (M := fun d : ℕ ↦ (⋀[R]^p P) ⊗[R] (⋀[R]^d Q))
      (Nat.add_sub_cancel_left p q)).toLinearMap ∘ₗ
      DirectSum.component R (Fin (p + q + 1))
        (fun i ↦ (⋀[R]^i.1 P) ⊗[R] (⋀[R]^(p + q - i.1) Q))
        ⟨p, Nat.lt_succ_of_le (Nat.le_add_right p q)⟩
  have hT : T.comp e.symm.toLinearMap = c := by
    apply DirectSum.linearMap_ext
    intro i
    apply TensorProduct.curry_injective (σ₁₂ := RingHom.id R)
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _ (ιMulti_span R i.1 P)]
    rintro ⟨_, x, rfl⟩
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _
      (ιMulti_span R (p + q - i.1) Q)]
    rintro ⟨_, y, rfl⟩
    simp only [TensorProduct.curry_apply, LinearMap.comp_apply]
    let h : i.1 + (p + q - i.1) = p + q :=
      Nat.add_sub_of_le (Nat.lt_succ_iff.mp i.2)
    let w := Fin.append (LinearMap.inl R P Q ∘ x) (LinearMap.inr R P Q ∘ y)
    have hinv : e.symm
        (DirectSum.lof R (Fin (p + q + 1))
          (fun j ↦ (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(p + q - j.1) Q)) i
          (ιMulti R i.1 x ⊗ₜ[R] ιMulti R (p + q - i.1) y)) =
        ιMulti R (p + q) (w ∘ Equiv.cast (congrArg Fin h.symm)) := by
      apply Subtype.ext
      rw [DirectSum.lof_eq_of]
      exact (coe_prodEquivDirectSum_symm_of_tmul_ιMulti R P Q (p + q) i x y).trans
        (prodComponent_ιMulti_coe_reindex R h w)
    change T (e.symm
      (DirectSum.lof R (Fin (p + q + 1))
        (fun j ↦ (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(p + q - j.1) Q)) i
        (ιMulti R i.1 x ⊗ₜ[R] ιMulti R (p + q - i.1) y))) =
      LinearEquiv.cast (R := R)
        (M := fun d : ℕ ↦ (⋀[R]^p P) ⊗[R] (⋀[R]^d Q))
        (Nat.add_sub_cancel_left p q)
        (DirectSum.component R (Fin (p + q + 1))
          (fun j ↦ (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(p + q - j.1) Q))
          ⟨p, Nat.lt_succ_of_le (Nat.le_add_right p q)⟩
          (DirectSum.lof R (Fin (p + q + 1))
            (fun j ↦ (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(p + q - j.1) Q)) i
            (ιMulti R i.1 x ⊗ₜ[R] ιMulti R (p + q - i.1) y)))
    rw [hinv]
    simp only [T, alternatingMapLinearEquiv_apply_ιMulti,
      AlternatingMap.domDomCongr_apply]
    by_cases hi : i.1 = p
    · have hie : i = ⟨p, Nat.lt_succ_of_le (Nat.le_add_right p q)⟩ := Fin.ext hi
      subst i
      rw [DirectSum.component.lof_self]
      exact prodComponent_domCoprod_append_cast R P Q p q (p + q - p)
        (Nat.add_sub_cancel_left p q) x y
    · have hie : i ≠ ⟨p, Nat.lt_succ_of_le (Nat.le_add_right p q)⟩ := by
        intro he
        exact hi (congrArg Fin.val he)
      rw [DirectSum.component.of, dite_eq_right hie, map_zero]
      let e' : Fin p ⊕ Fin q ≃ Fin i.1 ⊕ Fin (p + q - i.1) :=
        finSumFinEquiv.trans
          ((Equiv.cast (congrArg Fin h.symm)).trans finSumFinEquiv.symm)
      have hw : (w ∘ Equiv.cast (congrArg Fin h.symm)) ∘ finSumFinEquiv =
          Sum.elim (LinearMap.inl R P Q ∘ x) (LinearMap.inr R P Q ∘ y) ∘ e' := by
        have happend : w ∘ (finSumFinEquiv :
            Fin i.1 ⊕ Fin (p + q - i.1) ≃ Fin (i.1 + (p + q - i.1))) =
            Sum.elim (LinearMap.inl R P Q ∘ x) (LinearMap.inr R P Q ∘ y) :=
          Fin.append_comp_sumElim
        funext z
        simpa only [e', Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply] using
          congrFun happend (finSumFinEquiv.symm
            (Equiv.cast (congrArg Fin h.symm) (finSumFinEquiv z)))
      rw [hw]
      exact prodComponent_domCoprod_eq_zero R P Q p q i.1 (p + q - i.1) hi x y e'
  have hv := LinearMap.congr_fun hT (e (ιMulti R (p + q) v))
  change c (e (ιMulti R (p + q) v)) = A (v ∘ finSumFinEquiv)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    T, alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.domDomCongr_apply] using hv.symm

private theorem prodComponent_tensor_map_cast (p : ℕ) {a b : ℕ} (h : a = b)
    (f : P →ₗ[R] P') (g : Q →ₗ[R] Q')
    (x : (⋀[R]^p P) ⊗[R] (⋀[R]^a Q)) :
    TensorProduct.map (map p f) (map b g)
        (LinearEquiv.cast (R := R)
          (M := fun d : ℕ ↦ (⋀[R]^p P) ⊗[R] (⋀[R]^d Q)) h x) =
      LinearEquiv.cast (R := R)
        (M := fun d : ℕ ↦ (⋀[R]^p P') ⊗[R] (⋀[R]^d Q')) h
        (TensorProduct.map (map p f) (map a g) x) := by
  cases h
  rfl

/-- The homogeneous product component is natural in both module arguments. -/
theorem prodComponent_naturality (p q : ℕ)
    (f : P →ₗ[R] P') (g : Q →ₗ[R] Q') :
    TensorProduct.map (map p f) (map q g) ∘ₗ prodComponent R P Q p q =
      prodComponent R P' Q' p q ∘ₗ map (p + q) (f.prodMap g) := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun
    (prodEquivDirectSum_naturality R P Q (p + q) f g) x
  change prodEquivDirectSum R P' Q' (p + q) (map (p + q) (f.prodMap g) x) =
    prodDirectSumMap R P Q (p + q) f g (prodEquivDirectSum R P Q (p + q) x) at h
  change TensorProduct.map (map p f) (map q g)
      (LinearEquiv.cast (R := R)
        (M := fun d : ℕ ↦ (⋀[R]^p P) ⊗[R] (⋀[R]^d Q))
        (Nat.add_sub_cancel_left p q)
        (prodEquivDirectSum R P Q (p + q) x
          ⟨p, Nat.lt_succ_of_le (Nat.le_add_right p q)⟩)) =
    LinearEquiv.cast (R := R)
      (M := fun d : ℕ ↦ (⋀[R]^p P') ⊗[R] (⋀[R]^d Q'))
      (Nat.add_sub_cancel_left p q)
      (prodEquivDirectSum R P' Q' (p + q) (map (p + q) (f.prodMap g) x)
        ⟨p, Nat.lt_succ_of_le (Nat.le_add_right p q)⟩)
  simp only [prodComponent_tensor_map_cast, h, prodDirectSumMap, DirectSum.lmap_apply]

/-- Applying the homogeneous product component after a product map applies the
induced exterior-power maps to its two tensor factors. -/
@[simp]
theorem prodComponent_map (p q : ℕ) (f : P →ₗ[R] P') (g : Q →ₗ[R] Q')
    (x : ⋀[R]^(p + q) (P × Q)) :
    prodComponent R P' Q' p q (map (p + q) (f.prodMap g) x) =
      TensorProduct.map (map p f) (map q g) (prodComponent R P Q p q x) := by
  exact (LinearMap.congr_fun (prodComponent_naturality R P Q p q f g) x).symm

/-- On the inverse Cauchy decomposition, the homogeneous product component is the
selected direct-sum component with its canonical right-degree transport. -/
@[simp]
theorem prodComponent_symm_apply (p q : ℕ)
    (x : ⨁ i : Fin (p + q + 1), (⋀[R]^i.1 P) ⊗[R] (⋀[R]^(p + q - i.1) Q)) :
    prodComponent R P Q p q ((prodEquivDirectSum R P Q (p + q)).symm x) =
      LinearEquiv.cast (R := R)
        (M := fun d : ℕ ↦ (⋀[R]^p P) ⊗[R] (⋀[R]^d Q))
        (Nat.add_sub_cancel_left p q)
        (x ⟨p, Nat.lt_succ_of_le (Nat.le_add_right p q)⟩) := by
  simp only [prodComponent, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, ← DirectSum.apply_eq_component]

/-- The indexed linear cast between equal exterior degrees preserves the image in the
exterior algebra. -/
theorem coe_cast {a b : ℕ} (h : a = b) (x : ⋀[R]^a P) :
    (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d P) h x :
      ExteriorAlgebra R P) = x.1 := by
  cases h
  rfl

/-- Transporting the right exterior degree of a pure tensor transports only its right factor. -/
theorem tensor_cast_tmul (p : ℕ) {a b : ℕ} (h : a = b)
    (x : ⋀[R]^p P) (y : ⋀[R]^a Q) :
    LinearEquiv.cast (R := R)
        (M := fun d : ℕ ↦ (⋀[R]^p P) ⊗[R] (⋀[R]^d Q)) h (x ⊗ₜ[R] y) =
      x ⊗ₜ[R] LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d Q) h y := by
  cases h
  rfl

/-- Linear maps out of an exterior power of a binary product agree if they agree on
pure tensors in every summand of the inverse Cauchy decomposition. -/
theorem prodEquivDirectSum_ext {T : Type*} [AddCommMonoid T] [Module R T]
    (n : ℕ) {F G : (⋀[R]^n (P × Q)) →ₗ[R] T}
    (h : ∀ (i : Fin (n + 1)) (a : ⋀[R]^i.1 P) (b : ⋀[R]^(n - i.1) Q),
      F ((prodEquivDirectSum R P Q n).symm
        (DirectSum.of (fun j : Fin (n + 1) ↦
          (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(n - j.1) Q)) i (a ⊗ₜ[R] b))) =
      G ((prodEquivDirectSum R P Q n).symm
        (DirectSum.of (fun j : Fin (n + 1) ↦
          (⋀[R]^j.1 P) ⊗[R] (⋀[R]^(n - j.1) Q)) i (a ⊗ₜ[R] b)))) :
    F = G := by
  have heq : F ∘ₗ (prodEquivDirectSum R P Q n).symm.toLinearMap =
      G ∘ₗ (prodEquivDirectSum R P Q n).symm.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro i
    apply TensorProduct.ext'
    intro a b
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      DirectSum.lof_eq_of] using h i a b
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (prodEquivDirectSum R P Q n).symm.surjective x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using
    LinearMap.congr_fun heq y

private theorem exists_prod_coe_eq_mul (n i j : ℕ) (h : i + j = n)
    (a : ⋀[R]^i P) (b : ⋀[R]^j Q) :
    ∃ x : ⋀[R]^n (P × Q), x.1 =
      ExteriorAlgebra.map (LinearMap.inl R P Q) a.1 *
        ExteriorAlgebra.map (LinearMap.inr R P Q) b.1 := by
  have hi : i < n + 1 := by omega
  have hj : j = n - i := by omega
  let b' := LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d Q) hj b
  refine ⟨(prodEquivDirectSum R P Q n).symm
    (DirectSum.of (fun k : Fin (n + 1) ↦
      (⋀[R]^k.1 P) ⊗[R] (⋀[R]^(n - k.1) Q)) ⟨i, hi⟩ (a ⊗ₜ[R] b')), ?_⟩
  rw [coe_prodEquivDirectSum_symm_of_tmul]
  simp only [b', coe_cast]

private theorem prodComponent_of_coe_eq_mul (p q : ℕ)
    (a : ⋀[R]^p P) (b : ⋀[R]^q Q) (x : ⋀[R]^(p + q) (P × Q))
    (hx : x.1 = ExteriorAlgebra.map (LinearMap.inl R P Q) a.1 *
      ExteriorAlgebra.map (LinearMap.inr R P Q) b.1) :
    prodComponent R P Q p q x = a ⊗ₜ[R] b := by
  let b' := LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d Q)
    (Nat.add_sub_cancel_left p q).symm b
  have heq : x = (prodEquivDirectSum R P Q (p + q)).symm
      (DirectSum.of (fun k : Fin (p + q + 1) ↦
        (⋀[R]^k.1 P) ⊗[R] (⋀[R]^(p + q - k.1) Q))
        ⟨p, Nat.lt_succ_of_le (Nat.le_add_right p q)⟩ (a ⊗ₜ[R] b')) := by
    apply Subtype.ext
    rw [coe_prodEquivDirectSum_symm_of_tmul, hx]
    simp only [b', coe_cast]
  rw [heq, prodComponent_symm_apply]
  rw [← DirectSum.lof_eq_of R, DirectSum.lof_apply, tensor_cast_tmul]
  congr 1
  apply Subtype.ext
  simp only [b', coe_cast]

private theorem prodComponent_of_coe_eq_mul_of_ne (p q i j : ℕ) (h : i + j = p + q)
    (hi : i ≠ p) (a : ⋀[R]^i P) (b : ⋀[R]^j Q)
    (x : ⋀[R]^(p + q) (P × Q))
    (hx : x.1 = ExteriorAlgebra.map (LinearMap.inl R P Q) a.1 *
      ExteriorAlgebra.map (LinearMap.inr R P Q) b.1) :
    prodComponent R P Q p q x = 0 := by
  have hin : i < p + q + 1 := by omega
  have hj : j = p + q - i := by omega
  let b' := LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d Q) hj b
  have heq : x = (prodEquivDirectSum R P Q (p + q)).symm
      (DirectSum.of (fun k : Fin (p + q + 1) ↦
        (⋀[R]^k.1 P) ⊗[R] (⋀[R]^(p + q - k.1) Q))
        ⟨i, hin⟩ (a ⊗ₜ[R] b')) := by
    apply Subtype.ext
    rw [coe_prodEquivDirectSum_symm_of_tmul, hx]
    simp only [b', coe_cast]
  have hfin : (⟨i, hin⟩ : Fin (p + q + 1)) ≠
      ⟨p, Nat.lt_succ_of_le (Nat.le_add_right p q)⟩ := by
    intro he
    exact hi (congrArg Fin.val he)
  rw [heq, prodComponent_symm_apply]
  change LinearEquiv.cast (R := R)
    (M := fun d : ℕ ↦ (⋀[R]^p P) ⊗[R] (⋀[R]^d Q))
    (Nat.add_sub_cancel_left p q)
    (DirectSum.component R (Fin (p + q + 1))
      (fun k ↦ (⋀[R]^k.1 P) ⊗[R] (⋀[R]^(p + q - k.1) Q))
      ⟨p, Nat.lt_succ_of_le (Nat.le_add_right p q)⟩
      (DirectSum.lof R _ _ ⟨i, hin⟩ (a ⊗ₜ[R] b'))) = 0
  rw [DirectSum.component.of, dite_eq_right hfin, map_zero]

/-- Product commutation corresponds to graded tensor commutation on each
homogeneous component. The sign uses the ordered convention for the inverse
Cauchy decomposition. -/
theorem prodComponent_comm (p q : ℕ) :
    (TensorProduct.comm R (⋀[R]^p P) (⋀[R]^q Q)).toLinearMap ∘ₗ
        prodComponent R P Q p q =
      ((-1 : R) ^ (p * q)) •
        (prodComponent R Q P q p ∘ₗ
          map (q + p) (LinearEquiv.prodComm R P Q).toLinearMap ∘ₗ
          (LinearEquiv.cast (R := R)
            (M := fun d : ℕ ↦ ⋀[R]^d (P × Q))
            (Nat.add_comm p q)).toLinearMap) := by
  apply prodEquivDirectSum_ext (T := (⋀[R]^q Q) ⊗[R] (⋀[R]^p P)) R P Q (p + q)
  intro i a b
  let x := (prodEquivDirectSum R P Q (p + q)).symm
    (DirectSum.of (fun k : Fin (p + q + 1) ↦
      (⋀[R]^k.1 P) ⊗[R] (⋀[R]^(p + q - k.1) Q)) i (a ⊗ₜ[R] b))
  have hx : x.1 = ExteriorAlgebra.map (LinearMap.inl R P Q) a.1 *
      ExteriorAlgebra.map (LinearMap.inr R P Q) b.1 :=
    coe_prodEquivDirectSum_symm_of_tmul R P Q (p + q) i a b
  have hi : i.1 ≤ p + q := Nat.lt_succ_iff.mp i.2
  obtain ⟨y, hy⟩ := exists_prod_coe_eq_mul R Q P (q + p) (p + q - i.1) i.1
    (by omega) b a
  let σ := (LinearEquiv.prodComm R P Q).toLinearMap
  have hσl : σ.comp (LinearMap.inl R P Q) = LinearMap.inr R Q P := by
    apply LinearMap.ext
    intro a
    rfl
  have hσr : σ.comp (LinearMap.inr R P Q) = LinearMap.inl R Q P := by
    apply LinearMap.ext
    intro b
    rfl
  have hac :
      ExteriorAlgebra.map (LinearMap.inl R P Q) a.1 *
          ExteriorAlgebra.map (LinearMap.inr R P Q) b.1 =
        ((-1 : ℤˣ) ^ ((p + q - i.1) * i.1)) •
          (ExteriorAlgebra.map (LinearMap.inr R P Q) b.1 *
            ExteriorAlgebra.map (LinearMap.inl R P Q) a.1) :=
    ExteriorAlgebra.map_inl_inr_anticomm R i.1 (p + q - i.1) a b
  -- Compare the existing quotient actions pointwise through canonical zsmul.
  let E := ExteriorAlgebra R (P × Q)
  let hℤ : Module ℤ E :=
    @Algebra.toModule ℤ E (inferInstance : CommSemiring ℤ) (inferInstance : Semiring E)
      (CliffordAlgebra.instAlgebra' (R := ℤ) (A := R) (M := P × Q)
        (0 : QuadraticForm R (P × Q)))
  let hR : Module R E :=
    @Algebra.toModule R E (inferInstance : CommSemiring R) (inferInstance : Semiring E)
      (CliffordAlgebra.instAlgebra' (R := R) (A := R) (M := P × Q)
        (0 : QuadraticForm R (P × Q)))
  have hac := hac.trans
    ((@Units.smul_def ℤ E (inferInstance : Monoid ℤ) hℤ.toSMul
      ((-1 : ℤˣ) ^ ((p + q - i.1) * i.1))
      (ExteriorAlgebra.map (LinearMap.inr R P Q) b.1 *
        ExteriorAlgebra.map (LinearMap.inl R P Q) a.1)).trans
      ((@int_smul_eq_zsmul E (inferInstance : AddCommGroup E) hℤ _ _).trans
        (@Int.cast_smul_eq_zsmul R E (inferInstance : Ring R)
          (inferInstance : AddCommGroup E) hR _ _).symm))
  simp only [Units.val_pow_eq_pow_val, Units.coe_neg_one,
    Int.cast_pow, Int.cast_neg, Int.cast_one] at hac
  have hswap : map (q + p) σ
      (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d (P × Q))
        (Nat.add_comm p q) x) =
      ((-1 : R) ^ ((p + q - i.1) * i.1)) • y := by
    apply Subtype.ext
    rw [coe_map, coe_cast, Submodule.coe_smul, hx, hac, map_smul, map_mul, hy]
    simp only [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hσl, hσr]
  change TensorProduct.comm R (⋀[R]^p P) (⋀[R]^q Q)
      (prodComponent R P Q p q x) =
    ((-1 : R) ^ (p * q)) • prodComponent R Q P q p
      (map (q + p) σ
        (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d (P × Q))
          (Nat.add_comm p q) x))
  by_cases hip : i.1 = p
  · have hjq : p + q - i.1 = q := by omega
    let a' := LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d P) hip a
    let b' := LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d Q) hjq b
    have hx' : x.1 = ExteriorAlgebra.map (LinearMap.inl R P Q) a'.1 *
        ExteriorAlgebra.map (LinearMap.inr R P Q) b'.1 := by
      simpa only [a', b', coe_cast] using hx
    have hy' : y.1 = ExteriorAlgebra.map (LinearMap.inl R Q P) b'.1 *
        ExteriorAlgebra.map (LinearMap.inr R Q P) a'.1 := by
      simpa only [a', b', coe_cast] using hy
    rw [prodComponent_of_coe_eq_mul R P Q p q a' b' x hx', hswap, map_smul,
      prodComponent_of_coe_eq_mul R Q P q p b' a' y hy', TensorProduct.comm_tmul]
    rw [hjq, hip, Nat.mul_comm q p, smul_smul]
    have hsign : ((-1 : R) ^ (p * q)) * ((-1 : R) ^ (p * q)) = 1 := by
      rw [← mul_pow]
      simp
    rw [hsign, one_smul]
  · have hjq : p + q - i.1 ≠ q := by omega
    rw [prodComponent_of_coe_eq_mul_of_ne R P Q p q i.1 (p + q - i.1)
        (by omega) hip a b x hx,
      hswap, map_smul,
      prodComponent_of_coe_eq_mul_of_ne R Q P q p (p + q - i.1) i.1
        (by omega) hjq b a y hy]
    simp

universe z

variable (S : Type z) [AddCommGroup S] [Module R S]

/-- The binary product decomposition respects association of product modules and
tensor products. Association preserves the block order and introduces no sign. -/
theorem prodComponent_assoc (p q r : ℕ) :
    (TensorProduct.assoc R (⋀[R]^p P) (⋀[R]^q Q) (⋀[R]^r S)).toLinearMap ∘ₗ
        TensorProduct.map (prodComponent R P Q p q) LinearMap.id ∘ₗ
        prodComponent R (P × Q) S (p + q) r =
      TensorProduct.map LinearMap.id (prodComponent R Q S q r) ∘ₗ
        prodComponent R P (Q × S) p (q + r) ∘ₗ
        map (p + (q + r)) (LinearEquiv.prodAssoc R P Q S).toLinearMap ∘ₗ
        (LinearEquiv.cast (R := R)
          (M := fun d : ℕ ↦ ⋀[R]^d ((P × Q) × S))
          (Nat.add_assoc p q r)).toLinearMap := by
  let n := (p + q) + r
  let F := (TensorProduct.assoc R (⋀[R]^p P) (⋀[R]^q Q) (⋀[R]^r S)).toLinearMap ∘ₗ
    TensorProduct.map (prodComponent R P Q p q) LinearMap.id ∘ₗ
    prodComponent R (P × Q) S (p + q) r
  let G := TensorProduct.map LinearMap.id (prodComponent R Q S q r) ∘ₗ
    prodComponent R P (Q × S) p (q + r) ∘ₗ
    map (p + (q + r)) (LinearEquiv.prodAssoc R P Q S).toLinearMap ∘ₗ
    (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d ((P × Q) × S))
      (Nat.add_assoc p q r)).toLinearMap
  change F = G
  apply prodEquivDirectSum_ext
    (T := (⋀[R]^p P) ⊗[R] ((⋀[R]^q Q) ⊗[R] (⋀[R]^r S))) R (P × Q) S n
  intro i a c
  let outer : (⋀[R]^i.1 (P × Q)) →ₗ[R] ⋀[R]^n ((P × Q) × S) :=
    (prodEquivDirectSum R (P × Q) S n).symm.toLinearMap ∘ₗ
      DirectSum.lof R (Fin (n + 1))
        (fun k ↦ (⋀[R]^k.1 (P × Q)) ⊗[R] (⋀[R]^(n - k.1) S)) i ∘ₗ
      (TensorProduct.mk R (⋀[R]^i.1 (P × Q)) (⋀[R]^(n - i.1) S)).flip c
  suffices h : F ∘ₗ outer = G ∘ₗ outer from LinearMap.congr_fun h a
  apply prodEquivDirectSum_ext
    (T := (⋀[R]^p P) ⊗[R] ((⋀[R]^q Q) ⊗[R] (⋀[R]^r S))) R P Q i.1
  intro j x y
  let b := (prodEquivDirectSum R P Q i.1).symm
    (DirectSum.of (fun k : Fin (i.1 + 1) ↦
      (⋀[R]^k.1 P) ⊗[R] (⋀[R]^(i.1 - k.1) Q)) j (x ⊗ₜ[R] y))
  let t := outer b
  have hb : b.1 = ExteriorAlgebra.map (LinearMap.inl R P Q) x.1 *
      ExteriorAlgebra.map (LinearMap.inr R P Q) y.1 :=
    coe_prodEquivDirectSum_symm_of_tmul R P Q i.1 j x y
  have ht : t.1 = ExteriorAlgebra.map (LinearMap.inl R (P × Q) S) b.1 *
      ExteriorAlgebra.map (LinearMap.inr R (P × Q) S) c.1 :=
    coe_prodEquivDirectSum_symm_of_tmul R (P × Q) S n i b c
  have hi : i.1 ≤ n := Nat.lt_succ_iff.mp i.2
  have hj : j.1 ≤ i.1 := Nat.lt_succ_iff.mp j.2
  obtain ⟨v, hv⟩ := exists_prod_coe_eq_mul R Q S
    ((i.1 - j.1) + (n - i.1)) (i.1 - j.1) (n - i.1) rfl y c
  obtain ⟨t', ht'⟩ := exists_prod_coe_eq_mul R P (Q × S) (p + (q + r))
    j.1 ((i.1 - j.1) + (n - i.1)) (by dsimp only [n] at hi ⊢; omega) x v
  let α := (LinearEquiv.prodAssoc R P Q S).toLinearMap
  have hP : α.comp ((LinearMap.inl R (P × Q) S).comp (LinearMap.inl R P Q)) =
      LinearMap.inl R P (Q × S) := by
    apply LinearMap.ext
    intro x
    rfl
  have hQ : α.comp ((LinearMap.inl R (P × Q) S).comp (LinearMap.inr R P Q)) =
      (LinearMap.inr R P (Q × S)).comp (LinearMap.inl R Q S) := by
    apply LinearMap.ext
    intro y
    rfl
  have hS : α.comp (LinearMap.inr R (P × Q) S) =
      (LinearMap.inr R P (Q × S)).comp (LinearMap.inr R Q S) := by
    apply LinearMap.ext
    intro c
    rfl
  have hassoc : map (p + (q + r)) α
      (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d ((P × Q) × S))
        (Nat.add_assoc p q r) t) = t' := by
    apply Subtype.ext
    rw [coe_map, coe_cast, ht, hb, ht', hv]
    simp only [map_mul, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
      hP, hQ, hS, mul_assoc]
  change TensorProduct.assoc R (⋀[R]^p P) (⋀[R]^q Q) (⋀[R]^r S)
      (TensorProduct.map (prodComponent R P Q p q) LinearMap.id
        (prodComponent R (P × Q) S (p + q) r t)) =
    TensorProduct.map LinearMap.id (prodComponent R Q S q r)
      (prodComponent R P (Q × S) p (q + r)
        (map (p + (q + r)) α
          (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d ((P × Q) × S))
            (Nat.add_assoc p q r) t)))
  rw [hassoc]
  by_cases hjp : j.1 = p
  · have hrest : (i.1 - j.1) + (n - i.1) = q + r := by dsimp only [n] at hi ⊢; omega
    let x' := LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d P) hjp x
    let v' := LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d (Q × S)) hrest v
    have ht'0 : t'.1 = ExteriorAlgebra.map (LinearMap.inl R P (Q × S)) x'.1 *
        ExteriorAlgebra.map (LinearMap.inr R P (Q × S)) v'.1 := by
      simpa only [x', v', coe_cast] using ht'
    have hv' : v'.1 = ExteriorAlgebra.map (LinearMap.inl R Q S) y.1 *
        ExteriorAlgebra.map (LinearMap.inr R Q S) c.1 := by
      simpa only [v', coe_cast] using hv
    rw [prodComponent_of_coe_eq_mul R P (Q × S) p (q + r) x' v' t' ht'0,
      TensorProduct.map_tmul, LinearMap.id_apply]
    by_cases hipq : i.1 = p + q
    · have hyq : i.1 - j.1 = q := by omega
      have hcr : n - i.1 = r := by dsimp [n]; omega
      let b' := LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d (P × Q)) hipq b
      let y' := LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d Q) hyq y
      let c' := LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d S) hcr c
      have ht0 : t.1 = ExteriorAlgebra.map (LinearMap.inl R (P × Q) S) b'.1 *
          ExteriorAlgebra.map (LinearMap.inr R (P × Q) S) c'.1 := by
        simpa only [b', c', coe_cast] using ht
      have hb' : b'.1 = ExteriorAlgebra.map (LinearMap.inl R P Q) x'.1 *
          ExteriorAlgebra.map (LinearMap.inr R P Q) y'.1 := by
        simpa only [b', x', y', coe_cast] using hb
      have hv'0 : v'.1 = ExteriorAlgebra.map (LinearMap.inl R Q S) y'.1 *
          ExteriorAlgebra.map (LinearMap.inr R Q S) c'.1 := by
        simpa only [y', c', coe_cast] using hv'
      rw [prodComponent_of_coe_eq_mul R (P × Q) S (p + q) r b' c' t ht0,
        TensorProduct.map_tmul, LinearMap.id_apply,
        prodComponent_of_coe_eq_mul R P Q p q x' y' b' hb', TensorProduct.assoc_tmul,
        prodComponent_of_coe_eq_mul R Q S q r y' c' v' hv'0]
    · have hyq : i.1 - j.1 ≠ q := by omega
      rw [prodComponent_of_coe_eq_mul_of_ne R (P × Q) S (p + q) r i.1 (n - i.1)
          (by dsimp only [n] at hi ⊢; omega) hipq b c t ht,
        map_zero, map_zero,
        prodComponent_of_coe_eq_mul_of_ne R Q S q r (i.1 - j.1) (n - i.1)
          hrest hyq y c v' hv', TensorProduct.tmul_zero]
  · have hright : prodComponent R P (Q × S) p (q + r) t' = 0 :=
      prodComponent_of_coe_eq_mul_of_ne R P (Q × S) p (q + r)
        j.1 ((i.1 - j.1) + (n - i.1)) (by dsimp only [n] at hi ⊢; omega) hjp x v t' ht'
    rw [hright, map_zero]
    by_cases hipq : i.1 = p + q
    · have hcr : n - i.1 = r := by dsimp [n]; omega
      let b' := LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d (P × Q)) hipq b
      let c' := LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d S) hcr c
      have ht0 : t.1 = ExteriorAlgebra.map (LinearMap.inl R (P × Q) S) b'.1 *
          ExteriorAlgebra.map (LinearMap.inr R (P × Q) S) c'.1 := by
        simpa only [b', c', coe_cast] using ht
      have hb' : b'.1 = ExteriorAlgebra.map (LinearMap.inl R P Q) x.1 *
          ExteriorAlgebra.map (LinearMap.inr R P Q) y.1 := by
        simpa only [b', coe_cast] using hb
      rw [prodComponent_of_coe_eq_mul R (P × Q) S (p + q) r b' c' t ht0,
        TensorProduct.map_tmul, LinearMap.id_apply,
        prodComponent_of_coe_eq_mul_of_ne R P Q p q j.1 (i.1 - j.1)
          (by omega) hjp x y b' hb', TensorProduct.zero_tmul, map_zero]
    · rw [prodComponent_of_coe_eq_mul_of_ne R (P × Q) S (p + q) r i.1 (n - i.1)
        (by dsimp only [n] at hi ⊢; omega) hipq b c t ht, map_zero, map_zero]

end exteriorPower
