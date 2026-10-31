/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.SymmetricPower.Tensor
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic

/-!
# Symmetric powers of product modules

The symmetric power of `M × N` decomposes as the direct sum of the tensors
of the complementary symmetric degrees of `M` and `N`. The forward map is
expansion over subsets of the labels. The inverse concatenates the two
blocks after inserting them into the product module.

The decomposition is natural in both modules. In degree zero it agrees
with the scalar module, and in degree one its target is ordered as `N × M`;
the normalized inverse therefore swaps the two coordinates.

The construction works for arbitrary semimodules over commutative semirings;
projectivity, additive inverses and invertibility of factorials are unnecessary.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*.
-/

public section

open scoped TensorProduct DirectSum BigOperators

namespace SymmetricPower

noncomputable section

universe uR uM uN

variable {R : Type uR} [CommSemiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {N : Type uN} [AddCommMonoid N] [Module R N]
variable {I J K : Type uR}

/-- Places two labelled symmetric blocks in the product module. -/
private def productBlockAssembly (e : I ⊕ J ≃ K) :
    SymmetricPower R I M ⊗[R] SymmetricPower R J N →ₗ[R]
      SymmetricPower R K (M × N) :=
  (reindex (R := R) (M := M × N) e).toLinearMap.comp
    ((concat (R := R) (I := I) (J := J) (P := M × N)).comp
      (TensorProduct.map
        (map (ι := I) (LinearMap.inl R M N))
        (map (ι := J) (LinearMap.inr R M N))))

private theorem productBlockAssembly_tprod (e : I ⊕ J ≃ K)
    (m : I → M) (z : J → N) :
    productBlockAssembly (R := R) (M := M) (N := N) e
        (tprod R m ⊗ₜ[R] tprod R z) =
      tprod R (fun k =>
        Sum.elim (fun a => (m a, (0 : N)))
          (fun b => ((0 : M), z b)) (e.symm k)) := by
  simp [productBlockAssembly, TensorProduct.map_tmul, map_tprod,
    concat_tprod, reindex_tprod, LinearMap.inl_apply, LinearMap.inr_apply]

private theorem tprod_relabel_independent {A K : Type uR}
    (e₀ e : A ≃ K) (c : A → M × N) :
    tprod R (fun k => c (e₀.symm k)) =
      tprod R (fun k => c (e.symm k)) := by
  simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using
    (tprod_equiv (R := R) (e.symm.trans e₀)
      (fun k => c (e₀.symm k))).symm

/-- Identifies two lifted finite degree blocks with the total label set. -/
private def degreeSplitEquiv (n : Nat) (i : Fin (n + 1)) :
    (ULift.{uR} (Fin i.val) ⊕ ULift.{uR} (Fin (n - i.val))) ≃
      ULift.{uR} (Fin n) := by
  have hi : i.val < n + 1 := i.isLt
  have h : i.val + (n - i.val) = n := by omega
  exact
    (Equiv.sumCongr
      (Equiv.ulift : ULift.{uR} (Fin i.val) ≃ Fin i.val)
      (Equiv.ulift : ULift.{uR} (Fin (n - i.val)) ≃
        Fin (n - i.val))).trans
      ((finSumFinEquiv :
        (Fin i.val ⊕ Fin (n - i.val)) ≃ Fin (i.val + (n - i.val))).trans
        ((Equiv.cast (congrArg Fin h)).trans
          (Equiv.ulift : ULift.{uR} (Fin n) ≃ Fin n).symm))

/-- Assembles the symmetric degree blocks in a product module. -/
private def binomialAssembly (n : Nat) :
    (⨁ i : Fin (n + 1),
      SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N) →ₗ[R]
      SymmetricPower R (ULift.{uR} (Fin n)) (M × N) :=
  DirectSum.toModule R (Fin (n + 1))
    (SymmetricPower R (ULift.{uR} (Fin n)) (M × N))
    (fun i => productBlockAssembly (R := R) (M := M) (N := N)
      (degreeSplitEquiv.{uR} n i))

private theorem binomialAssembly_lof (n : Nat) (i : Fin (n + 1))
    (s : SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
      SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N) :
    binomialAssembly (R := R) (M := M) (N := N) n
        (DirectSum.lof R (Fin (n + 1))
          (fun j : Fin (n + 1) =>
            SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
              SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N)
          i s) =
      productBlockAssembly (R := R) (M := M) (N := N)
        (degreeSplitEquiv.{uR} n i) s := by
  simp only [binomialAssembly, DirectSum.toModule_lof]

private theorem binomialAssembly_lof_tprod
    (n : Nat) (i : Fin (n + 1))
    (e : (ULift.{uR} (Fin i.val) ⊕
      ULift.{uR} (Fin (n - i.val))) ≃ ULift.{uR} (Fin n))
    (m : ULift.{uR} (Fin i.val) → M)
    (z : ULift.{uR} (Fin (n - i.val)) → N) :
    binomialAssembly (R := R) (M := M) (N := N) n
        (DirectSum.lof R (Fin (n + 1))
          (fun j : Fin (n + 1) =>
            SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
              SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N)
          i (tprod R m ⊗ₜ[R] tprod R z)) =
      tprod R (fun k : ULift.{uR} (Fin n) =>
        Sum.elim (fun a => (m a, (0 : N)))
          (fun b => ((0 : M), z b)) (e.symm k)) := by
  rw [binomialAssembly_lof, productBlockAssembly_tprod]
  exact tprod_relabel_independent (R := R) (M := M) (N := N)
    (degreeSplitEquiv.{uR} n i) e
    (Sum.elim (fun a => (m a, (0 : N))) (fun b => ((0 : M), z b)))

end

end SymmetricPower

universe uR uM uN uI uJ uP uQ

namespace SymmetricPower

noncomputable section

/-- Increasing enumeration of a finite subset by a lifted degree index. -/
private def subsetEnumeration
    {I : Type uR} [LinearOrder I] {k : ℕ}
    (s : Finset I) (hs : s.card = k) : ULift.{uR} (Fin k) ≃ s :=
  Equiv.ulift.trans (s.orderIsoOfFin hs).toEquiv

private theorem restrict_update_mem
    {I : Type uI} {J : Type uJ} {P : Type uP} {Q : Type uQ}
    [DecidableEq I] [DecidableEq J]
    (s : Finset I) (a : J ≃ s) (q : I) (hq : q ∈ s)
    (x : I → P) (v : P) (f : P → Q) :
    (fun j => f (Function.update x q v (a j).val)) =
      Function.update (fun j => f (x (a j).val))
        (a.symm ⟨q, hq⟩) (f v) := by
  funext j
  by_cases h : j = a.symm ⟨q, hq⟩
  · subst j
    simp
  · have hne : (a j).val ≠ q := by
      intro hval
      apply h
      apply a.injective
      apply Subtype.ext
      simpa using hval
    simp [h, hne]

private theorem restrict_update_not_mem
    {I : Type uI} {J : Type uJ} {P : Type uP} {Q : Type uQ}
    [DecidableEq I]
    (s : Finset I) (a : J ≃ s) (q : I) (hq : q ∉ s)
    (x : I → P) (v : P) (f : P → Q) :
    (fun j => f (Function.update x q v (a j).val)) =
      (fun j => f (x (a j).val)) := by
  funext j
  have hne : (a j).val ≠ q := by
    intro hval
    exact hq (hval ▸ (a j).property)
  simp [hne]

/-- The tensor term associated to two enumerated complementary blocks. -/
private def blockValue
    {R : Type uR} [CommSemiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {N : Type uN} [AddCommMonoid N] [Module R N]
    {I J K : Type uR} [Fintype I] [DecidableEq I]
    (s : Finset I) (a : J ≃ s) (b : K ≃ ↥(sᶜ)) (x : I → M × N) :
    SymmetricPower R J M ⊗[R] SymmetricPower R K N :=
  tprod R (fun j => (x (a j).val).1) ⊗ₜ[R]
    tprod R (fun k => (x (b k).val).2)

/-- Each tensor term is multilinear in the uniformly pair-valued labels. -/
private def blockMultilinear
    {R : Type uR} [CommSemiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {N : Type uN} [AddCommMonoid N] [Module R N]
    {I J K : Type uR} [Fintype I] [DecidableEq I]
    (s : Finset I) (a : J ≃ s) (b : K ≃ ↥(sᶜ)) :
    MultilinearMap R (fun _ : I => M × N)
      (SymmetricPower R J M ⊗[R] SymmetricPower R K N) := by
  let f := blockValue (R := R) (M := M) (N := N) s a b
  let t : Finset I := sᶜ
  have ht (q : I) : q ∈ t ↔ q ∉ s := Finset.mem_compl
  classical
  refine
    { toFun := f
      map_update_add' := ?_
      map_update_smul' := ?_ }
  · intro _ x q w v
    by_cases hq : q ∈ s
    · have hc : q ∉ t := fun h => (ht q).mp h hq
      simp only [f, blockValue,
        restrict_update_mem s a q hq,
        restrict_update_not_mem t b q hc]
      have hadd : (w + v).1 = w.1 + v.1 := by
        simpa only [LinearMap.fst_apply] using (LinearMap.fst R M N).map_add w v
      simpa only [hadd, TensorProduct.add_tmul] using
        congrArg
          (fun y => y ⊗ₜ[R] tprod R (fun k => (x (b k).val).2))
          ((tprod R).map_update_add
            (fun j => (x (a j).val).1) (a.symm ⟨q, hq⟩) w.1 v.1)
    · have hc : q ∈ t := (ht q).mpr hq
      simp only [f, blockValue,
        restrict_update_not_mem s a q hq,
        restrict_update_mem t b q hc]
      have hadd : (w + v).2 = w.2 + v.2 := by
        simpa only [LinearMap.snd_apply] using (LinearMap.snd R M N).map_add w v
      simpa only [hadd, TensorProduct.tmul_add] using
        congrArg
          (fun y => tprod R (fun j => (x (a j).val).1) ⊗ₜ[R] y)
          ((tprod R).map_update_add
            (fun k => (x (b k).val).2) (b.symm ⟨q, hc⟩) w.2 v.2)
  · intro _ x q c w
    by_cases hq : q ∈ s
    · have hc : q ∉ t := fun h => (ht q).mp h hq
      simp only [f, blockValue,
        restrict_update_mem s a q hq,
        restrict_update_not_mem t b q hc]
      have hsmul : (c • w).1 = c • w.1 := by
        simpa only [LinearMap.fst_apply] using (LinearMap.fst R M N).map_smul c w
      simpa only [hsmul, ← TensorProduct.smul_tmul'] using
        congrArg
          (fun y => y ⊗ₜ[R] tprod R (fun k => (x (b k).val).2))
          ((tprod R).map_update_smul
            (fun j => (x (a j).val).1) (a.symm ⟨q, hq⟩) c w.1)
    · have hc : q ∈ t := (ht q).mpr hq
      simp only [f, blockValue,
        restrict_update_not_mem s a q hq,
        restrict_update_mem t b q hc]
      have hsmul : (c • w).2 = c • w.2 := by
        simpa only [LinearMap.snd_apply] using (LinearMap.snd R M N).map_smul c w
      simpa only [hsmul, TensorProduct.tmul_smul] using
        congrArg
          (fun y => tprod R (fun j => (x (a j).val).1) ⊗ₜ[R] y)
          ((tprod R).map_update_smul
            (fun k => (x (b k).val).2) (b.symm ⟨q, hc⟩) c w.2)

/-- A permutation of the labels permutes the subsets of each fixed size. -/
private noncomputable def permuteSizedSubsets
    {I : Type uR} (k : ℕ) (p : Equiv.Perm I) :
    {s : Finset I // s.card = k} ≃ {s : Finset I // s.card = k} := by
  classical
  exact
    { toFun := fun s =>
        ⟨s.val.map p.toEmbedding,
          by simpa only [Finset.card_map] using s.property⟩
      invFun := fun s =>
        ⟨s.val.map p.symm.toEmbedding,
          by simpa only [Finset.card_map] using s.property⟩
      left_inv := by
        intro s
        apply Subtype.ext
        apply Finset.ext
        intro q
        change
          q ∈ (s.val.map p.toEmbedding).map p.symm.toEmbedding ↔ q ∈ s.val
        simp only [Finset.mem_map_equiv, Equiv.symm_symm,
          Equiv.symm_apply_apply]
      right_inv := by
        intro s
        apply Subtype.ext
        apply Finset.ext
        intro q
        change
          q ∈ (s.val.map p.symm.toEmbedding).map p.toEmbedding ↔ q ∈ s.val
        simp only [Finset.mem_map_equiv, Equiv.symm_symm,
          Equiv.apply_symm_apply] }

/-- The restriction of a label permutation to a subset and its image. -/
private noncomputable def permuteSubset
    {I : Type uR} (p : Equiv.Perm I) (s : Finset I) :
    s ≃ s.map p.toEmbedding := by
  classical
  exact
    { toFun := fun a =>
        ⟨p a.val, by
          apply Finset.mem_map_equiv.mpr
          simpa only [Equiv.symm_apply_apply] using a.property⟩
      invFun := fun a =>
        ⟨p.symm a.val, Finset.mem_map_equiv.mp a.property⟩
      left_inv := by
        intro a
        apply Subtype.ext
        exact p.symm_apply_apply a.val
      right_inv := by
        intro a
        apply Subtype.ext
        exact p.apply_symm_apply a.val }

/-- The restriction of a label permutation to complementary subsets. -/
private noncomputable def permuteComplement
    {I : Type uR} [Fintype I] [DecidableEq I]
    (p : Equiv.Perm I) (s : Finset I) :
    ↥(sᶜ) ≃ ↥((s.map p.toEmbedding)ᶜ) := by
  classical
  exact
    { toFun := fun a =>
        ⟨p a.val, by
          apply Finset.mem_compl.mpr
          intro h
          have hs : p.symm (p a.val) ∈ s := Finset.mem_map_equiv.mp h
          have ha : a.val ∈ s := by
            simpa only [Equiv.symm_apply_apply] using hs
          exact (Finset.mem_compl.mp a.property) ha⟩
      invFun := fun a =>
        ⟨p.symm a.val, by
          apply Finset.mem_compl.mpr
          intro h
          apply (Finset.mem_compl.mp a.property)
          exact Finset.mem_map_equiv.mpr h⟩
      left_inv := by
        intro a
        apply Subtype.ext
        exact p.symm_apply_apply a.val
      right_inv := by
        intro a
        apply Subtype.ext
        exact p.apply_symm_apply a.val }

/-- The underlying value of subset transport is the label permutation. -/
private theorem permuteSubset_val
    {I : Type uR} (p : Equiv.Perm I) (s : Finset I) (a : s) :
    (permuteSubset p s a).val = p a.val := by
  rfl

/-- The underlying value of complement transport is the label permutation. -/
private theorem permuteComplement_val
    {I : Type uR} [Fintype I] [DecidableEq I]
    (p : Equiv.Perm I) (s : Finset I) (a : ↥(sᶜ)) :
    (permuteComplement p s a).val = p a.val := by
  rfl

/-- Transporting the labels of two enumerated complementary blocks does not
change their tensor of symmetric products. -/
private theorem tensorBlock_permute
    {R : Type uR} [CommSemiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {N : Type uN} [AddCommMonoid N] [Module R N]
    {I J K : Type uR} [Fintype I] [DecidableEq I]
    (p : Equiv.Perm I) (s : Finset I)
    (a : J ≃ s) (b : K ≃ ↥(sᶜ))
    (a' : J ≃ s.map p.toEmbedding)
    (b' : K ≃ ↥((s.map p.toEmbedding)ᶜ))
    (x : I → M × N) :
    (SymmetricPower.tprod R (fun j => (x (p (a j).val)).1) ⊗ₜ[R]
      SymmetricPower.tprod R (fun l => (x (p (b l).val)).2)) =
    (SymmetricPower.tprod R (fun j => (x (a' j).val).1) ⊗ₜ[R]
      SymmetricPower.tprod R (fun l => (x (b' l).val).2)) := by
  let pM : Equiv.Perm J :=
    (a.trans (permuteSubset p s)).trans a'.symm
  let pN : Equiv.Perm K :=
    (b.trans (permuteComplement p s)).trans b'.symm
  have hpM (j : J) : (a' (pM j)).val = p (a j).val := by
    change
      (a' (a'.symm (permuteSubset p s (a j)))).val = p (a j).val
    rw [a'.apply_symm_apply]
    exact permuteSubset_val p s (a j)
  have hpN (l : K) : (b' (pN l)).val = p (b l).val := by
    change
      (b' (b'.symm (permuteComplement p s (b l)))).val = p (b l).val
    rw [b'.apply_symm_apply]
    exact permuteComplement_val p s (b l)
  have hM :
      SymmetricPower.tprod R (fun j => (x (p (a j).val)).1) =
        SymmetricPower.tprod R (fun j => (x (a' j).val).1) := by
    calc
      _ = SymmetricPower.tprod R
          (fun j => (x (a' (pM j)).val).1) := by
        apply congrArg (SymmetricPower.tprod R)
        funext j
        rw [hpM j]
      _ = _ := SymmetricPower.tprod_equiv (R := R) pM
        (fun j => (x (a' j).val).1)
  have hN :
      SymmetricPower.tprod R (fun l => (x (p (b l).val)).2) =
        SymmetricPower.tprod R (fun l => (x (b' l).val).2) := by
    calc
      _ = SymmetricPower.tprod R
          (fun l => (x (b' (pN l)).val).2) := by
        apply congrArg (SymmetricPower.tprod R)
        funext l
        rw [hpN l]
      _ = _ := SymmetricPower.tprod_equiv (R := R) pN
        (fun l => (x (b' l).val).2)
  rw [hM, hN]

/-- The size-k subset expansion is invariant under permutation of the labels.
The two enumeration families are arbitrary and need not commute with p. -/
private theorem subsetExpansion_permute
    {R : Type uR} [CommSemiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {N : Type uN} [AddCommMonoid N] [Module R N]
    {I J K : Type uR} [Fintype I] [DecidableEq I]
    {k : ℕ}
    (a : (s : {s : Finset I // s.card = k}) → J ≃ s.val)
    (b : (s : {s : Finset I // s.card = k}) → K ≃ ↥(s.valᶜ))
    (p : Equiv.Perm I) (x : I → M × N) :
    (∑ s : {s : Finset I // s.card = k},
      SymmetricPower.tprod R (fun j => (x (p (a s j).val)).1) ⊗ₜ[R]
        SymmetricPower.tprod R (fun l => (x (p (b s l).val)).2)) =
    (∑ s : {s : Finset I // s.card = k},
      SymmetricPower.tprod R (fun j => (x (a s j).val).1) ⊗ₜ[R]
        SymmetricPower.tprod R (fun l => (x (b s l).val).2)) := by
  classical
  apply (Multiplicative.ofAdd :
    (SymmetricPower R J M ⊗[R] SymmetricPower R K N) ≃
      Multiplicative
        (SymmetricPower R J M ⊗[R] SymmetricPower R K N)).injective
  rw [ofAdd_sum, ofAdd_sum]
  refine Fintype.prod_equiv (permuteSizedSubsets k p) _ _ ?_
  intro s
  exact congrArg
    (fun z : SymmetricPower R J M ⊗[R] SymmetricPower R K N =>
      Multiplicative.ofAdd z)
    (tensorBlock_permute (R := R) p s.val
      (a s) (b s)
      (a (permuteSizedSubsets k p s))
      (b (permuteSizedSubsets k p s)) x)

/-- The size-i part of the subset expansion. -/
private def binomialComponent
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    (N : Type uN) [AddCommMonoid N] [Module R N]
    (n : ℕ) (i : Fin (n + 1)) :
    MultilinearMap R (fun _ : ULift.{uR} (Fin n) => M × N)
      (SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N) :=
  ∑ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val},
    blockMultilinear (R := R) (M := M) (N := N) s.val
      (subsetEnumeration s.val s.property)
      (subsetEnumeration (k := n - i.val) s.valᶜ (by simp [Finset.card_compl, s.property]))

/-- Evaluation of the finite sum of block multilinear maps. -/
private theorem binomialComponent_apply
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    (N : Type uN) [AddCommMonoid N] [Module R N]
    (n : ℕ) (i : Fin (n + 1)) (x : ULift.{uR} (Fin n) → M × N) :
    binomialComponent R M N n i x =
      ∑ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val},
        blockValue (R := R) s.val
          (subsetEnumeration s.val s.property)
          (subsetEnumeration (k := n - i.val) s.valᶜ
            (by simp [Finset.card_compl, s.property])) x := by
  let D := SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
    SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N
  let B := MultilinearMap R (fun _ : ULift.{uR} (Fin n) => M × N) D
  let ev : Multiplicative B →* Multiplicative D :=
    { toFun := fun f => Multiplicative.ofAdd
        (((Multiplicative.ofAdd : B ≃ Multiplicative B).symm f) x)
      map_one' := rfl
      map_mul' := by intro f g; rfl }
  apply (Multiplicative.ofAdd : D ≃ Multiplicative D).injective
  change ev (Multiplicative.ofAdd
      (∑ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val},
        blockMultilinear (R := R) (M := M) (N := N) s.val
          (subsetEnumeration s.val s.property)
          (subsetEnumeration (k := n - i.val) s.valᶜ
            (by simp [Finset.card_compl, s.property])))) = _
  rw [ofAdd_sum, ofAdd_sum, map_prod]
  apply Finset.prod_congr rfl
  intro s hs
  rfl

private theorem binomialComponent_permutation
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    (N : Type uN) [AddCommMonoid N] [Module R N]
    (n : ℕ) (i : Fin (n + 1))
    (p : Equiv.Perm (ULift.{uR} (Fin n)))
    (x : ULift.{uR} (Fin n) → M × N) :
    binomialComponent R M N n i (fun q => x (p q)) =
      binomialComponent R M N n i x := by
  rw [binomialComponent_apply, binomialComponent_apply]
  exact subsetExpansion_permute (R := R)
    (a := fun s => subsetEnumeration s.val s.property)
    (b := fun s => subsetEnumeration (k := n - i.val) s.valᶜ
      (by simp [Finset.card_compl, s.property])) p x

/-- All size components, injected into the dependent direct sum. -/
private def binomialMultilinear
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    (N : Type uN) [AddCommMonoid N] [Module R N]
    (n : ℕ) :
    MultilinearMap R (fun _ : ULift.{uR} (Fin n) => M × N)
      (⨁ i : Fin (n + 1),
        SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
          SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N) :=
  ∑ i : Fin (n + 1),
    (DirectSum.lof R (Fin (n + 1))
      (fun j : Fin (n + 1) =>
        SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
          SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N) i).compMultilinearMap
      (binomialComponent R M N n i)

/-- Evaluation commutes with this particular direct-sum-valued finite sum. -/
private theorem binomialMultilinear_apply
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    (N : Type uN) [AddCommMonoid N] [Module R N]
    (n : ℕ) (x : ULift.{uR} (Fin n) → M × N) :
    binomialMultilinear R M N n x =
      ∑ i : Fin (n + 1),
        DirectSum.lof R (Fin (n + 1))
          (fun j : Fin (n + 1) =>
            SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
              SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N)
          i (binomialComponent R M N n i x) := by
  let D := fun i : Fin (n + 1) =>
    SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
      SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N
  let T := ⨁ i : Fin (n + 1), D i
  let B := MultilinearMap R (fun _ : ULift.{uR} (Fin n) => M × N) T
  let ev : Multiplicative B →* Multiplicative T :=
    { toFun := fun f => Multiplicative.ofAdd
        (((Multiplicative.ofAdd : B ≃ Multiplicative B).symm f) x)
      map_one' := rfl
      map_mul' := by intro f g; rfl }
  apply (Multiplicative.ofAdd : T ≃ Multiplicative T).injective
  change ev (Multiplicative.ofAdd
      (∑ i : Fin (n + 1),
        (DirectSum.lof R (Fin (n + 1)) D i).compMultilinearMap
          (binomialComponent R M N n i))) = _
  rw [ofAdd_sum, ofAdd_sum, map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun z : T => Multiplicative.ofAdd z)
    (congrFun
      (LinearMap.coe_compMultilinearMap
        (DirectSum.lof R (Fin (n + 1)) D i)
        (binomialComponent R M N n i)) x)

private theorem binomialMultilinear_permutation
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    (N : Type uN) [AddCommMonoid N] [Module R N]
    (n : ℕ) (p : Equiv.Perm (ULift.{uR} (Fin n)))
    (x : ULift.{uR} (Fin n) → M × N) :
    binomialMultilinear R M N n (fun q => x (p q)) =
      binomialMultilinear R M N n x := by
  rw [binomialMultilinear_apply, binomialMultilinear_apply]
  let D := fun i : Fin (n + 1) =>
    SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
      SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N
  have h : (fun i => binomialComponent R M N n i (fun q => x (p q))) =
      (fun i => binomialComponent R M N n i x) := by
    funext i
    exact binomialComponent_permutation R M N n i p x
  exact congrArg
    (fun v : ∀ i : Fin (n + 1), D i =>
      ∑ i : Fin (n + 1), DirectSum.lof R (Fin (n + 1)) D i (v i)) h

/-- Binomial expansion of the symmetric power of a binary product. -/
private def binomialLinearMap
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    (N : Type uN) [AddCommMonoid N] [Module R N]
    (n : ℕ) :
    SymmetricPower R (ULift.{uR} (Fin n)) (M × N) →ₗ[R]
      (⨁ i : Fin (n + 1),
        SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
          SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N) :=
  lift (binomialMultilinear R M N n)
    (binomialMultilinear_permutation R M N n)

/-- The expansion of a labelled product, grouped by degree. -/
private theorem binomialForward_tprod_sum_grouped
    {R : Type uR} [CommSemiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {N : Type uN} [AddCommMonoid N] [Module R N]
    (n : ℕ) (x : ULift.{uR} (Fin n) → M × N) :
    binomialLinearMap R M N n (tprod R x) =
      ∑ i : Fin (n + 1),
        DirectSum.lof R (Fin (n + 1))
          (fun j : Fin (n + 1) =>
            SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
              SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N)
          i (∑ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val},
            blockValue (R := R) s.val
              (subsetEnumeration s.val s.property)
              (subsetEnumeration (k := n - i.val) s.valᶜ
                (by simp [Finset.card_compl, s.property])) x) := by
  change lift (binomialMultilinear R M N n)
      (binomialMultilinear_permutation R M N n) (tprod R x) = _
  rw [lift_tprod, binomialMultilinear_apply]
  let D := fun i : Fin (n + 1) =>
    SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
      SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N
  have h : (fun i => binomialComponent R M N n i x) =
      (fun i =>
        ∑ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val},
          blockValue (R := R) s.val
            (subsetEnumeration s.val s.property)
            (subsetEnumeration (k := n - i.val) s.valᶜ
              (by simp [Finset.card_compl, s.property])) x) := by
    funext i
    exact binomialComponent_apply R M N n i x
  exact congrArg
    (fun v : ∀ i : Fin (n + 1), D i =>
      ∑ i : Fin (n + 1), DirectSum.lof R (Fin (n + 1)) D i (v i)) h

/-- Every labelled subset contributes once to the direct-sum expansion. -/
private theorem binomialForward_tprod_sum
    {R : Type uR} [CommSemiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {N : Type uN} [AddCommMonoid N] [Module R N]
    (n : ℕ) (x : ULift.{uR} (Fin n) → M × N) :
    binomialLinearMap R M N n (tprod R x) =
      ∑ i : Fin (n + 1),
        ∑ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val},
          DirectSum.lof R (Fin (n + 1))
            (fun j : Fin (n + 1) =>
              SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
                SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N)
            i (blockValue (R := R) s.val
              (subsetEnumeration s.val s.property)
              (subsetEnumeration (k := n - i.val) s.valᶜ
                (by simp [Finset.card_compl, s.property])) x) := by
  rw [binomialForward_tprod_sum_grouped]
  let D := fun i : Fin (n + 1) =>
    SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
      SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N
  let T := ⨁ i : Fin (n + 1), D i
  apply (Multiplicative.ofAdd : T ≃ Multiplicative T).injective
  rw [ofAdd_sum, ofAdd_sum]
  apply Finset.prod_congr rfl
  intro i hi
  let ell := DirectSum.lof R (Fin (n + 1)) D i
  let tell : Multiplicative (D i) →* Multiplicative T :=
    { toFun := fun v =>
        Multiplicative.ofAdd (ell ((Multiplicative.ofAdd : D i ≃ Multiplicative (D i)).symm v))
      map_one' := by
        change Multiplicative.ofAdd (ell 0) = 1
        rw [ell.map_zero]
        rfl
      map_mul' := by
        intro v w
        change Multiplicative.ofAdd
            (ell ((Multiplicative.ofAdd : D i ≃ Multiplicative (D i)).symm v +
              (Multiplicative.ofAdd : D i ≃ Multiplicative (D i)).symm w)) = _
        rw [ell.map_add]
        rfl }
  change tell (Multiplicative.ofAdd
      (∑ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val},
        blockValue (R := R) s.val
          (subsetEnumeration s.val s.property)
          (subsetEnumeration (k := n - i.val) s.valᶜ
            (by simp [Finset.card_compl, s.property])) x)) = _
  rw [ofAdd_sum, ofAdd_sum, map_prod]
  rfl

/-- The product presentation of the direct-sum binomial expansion. -/
private theorem binomialForward_tprod_pi
    {R : Type uR} [CommSemiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {N : Type uN} [AddCommMonoid N] [Module R N]
    (n : ℕ) (x : ULift.{uR} (Fin n) → M × N) :
    DirectSum.linearEquivFunOnFintype R (Fin (n + 1))
      (fun j : Fin (n + 1) =>
        SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
          SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N)
      (binomialLinearMap R M N n (tprod R x)) =
      (fun i =>
        ∑ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val},
          blockValue (R := R) s.val
            (subsetEnumeration s.val s.property)
            (subsetEnumeration (k := n - i.val) s.valᶜ
              (by simp [Finset.card_compl, s.property])) x) := by
  rw [binomialForward_tprod_sum_grouped]
  let D := fun i : Fin (n + 1) =>
    SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
      SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N
  let T := ⨁ i : Fin (n + 1), D i
  let E := DirectSum.linearEquivFunOnFintype R (Fin (n + 1)) D
  let v : ∀ i : Fin (n + 1), D i := fun i =>
    ∑ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val},
      blockValue (R := R) s.val
        (subsetEnumeration s.val s.property)
        (subsetEnumeration (k := n - i.val) s.valᶜ
          (by simp [Finset.card_compl, s.property])) x
  change E (∑ i : Fin (n + 1), DirectSum.lof R (Fin (n + 1)) D i (v i)) = v
  funext j
  let ev : Multiplicative T →* Multiplicative (D j) :=
    { toFun := fun y =>
        Multiplicative.ofAdd ((E ((Multiplicative.ofAdd : T ≃ Multiplicative T).symm y)) j)
      map_one' := by
        change Multiplicative.ofAdd ((E 0) j) = 1
        rw [E.map_zero]
        rfl
      map_mul' := by
        intro y z
        change Multiplicative.ofAdd
            ((E ((Multiplicative.ofAdd : T ≃ Multiplicative T).symm y +
              (Multiplicative.ofAdd : T ≃ Multiplicative T).symm z)) j) = _
        rw [E.map_add]
        rfl }
  apply (Multiplicative.ofAdd : D j ≃ Multiplicative (D j)).injective
  change ev (Multiplicative.ofAdd
      (∑ i : Fin (n + 1), DirectSum.lof R (Fin (n + 1)) D i (v i))) =
    Multiplicative.ofAdd (v j)
  rw [ofAdd_sum, map_prod]
  calc
    _ = ev (Multiplicative.ofAdd (DirectSum.lof R (Fin (n + 1)) D j (v j))) := by
      apply Finset.prod_eq_single_of_mem j (Finset.mem_univ j)
      intro i hi hne
      change Multiplicative.ofAdd
          ((E (DirectSum.lof R (Fin (n + 1)) D i (v i))) j) = 1
      rw [DirectSum.linearEquivFunOnFintype_lof]
      simp [Ne.symm hne]
    _ = Multiplicative.ofAdd (v j) := by
      change Multiplicative.ofAdd
          ((E (DirectSum.lof R (Fin (n + 1)) D j (v j))) j) = _
      rw [DirectSum.linearEquivFunOnFintype_lof]
      simp

/-- Evaluation of any component of the binomial expansion of a labelled product. -/
private theorem binomialForward_tprod_component
    {R : Type uR} [CommSemiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {N : Type uN} [AddCommMonoid N] [Module R N]
    (n : ℕ) (i : Fin (n + 1)) (x : ULift.{uR} (Fin n) → M × N) :
    (binomialLinearMap R M N n (tprod R x)) i =
      ∑ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val},
        blockValue (R := R) s.val
          (subsetEnumeration s.val s.property)
          (subsetEnumeration (k := n - i.val) s.valᶜ
            (by simp [Finset.card_compl, s.property])) x := by
  let D := fun i : Fin (n + 1) =>
    SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
      SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N
  let E := DirectSum.linearEquivFunOnFintype R (Fin (n + 1)) D
  let y := binomialLinearMap R M N n (tprod R x)
  let v : ∀ j : Fin (n + 1), D j := fun j =>
    ∑ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = j.val},
      blockValue (R := R) s.val
        (subsetEnumeration s.val s.property)
        (subsetEnumeration (k := n - j.val) s.valᶜ
          (by simp [Finset.card_compl, s.property])) x
  have hp : E y = v := binomialForward_tprod_pi n x
  have hc : (fun j => y j) = v := by
    apply E.symm.injective
    calc
      E.symm (fun j => y j) = y :=
        DirectSum.linearEquivFunOnFintype_symm_coe R (Fin (n + 1)) D y
      _ = E.symm v := by
        apply E.injective
        simpa only [E.apply_symm_apply] using hp
  exact congrFun hc i

end

end SymmetricPower

namespace SymmetricPower

noncomputable section

/-- A wrong subset in a separated-support tensor term forces a zero factor. -/
private theorem tensorBlock_wrong_support_zero
    {R : Type uR} [CommSemiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {N : Type uN} [AddCommMonoid N] [Module R N]
    {n : ℕ} {J K : Type uR}
    (s : Finset (ULift.{uR} (Fin n)))
    (T : Set (ULift.{uR} (Fin n)))
    (a : J ≃ s) (b : K ≃ ↥(sᶜ))
    (x : ULift.{uR} (Fin n) → M × N)
    (hM : ∀ q, q ∉ T → (x q).1 = 0)
    (hN : ∀ q, q ∈ T → (x q).2 = 0)
    (hne : (s : Set (ULift.{uR} (Fin n))) ≠ T) :
    (SymmetricPower.tprod R (fun j => (x (a j).val).1) ⊗ₜ[R]
      SymmetricPower.tprod R (fun l => (x (b l).val).2)) = 0 := by
  classical
  have hmismatch :
      (∃ q, q ∈ s ∧ q ∉ T) ∨ (∃ q, q ∈ T ∧ q ∉ s) := by
    by_cases h : ∃ q, q ∈ s ∧ q ∉ T
    · exact Or.inl h
    · right
      by_contra h'
      apply hne
      ext q
      constructor
      · intro hqs
        by_contra hqT
        exact h ⟨q, hqs, hqT⟩
      · intro hqT
        by_contra hqs
        exact h' ⟨q, hqT, hqs⟩
  rcases hmismatch with ⟨q, hqs, hqT⟩ | ⟨q, hqT, hqs⟩
  · have hz :
        SymmetricPower.tprod R (fun j => (x (a j).val).1) = 0 := by
      apply (SymmetricPower.tprod R).map_coord_zero
        (a.symm ⟨q, hqs⟩)
      rw [a.apply_symm_apply]
      exact hM q hqT
    rw [hz, TensorProduct.zero_tmul]
  · have hqc : q ∈ sᶜ := Finset.mem_compl.mpr hqs
    have hz :
        SymmetricPower.tprod R (fun l => (x (b l).val).2) = 0 := by
      apply (SymmetricPower.tprod R).map_coord_zero
        (b.symm ⟨q, hqc⟩)
      rw [b.apply_symm_apply]
      exact hN q hqT
    rw [hz, TensorProduct.tmul_zero]

/-- A subset other than the left labels contributes zero on a
separated family of inl/inr generators. -/
private theorem tensorBlock_separated_zero
    {R : Type uR} [CommSemiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {N : Type uN} [AddCommMonoid N] [Module R N]
    {n : ℕ} {A B J K : Type uR}
    (e : (A ⊕ B) ≃ ULift.{uR} (Fin n))
    (s : Finset (ULift.{uR} (Fin n)))
    (a : J ≃ s) (b : K ≃ ↥(sᶜ))
    (m : A → M) (z : B → N)
    (hne : (s : Set (ULift.{uR} (Fin n))) ≠
      {q | ∃ a₀, e.symm q = Sum.inl a₀}) :
    (SymmetricPower.tprod R
        (fun j =>
          (Sum.elim (fun a₀ => (m a₀, (0 : N)))
            (fun b₀ => ((0 : M), z b₀)) (e.symm (a j).val)).1) ⊗ₜ[R]
      SymmetricPower.tprod R
        (fun l =>
          (Sum.elim (fun a₀ => (m a₀, (0 : N)))
            (fun b₀ => ((0 : M), z b₀)) (e.symm (b l).val)).2)) = 0 := by
  classical
  refine tensorBlock_wrong_support_zero (R := R) s
    {q | ∃ a₀, e.symm q = Sum.inl a₀} a b
    (fun q => Sum.elim (fun a₀ => (m a₀, (0 : N)))
      (fun b₀ => ((0 : M), z b₀)) (e.symm q)) ?_ ?_ hne
  · intro q hnot
    cases hq : e.symm q with
    | inl a₀ =>
        exact False.elim (hnot ⟨a₀, hq⟩)
    | inr b₀ =>
        rfl
  · intro q hleft
    rcases hleft with ⟨a₀, hq⟩
    rw [hq]
    rfl

variable {R : Type uR} [CommSemiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {N : Type uN} [AddCommMonoid N] [Module R N]

/-- Glues an enumeration of a subset and an enumeration of its complement. -/
private def subsetSplitEquiv
    {I J K : Type uR} [Fintype I] [DecidableEq I]
    (s : Finset I) (a : J ≃ s) (b : K ≃ ↥(sᶜ)) : J ⊕ K ≃ I where
  toFun := Sum.elim (fun j => (a j).val) (fun k => (b k).val)
  invFun := fun q =>
    if hq : q ∈ s then Sum.inl (a.symm ⟨q, hq⟩)
    else Sum.inr (b.symm ⟨q, by simpa only [Finset.mem_compl] using hq⟩)
  left_inv := by
    rintro (j | k)
    · have hj : (a j).val ∈ s := (a j).property
      simp [hj]
    · have hk : (b k).val ∉ s := Finset.mem_compl.mp (b k).property
      simp [hk]
  right_inv := by
    intro q
    by_cases hq : q ∈ s <;> simp [hq]

/-- The glued family is the piecewise family of finite multilinearity. -/
private theorem subsetSplitEquiv_family
    {I J K : Type uR} [Fintype I] [DecidableEq I]
    (s : Finset I) (a : J ≃ s) (b : K ≃ ↥(sᶜ)) (x : I → M × N) :
    (fun q =>
      Sum.elim (fun j => ((x (a j).val).1, (0 : N)))
        (fun k => ((0 : M), (x (b k).val).2))
        ((subsetSplitEquiv s a b).symm q)) =
      s.piecewise (fun q => ((x q).1, (0 : N)))
        (fun q => ((0 : M), (x q).2)) := by
  funext q
  by_cases hq : q ∈ s <;> simp [subsetSplitEquiv, hq]

/-- A finite subset belongs to the unique degree given by its cardinality. -/
private def subsetsByCard (n : ℕ) :
    (Σ i : Fin (n + 1),
      {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val}) ≃
        Finset (ULift.{uR} (Fin n)) where
  toFun := fun p => p.2.val
  invFun := fun s =>
    ⟨⟨s.card, by
      have hs : s.card ≤ n := by
        simpa only [Fintype.card_ulift, Fintype.card_fin] using
          (Finset.card_le_univ s)
      exact Nat.lt_succ_of_le hs⟩, ⟨s, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨i, hi⟩, s, hs⟩
    dsimp only at hs ⊢
    subst i
    rfl
  right_inv := by
    intro s
    rfl

/-- Assembly of one canonical forward tensor is its piecewise product. -/
private theorem binomialAssembly_sizedBlock
    (n : ℕ) (i : Fin (n + 1))
    (s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val})
    (x : ULift.{uR} (Fin n) → M × N) :
    binomialAssembly (R := R) (M := M) (N := N) n
        (DirectSum.lof R (Fin (n + 1))
          (fun j : Fin (n + 1) =>
            SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
              SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N)
          i (blockValue (R := R) s.val
            (subsetEnumeration s.val s.property)
            (subsetEnumeration (k := n - i.val) s.valᶜ
              (by simp [Finset.card_compl, s.property])) x)) =
      tprod R (s.val.piecewise (fun q => ((x q).1, (0 : N)))
        (fun q => ((0 : M), (x q).2))) := by
  let a : ULift.{uR} (Fin i.val) ≃ s.val :=
    subsetEnumeration s.val s.property
  let b : ULift.{uR} (Fin (n - i.val)) ≃ ↥(s.valᶜ) :=
    subsetEnumeration (k := n - i.val) s.valᶜ (by simp [Finset.card_compl, s.property])
  exact
    (binomialAssembly_lof_tprod (R := R) (M := M) (N := N) n i
      (subsetSplitEquiv s.val a b)
      (fun j => (x (a j).val).1) (fun k => (x (b k).val).2)).trans
      (congrArg (tprod R) (subsetSplitEquiv_family s.val a b x))

/-- Assembly of all subset terms recovers the labelled product. -/
private theorem binomialAssembly_sum_sizedBlocks
    (n : ℕ) (x : ULift.{uR} (Fin n) → M × N) :
    binomialAssembly (R := R) (M := M) (N := N) n
        (∑ i : Fin (n + 1),
          ∑ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val},
            DirectSum.lof R (Fin (n + 1))
              (fun j : Fin (n + 1) =>
                SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
                  SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N)
              i (blockValue (R := R) s.val
                (subsetEnumeration s.val s.property)
                (subsetEnumeration (k := n - i.val) s.valᶜ
                  (by simp [Finset.card_compl, s.property])) x)) =
      tprod R x := by
  let I := ULift.{uR} (Fin n)
  let D := fun i : Fin (n + 1) =>
    SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
      SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N
  let T := ⨁ i : Fin (n + 1), D i
  let V := SymmetricPower R I (M × N)
  let A := binomialAssembly (R := R) (M := M) (N := N) n
  let v (i : Fin (n + 1))
      (s : {s : Finset I // s.card = i.val}) : T :=
    DirectSum.lof R (Fin (n + 1)) D i
      (blockValue (R := R) s.val
        (subsetEnumeration s.val s.property)
        (subsetEnumeration (k := n - i.val) s.valᶜ
          (by simp [Finset.card_compl, s.property, I])) x)
  let W (s : Finset I) : V :=
    tprod R (s.piecewise (fun q => ((x q).1, (0 : N)))
      (fun q => ((0 : M), (x q).2)))
  let tA : Multiplicative T →* Multiplicative V :=
    { toFun := fun y => Multiplicative.ofAdd
        (A ((Multiplicative.ofAdd : T ≃ Multiplicative T).symm y))
      map_one' := by
        change Multiplicative.ofAdd (A 0) = 1
        rw [A.map_zero]
        rfl
      map_mul' := by
        intro y z
        change Multiplicative.ofAdd
            (A ((Multiplicative.ofAdd : T ≃ Multiplicative T).symm y +
              (Multiplicative.ofAdd : T ≃ Multiplicative T).symm z)) = _
        rw [A.map_add]
        rfl }
  have hmap :
      A (∑ i : Fin (n + 1), ∑ s : {s : Finset I // s.card = i.val}, v i s) =
        ∑ i : Fin (n + 1), ∑ s : {s : Finset I // s.card = i.val}, W s.val := by
    apply (Multiplicative.ofAdd : V ≃ Multiplicative V).injective
    change tA (Multiplicative.ofAdd
        (∑ i : Fin (n + 1), ∑ s : {s : Finset I // s.card = i.val}, v i s)) = _
    rw [ofAdd_sum, ofAdd_sum, map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    change tA (Multiplicative.ofAdd
        (∑ s : {s : Finset I // s.card = i.val}, v i s)) = _
    rw [ofAdd_sum, ofAdd_sum, map_prod]
    apply Finset.prod_congr rfl
    intro s hs
    exact congrArg (fun z : V => Multiplicative.ofAdd z)
      (binomialAssembly_sizedBlock n i s x)
  have hcard :
      (∑ i : Fin (n + 1), ∑ s : {s : Finset I // s.card = i.val}, W s.val) =
        ∑ s : Finset I, W s := by
    apply (Multiplicative.ofAdd : V ≃ Multiplicative V).injective
    simp only [ofAdd_sum]
    calc
      _ = ∏ p : (Σ i : Fin (n + 1), {s : Finset I // s.card = i.val}),
          Multiplicative.ofAdd (W p.2.val) :=
        (Fintype.prod_sigma
          (fun p : (Σ i : Fin (n + 1), {s : Finset I // s.card = i.val}) =>
            Multiplicative.ofAdd (W p.2.val))).symm
      _ = ∏ s : Finset I, Multiplicative.ofAdd (W s) := by
        exact Fintype.prod_equiv (subsetsByCard.{uR} n) _ _ (fun _ => rfl)
  have hexpand : (∑ s : Finset I, W s) = tprod R x := by
    let m : I → M × N := fun q => ((x q).1, 0)
    let z : I → M × N := fun q => (0, (x q).2)
    have hsplit : m + z = x := by
      funext q
      exact Prod.ext (add_zero _) (zero_add _)
    have h := (tprod R (ι := I) (M := M × N)).map_add_univ m z
    rw [hsplit] at h
    simpa only [W, m, z] using h.symm
  change A (∑ i : Fin (n + 1), ∑ s : {s : Finset I // s.card = i.val}, v i s) =
    tprod R x
  exact hmap.trans (hcard.trans hexpand)

private theorem binomialAssembly_binomialLinearMap_tprod
    (n : ℕ) (x : ULift.{uR} (Fin n) → M × N) :
    binomialAssembly (R := R) (M := M) (N := N) n
        (binomialLinearMap R M N n (tprod R x)) = tprod R x := by
  rw [binomialForward_tprod_sum]
  exact binomialAssembly_sum_sizedBlocks n x

private theorem binomialAssembly_comp_binomialLinearMap (n : ℕ) :
    (binomialAssembly (R := R) (M := M) (N := N) n).comp
      (binomialLinearMap R M N n) = LinearMap.id := by
  apply SymmetricPower.hom_ext
  intro x
  change binomialAssembly (R := R) (M := M) (N := N) n
      (binomialLinearMap R M N n (tprod R x)) = tprod R x
  exact binomialAssembly_binomialLinearMap_tprod n x

/-- The right composite fixes each injected tensor of labelled generators. -/
private theorem binomialLinearMap_assembly_lof_tprod
    (n : Nat) (i : Fin (n + 1))
    (m : ULift.{uR} (Fin i.val) → M)
    (z : ULift.{uR} (Fin (n - i.val)) → N) :
    binomialLinearMap R M N n
      (binomialAssembly (R := R) (M := M) (N := N) n
        (DirectSum.lof R (Fin (n + 1))
          (fun j : Fin (n + 1) =>
            SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
              SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N)
          i (tprod R m ⊗ₜ[R] tprod R z))) =
      DirectSum.lof R (Fin (n + 1))
        (fun j : Fin (n + 1) =>
          SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
            SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N)
        i (tprod R m ⊗ₜ[R] tprod R z) := by
  let I := ULift.{uR} (Fin n)
  let A := ULift.{uR} (Fin i.val)
  let C := ULift.{uR} (Fin (n - i.val))
  let D := fun j : Fin (n + 1) =>
    SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
      SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N
  let e : (A ⊕ C) ≃ I := degreeSplitEquiv.{uR} n i
  let x : I → M × N := fun q =>
    Sum.elim (fun a => (m a, (0 : N)))
      (fun c => ((0 : M), z c)) (e.symm q)
  let w : D i := tprod R m ⊗ₜ[R] tprod R z
  let leftEmbedding : A ↪ I :=
    ⟨fun a => e (Sum.inl a), by
      intro a a' h
      exact Sum.inl.inj (e.injective h)⟩
  let L : Finset I := Finset.univ.map leftEmbedding
  have cardL : L.card = i.val := by
    change (Finset.univ.map leftEmbedding).card = i.val
    rw [Finset.card_map]
    change Fintype.card A = i.val
    simp only [A, Fintype.card_ulift, Fintype.card_fin]
  have memL (q : I) : q ∈ L ↔ ∃ a : A, e.symm q = Sum.inl a := by
    constructor
    · intro h
      rcases Finset.mem_map.mp h with ⟨a, _, ha⟩
      change e (Sum.inl a) = q at ha
      exact ⟨a, by rw [← ha, e.symm_apply_apply]⟩
    · rintro ⟨a, ha⟩
      apply Finset.mem_map.mpr
      refine ⟨a, Finset.mem_univ a, ?_⟩
      change e (Sum.inl a) = q
      rw [← ha, e.apply_symm_apply]
  -- Enumeration of the left labels.
  let fA : A → L := fun a =>
    ⟨e (Sum.inl a), (memL _).mpr ⟨a, e.symm_apply_apply _⟩⟩
  have hfA : Function.Bijective fA := by
    constructor
    · intro a a' h
      apply Sum.inl.inj
      apply e.injective
      exact congrArg Subtype.val h
    · intro q
      rcases (memL q.val).mp q.property with ⟨a, ha⟩
      refine ⟨a, Subtype.ext ?_⟩
      change e (Sum.inl a) = q.val
      rw [← ha, e.apply_symm_apply]
  let a₀ : A ≃ L := Equiv.ofBijective fA hfA
  have a₀_apply (a : A) : a₀ a = fA a := by
    apply a₀.symm.injective
    rw [a₀.symm_apply_apply]
    exact (Equiv.ofBijective_symm_apply_apply fA hfA a).symm
  have a₀_val (a : A) : (a₀ a).val = e (Sum.inl a) := by
    simpa only [fA] using congrArg Subtype.val (a₀_apply a)
  -- Enumeration of the complementary labels.
  have memRight (c : C) : e (Sum.inr c) ∈ Lᶜ := by
    apply Finset.mem_compl.mpr
    intro h
    rcases (memL _).mp h with ⟨a, ha⟩
    have hbad : (Sum.inr c : A ⊕ C) = Sum.inl a := by
      simpa only [Equiv.symm_apply_apply] using ha
    cases hbad
  let fC : C → ↥(Lᶜ) := fun c => ⟨e (Sum.inr c), memRight c⟩
  have hfC : Function.Bijective fC := by
    constructor
    · intro c c' h
      apply Sum.inr.inj
      apply e.injective
      exact congrArg Subtype.val h
    · intro q
      cases hq : e.symm q.val with
      | inl a =>
          exact False.elim
            ((Finset.mem_compl.mp q.property) ((memL _).mpr ⟨a, hq⟩))
      | inr c =>
          refine ⟨c, Subtype.ext ?_⟩
          change e (Sum.inr c) = q.val
          rw [← hq, e.apply_symm_apply]
  let b₀ : C ≃ ↥(Lᶜ) := Equiv.ofBijective fC hfC
  have b₀_apply (c : C) : b₀ c = fC c := by
    apply b₀.symm.injective
    rw [b₀.symm_apply_apply]
    exact (Equiv.ofBijective_symm_apply_apply fC hfC c).symm
  have b₀_val (c : C) : (b₀ c).val = e (Sum.inr c) := by
    simpa only [fC] using congrArg Subtype.val (b₀_apply c)
  -- Abbreviate the forward tensor terms.
  let W (j : Fin (n + 1))
      (s : {s : Finset I // s.card = j.val}) : D j :=
    blockValue (R := R) s.val
      (subsetEnumeration s.val s.property)
      (subsetEnumeration (k := n - j.val) s.valᶜ
        (by simp [Finset.card_compl, s.property, I])) x
  have wrong (j : Fin (n + 1))
      (s : {s : Finset I // s.card = j.val})
      (hSL : s.val ≠ L) : W j s = 0 := by
    have hsupport : (s.val : Set I) ≠
        {q | ∃ a : A, e.symm q = Sum.inl a} := by
      intro h
      apply hSL
      ext q
      change q ∈ (s.val : Set I) ↔ q ∈ L
      rw [h]
      exact (memL q).symm
    simpa only [W, blockValue, x] using
      (tensorBlock_separated_zero (R := R) e s.val
        (subsetEnumeration s.val s.property)
        (subsetEnumeration (k := n - j.val) s.valᶜ
          (by simp [Finset.card_compl, s.property, I])) m z hsupport)
  let ell : {s : Finset I // s.card = i.val} := ⟨L, cardL⟩
  let a : A ≃ L := subsetEnumeration L cardL
  let b : C ≃ ↥(Lᶜ) := subsetEnumeration (k := n - i.val) Lᶜ
    (by simp [Finset.card_compl, cardL, I])
  let pM : Equiv.Perm A := a.trans a₀.symm
  let pN : Equiv.Perm C := b.trans b₀.symm
  have heA (u : A) : e.symm (a u).val = Sum.inl (pM u) := by
    have h := congrArg Subtype.val (a₀.apply_symm_apply (a u))
    rw [a₀_val] at h
    change e (Sum.inl (pM u)) = (a u).val at h
    rw [← h, e.symm_apply_apply]
  have heC (u : C) : e.symm (b u).val = Sum.inr (pN u) := by
    have h := congrArg Subtype.val (b₀.apply_symm_apply (b u))
    rw [b₀_val] at h
    change e (Sum.inr (pN u)) = (b u).val at h
    rw [← h, e.symm_apply_apply]
  have hM : tprod R (fun u => (x (a u).val).1) = tprod R m := by
    calc
      _ = tprod R (fun u => m (pM u)) := by
        apply congrArg (tprod R)
        funext u
        change
          (Sum.elim (fun a => (m a, (0 : N)))
            (fun c => ((0 : M), z c)) (e.symm (a u).val)).1 = m (pM u)
        rw [heA u]
        rfl
      _ = _ := tprod_equiv (R := R) pM m
  have hN : tprod R (fun u => (x (b u).val).2) = tprod R z := by
    calc
      _ = tprod R (fun u => z (pN u)) := by
        apply congrArg (tprod R)
        funext u
        change
          (Sum.elim (fun a => (m a, (0 : N)))
            (fun c => ((0 : M), z c)) (e.symm (b u).val)).2 = z (pN u)
        rw [heC u]
        rfl
      _ = _ := tprod_equiv (R := R) pN z
  have matching : W i ell = w := by
    change
      (tprod R (fun u => (x (a u).val).1) ⊗ₜ[R]
        tprod R (fun u => (x (b u).val).2)) = w
    rw [hM, hN]
  -- Off degree: cardinality rules out the one potentially surviving subset.
  have sum_other (j : Fin (n + 1)) (hji : j ≠ i) :
      (∑ s : {s : Finset I // s.card = j.val}, W j s) = 0 := by
    apply (Multiplicative.ofAdd : D j ≃ Multiplicative (D j)).injective
    rw [ofAdd_sum]
    change (∏ s, Multiplicative.ofAdd (W j s)) = 1
    apply Finset.prod_eq_one
    intro s hs
    have hSL : s.val ≠ L := by
      intro h
      have hv : j.val = i.val := by
        calc
          j.val = s.val.card := s.property.symm
          _ = L.card := congrArg Finset.card h
          _ = i.val := cardL
      exact hji (Fin.ext hv)
    rw [wrong j s hSL]
    rfl
  -- Matching degree: exactly ell survives, with coefficient one.
  have sum_same :
      (∑ s : {s : Finset I // s.card = i.val}, W i s) = w := by
    apply (Multiplicative.ofAdd : D i ≃ Multiplicative (D i)).injective
    rw [ofAdd_sum]
    calc
      _ = Multiplicative.ofAdd (W i ell) := by
        apply Finset.prod_eq_single_of_mem ell (Finset.mem_univ ell)
        intro s hs hne
        have hSL : s.val ≠ L := by
          intro h
          apply hne
          apply Subtype.ext
          exact h
        rw [wrong i s hSL]
        rfl
      _ = Multiplicative.ofAdd w :=
        congrArg (fun y : D i => Multiplicative.ofAdd y) matching
  -- Apply the calculation to the expansion and assembly maps.
  let E := DirectSum.linearEquivFunOnFintype R (Fin (n + 1)) D
  have hforward : E (binomialLinearMap R M N n (tprod R x)) =
      (fun j => ∑ s : {s : Finset I // s.card = j.val}, W j s) := by
    simpa only [E, W, I, D] using
      (binomialForward_tprod_pi (R := R) (M := M) (N := N) n x)
  have hlof : E (DirectSum.lof R (Fin (n + 1)) D i w) = Pi.single i w := by
    exact DirectSum.linearEquivFunOnFintype_lof
      (R := R) (ι := Fin (n + 1)) (M := D) i w
  change binomialLinearMap R M N n
      (binomialAssembly (R := R) (M := M) (N := N) n
        (DirectSum.lof R (Fin (n + 1)) D i w)) =
    DirectSum.lof R (Fin (n + 1)) D i w
  have hAssembly :=
    binomialAssembly_lof_tprod (R := R) (M := M) (N := N) n i e m z
  change binomialAssembly (R := R) (M := M) (N := N) n
      (DirectSum.lof R (Fin (n + 1)) D i w) = tprod R x at hAssembly
  rw [hAssembly]
  apply E.injective
  rw [hforward, hlof]
  funext j
  by_cases hji : j = i
  · subst j
    simpa using sum_same
  · simpa [hji, Ne.symm hji] using sum_other j hji

/-- The binomial expansion is a right inverse to block assembly. -/
private theorem binomialLinearMap_comp_assembly (n : Nat) :
    (binomialLinearMap R M N n).comp
      (binomialAssembly (R := R) (M := M) (N := N) n) =
        LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro i
  apply TensorProduct.ext
  apply SymmetricPower.hom_ext
  intro m
  apply SymmetricPower.hom_ext
  intro z
  change
    binomialLinearMap R M N n
      (binomialAssembly (R := R) (M := M) (N := N) n
        (DirectSum.lof R (Fin (n + 1))
          (fun j : Fin (n + 1) =>
            SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
              SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N)
          i (tprod R m ⊗ₜ[R] tprod R z))) =
      DirectSum.lof R (Fin (n + 1))
        (fun j : Fin (n + 1) =>
          SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
            SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N)
        i (tprod R m ⊗ₜ[R] tprod R z)
  exact binomialLinearMap_assembly_lof_tprod n i m z

/-- The binomial decomposition of the symmetric power of a product module.
See Weibel, *The K-book: An Introduction to Algebraic K-theory*. This version
applies to arbitrary semimodules over a commutative semiring. -/
def binomialEquiv (n : ℕ) :
    SymmetricPower R (ULift.{uR} (Fin n)) (M × N) ≃ₗ[R]
      (⨁ j : Fin (n + 1),
      SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N) :=
  LinearEquiv.ofLinearMap
    (binomialLinearMap R M N n)
    (binomialAssembly (R := R) (M := M) (N := N) n)
    (binomialLinearMap_comp_assembly (R := R) (M := M) (N := N) n)
    (binomialAssembly_comp_binomialLinearMap (R := R) (M := M) (N := N) n)

/-- The tensor associated to a labelled subset is independent of its enumerations. -/
private theorem blockValue_enumeration
    {R : Type uR} [CommSemiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {N : Type uN} [AddCommMonoid N] [Module R N]
    {I J K : Type uR} [Fintype I] [DecidableEq I]
    (s : Finset I) (a a' : J ≃ s) (b b' : K ≃ ↥(sᶜ))
    (x : I → M × N) :
    blockValue (R := R) s a b x = blockValue (R := R) s a' b' x := by
  let pM : Equiv.Perm J := a.trans a'.symm
  let pN : Equiv.Perm K := b.trans b'.symm
  have hpM (j : J) : a' (pM j) = a j := by
    change a' (a'.symm (a j)) = a j
    exact a'.apply_symm_apply (a j)
  have hpN (k : K) : b' (pN k) = b k := by
    change b' (b'.symm (b k)) = b k
    exact b'.apply_symm_apply (b k)
  have hM :
      tprod R (fun j => (x (a j).val).1) =
        tprod R (fun j => (x (a' j).val).1) := by
    calc
      _ = tprod R (fun j => (x (a' (pM j)).val).1) := by
        apply congrArg (tprod R)
        funext j
        rw [hpM j]
      _ = _ := tprod_equiv (R := R) pM (fun j => (x (a' j).val).1)
  have hN :
      tprod R (fun k => (x (b k).val).2) =
        tprod R (fun k => (x (b' k).val).2) := by
    calc
      _ = tprod R (fun k => (x (b' (pN k)).val).2) := by
        apply congrArg (tprod R)
        funext k
        rw [hpN k]
      _ = _ := tprod_equiv (R := R) pN (fun k => (x (b' k).val).2)
  change
    (tprod R (fun j => (x (a j).val).1) ⊗ₜ[R]
      tprod R (fun k => (x (b k).val).2)) =
    (tprod R (fun j => (x (a' j).val).1) ⊗ₜ[R]
      tprod R (fun k => (x (b' k).val).2))
  rw [hM, hN]

/-- Each component is the coefficient-one sum over subsets of its degree,
independently of the bijections used to enumerate the subsets and complements. -/
theorem binomialEquiv_tprod_component
    (n : ℕ) (i : Fin (n + 1))
    (a : ∀ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val}, ULift.{uR} (Fin i.val) ≃ ↥s.val)
    (b : ∀ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val},
      ULift.{uR} (Fin (n - i.val)) ≃ ↥(s.valᶜ))
    (x : ULift.{uR} (Fin n) → M × N) :
    ((binomialEquiv (R := R) (M := M) (N := N) n) (tprod R x)) i =
      ∑ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val},
        tprod R (fun p => (x (a s p).val).1) ⊗ₜ[R]
          tprod R (fun q => (x (b s q).val).2) := by
  classical
  change (binomialLinearMap R M N n (tprod R x)) i = _
  rw [binomialForward_tprod_component]
  apply congrArg
    (fun f : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val} →
        SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
          SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N =>
      ∑ s, f s)
  funext s
  exact blockValue_enumeration s.val
    (subsetEnumeration s.val s.property) (a s)
    (subsetEnumeration (k := n - i.val) s.valᶜ
      (by simp [Finset.card_compl, s.property])) (b s) x

/-- The full coefficient-one expansion, grouped by degree and subset. -/
theorem binomialEquiv_tprod_sum
    (n : ℕ)
    (a : ∀ (i : Fin (n + 1)) (s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val}),
      ULift.{uR} (Fin i.val) ≃ ↥s.val)
    (b : ∀ (i : Fin (n + 1)) (s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val}),
      ULift.{uR} (Fin (n - i.val)) ≃ ↥(s.valᶜ))
    (x : ULift.{uR} (Fin n) → M × N) :
    (binomialEquiv (R := R) (M := M) (N := N) n) (tprod R x) =
      ∑ i : Fin (n + 1), ∑ s : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val},
        DirectSum.lof R (Fin (n + 1))
          (fun j : Fin (n + 1) =>
          SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
            SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N) i
          (tprod R (fun p => (x (a i s p).val).1) ⊗ₜ[R]
            tprod R (fun q => (x (b i s q).val).2)) := by
  classical
  change binomialLinearMap R M N n (tprod R x) = _
  rw [binomialForward_tprod_sum]
  let D := fun j : Fin (n + 1) =>
    SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
      SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N
  apply congrArg
    (fun f : Fin (n + 1) → (⨁ j : Fin (n + 1), D j) => ∑ i, f i)
  funext i
  apply congrArg
    (fun f : {s : Finset (ULift.{uR} (Fin n)) // s.card = i.val} →
        (⨁ j : Fin (n + 1), D j) =>
      ∑ s, f s)
  funext s
  apply congrArg (DirectSum.lof R (Fin (n + 1)) D i)
  exact blockValue_enumeration s.val
    (subsetEnumeration s.val s.property) (a i s)
    (subsetEnumeration (k := n - i.val) s.valᶜ
      (by simp [Finset.card_compl, s.property])) (b i s) x

private theorem binomialEquiv_apply (n : ℕ)
    (x : SymmetricPower R (ULift.{uR} (Fin n)) (M × N)) :
    binomialEquiv (R := R) (M := M) (N := N) n x =
      binomialLinearMap R M N n x := rfl

private theorem binomialEquiv_symm_apply (n : ℕ)
    (s : ⨁ j : Fin (n + 1),
      SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N) :
    (binomialEquiv (R := R) (M := M) (N := N) n).symm s =
      binomialAssembly (R := R) (M := M) (N := N) n s := rfl

/-- The inverse assembles every labelled pure tensor using any bijection
from the two label blocks to the total label set. -/
theorem binomialEquiv_symm_lof_tprod
    (n : ℕ) (i : Fin (n + 1))
    (e : (ULift.{uR} (Fin i.val) ⊕ ULift.{uR} (Fin (n - i.val))) ≃
      ULift.{uR} (Fin n))
    (m : ULift.{uR} (Fin i.val) → M)
    (z : ULift.{uR} (Fin (n - i.val)) → N) :
    (binomialEquiv (R := R) (M := M) (N := N) n).symm
      (DirectSum.lof R (Fin (n + 1))
        (fun j : Fin (n + 1) =>
          SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
            SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N) i (tprod R m ⊗ₜ[R] tprod R z)) =
      tprod R (fun k : ULift.{uR} (Fin n) =>
        Sum.elim (fun p => (m p, (0 : N)))
          (fun q => ((0 : M), z q)) (e.symm k)) := by
  rw [binomialEquiv_symm_apply]
  exact binomialAssembly_lof_tprod (R := R) (M := M) (N := N) n i e m z

end

end SymmetricPower

namespace SymmetricPower

noncomputable section

universe uM' uN'

variable {R : Type uR} [CommSemiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {N : Type uN} [AddCommMonoid N] [Module R N]
variable {M' : Type uM'} [AddCommMonoid M'] [Module R M']
variable {N' : Type uN'} [AddCommMonoid N'] [Module R N']

private theorem tensor_hom_ext {I J : Type uR}
    {Q : Type uQ} [AddCommMonoid Q] [Module R Q]
    {F G : SymmetricPower R I M ⊗[R] SymmetricPower R J N →ₗ[R] Q}
    (h : ∀ (m : I → M) (z : J → N),
      F (tprod R m ⊗ₜ[R] tprod R z) =
        G (tprod R m ⊗ₜ[R] tprod R z)) : F = G := by
  apply TensorProduct.curry_injective
  apply hom_ext
  intro m
  apply hom_ext
  intro z
  simpa only [TensorProduct.curry_apply] using h m z

/-- Maps each symmetric degree block by its two module maps. -/
private def binomialDegreeMap (n : Nat) (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    (⨁ i : Fin (n + 1),
      SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N) →ₗ[R]
    (⨁ i : Fin (n + 1),
      SymmetricPower R (ULift.{uR} (Fin i.val)) M' ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (n - i.val))) N') :=
  DirectSum.toModule R (Fin (n + 1))
    (⨁ j : Fin (n + 1),
      SymmetricPower R (ULift.{uR} (Fin j.val)) M' ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N')
    (fun i =>
      (DirectSum.lof R (Fin (n + 1))
        (fun j : Fin (n + 1) =>
          SymmetricPower R (ULift.{uR} (Fin j.val)) M' ⊗[R]
            SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N')
        i).comp
        (TensorProduct.map
          (map (ι := ULift.{uR} (Fin i.val)) f)
          (map (ι := ULift.{uR} (Fin (n - i.val))) g)))

private theorem binomialDegreeMap_lof_tprod
    (n : Nat) (f : M →ₗ[R] M') (g : N →ₗ[R] N') (i : Fin (n + 1))
    (m : ULift.{uR} (Fin i.val) → M)
    (z : ULift.{uR} (Fin (n - i.val)) → N) :
    binomialDegreeMap n f g
        (DirectSum.lof R (Fin (n + 1))
          (fun j : Fin (n + 1) =>
            SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
              SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N)
          i (tprod R m ⊗ₜ[R] tprod R z)) =
      DirectSum.lof R (Fin (n + 1))
        (fun j : Fin (n + 1) =>
          SymmetricPower R (ULift.{uR} (Fin j.val)) M' ⊗[R]
            SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N')
        i (tprod R (fun a => f (m a)) ⊗ₜ[R]
          tprod R (fun b => g (z b))) := by
  simp [binomialDegreeMap, DirectSum.toModule_lof,
    TensorProduct.map_tmul, map_tprod]

/-- The symmetric-block assembly commutes with both module maps. -/
private theorem binomialAssembly_natural
    (n : Nat) (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    (map (ι := ULift.{uR} (Fin n)) (LinearMap.prodMap f g)).comp
        (binomialAssembly (R := R) (M := M) (N := N) n) =
      (binomialAssembly (R := R) (M := M') (N := N') n).comp
        (binomialDegreeMap n f g) := by
  apply DirectSum.linearMap_ext
  intro i
  apply tensor_hom_ext
  intro m z
  change
    map (ι := ULift.{uR} (Fin n)) (LinearMap.prodMap f g)
        (binomialAssembly (R := R) (M := M) (N := N) n
          (DirectSum.lof R (Fin (n + 1))
            (fun j : Fin (n + 1) =>
              SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
                SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N)
            i (tprod R m ⊗ₜ[R] tprod R z))) =
      binomialAssembly (R := R) (M := M') (N := N') n
        (binomialDegreeMap n f g
          (DirectSum.lof R (Fin (n + 1))
            (fun j : Fin (n + 1) =>
              SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
                SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N)
            i (tprod R m ⊗ₜ[R] tprod R z)))
  rw [binomialDegreeMap_lof_tprod]
  let e : (ULift.{uR} (Fin i.val) ⊕
      ULift.{uR} (Fin (n - i.val))) ≃ ULift.{uR} (Fin n) :=
    degreeSplitEquiv.{uR} n i
  rw [binomialAssembly_lof_tprod (R := R) (M := M) (N := N)
      n i e m z,
    binomialAssembly_lof_tprod (R := R) (M := M') (N := N')
      n i e (fun a => f (m a)) (fun b => g (z b)),
    map_tprod]
  apply congrArg
    (fun c : ULift.{uR} (Fin n) → M' × N' => tprod R c)
  funext k
  cases h : e.symm k <;> simp [LinearMap.prodMap_apply]

/-- Naturality of the binomial decomposition in both module variables. -/
theorem binomialEquiv_natural
    (n : ℕ) (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    (binomialEquiv (R := R) (M := M') (N := N') n).toLinearMap.comp
      (map (ι := ULift.{uR} (Fin n)) (LinearMap.prodMap f g)) =
    (DirectSum.toModule R (Fin (n + 1))
      (⨁ j : Fin (n + 1),
      SymmetricPower R (ULift.{uR} (Fin j.val)) M' ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N')
      (fun i =>
        (DirectSum.lof R (Fin (n + 1))
          (fun j : Fin (n + 1) =>
          SymmetricPower R (ULift.{uR} (Fin j.val)) M' ⊗[R]
            SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N') i).comp
          (TensorProduct.map
            (map (ι := ULift.{uR} (Fin i.val)) f)
            (map (ι := ULift.{uR} (Fin (n - i.val))) g)))).comp
      (binomialEquiv (R := R) (M := M) (N := N) n).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply (binomialEquiv (R := R) (M := M') (N := N') n).symm.injective
  change
    (binomialEquiv (R := R) (M := M') (N := N') n).symm
        (binomialEquiv (R := R) (M := M') (N := N') n
          (map (ι := ULift.{uR} (Fin n)) (LinearMap.prodMap f g) x)) =
      (binomialEquiv (R := R) (M := M') (N := N') n).symm
        (binomialDegreeMap n f g
          (binomialEquiv (R := R) (M := M) (N := N) n x))
  rw [LinearEquiv.symm_apply_apply, binomialEquiv_symm_apply]
  have hleft :
      binomialAssembly (R := R) (M := M) (N := N) n
        (binomialEquiv (R := R) (M := M) (N := N) n x) = x := by
    change (binomialEquiv (R := R) (M := M) (N := N) n).symm
      (binomialEquiv (R := R) (M := M) (N := N) n x) = x
    exact (binomialEquiv (R := R) (M := M) (N := N) n).symm_apply_apply x
  have h := congrArg
    (fun F :
        (⨁ j : Fin (n + 1),
          SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
            SymmetricPower R (ULift.{uR} (Fin (n - j.val))) N) →ₗ[R]
          SymmetricPower R (ULift.{uR} (Fin n)) (M' × N') =>
      F (binomialEquiv (R := R) (M := M) (N := N) n x))
    (binomialAssembly_natural (R := R) n f g)
  simpa only [LinearMap.comp_apply, hleft] using h

end

end SymmetricPower

namespace SymmetricPower

noncomputable section

variable {R : Type uR} [CommSemiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {N : Type uN} [AddCommMonoid N] [Module R N]

/-- Identifies the unique degree-zero tensor component with the scalar module. -/
private def binomialTargetZeroComponentEquiv (i : Fin 1) :
    (SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
      SymmetricPower R (ULift.{uR} (Fin (0 - i.val))) N) ≃ₗ[R] R := by
  rcases i with ⟨i, hi⟩
  have hi0 : i = 0 := by omega
  subst i
  exact
    (TensorProduct.congr
      (isEmptyEquiv (R := R) (ι := ULift.{uR} (Fin 0)) (M := M))
      (isEmptyEquiv (R := R) (ι := ULift.{uR} (Fin 0)) (M := N))).trans
      (TensorProduct.lid R R)

/-- The degree-zero binomial target, identified with the scalar module. -/
def binomialTargetZeroEquiv :
    (⨁ j : Fin (0 + 1),
      SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (0 - j.val))) N) ≃ₗ[R] R :=
  (DirectSum.linearEquivFunOnFintype R (Fin 1)
    (fun i : Fin 1 =>
      SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (0 - i.val))) N)).trans
    ((LinearEquiv.piCongrRight
      (fun i : Fin 1 => binomialTargetZeroComponentEquiv (R := R) (M := M) (N := N) i)).trans
      (LinearEquiv.funUnique (Fin 1) R R))

/-- The empty labelled products give the unit in the degree-zero target. -/
theorem binomialTargetZeroEquiv_lof_tprod (i : Fin (0 + 1))
    (m : ULift.{uR} (Fin i.val) → M)
    (z : ULift.{uR} (Fin (0 - i.val)) → N) :
    binomialTargetZeroEquiv (R := R) (M := M) (N := N)
      (DirectSum.lof R (Fin (0 + 1))
        (fun j : Fin (0 + 1) =>
          SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
            SymmetricPower R (ULift.{uR} (Fin (0 - j.val))) N)
        i (tprod R m ⊗ₜ[R] tprod R z)) = 1 := by
  rcases i with ⟨i, hi⟩
  have hi0 : i = 0 := by omega
  subst i
  simp [binomialTargetZeroEquiv, binomialTargetZeroComponentEquiv,
    DirectSum.linearEquivFunOnFintype_lof, LinearEquiv.funUnique_apply,
    LinearEquiv.piCongrRight_apply, TensorProduct.congr_tmul,
    TensorProduct.lid_tmul]

/-- The degree-one zero-index component is the second product factor. -/
private def binomialTargetOneLeftEquiv :
    (SymmetricPower R (ULift.{uR} (Fin 0)) M ⊗[R]
      SymmetricPower R (ULift.{uR} (Fin 1)) N) ≃ₗ[R] N :=
  (TensorProduct.congr
    (isEmptyEquiv (R := R) (ι := ULift.{uR} (Fin 0)) (M := M))
    (subsingletonEquiv (R := R) (M := N) (⟨0⟩ : ULift.{uR} (Fin 1)))).trans
    (TensorProduct.lid R N)

/-- The degree-one one-index component is the first product factor. -/
private def binomialTargetOneRightEquiv :
    (SymmetricPower R (ULift.{uR} (Fin 1)) M ⊗[R]
      SymmetricPower R (ULift.{uR} (Fin 0)) N) ≃ₗ[R] M :=
  (TensorProduct.congr
    (subsingletonEquiv (R := R) (M := M) (⟨0⟩ : ULift.{uR} (Fin 1)))
    (isEmptyEquiv (R := R) (ι := ULift.{uR} (Fin 0)) (M := N))).trans
    (TensorProduct.rid R M)

/-- The degree-one target in increasing degree order: the second module,
then the first module. -/
def binomialTargetOneEquiv :
    (⨁ j : Fin (1 + 1),
      SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (1 - j.val))) N) ≃ₗ[R] N × M :=
  (DirectSum.linearEquivFunOnFintype R (Fin 2)
    (fun i : Fin 2 =>
      SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (1 - i.val))) N)).trans
    ((LinearEquiv.piFinTwo R
      (fun i : Fin 2 =>
        SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
          SymmetricPower R (ULift.{uR} (Fin (1 - i.val))) N)).trans
      ((binomialTargetOneLeftEquiv (R := R) (M := M) (N := N)).prodCongr
        (binomialTargetOneRightEquiv (R := R) (M := M) (N := N))))

/-- The zero-index summand of the degree-one target is the second module. -/
theorem binomialTargetOneEquiv_lof_zero (z : N) :
    binomialTargetOneEquiv (R := R) (M := M) (N := N)
      (DirectSum.lof R (Fin (1 + 1))
        (fun j : Fin (1 + 1) =>
          SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
            SymmetricPower R (ULift.{uR} (Fin (1 - j.val))) N) 0
        (tprod R (fun p : ULift.{uR} (Fin 0) => isEmptyElim p) ⊗ₜ[R]
          tprod R (fun _ : ULift.{uR} (Fin 1) => z))) = (z, 0) := by
  simp [binomialTargetOneEquiv, binomialTargetOneLeftEquiv,
    binomialTargetOneRightEquiv, DirectSum.linearEquivFunOnFintype_lof,
    LinearEquiv.piFinTwo_apply, LinearEquiv.prodCongr_apply,
    TensorProduct.congr_tmul, TensorProduct.lid_tmul]

/-- The one-index summand of the degree-one target is the first module. -/
theorem binomialTargetOneEquiv_lof_one (m : M) :
    binomialTargetOneEquiv (R := R) (M := M) (N := N)
      (DirectSum.lof R (Fin (1 + 1))
        (fun j : Fin (1 + 1) =>
          SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
            SymmetricPower R (ULift.{uR} (Fin (1 - j.val))) N) 1
        (tprod R (fun _ : ULift.{uR} (Fin 1) => m) ⊗ₜ[R]
          tprod R (fun p : ULift.{uR} (Fin 0) => isEmptyElim p))) = (0, m) := by
  simp [binomialTargetOneEquiv, binomialTargetOneLeftEquiv,
    binomialTargetOneRightEquiv, DirectSum.linearEquivFunOnFintype_lof,
    LinearEquiv.piFinTwo_apply, LinearEquiv.prodCongr_apply,
    TensorProduct.congr_tmul, TensorProduct.rid_tmul]

/-- The assembly is the scalar identity in degree zero under the canonical units. -/
private theorem binomialAssembly_zero_normalized (r : R) :
    (isEmptyEquiv (R := R) (ι := ULift.{uR} (Fin 0)) (M := M × N))
      (binomialAssembly (R := R) (M := M) (N := N) 0
        ((binomialTargetZeroEquiv (R := R) (M := M) (N := N)).symm r)) = r := by
  let f : R →ₗ[R] R :=
    (isEmptyEquiv (R := R) (ι := ULift.{uR} (Fin 0)) (M := M × N)).toLinearMap.comp
      ((binomialAssembly (R := R) (M := M) (N := N) 0).comp
        (binomialTargetZeroEquiv (R := R) (M := M) (N := N)).symm.toLinearMap)
  change f r = r
  have hunit : f 1 = 1 := by
    let g := DirectSum.lof R (Fin 1)
      (fun j : Fin 1 =>
        SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
          SymmetricPower R (ULift.{uR} (Fin (0 - j.val))) N)
      0 (tprod R (fun a : ULift.{uR} (Fin 0) => isEmptyElim a) ⊗ₜ[R]
        tprod R (fun a : ULift.{uR} (Fin 0) => isEmptyElim a))
    have hg : binomialTargetZeroEquiv (R := R) (M := M) (N := N) g = 1 :=
      binomialTargetZeroEquiv_lof_tprod (R := R) (M := M) (N := N) 0 _ _
    have hpre : (binomialTargetZeroEquiv (R := R) (M := M) (N := N)).symm 1 = g := by
      apply (binomialTargetZeroEquiv (R := R) (M := M) (N := N)).injective
      simpa using hg.symm
    change (isEmptyEquiv (R := R) (ι := ULift.{uR} (Fin 0)) (M := M × N))
      (binomialAssembly (R := R) (M := M) (N := N) 0
        ((binomialTargetZeroEquiv (R := R) (M := M) (N := N)).symm 1)) = 1
    rw [hpre]
    simpa only [g, isEmptyEquiv_tprod] using
      congrArg (isEmptyEquiv (R := R) (ι := ULift.{uR} (Fin 0)) (M := M × N))
        (binomialAssembly_lof_tprod (R := R) (M := M) (N := N)
          0 0 (degreeSplitEquiv.{uR} 0 0)
          (fun a : ULift.{uR} (Fin 0) => isEmptyElim a)
          (fun a : ULift.{uR} (Fin 0) => isEmptyElim a))
  calc
    f r = f (r • (1 : R)) := by simp
    _ = r • f 1 := f.map_smul r (1 : R)
    _ = r := by rw [hunit]; simp

/-- The assembly swaps the two coordinates of the ordered degree-one target. -/
private theorem binomialAssembly_one_normalized (z : N) (m : M) :
    (subsingletonEquiv (R := R) (M := M × N) (⟨0⟩ : ULift.{uR} (Fin 1)))
      (binomialAssembly (R := R) (M := M) (N := N) 1
        ((binomialTargetOneEquiv (R := R) (M := M) (N := N)).symm (z, m))) =
      (m, z) := by
  let f : (N × M) →ₗ[R] M × N :=
    (subsingletonEquiv (R := R) (M := M × N)
      (⟨0⟩ : ULift.{uR} (Fin 1))).toLinearMap.comp
      ((binomialAssembly (R := R) (M := M) (N := N) 1).comp
        (binomialTargetOneEquiv (R := R) (M := M) (N := N)).symm.toLinearMap)
  change f (z, m) = (m, z)
  have hleft (z : N) : f (z, 0) = (0, z) := by
    let g := DirectSum.lof R (Fin 2)
      (fun j : Fin 2 =>
        SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
          SymmetricPower R (ULift.{uR} (Fin (1 - j.val))) N)
      0 (tprod R (fun a : ULift.{uR} (Fin 0) => isEmptyElim a) ⊗ₜ[R]
        tprod R (fun _ : ULift.{uR} (Fin 1) => z))
    have hg : binomialTargetOneEquiv (R := R) (M := M) (N := N) g = (z, 0) :=
      binomialTargetOneEquiv_lof_zero (R := R) (M := M) (N := N) z
    have hpre : (binomialTargetOneEquiv (R := R) (M := M) (N := N)).symm (z, 0) = g := by
      apply (binomialTargetOneEquiv (R := R) (M := M) (N := N)).injective
      simpa using hg.symm
    change (subsingletonEquiv (R := R) (M := M × N)
      (⟨0⟩ : ULift.{uR} (Fin 1)))
      (binomialAssembly (R := R) (M := M) (N := N) 1
        ((binomialTargetOneEquiv (R := R) (M := M) (N := N)).symm (z, 0))) = (0, z)
    rw [hpre]
    dsimp only [g]
    rw [binomialAssembly_lof_tprod (R := R) (M := M) (N := N)
      1 (0 : Fin 2) (degreeSplitEquiv.{uR} 1 0), subsingletonEquiv_tprod]
    change Sum.elim
      (fun a : ULift.{uR} (Fin 0) => (isEmptyElim a, (0 : N)))
      (fun _ : ULift.{uR} (Fin 1) => ((0 : M), z))
      ((degreeSplitEquiv.{uR} 1 0).symm (⟨0⟩ : ULift.{uR} (Fin 1))) = (0, z)
    cases h : (degreeSplitEquiv.{uR} 1 0).symm (⟨0⟩ : ULift.{uR} (Fin 1)) with
    | inl a => exact isEmptyElim (show ULift.{uR} (Fin 0) from a)
    | inr b => rfl
  have hright (m : M) : f (0, m) = (m, 0) := by
    let g := DirectSum.lof R (Fin 2)
      (fun j : Fin 2 =>
        SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
          SymmetricPower R (ULift.{uR} (Fin (1 - j.val))) N)
      1 (tprod R (fun _ : ULift.{uR} (Fin 1) => m) ⊗ₜ[R]
        tprod R (fun a : ULift.{uR} (Fin 0) => isEmptyElim a))
    have hg : binomialTargetOneEquiv (R := R) (M := M) (N := N) g = (0, m) :=
      binomialTargetOneEquiv_lof_one (R := R) (M := M) (N := N) m
    have hpre : (binomialTargetOneEquiv (R := R) (M := M) (N := N)).symm (0, m) = g := by
      apply (binomialTargetOneEquiv (R := R) (M := M) (N := N)).injective
      simpa using hg.symm
    change (subsingletonEquiv (R := R) (M := M × N)
      (⟨0⟩ : ULift.{uR} (Fin 1)))
      (binomialAssembly (R := R) (M := M) (N := N) 1
        ((binomialTargetOneEquiv (R := R) (M := M) (N := N)).symm (0, m))) = (m, 0)
    rw [hpre]
    dsimp only [g]
    rw [binomialAssembly_lof_tprod (R := R) (M := M) (N := N)
      1 (1 : Fin 2) (degreeSplitEquiv.{uR} 1 1), subsingletonEquiv_tprod]
    change Sum.elim
      (fun _ : ULift.{uR} (Fin 1) => (m, (0 : N)))
      (fun a : ULift.{uR} (Fin 0) => ((0 : M), isEmptyElim a))
      ((degreeSplitEquiv.{uR} 1 1).symm (⟨0⟩ : ULift.{uR} (Fin 1))) = (m, 0)
    cases h : (degreeSplitEquiv.{uR} 1 1).symm (⟨0⟩ : ULift.{uR} (Fin 1)) with
    | inl a => rfl
    | inr b => exact isEmptyElim (show ULift.{uR} (Fin 0) from b)
  calc
    f (z, m) = f ((z, 0) + (0, m)) := by simp
    _ = f (z, 0) + f (0, m) := f.map_add _ _
    _ = (0, z) + (m, 0) := by rw [hleft, hright]
    _ = (m, z) := by simp

/-- The degree-zero assembly square commutes with the canonical unit maps. -/
private theorem binomialAssembly_zero_square
    (s : ⨁ i : Fin 1,
      SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (0 - i.val))) N) :
    (isEmptyEquiv (R := R) (ι := ULift.{uR} (Fin 0)) (M := M × N))
      (binomialAssembly (R := R) (M := M) (N := N) 0 s) =
      binomialTargetZeroEquiv (R := R) (M := M) (N := N) s := by
  simpa using binomialAssembly_zero_normalized (R := R) (M := M) (N := N)
    (binomialTargetZeroEquiv (R := R) (M := M) (N := N) s)

/-- The degree-one assembly square commutes after swapping target coordinates. -/
private theorem binomialAssembly_one_square
    (s : ⨁ i : Fin 2,
      SymmetricPower R (ULift.{uR} (Fin i.val)) M ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (1 - i.val))) N) :
    (subsingletonEquiv (R := R) (M := M × N) (⟨0⟩ : ULift.{uR} (Fin 1)))
      (binomialAssembly (R := R) (M := M) (N := N) 1 s) =
      ((binomialTargetOneEquiv (R := R) (M := M) (N := N) s).2,
        (binomialTargetOneEquiv (R := R) (M := M) (N := N) s).1) := by
  simpa using binomialAssembly_one_normalized (R := R) (M := M) (N := N)
    (binomialTargetOneEquiv (R := R) (M := M) (N := N) s).1
    (binomialTargetOneEquiv (R := R) (M := M) (N := N) s).2

/-- The normalized inverse in degree zero is the identity of the scalars. -/
theorem binomialEquiv_symm_zero (s : (⨁ j : Fin (0 + 1),
      SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (0 - j.val))) N)) :
    isEmptyEquiv (R := R) (ι := ULift.{uR} (Fin 0)) (M := M × N)
      ((binomialEquiv (R := R) (M := M) (N := N) 0).symm s) =
      binomialTargetZeroEquiv (R := R) (M := M) (N := N) s := by
  rw [binomialEquiv_symm_apply]
  exact binomialAssembly_zero_square (R := R) (M := M) (N := N) s

/-- The normalized inverse in degree one swaps the target coordinates. -/
theorem binomialEquiv_symm_one (s : (⨁ j : Fin (1 + 1),
      SymmetricPower R (ULift.{uR} (Fin j.val)) M ⊗[R]
        SymmetricPower R (ULift.{uR} (Fin (1 - j.val))) N)) :
    subsingletonEquiv (R := R) (M := M × N) (⟨0⟩ : ULift.{uR} (Fin 1))
      ((binomialEquiv (R := R) (M := M) (N := N) 1).symm s) =
      ((binomialTargetOneEquiv (R := R) (M := M) (N := N) s).2,
        (binomialTargetOneEquiv (R := R) (M := M) (N := N) s).1) := by
  rw [binomialEquiv_symm_apply]
  exact binomialAssembly_one_square (R := R) (M := M) (N := N) s

end

end SymmetricPower

end
