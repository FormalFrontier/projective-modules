/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Tactic.Abel

/-!
# Cancellation for countably generated free modules

This file proves that a module whose product with a finite-coordinate free
module is countably free is itself countably free. The coefficient ring may be
noncommutative and the construction also covers the zero ring and the empty
finite index.
-/

public section

universe u v w x y

namespace Module.Free

noncomputable section

variable (R : Type u) [Ring R]

/-- The countable coordinate module used by the cancellation interface. -/
abbrev CountableFree := ℕ →₀ R
/-- The finite coordinate module used by the cancellation interface. -/
abbrev FiniteFree (m : ℕ) := Fin m →₀ R

/-! ### Finite-coordinate containment -/

/-- The union of the supports of the images of the standard finite basis. -/
private def finiteImageSupport (m : ℕ) (j : FiniteFree R m →ₗ[R] CountableFree R) : Finset ℕ :=
  Finset.univ.biUnion fun i : Fin m ↦ (j (Finsupp.single i 1)).support

/-- A map from a finite-coordinate free module into `R∞` has all of its image
in one finite set of coordinates. -/
private theorem support_image_subset_finiteImageSupport
    (m : ℕ) (j : FiniteFree R m →ₗ[R] CountableFree R) (x : FiniteFree R m) :
    (j x).support ⊆ finiteImageSupport R m j := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | single_add i a x hi ha ih =>
      rw [j.map_add]
      exact Finsupp.support_add.trans <| Finset.union_subset
        (by
          rw [show Finsupp.single i a = a • Finsupp.single i (1 : R) by ext; simp,
            j.map_smul]
          exact Finsupp.support_smul.trans <|
            Finset.subset_biUnion_of_mem
              (fun k : Fin m ↦ (j (Finsupp.single k 1)).support)
              (Finset.mem_univ i))
        ih

/-! ### Splitting and reindexing countable coordinates -/

/-- Split finitely supported natural coordinates into a set and its
complement. -/
private def coordinateSplit (s : Set ℕ) [DecidablePred (· ∈ s)] :
    CountableFree R ≃ₗ[R] (s →₀ R) × ((sᶜ : Set ℕ) →₀ R) :=
  (Finsupp.domLCongr (Equiv.Set.sumCompl s).symm).trans
    (Finsupp.sumFinsuppLEquivProdFinsupp R)

private theorem coordinateSplit_snd_eq_zero_of_support_subset
    (s : Set ℕ) [DecidablePred (· ∈ s)] (x : CountableFree R)
    (hx : ↑x.support ⊆ s) :
    (coordinateSplit R s x).2 = 0 := by
  ext i
  change x i.1 = 0
  apply Finsupp.notMem_support_iff.mp
  intro hi
  exact i.2 (hx hi)

/-- The complement of a finite set of natural coordinates is again
countably infinite. -/
private def finiteComplEquivNat (s : Finset ℕ) : (sᶜ : Set ℕ) ≃ ℕ := by
  have hc : (sᶜ : Set ℕ).Countable := Set.to_countable _
  have hi : (sᶜ : Set ℕ).Infinite := s.finite_toSet.infinite_compl
  letI : Denumerable (sᶜ : Set ℕ) :=
    Classical.choice (Set.countable_infinite_iff_nonempty_denumerable.mp ⟨hc, hi⟩)
  exact Denumerable.eqv _

private def finiteComplFinsuppEquiv (s : Finset ℕ) :
    ((sᶜ : Set ℕ) →₀ R) ≃ₗ[R] CountableFree R :=
  Finsupp.domLCongr (finiteComplEquivNat s)

/-- A countable free module absorbs any finite-coordinate free module. -/
private def countableFinsuppAbsorbFinite (m : ℕ) :
    CountableFree R ≃ₗ[R] CountableFree R × FiniteFree R m := by
  letI : Denumerable (ℕ ⊕ Fin m) := Classical.choice <|
    nonempty_denumerable_iff.mpr ⟨by infer_instance, by infer_instance⟩
  exact (Finsupp.domLCongr (Denumerable.eqv (ℕ ⊕ Fin m)).symm).trans
    (Finsupp.sumFinsuppLEquivProdFinsupp R)

/-- The complement-coordinate module also absorbs every finite free module. -/
private def finiteComplAbsorbFinite (s : Finset ℕ) (m : ℕ) :
    ((sᶜ : Set ℕ) →₀ R) ≃ₗ[R]
      ((sᶜ : Set ℕ) →₀ R) × FiniteFree R m :=
  (finiteComplFinsuppEquiv R s).trans <|
    (countableFinsuppAbsorbFinite R m).trans <|
      ((finiteComplFinsuppEquiv R s).symm.prodCongr
        (LinearEquiv.refl R (FiniteFree R m)))

/-! ### The block-linear form of the source hint -/

section Block

variable {P : Type v} {Q : Type w} {N : Type x} {F : Type y}
variable [AddCommGroup P] [Module R P]
variable [AddCommGroup Q] [Module R Q]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup F] [Module R F]

/-- The lower-left block of an equivalence `P × Q ≃ N × F`. -/
private def blockTail (e : (P × Q) ≃ₗ[R] (N × F)) : P →ₗ[R] F :=
  (LinearMap.snd R N F).comp
    (e.toLinearMap.comp (LinearMap.inl R P Q))

/-- A right inverse to the lower-left block, obtained from `e⁻¹(0,f)`. -/
private def blockTailRightInverse (e : (P × Q) ≃ₗ[R] (N × F)) : F →ₗ[R] P :=
  (LinearMap.fst R P Q).comp
    (e.symm.toLinearMap.comp (LinearMap.inr R N F))

private theorem blockTailRightInverse_splits
    (e : (P × Q) ≃ₗ[R] (N × F))
    (hQ : (LinearMap.snd R N F).comp
      (e.toLinearMap.comp (LinearMap.inr R P Q)) = 0) :
    (blockTail R e).comp (blockTailRightInverse R e) = LinearMap.id := by
  ext f
  let pq := e.symm (0, f)
  have he := congrArg Prod.snd (e.apply_symm_apply (0, f))
  have hdecomp : e (pq.1, pq.2) = e (pq.1, 0) + e (0, pq.2) := by
    rw [show (pq.1, pq.2) = (pq.1, 0) + (0, pq.2) by simp, e.map_add]
  have hq : (e (0, pq.2)).2 = 0 := by
    exact LinearMap.congr_fun hQ pq.2
  change (e (pq.1, pq.2)).2 = f at he
  rw [hdecomp] at he
  simpa [blockTail, blockTailRightInverse, pq, hq] using he

/-- The upper block on `ker(blockTail) × Q`. -/
private def blockTop (e : (P × Q) ≃ₗ[R] (N × F)) :
    (LinearMap.ker (blockTail R e) × Q) →ₗ[R] N :=
  (LinearMap.fst R N F).comp <|
    e.toLinearMap.comp <|
      (LinearMap.ker (blockTail R e)).subtype.prodMap LinearMap.id

private theorem blockTail_fst_symm_inl_eq_zero
    (e : (P × Q) ≃ₗ[R] (N × F))
    (hQ : (LinearMap.snd R N F).comp
      (e.toLinearMap.comp (LinearMap.inr R P Q)) = 0)
    (n : N) :
    blockTail R e (e.symm (n, 0)).1 = 0 := by
  let pq := e.symm (n, 0)
  have he := congrArg Prod.snd (e.apply_symm_apply (n, 0))
  have hdecomp : e (pq.1, pq.2) = e (pq.1, 0) + e (0, pq.2) := by
    rw [show (pq.1, pq.2) = (pq.1, 0) + (0, pq.2) by simp, e.map_add]
  have hq : (e (0, pq.2)).2 = 0 := LinearMap.congr_fun hQ pq.2
  change (e (pq.1, pq.2)).2 = 0 at he
  rw [hdecomp] at he
  simpa [blockTail, pq, hq] using he

private def blockTopInverse
    (e : (P × Q) ≃ₗ[R] (N × F))
    (hQ : (LinearMap.snd R N F).comp
      (e.toLinearMap.comp (LinearMap.inr R P Q)) = 0) :
    N →ₗ[R] (LinearMap.ker (blockTail R e) × Q) where
  toFun n :=
    (⟨(e.symm (n, 0)).1, blockTail_fst_symm_inl_eq_zero R e hQ n⟩,
      (e.symm (n, 0)).2)
  map_add' n n' := by
    have h := e.symm.map_add (n, 0) (n', 0)
    apply Prod.ext
    · apply Subtype.ext
      simpa using congrArg Prod.fst h
    · simpa using congrArg Prod.snd h
  map_smul' a n := by
    have h := e.symm.map_smul a (n, 0)
    apply Prod.ext
    · apply Subtype.ext
      simpa using congrArg Prod.fst h
    · simpa using congrArg Prod.snd h

/-- When the lower-right block is zero, invertibility of the whole block map
identifies `ker(blockTail) × Q` with `N`. -/
private def blockTopEquiv
    (e : (P × Q) ≃ₗ[R] (N × F))
    (hQ : (LinearMap.snd R N F).comp
      (e.toLinearMap.comp (LinearMap.inr R P Q)) = 0) :
    (LinearMap.ker (blockTail R e) × Q) ≃ₗ[R] N where
  toLinearMap := blockTop R e
  invFun := blockTopInverse R e hQ
  left_inv kq := by
    have hbottom : (e ((kq.1 : P), kq.2)).2 = 0 := by
      have hdecomp : e ((kq.1 : P), kq.2) =
          e ((kq.1 : P), 0) + e (0, kq.2) := by
        rw [show ((kq.1 : P), kq.2) =
          ((kq.1 : P), 0) + (0, kq.2) by simp, e.map_add]
      rw [hdecomp]
      change blockTail R e kq.1 +
        ((LinearMap.snd R N F).comp
          (e.toLinearMap.comp (LinearMap.inr R P Q))) kq.2 = 0
      rw [kq.1.property, hQ]
      simp
    have hpq : e.symm (blockTop R e kq, 0) = ((kq.1 : P), kq.2) := by
      apply e.injective
      rw [e.apply_symm_apply]
      apply Prod.ext
      · rfl
      · exact hbottom.symm
    apply Prod.ext
    · apply Subtype.ext
      simpa [blockTopInverse] using congrArg Prod.fst hpq
    · simpa [blockTopInverse] using congrArg Prod.snd hpq
  right_inv n := by
    change (e (e.symm (n, 0))).1 = n
    rw [e.apply_symm_apply]

/-- The source hint's first decomposition: the left block is its kernel plus
the infinite tail. -/
private def leftBlockDecomposition
    (e : (P × Q) ≃ₗ[R] (N × F))
    (hQ : (LinearMap.snd R N F).comp
      (e.toLinearMap.comp (LinearMap.inr R P Q)) = 0) :
    P ≃ₗ[R] LinearMap.ker (blockTail R e) × F where
  toFun p :=
    (⟨p - blockTailRightInverse R e (blockTail R e p), by
        rw [LinearMap.mem_ker, map_sub]
        have hs : blockTail R e
            (blockTailRightInverse R e (blockTail R e p)) = blockTail R e p := by
          simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
            LinearMap.congr_fun
              (blockTailRightInverse_splits R e hQ) (blockTail R e p)
        change blockTail R e p -
          blockTail R e (blockTailRightInverse R e (blockTail R e p)) = 0
        rw [hs]
        simp⟩,
      blockTail R e p)
  invFun kf := (kf.1 : P) + blockTailRightInverse R e kf.2
  left_inv p := by
    simp
  right_inv kf := by
    have hk : blockTail R e (kf.1 : P) = 0 := kf.1.property
    have hs : blockTail R e (blockTailRightInverse R e kf.2) = kf.2 := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        LinearMap.congr_fun (blockTailRightInverse_splits R e hQ) kf.2
    have ht : blockTail R e
        ((kf.1 : P) + blockTailRightInverse R e kf.2) = kf.2 := by
      rw [map_add, hk, hs, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change (kf.1 : P) + blockTailRightInverse R e kf.2 -
        blockTailRightInverse R e
          (blockTail R e ((kf.1 : P) + blockTailRightInverse R e kf.2)) = kf.1
      rw [ht]
      abel
    · change blockTail R e
        ((kf.1 : P) + blockTailRightInverse R e kf.2) = kf.2
      exact ht
  map_add' p p' := by
    apply Prod.ext
    · apply Subtype.ext
      change p + p' - blockTailRightInverse R e (blockTail R e (p + p')) =
        (p - blockTailRightInverse R e (blockTail R e p)) +
          (p' - blockTailRightInverse R e (blockTail R e p'))
      simp only [map_add]
      abel
    · simp
  map_smul' a p := by
    apply Prod.ext
    · apply Subtype.ext
      change a • p - blockTailRightInverse R e (blockTail R e (a • p)) =
        a • (p - blockTailRightInverse R e (blockTail R e p))
      simp only [map_smul]
      rw [smul_sub]
    · simp

/-- Reorder `K × (F × Q)` as `(K × Q) × F`. -/
private def reassociateAbsorption (K : Type v) (F : Type y) (Q : Type w)
    [AddCommGroup K] [Module R K]
    [AddCommGroup F] [Module R F]
    [AddCommGroup Q] [Module R Q] :
    (K × (F × Q)) ≃ₗ[R] (K × Q) × F :=
  ((LinearEquiv.refl R K).prodCongr (LinearEquiv.prodComm R F Q)).trans
    (LinearEquiv.prodAssoc R K Q F).symm

/-- Generic block form of the Eilenberg swindle used in Exercise I.1.9. -/
private def blockSwindle
    (e : (P × Q) ≃ₗ[R] (N × F))
    (hQ : (LinearMap.snd R N F).comp
      (e.toLinearMap.comp (LinearMap.inr R P Q)) = 0)
    (absorb : F ≃ₗ[R] F × Q) :
    P ≃ₗ[R] N × F :=
  (leftBlockDecomposition R e hQ).trans <|
    (((LinearEquiv.refl R (LinearMap.ker (blockTail R e))).prodCongr
      absorb).trans <|
    (reassociateAbsorption R (LinearMap.ker (blockTail R e)) F Q).trans <|
    (blockTopEquiv R e hQ).prodCongr (LinearEquiv.refl R F))

end Block

/-! ### Countable free cancellation -/

/-- Removing a finite-coordinate free summand from a module equivalent to the
countable free module does not change the module's isomorphism type. -/
def natFinsuppEquivOfProdFinFinsuppEquiv
    {P : Type v} [AddCommGroup P] [Module R P]
    (m : ℕ) (h : (P × FiniteFree R m) ≃ₗ[R] CountableFree R) :
    P ≃ₗ[R] CountableFree R := by
  let j : FiniteFree R m →ₗ[R] CountableFree R :=
    h.toLinearMap.comp (LinearMap.inr R P (FiniteFree R m))
  let s : Finset ℕ := finiteImageSupport R m j
  let e : (P × FiniteFree R m) ≃ₗ[R]
      ((s : Set ℕ) →₀ R) × (((s : Set ℕ)ᶜ : Set ℕ) →₀ R) :=
    h.trans (coordinateSplit R (s : Set ℕ))
  have hQ :
      (LinearMap.snd R ((s : Set ℕ) →₀ R)
          (((s : Set ℕ)ᶜ : Set ℕ) →₀ R)).comp
        (e.toLinearMap.comp (LinearMap.inr R P (FiniteFree R m))) = 0 := by
    apply LinearMap.ext
    intro q
    change (coordinateSplit R (s : Set ℕ) (h (0, q))).2 = 0
    apply coordinateSplit_snd_eq_zero_of_support_subset
    simpa [j, s] using support_image_subset_finiteImageSupport R m j q
  exact
    (blockSwindle R e hQ (finiteComplAbsorbFinite R s m)).trans
      (coordinateSplit R (s : Set ℕ)).symm

/-- Removing a standard finite coordinate module from a module equivalent to
the countable free module does not change the module's isomorphism type. -/
def natFinsuppEquivOfProdFinEquiv
    {P : Type v} [AddCommGroup P] [Module R P]
    (m : ℕ) (h : (P × (Fin m → R)) ≃ₗ[R] (ℕ →₀ R)) :
    P ≃ₗ[R] (ℕ →₀ R) :=
  natFinsuppEquivOfProdFinFinsuppEquiv R m <|
    ((LinearEquiv.refl R P).prodCongr
      (Finsupp.linearEquivFunOnFinite R R (Fin m))).trans h

/-- A version of `natFinsuppEquivOfProdFinFinsuppEquiv` for arbitrary finite
and countably infinite coordinate types. -/
def countableFinsuppEquivOfProdFiniteFinsuppEquiv
    {P : Type v} [AddCommGroup P] [Module R P]
    {ι : Type w} [Finite ι]
    {κ : Type x} [Countable κ] [Infinite κ]
    (e : (P × (ι →₀ R)) ≃ₗ[R] (κ →₀ R)) :
    P ≃ₗ[R] (κ →₀ R) := by
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Denumerable κ := Classical.choice (nonempty_denumerable κ)
  let finiteEquiv :
      (ι →₀ R) ≃ₗ[R] (Fin (Fintype.card ι) →₀ R) :=
    Finsupp.domLCongr (Fintype.equivFin ι)
  let countableEquiv : (κ →₀ R) ≃ₗ[R] (ℕ →₀ R) :=
    Finsupp.domLCongr (Denumerable.eqv κ)
  let e' : (P × (Fin (Fintype.card ι) →₀ R)) ≃ₗ[R] (ℕ →₀ R) :=
    (((LinearEquiv.refl R P).prodCongr finiteEquiv).symm.trans e).trans
      countableEquiv
  exact
    (natFinsuppEquivOfProdFinFinsuppEquiv R (Fintype.card ι) e').trans
      countableEquiv.symm

end

end Module.Free
