/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import ProjectiveModules.Module.CountablyGenerated
public import ProjectiveModules.Module.LocalProjectiveElement

/-!
# Countably generated projective modules over local rings

This file constructs coherent finite free split summands in a countably
generated projective right module over a possibly noncommutative local ring.
-/

@[expose] public section

universe uR uP

namespace Module.Projective

variable {R : Type uR} [Ring R]
variable {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P]
variable [Module.Projective Rᵐᵒᵖ P]

private structure FiniteFreeSplitBlock where
  rank : ℕ
  injection : (Fin rank → R) →ₗ[Rᵐᵒᵖ] P
  project : P →ₗ[Rᵐᵒᵖ] (Fin rank → R)
  split : project.comp injection = LinearMap.id

private structure FiniteFreeSplitFamily (n : ℕ) where
  block : Fin n → FiniteFreeSplitBlock (R := R) (P := P)
  orthogonal : ∀ i j, i ≠ j →
    (block i).project.comp (block j).injection = 0

private def FiniteFreeSplitFamily.total {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n) : Module.End Rᵐᵒᵖ P :=
  ∑ i, (s.block i).injection.comp (s.block i).project

omit [Module.Projective Rᵐᵒᵖ P] in
private theorem FiniteFreeSplitFamily.total_apply_include {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n) (i : Fin n)
    (y : Fin (s.block i).rank → R) :
    s.total ((s.block i).injection y) = (s.block i).injection y := by
  classical
  simp only [FiniteFreeSplitFamily.total, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [Finset.sum_eq_single i]
  · change (s.block i).injection
      ((s.block i).project ((s.block i).injection y)) = _
    have hsplit := LinearMap.congr_fun (s.block i).split y
    change (s.block i).project ((s.block i).injection y) = y at hsplit
    rw [hsplit]
  · intro j _ hji
    change (s.block j).injection
      ((s.block j).project ((s.block i).injection y)) = 0
    have hzero : (s.block j).project ((s.block i).injection y) = 0 := by
      exact LinearMap.congr_fun (s.orthogonal j i hji) y
    rw [hzero, map_zero]
  · simp

omit [Module.Projective Rᵐᵒᵖ P] in
private theorem FiniteFreeSplitFamily.project_apply_total {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n) (i : Fin n) (x : P) :
    (s.block i).project (s.total x) = (s.block i).project x := by
  classical
  simp only [FiniteFreeSplitFamily.total, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  rw [Finset.sum_eq_single i]
  · have hsplit := LinearMap.congr_fun (s.block i).split ((s.block i).project x)
    change (s.block i).project ((s.block i).injection ((s.block i).project x)) =
      (s.block i).project x at hsplit
    exact hsplit
  · intro j _ hji
    exact LinearMap.congr_fun (s.orthogonal i j hji.symm) ((s.block j).project x)
  · simp

omit [Module.Projective Rᵐᵒᵖ P] in
private theorem FiniteFreeSplitFamily.total_idem {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n) (x : P) :
    s.total (s.total x) = s.total x := by
  classical
  calc
    s.total (s.total x) =
        ∑ i, (s.block i).injection ((s.block i).project (s.total x)) := by
      rw [FiniteFreeSplitFamily.total]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    _ = ∑ i, (s.block i).injection ((s.block i).project x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [s.project_apply_total]
    _ = s.total x := by
      rw [FiniteFreeSplitFamily.total]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]

private def FiniteFreeSplitFamily.complement {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n) : Module.End Rᵐᵒᵖ P :=
  LinearMap.id - s.total

omit [Module.Projective Rᵐᵒᵖ P] in
private theorem FiniteFreeSplitFamily.complement_apply {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n) (x : P) :
    s.complement x = x - s.total x := rfl

omit [Module.Projective Rᵐᵒᵖ P] in
private theorem FiniteFreeSplitFamily.complement_idem {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n) (x : P) :
    s.complement (s.complement x) = s.complement x := by
  simp only [s.complement_apply, map_sub, s.total_idem]
  abel

omit [Module.Projective Rᵐᵒᵖ P] in
private theorem FiniteFreeSplitFamily.complement_apply_include {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n) (i : Fin n)
    (y : Fin (s.block i).rank → R) :
    s.complement ((s.block i).injection y) = 0 := by
  rw [s.complement_apply, s.total_apply_include, sub_self]

omit [Module.Projective Rᵐᵒᵖ P] in
private theorem FiniteFreeSplitFamily.project_apply_complement {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n) (i : Fin n) (x : P) :
    (s.block i).project (s.complement x) = 0 := by
  rw [s.complement_apply, map_sub, s.project_apply_total, sub_self]

private def FiniteFreeSplitFamily.complementRetraction {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n) :
    P →ₗ[Rᵐᵒᵖ] LinearMap.range s.complement :=
  s.complement.codRestrict (LinearMap.range s.complement)
    (LinearMap.mem_range_self s.complement)

omit [Module.Projective Rᵐᵒᵖ P] in
private theorem FiniteFreeSplitFamily.complementRetraction_comp_subtype {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n) :
    s.complementRetraction.comp (LinearMap.range s.complement).subtype =
      LinearMap.id := by
  ext y
  rcases y.property with ⟨x, hx⟩
  change s.complement y = y
  rw [← hx]
  exact s.complement_idem x

omit [Module.Projective Rᵐᵒᵖ P] in
private theorem FiniteFreeSplitFamily.complementRetraction_apply_include {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n) (i : Fin n)
    (y : Fin (s.block i).rank → R) :
    s.complementRetraction ((s.block i).injection y) = 0 := by
  apply Subtype.ext
  exact s.complement_apply_include i y

omit [Module.Projective Rᵐᵒᵖ P] in
private theorem FiniteFreeSplitFamily.project_apply_subtype_complementRange {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n) (i : Fin n)
    (y : LinearMap.range s.complement) :
    (s.block i).project y = 0 := by
  rcases y.property with ⟨x, hx⟩
  rw [← hx]
  exact s.project_apply_complement i x

private def FiniteFreeSplitFamily.snocBlock {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n)
    (b : FiniteFreeSplitBlock (R := R) (P := P)) :
    Fin (n + 1) → FiniteFreeSplitBlock (R := R) (P := P) :=
  Fin.lastCases b s.block

omit [Module.Projective Rᵐᵒᵖ P] in
@[simp] private theorem FiniteFreeSplitFamily.snocBlock_castSucc {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n)
    (b : FiniteFreeSplitBlock (R := R) (P := P)) (i : Fin n) :
    s.snocBlock b i.castSucc = s.block i := by
  simp [FiniteFreeSplitFamily.snocBlock]

omit [Module.Projective Rᵐᵒᵖ P] in
@[simp] private theorem FiniteFreeSplitFamily.snocBlock_last {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n)
    (b : FiniteFreeSplitBlock (R := R) (P := P)) :
    s.snocBlock b (Fin.last n) = b := by
  simp [FiniteFreeSplitFamily.snocBlock]

omit [Module.Projective Rᵐᵒᵖ P] in
private theorem FiniteFreeSplitFamily.snocBlock_castSucc_component {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n)
    (b : FiniteFreeSplitBlock (R := R) (P := P)) (i : Fin n) (x : P) :
    (s.snocBlock b i.castSucc).injection
        ((s.snocBlock b i.castSucc).project x) =
      (s.block i).injection ((s.block i).project x) := by
  exact congrArg
    (fun q : FiniteFreeSplitBlock (R := R) (P := P) ↦
      q.injection (q.project x))
    (s.snocBlock_castSucc b i)

omit [Module.Projective Rᵐᵒᵖ P] in
private theorem FiniteFreeSplitFamily.snocBlock_last_component {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n)
    (b : FiniteFreeSplitBlock (R := R) (P := P)) (x : P) :
    (s.snocBlock b (Fin.last n)).injection
        ((s.snocBlock b (Fin.last n)).project x) =
      b.injection (b.project x) := by
  exact congrArg
    (fun q : FiniteFreeSplitBlock (R := R) (P := P) ↦
      q.injection (q.project x))
    (s.snocBlock_last b)

private theorem FiniteFreeSplitFamily.exists_snoc {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n)
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r) (x : P) :
    ∃ t : FiniteFreeSplitFamily (R := R) (P := P) (n + 1),
      (∀ i, t.block i.castSucc = s.block i) ∧
      t.total x = x ∧
      ∀ y, s.total y = y → t.total y = y := by
  classical
  let C := LinearMap.range s.complement
  let _ : Module.Projective Rᵐᵒᵖ C :=
    Module.Projective.of_split C.subtype s.complementRetraction
      s.complementRetraction_comp_subtype
  obtain ⟨r, f, g, hgf, hx⟩ :=
    Module.Projective.exists_fin_rightFree_split_containing I hI hunit
      (s.complementRetraction x)
  let b : FiniteFreeSplitBlock (R := R) (P := P) :=
    { rank := r
      injection := C.subtype.comp f
      project := g.comp s.complementRetraction
      split := by
        apply LinearMap.ext
        intro y
        have hret := LinearMap.congr_fun s.complementRetraction_comp_subtype (f y)
        change s.complementRetraction (C.subtype (f y)) = f y at hret
        have hsplit := LinearMap.congr_fun hgf y
        change g (f y) = y at hsplit
        change g (s.complementRetraction (C.subtype (f y))) = y
        rw [hret, hsplit] }
  let t : FiniteFreeSplitFamily (R := R) (P := P) (n + 1) :=
    { block := s.snocBlock b
      orthogonal := by
        intro i j hij
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => exact (hij rfl).elim
          | cast j =>
            rw [s.snocBlock_last, s.snocBlock_castSucc]
            apply LinearMap.ext
            intro y
            change g (s.complementRetraction ((s.block j).injection y)) = 0
            rw [s.complementRetraction_apply_include, map_zero]
        | cast i =>
          induction j using Fin.lastCases with
          | last =>
            rw [s.snocBlock_castSucc, s.snocBlock_last]
            apply LinearMap.ext
            intro y
            change (s.block i).project (C.subtype (f y)) = 0
            exact s.project_apply_subtype_complementRange i (f y)
          | cast j =>
            rw [s.snocBlock_castSucc, s.snocBlock_castSucc]
            exact s.orthogonal i j (fun h ↦ hij (congrArg Fin.castSucc h)) }
  have htblock (i : Fin n) : t.block i.castSucc = s.block i := by
    simp [t]
  have htotal (y : P) :
      t.total y = s.total y + b.injection (b.project y) := by
    simp only [FiniteFreeSplitFamily.total, LinearMap.sum_apply, LinearMap.comp_apply]
    rw [Fin.sum_univ_castSucc]
    dsimp only [t]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i _
      exact s.snocBlock_castSucc_component b i y
    · exact s.snocBlock_last_component b y
  have hnewx : b.injection (b.project x) = s.complement x := by
    rcases hx with ⟨z, hz⟩
    have hsplit := LinearMap.congr_fun hgf z
    change g (f z) = z at hsplit
    change C.subtype (f (g (s.complementRetraction x))) = s.complement x
    rw [← hz, hsplit, hz]
    rfl
  refine ⟨t, htblock, ?_, ?_⟩
  · rw [htotal, hnewx, s.complement_apply]
    abel
  · intro y hy
    have hcomp : s.complement y = 0 := by
      rw [s.complement_apply, hy, sub_self]
    have hret : s.complementRetraction y = 0 := by
      apply Subtype.ext
      exact hcomp
    rw [htotal, hy]
    change y + C.subtype (f (g (s.complementRetraction y))) = y
    rw [hret, map_zero, map_zero, map_zero, add_zero]

private structure FiniteFreeExhaustionState (x : ℕ → P) (n : ℕ) where
  family : FiniteFreeSplitFamily (R := R) (P := P) n
  fixed : ∀ i : Fin n, family.total (x i) = x i

private def FiniteFreeExhaustionState.nil (x : ℕ → P) :
    FiniteFreeExhaustionState (R := R) (P := P) x 0 :=
  { family :=
      { block := Fin.elim0
        orthogonal := fun i ↦ Fin.elim0 i }
    fixed := fun i ↦ Fin.elim0 i }

private theorem FiniteFreeExhaustionState.exists_succ {n : ℕ} (x : ℕ → P)
    (s : FiniteFreeExhaustionState (R := R) (P := P) x n)
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r) :
    ∃ t : FiniteFreeExhaustionState (R := R) (P := P) x (n + 1),
      ∀ i, t.family.block i.castSucc = s.family.block i := by
  obtain ⟨t, ht, hnew, hold⟩ := s.family.exists_snoc I hI hunit (x n)
  refine ⟨{ family := t, fixed := ?_ }, ht⟩
  intro i
  induction i using Fin.lastCases with
  | last => simpa using hnew
  | cast i => exact hold (x i) (s.fixed i)

private noncomputable def finiteFreeExhaustionState
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r)
    (x : ℕ → P) : (n : ℕ) → FiniteFreeExhaustionState (R := R) (P := P) x n
  | 0 => FiniteFreeExhaustionState.nil x
  | n + 1 =>
      (FiniteFreeExhaustionState.exists_succ x
        (finiteFreeExhaustionState I hI hunit x n) I hI hunit).choose

private theorem finiteFreeExhaustionState_succ_block
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r)
    (x : ℕ → P) (n : ℕ) (i : Fin n) :
    (finiteFreeExhaustionState I hI hunit x (n + 1)).family.block i.castSucc =
      (finiteFreeExhaustionState I hI hunit x n).family.block i := by
  exact (FiniteFreeExhaustionState.exists_succ x
    (finiteFreeExhaustionState I hI hunit x n) I hI hunit).choose_spec i

private noncomputable def finiteFreeExhaustionBlock
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r)
    (x : ℕ → P) (n : ℕ) : FiniteFreeSplitBlock (R := R) (P := P) :=
  (finiteFreeExhaustionState I hI hunit x (n + 1)).family.block (Fin.last n)

private theorem finiteFreeExhaustionState_block_eq
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r)
    (x : ℕ → P) {m n : ℕ} (hmn : m < n) :
    (finiteFreeExhaustionState I hI hunit x n).family.block ⟨m, hmn⟩ =
      finiteFreeExhaustionBlock I hI hunit x m := by
  induction n with
  | zero => exact (Nat.not_lt_zero _ hmn).elim
  | succ n ih =>
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hmn) with hlt | heq
      · calc
          (finiteFreeExhaustionState I hI hunit x (n + 1)).family.block
              ⟨m, hmn⟩ =
              (finiteFreeExhaustionState I hI hunit x n).family.block
                ⟨m, hlt⟩ := by
                simpa using finiteFreeExhaustionState_succ_block
                  I hI hunit x n ⟨m, hlt⟩
          _ = finiteFreeExhaustionBlock I hI hunit x m := ih hlt
      · subst m
        change
          (finiteFreeExhaustionState I hI hunit x (n + 1)).family.block
              ⟨n, hmn⟩ =
            (finiteFreeExhaustionState I hI hunit x (n + 1)).family.block
              (Fin.last n)
        congr

omit [Module.Projective Rᵐᵒᵖ P] in
private theorem FiniteFreeSplitFamily.orthogonal_of_block_eq {n : ℕ}
    (s : FiniteFreeSplitFamily (R := R) (P := P) n) (i j : Fin n)
    (hij : i ≠ j) (b c : FiniteFreeSplitBlock (R := R) (P := P))
    (hb : s.block i = b) (hc : s.block j = c) :
    b.project.comp c.injection = 0 := by
  subst b
  subst c
  exact s.orthogonal i j hij

/-- A sequence in a projective right module over a possibly noncommutative
local ring admits coherent finite standard-free split components.  The
components are pairwise biorthogonal, and the `n`th vector is reconstructed by
the first `n + 1` components. -/
theorem exists_fin_rightFree_biorthogonal_exhaustion
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r)
    (x : ℕ → P) :
    ∃ (k : ℕ → ℕ)
      (f : (n : ℕ) → (Fin (k n) → R) →ₗ[Rᵐᵒᵖ] P)
      (g : (n : ℕ) → P →ₗ[Rᵐᵒᵖ] (Fin (k n) → R)),
      (∀ n, (g n).comp (f n) = LinearMap.id) ∧
      (∀ m n, m ≠ n → (g m).comp (f n) = 0) ∧
      ∀ n, x n = ∑ i : Fin (n + 1), f i (g i (x n)) := by
  classical
  let b : ℕ → FiniteFreeSplitBlock (R := R) (P := P) :=
    finiteFreeExhaustionBlock I hI hunit x
  refine ⟨fun n ↦ (b n).rank, fun n ↦ (b n).injection,
    fun n ↦ (b n).project, ?_, ?_, ?_⟩
  · intro n
    exact (b n).split
  · intro m n hmn
    let N := max m n + 1
    let im : Fin N := ⟨m, Nat.lt_succ_of_le (Nat.le_max_left m n)⟩
    let jn : Fin N := ⟨n, Nat.lt_succ_of_le (Nat.le_max_right m n)⟩
    have hij : im ≠ jn := by
      intro h
      apply hmn
      exact congrArg Fin.val h
    let s := finiteFreeExhaustionState I hI hunit x N
    have him : s.family.block im = b m := by
      exact finiteFreeExhaustionState_block_eq I hI hunit x im.isLt
    have hjn : s.family.block jn = b n := by
      exact finiteFreeExhaustionState_block_eq I hI hunit x jn.isLt
    exact s.family.orthogonal_of_block_eq im jn hij (b m) (b n) him hjn
  · intro n
    let s := finiteFreeExhaustionState I hI hunit x (n + 1)
    have hfixed := s.fixed (Fin.last n)
    change s.family.total (x n) = x n at hfixed
    calc
      x n = s.family.total (x n) := hfixed.symm
      _ = ∑ i : Fin (n + 1),
          (s.family.block i).injection ((s.family.block i).project (x n)) := by
        rw [FiniteFreeSplitFamily.total]
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
      _ = ∑ i : Fin (n + 1), (b i).injection ((b i).project (x n)) := by
        apply Finset.sum_congr rfl
        intro i _
        have hi : s.family.block i = b i := by
          exact finiteFreeExhaustionState_block_eq I hI hunit x i.isLt
        exact congrArg
          (fun q : FiniteFreeSplitBlock (R := R) (P := P) ↦
            q.injection (q.project (x n))) hi

/-- A countably generated projective right module over a possibly
noncommutative local ring has a spanning sequence equipped with coherent finite
standard-free split components. -/
theorem exists_fin_rightFree_biorthogonal_exhaustion_of_countablyGenerated
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r)
    (hP : Module.CountablyGenerated Rᵐᵒᵖ P) :
    ∃ (x : ℕ → P) (k : ℕ → ℕ)
      (f : (n : ℕ) → (Fin (k n) → R) →ₗ[Rᵐᵒᵖ] P)
      (g : (n : ℕ) → P →ₗ[Rᵐᵒᵖ] (Fin (k n) → R)),
      Submodule.span Rᵐᵒᵖ (Set.range x) = ⊤ ∧
      (∀ n, (g n).comp (f n) = LinearMap.id) ∧
      (∀ m n, m ≠ n → (g m).comp (f n) = 0) ∧
      ∀ n, x n = ∑ i : Fin (n + 1), f i (g i (x n)) := by
  obtain ⟨x, hx⟩ := hP
  obtain ⟨k, f, g, hsplit, horth, hreconstruct⟩ :=
    exists_fin_rightFree_biorthogonal_exhaustion I hI hunit x
  exact ⟨x, k, f, g, hx, hsplit, horth, hreconstruct⟩

end Module.Projective
