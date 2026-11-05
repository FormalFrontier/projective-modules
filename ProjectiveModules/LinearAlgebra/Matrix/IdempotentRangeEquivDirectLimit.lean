/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Matrix.IdempotentRangeHomDirectLimit

/-!
# Canonical coefficient change of idempotent range equivalences

Linear equivalences between finite idempotent column ranges admit canonical
coefficient change. At a common stage of a directed system, equality-induced
range comparisons identify its result with an equivalence between the original
prescribed limit ranges. A prescribed limit equivalence is the canonical image
of an equivalence at one common later stage.
-/

@[expose] public section

universe uI uR uF uι uκ uν

namespace DirectLimit
section DirectedRangeEquiv

variable {I : Type uI} [Preorder I] [IsDirectedOrder I] [Nonempty I]
variable (R : I → Type uR) [∀ i, Semiring (R i)]
variable {F : ∀ ⦃i j : I⦄, i ≤ j → Type uF}
variable [∀ i j (h : i ≤ j), FunLike (F h) (R i) (R j)]
variable [∀ i j (h : i ≤ j), RingHomClass (F h) (R i) (R j)]
variable (f : ∀ i j (h : i ≤ j), F h)
variable [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]
variable {ι : Type uι} {κ : Type uκ} {ν : Type uν}
variable [Fintype ι] [Fintype κ] [Fintype ν]

/-- Canonical coefficient change of a common-stage range equivalence to the
original ranges of the two prescribed limit matrices. -/
noncomputable def rangeEquivToLimit
    (i j : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (k : I) (hik : i ≤ k) (hjk : j ≤ k)
    (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)))
    (hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k)))
    (e : (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (A.map (f i k hik : R i →+* R k))).range ≃ₗ[(R k)ᵐᵒᵖ]
      (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (B.map (f j k hjk : R j →+* R k))).range) :
    (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
        (A.map (DirectLimit.Ring.of R f i))).range ≃ₗ[(DirectLimit R f)ᵐᵒᵖ]
      (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
        (B.map (DirectLimit.Ring.of R f j))).range := by
  classical
  let φ : R k →+* DirectLimit R f := DirectLimit.Ring.of R f k
  let Ak : Matrix ι ι (R k) := A.map (f i k hik : R i →+* R k)
  let Bk : Matrix κ κ (R k) := B.map (f j k hjk : R j →+* R k)
  have eA : Ak.map φ = A.map (DirectLimit.Ring.of R f i) := by
    ext p q
    change (DirectLimit.Ring.of R f k) (f i k hik (A p q)) =
      (DirectLimit.Ring.of R f i) (A p q)
    simp only [DirectLimit.Ring.of_f]
  have eB : Bk.map φ = B.map (DirectLimit.Ring.of R f j) := by
    ext p q
    change (DirectLimit.Ring.of R f k) (f j k hjk (B p q)) =
      (DirectLimit.Ring.of R f j) (B p q)
    simp only [DirectLimit.Ring.of_f]
  have eSource :
      (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ (Ak.map φ)).range =
      (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
        (A.map (DirectLimit.Ring.of R f i))).range := by
    rw [eA]
  have eTarget :
      (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ (Bk.map φ)).range =
      (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
        (B.map (DirectLimit.Ring.of R f j))).range := by
    rw [eB]
  let eSourceLinear := LinearEquiv.ofEq _ _ eSource
  let eTargetLinear := LinearEquiv.ofEq _ _ eTarget
  exact (eSourceLinear.symm.trans (Matrix.rangeEquivMap φ hAk hBk e)).trans
    eTargetLinear

/-- The forward map of canonical coefficient change to the limit is the
existing original-range Hom coefficient change. -/
theorem rangeEquivToLimit_toLinearMap
    (i j : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (k : I) (hik : i ≤ k) (hjk : j ≤ k)
    (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)))
    (hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k)))
    (e : (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (A.map (f i k hik : R i →+* R k))).range ≃ₗ[(R k)ᵐᵒᵖ]
      (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (B.map (f j k hjk : R j →+* R k))).range) :
    (rangeEquivToLimit R f i j A B k hik hjk hAk hBk e).toLinearMap =
      rangeHomToLimit R f i j A B k hik hjk hAk hBk e.toLinearMap := by
  rfl

/-- The inverse map of canonical coefficient change to the limit is the
existing Hom coefficient change with source and target interchanged. -/
theorem rangeEquivToLimit_symm_toLinearMap
    (i j : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (k : I) (hik : i ≤ k) (hjk : j ≤ k)
    (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)))
    (hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k)))
    (e : (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (A.map (f i k hik : R i →+* R k))).range ≃ₗ[(R k)ᵐᵒᵖ]
      (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (B.map (f j k hjk : R j →+* R k))).range) :
    (rangeEquivToLimit R f i j A B k hik hjk hAk hBk e).symm.toLinearMap =
      rangeHomToLimit R f j i B A k hjk hik hBk hAk e.symm.toLinearMap := by
  rfl

/-- Canonical coefficient change to the limit evaluates on a coefficient-changed
projected stage column by mapping its stage image into the limit. -/
theorem rangeEquivToLimit_apply_projected
    (i j : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (k : I) (hik : i ≤ k) (hjk : j ≤ k)
    (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)))
    (hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k)))
    (e : (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (A.map (f i k hik : R i →+* R k))).range ≃ₗ[(R k)ᵐᵒᵖ]
      (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (B.map (f j k hjk : R j →+* R k))).range)
    (x : ι → R k) :
    ((rangeEquivToLimit R f i j A B k hik hjk hAk hBk e)
      ((Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
        (A.map (DirectLimit.Ring.of R f i))).rangeRestrict
        (fun p ↦ DirectLimit.Ring.of R f k (x p))) : κ → DirectLimit R f) =
      fun q ↦ DirectLimit.Ring.of R f k
        ((e ((Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
          (A.map (f i k hik : R i →+* R k))).rangeRestrict x) : κ → R k) q) := by
  classical
  let φ : R k →+* DirectLimit R f := DirectLimit.Ring.of R f k
  let Ak : Matrix ι ι (R k) := A.map (f i k hik : R i →+* R k)
  have eA : Ak.map φ = A.map (DirectLimit.Ring.of R f i) := by
    ext p q
    change (DirectLimit.Ring.of R f k) (f i k hik (A p q)) =
      (DirectLimit.Ring.of R f i) (A p q)
    simp only [DirectLimit.Ring.of_f]
  let c := LinearEquiv.ofEq _ _
    (congrArg (fun C : Matrix ι ι (DirectLimit R f) ↦
      (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ C).range) eA)
  have hx : c.symm
      ((Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
        (A.map (DirectLimit.Ring.of R f i))).rangeRestrict
          (fun p ↦ φ (x p))) =
      (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
        (Ak.map φ)).rangeRestrict (fun p ↦ φ (x p)) := by
    apply Subtype.ext
    simp only [c, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]
    change Matrix.mulVec (A.map (DirectLimit.Ring.of R f i)) (fun p ↦ φ (x p)) =
      Matrix.mulVec (Ak.map φ) (fun p ↦ φ (x p))
    rw [eA]
  have h := Matrix.rangeEquivMap_apply_projected φ hAk hBk e x
  rw [← hx] at h
  simpa only [rangeEquivToLimit, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply] using h

/-- Canonical coefficient change to the limit preserves the identity range
equivalence of a prescribed matrix. -/
theorem rangeEquivToLimit_refl
    (i : I) (A : Matrix ι ι (R i)) (k : I) (hik : i ≤ k)
    (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k))) :
    rangeEquivToLimit R f i i A A k hik hik hAk hAk
      (LinearEquiv.refl (R k)ᵐᵒᵖ
        ((Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
          (A.map (f i k hik : R i →+* R k))).range)) =
      LinearEquiv.refl (DirectLimit R f)ᵐᵒᵖ
        ((Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
          (A.map (DirectLimit.Ring.of R f i))).range) := by
  apply LinearEquiv.toLinearMap_injective
  rw [rangeEquivToLimit_toLinearMap]
  exact rangeHomToLimit_map_id R f i A k hik hAk

/-- Canonical coefficient change to the limit preserves composition of range
equivalences represented at the same common stage. -/
theorem rangeEquivToLimit_trans
    (i j l : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (C : Matrix ν ν (R l)) (k : I)
    (hik : i ≤ k) (hjk : j ≤ k) (hlk : l ≤ k)
    (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)))
    (hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k)))
    (hCk : IsIdempotentElem (C.map (f l k hlk : R l →+* R k)))
    (e : (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (A.map (f i k hik : R i →+* R k))).range ≃ₗ[(R k)ᵐᵒᵖ]
      (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (B.map (f j k hjk : R j →+* R k))).range)
    (d : (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (B.map (f j k hjk : R j →+* R k))).range ≃ₗ[(R k)ᵐᵒᵖ]
      (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (C.map (f l k hlk : R l →+* R k))).range) :
    rangeEquivToLimit R f i l A C k hik hlk hAk hCk (e.trans d) =
      (rangeEquivToLimit R f i j A B k hik hjk hAk hBk e).trans
        (rangeEquivToLimit R f j l B C k hjk hlk hBk hCk d) := by
  apply LinearEquiv.toLinearMap_injective
  change (rangeEquivToLimit R f i l A C k hik hlk hAk hCk
      (e.trans d)).toLinearMap =
    (rangeEquivToLimit R f j l B C k hjk hlk hBk hCk d).toLinearMap.comp
      (rangeEquivToLimit R f i j A B k hik hjk hAk hBk e).toLinearMap
  rw [rangeEquivToLimit_toLinearMap, rangeEquivToLimit_toLinearMap,
    rangeEquivToLimit_toLinearMap]
  exact rangeHomToLimit_map_comp R f i j l A B C k hik hjk hlk
    hAk hBk hCk e.toLinearMap d.toLinearMap

omit [IsDirectedOrder I] [Nonempty I] in
/-- Equality at an intermediate common stage persists under further coefficient change. -/
private theorem rangeHomTransition_eq_at_later_stage
    (i j : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (k l m : I) (hik : i ≤ k) (hjk : j ≤ k)
    (hil : i ≤ l) (hjl : j ≤ l) (him : i ≤ m) (hjm : j ≤ m)
    (hkl : k ≤ l) (hlm : l ≤ m)
    (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)))
    (hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k)))
    (hAl : IsIdempotentElem (A.map (f i l hil : R i →+* R l)))
    (hBl : IsIdempotentElem (B.map (f j l hjl : R j →+* R l)))
    (g h : (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (A.map (f i k hik : R i →+* R k))).range →ₗ[(R k)ᵐᵒᵖ]
      (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (B.map (f j k hjk : R j →+* R k))).range)
    (heq : rangeHomTransition R f i j A B k l hik hjk hil hjl hkl hAk hBk g =
      rangeHomTransition R f i j A B k l hik hjk hil hjl hkl hAk hBk h) :
    rangeHomTransition R f i j A B k m hik hjk him hjm
        (hkl.trans hlm) hAk hBk g =
      rangeHomTransition R f i j A B k m hik hjk him hjm
        (hkl.trans hlm) hAk hBk h := by
  have hcomp := rangeHomTransition_comp R f i j A B k l m
    hik hjk hil hjl him hjm hkl hlm hAk hBk hAl hBl
  have hg := DFunLike.congr_fun hcomp g
  have hh := DFunLike.congr_fun hcomp h
  exact hg.symm.trans
    ((congrArg (rangeHomTransition R f i j A B l m hil hjl him hjm hlm hAl hBl)
      heq).trans hh)

/-- A prescribed equivalence between the original limit ranges is the canonical
image of an equivalence between the corresponding original ranges at one common
later stage. -/
theorem exists_rangeEquiv_at_common_stage
    (i j : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B)
    (eLim :
      (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
        (A.map (DirectLimit.Ring.of R f i))).range ≃ₗ[(DirectLimit R f)ᵐᵒᵖ]
      (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
        (B.map (DirectLimit.Ring.of R f j))).range) :
    ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
      ∃ (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)))
        (hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k)))
        (ek : (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
            (A.map (f i k hik : R i →+* R k))).range ≃ₗ[(R k)ᵐᵒᵖ]
          (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
            (B.map (f j k hjk : R j →+* R k))).range),
        rangeEquivToLimit R f i j A B k hik hjk hAk hBk ek = eLim := by
  classical
  obtain ⟨k₁, hik₁, hjk₁, hAk₁, hBk₁, f₁, hf₁⟩ :=
    exists_rangeHom_at_common_stage R f i j A B hA hB eLim.toLinearMap
  obtain ⟨k₂, hjk₂, hik₂, hBk₂, hAk₂, g₂, hg₂⟩ :=
    exists_rangeHom_at_common_stage R f j i B A hB hA eLim.symm.toLinearMap
  obtain ⟨k, hk₁k, hk₂k⟩ := exists_ge_ge k₁ k₂
  let hik : i ≤ k := hik₁.trans hk₁k
  let hjk : j ≤ k := hjk₁.trans hk₁k
  have hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)) :=
    hA.map ((f i k hik : R i →+* R k).mapMatrix)
  have hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k)) :=
    hB.map ((f j k hjk : R j →+* R k).mapMatrix)
  let fk := rangeHomTransition R f i j A B k₁ k
    hik₁ hjk₁ hik hjk hk₁k hAk₁ hBk₁ f₁
  let gk := rangeHomTransition R f j i B A k₂ k
    hjk₂ hik₂ hjk hik hk₂k hBk₂ hAk₂ g₂
  have hfk : rangeHomToLimit R f i j A B k hik hjk hAk hBk fk =
      eLim.toLinearMap :=
    (DFunLike.congr_fun (rangeHomToLimit_comp_transition R f i j A B k₁ k
      hik₁ hjk₁ hik hjk hk₁k hAk₁ hBk₁ hAk hBk) f₁).trans hf₁
  have hgk : rangeHomToLimit R f j i B A k hjk hik hBk hAk gk =
      eLim.symm.toLinearMap :=
    (DFunLike.congr_fun (rangeHomToLimit_comp_transition R f j i B A k₂ k
      hjk₂ hik₂ hjk hik hk₂k hBk₂ hAk₂ hBk hAk) g₂).trans hg₂
  have hgfLim :
      rangeHomToLimit R f i i A A k hik hik hAk hAk (gk.comp fk) =
        rangeHomToLimit R f i i A A k hik hik hAk hAk LinearMap.id := by
    calc
      _ = (rangeHomToLimit R f j i B A k hjk hik hBk hAk gk).comp
          (rangeHomToLimit R f i j A B k hik hjk hAk hBk fk) :=
        rangeHomToLimit_map_comp R f i j i A B A k hik hjk hik hAk hBk hAk fk gk
      _ = eLim.symm.toLinearMap.comp eLim.toLinearMap := by rw [hfk, hgk]
      _ = LinearMap.id := by
        apply LinearMap.ext
        intro x
        exact eLim.symm_apply_apply x
      _ = _ := (rangeHomToLimit_map_id R f i A k hik hAk).symm
  have hfgLim :
      rangeHomToLimit R f j j B B k hjk hjk hBk hBk (fk.comp gk) =
        rangeHomToLimit R f j j B B k hjk hjk hBk hBk LinearMap.id := by
    calc
      _ = (rangeHomToLimit R f i j A B k hik hjk hAk hBk fk).comp
          (rangeHomToLimit R f j i B A k hjk hik hBk hAk gk) :=
        rangeHomToLimit_map_comp R f j i j B A B k hjk hik hjk hBk hAk hBk gk fk
      _ = eLim.toLinearMap.comp eLim.symm.toLinearMap := by rw [hfk, hgk]
      _ = LinearMap.id := by
        apply LinearMap.ext
        intro x
        exact eLim.apply_symm_apply x
      _ = _ := (rangeHomToLimit_map_id R f j B k hjk hBk).symm
  obtain ⟨lA, hklA, _, hgfA⟩ :=
    (rangeHomToLimit_eq_iff_eventually_eq R f i i A A k k
      hik hik hik hik hAk hAk hAk hAk (gk.comp fk) LinearMap.id).mp hgfLim
  obtain ⟨lB, hklB, _, hfgB⟩ :=
    (rangeHomToLimit_eq_iff_eventually_eq R f j j B B k k
      hjk hjk hjk hjk hBk hBk hBk hBk (fk.comp gk) LinearMap.id).mp hfgLim
  obtain ⟨m, hlAm, hlBm⟩ := exists_ge_ge lA lB
  let hkm : k ≤ m := hklA.trans hlAm
  let him : i ≤ m := hik.trans hkm
  let hjm : j ≤ m := hjk.trans hkm
  have hAm : IsIdempotentElem (A.map (f i m him : R i →+* R m)) :=
    hA.map ((f i m him : R i →+* R m).mapMatrix)
  have hBm : IsIdempotentElem (B.map (f j m hjm : R j →+* R m)) :=
    hB.map ((f j m hjm : R j →+* R m).mapMatrix)
  have hAlA : IsIdempotentElem
      (A.map (f i lA (hik.trans hklA) : R i →+* R lA)) :=
    hA.map ((f i lA (hik.trans hklA) : R i →+* R lA).mapMatrix)
  have hBlB : IsIdempotentElem
      (B.map (f j lB (hjk.trans hklB) : R j →+* R lB)) :=
    hB.map ((f j lB (hjk.trans hklB) : R j →+* R lB).mapMatrix)
  have hgfM :
      rangeHomTransition R f i i A A k m hik hik him him hkm hAk hAk (gk.comp fk) =
        rangeHomTransition R f i i A A k m hik hik him him hkm hAk hAk LinearMap.id :=
    rangeHomTransition_eq_at_later_stage R f i i A A k lA m
      hik hik (hik.trans hklA) (hik.trans hklA) him him hklA hlAm
      hAk hAk hAlA hAlA (gk.comp fk) LinearMap.id hgfA
  have hfgM :
      rangeHomTransition R f j j B B k m hjk hjk hjm hjm hkm hBk hBk (fk.comp gk) =
        rangeHomTransition R f j j B B k m hjk hjk hjm hjm hkm hBk hBk LinearMap.id :=
    rangeHomTransition_eq_at_later_stage R f j j B B k lB m
      hjk hjk (hjk.trans hklB) (hjk.trans hklB) hjm hjm hklB hlBm
      hBk hBk hBlB hBlB (fk.comp gk) LinearMap.id hfgB
  let fm := rangeHomTransition R f i j A B k m hik hjk him hjm hkm hAk hBk fk
  let gm := rangeHomTransition R f j i B A k m hjk hik hjm him hkm hBk hAk gk
  have hgf : gm.comp fm = LinearMap.id := by
    calc
      _ = rangeHomTransition R f i i A A k m hik hik him him hkm hAk hAk
          (gk.comp fk) :=
        (rangeHomTransition_map_comp R f i j i A B A k m hik hjk hik him hjm him
          hkm hAk hBk hAk fk gk).symm
      _ = rangeHomTransition R f i i A A k m hik hik him him hkm hAk hAk
          LinearMap.id := hgfM
      _ = LinearMap.id := rangeHomTransition_map_id R f i A k m hik him hkm hAk
  have hfg : fm.comp gm = LinearMap.id := by
    calc
      _ = rangeHomTransition R f j j B B k m hjk hjk hjm hjm hkm hBk hBk
          (fk.comp gk) :=
        (rangeHomTransition_map_comp R f j i j B A B k m hjk hik hjk hjm him hjm
          hkm hBk hAk hBk gk fk).symm
      _ = rangeHomTransition R f j j B B k m hjk hjk hjm hjm hkm hBk hBk
          LinearMap.id := hfgM
      _ = LinearMap.id := rangeHomTransition_map_id R f j B k m hjk hjm hkm hBk
  let em :
      (Matrix.mulVecBilin (R m) (R m)ᵐᵒᵖ
        (A.map (f i m him : R i →+* R m))).range ≃ₗ[(R m)ᵐᵒᵖ]
      (Matrix.mulVecBilin (R m) (R m)ᵐᵒᵖ
        (B.map (f j m hjm : R j →+* R m))).range :=
    LinearEquiv.ofLinearMap fm gm hfg hgf
  refine ⟨m, him, hjm, hAm, hBm, em, ?_⟩
  apply LinearEquiv.toLinearMap_injective
  rw [rangeEquivToLimit_toLinearMap]
  change rangeHomToLimit R f i j A B m him hjm hAm hBm fm = eLim.toLinearMap
  exact (DFunLike.congr_fun (rangeHomToLimit_comp_transition R f i j A B k m
    hik hjk him hjm hkm hAk hBk hAm hBm) fk).trans hfk

end DirectedRangeEquiv
end DirectLimit
