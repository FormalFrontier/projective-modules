/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import ProjectiveModules.LinearAlgebra.Matrix.IdempotentRangeHomMap
import AlgebraicDirectLimits.Order.DirectedSystem
import AlgebraicDirectLimits.LinearAlgebra.Matrix.NormalizedDescent

/-!
# Coefficient change between directed idempotent ranges

Equality-induced range equivalences align coefficient changes with the prescribed
matrices at each target stage and in the limit. The resulting additive maps have
codomains in the original homomorphism spaces.
-/

@[expose] public section

universe uI uR uF uι uκ

namespace DirectLimit
section DirectedRangeHom

variable {I : Type uI} [Preorder I] [IsDirectedOrder I] [Nonempty I]
variable (R : I → Type uR) [∀ i, Semiring (R i)]
variable {F : ∀ ⦃i j : I⦄, i ≤ j → Type uF}
variable [∀ i j (h : i ≤ j), FunLike (F h) (R i) (R j)]
variable [∀ i j (h : i ≤ j), RingHomClass (F h) (R i) (R j)]
variable (f : ∀ i j (h : i ≤ j), F h)
variable [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]

/-- Coefficient change from one common stage to another, with codomain the
original Hom of the prescribed matrices at the target stage. -/
noncomputable def rangeHomTransition
    (i j : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (k l : I) (hik : i ≤ k) (hjk : j ≤ k)
    (hil : i ≤ l) (hjl : j ≤ l) (hkl : k ≤ l)
    (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)))
    (hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k))) :
    ((Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (A.map (f i k hik : R i →+* R k))).range →ₗ[(R k)ᵐᵒᵖ]
      (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (B.map (f j k hjk : R j →+* R k))).range) →+
    ((Matrix.mulVecBilin (R l) (R l)ᵐᵒᵖ
        (A.map (f i l hil : R i →+* R l))).range →ₗ[(R l)ᵐᵒᵖ]
      (Matrix.mulVecBilin (R l) (R l)ᵐᵒᵖ
        (B.map (f j l hjl : R j →+* R l))).range) := by
  classical
  let φ : R k →+* R l := f k l hkl
  let Ak : Matrix ι ι (R k) := A.map (f i k hik : R i →+* R k)
  let Bk : Matrix κ κ (R k) := B.map (f j k hjk : R j →+* R k)
  have eA : Ak.map φ = A.map (f i l hil : R i →+* R l) := by
    ext p q
    change f k l hkl (f i k hik (A p q)) = f i l hil (A p q)
    exact DirectedSystem.map_map' f hik hkl (A p q)
  have eB : Bk.map φ = B.map (f j l hjl : R j →+* R l) := by
    ext p q
    change f k l hkl (f j k hjk (B p q)) = f j l hjl (B p q)
    exact DirectedSystem.map_map' f hjk hkl (B p q)
  have eSource :
      (Matrix.mulVecBilin (R l) (R l)ᵐᵒᵖ (Ak.map φ)).range =
      (Matrix.mulVecBilin (R l) (R l)ᵐᵒᵖ
        (A.map (f i l hil : R i →+* R l))).range := by
    rw [eA]
  have eTarget :
      (Matrix.mulVecBilin (R l) (R l)ᵐᵒᵖ (Bk.map φ)).range =
      (Matrix.mulVecBilin (R l) (R l)ᵐᵒᵖ
        (B.map (f j l hjl : R j →+* R l))).range := by
    rw [eB]
  let eSourceLinear := LinearEquiv.ofEq _ _ eSource
  let eTargetLinear := LinearEquiv.ofEq _ _ eTarget
  exact (LinearEquiv.arrowCongrAddEquiv eSourceLinear eTargetLinear).toAddMonoidHom.comp
    (Matrix.rangeHomMap φ hAk hBk)

/-- Coefficient change from a common stage to the original Hom of the two
prescribed limit ranges. -/
noncomputable def rangeHomToLimit
    (i j : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (k : I) (hik : i ≤ k) (hjk : j ≤ k)
    (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)))
    (hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k))) :
    ((Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (A.map (f i k hik : R i →+* R k))).range →ₗ[(R k)ᵐᵒᵖ]
      (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (B.map (f j k hjk : R j →+* R k))).range) →+
    ((Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
        (A.map (DirectLimit.Ring.of R f i))).range →ₗ[(DirectLimit R f)ᵐᵒᵖ]
      (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
        (B.map (DirectLimit.Ring.of R f j))).range) := by
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
  exact (LinearEquiv.arrowCongrAddEquiv eSourceLinear eTargetLinear).toAddMonoidHom.comp
    (Matrix.rangeHomMap φ hAk hBk)

omit [IsDirectedOrder I] [Nonempty I] in
/-- The existing classifier sends a canonical transition to entrywise change. -/
theorem rangeHomEquiv_rangeHomTransition
    (i j : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (k l : I) (hik : i ≤ k) (hjk : j ≤ k)
    (hil : i ≤ l) (hjl : j ≤ l) (hkl : k ≤ l)
    (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)))
    (hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k)))
    (hAl : IsIdempotentElem (A.map (f i l hil : R i →+* R l)))
    (hBl : IsIdempotentElem (B.map (f j l hjl : R j →+* R l)))
    (g : (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (A.map (f i k hik : R i →+* R k))).range →ₗ[(R k)ᵐᵒᵖ]
      (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (B.map (f j k hjk : R j →+* R k))).range) :
    (Matrix.rangeHomEquiv hAl hBl
        (rangeHomTransition R f i j A B k l hik hjk hil hjl hkl hAk hBk g) :
      Matrix κ ι (R l)) =
      (Matrix.rangeHomEquiv hAk hBk g : Matrix κ ι (R k)).map
        (f k l hkl : R k →+* R l) := by
  classical
  let φ : R k →+* R l := f k l hkl
  let Ak : Matrix ι ι (R k) := A.map (f i k hik : R i →+* R k)
  let Bk : Matrix κ κ (R k) := B.map (f j k hjk : R j →+* R k)
  have eA : Ak.map φ = A.map (f i l hil : R i →+* R l) := by
    ext p q
    change f k l hkl (f i k hik (A p q)) = f i l hil (A p q)
    exact DirectedSystem.map_map' f hik hkl (A p q)
  have eB : Bk.map φ = B.map (f j l hjl : R j →+* R l) := by
    ext p q
    change f k l hkl (f j k hjk (B p q)) = f j l hjl (B p q)
    exact DirectedSystem.map_map' f hjk hkl (B p q)
  have hAφ : IsIdempotentElem (Ak.map φ) := hAk.map (φ.mapMatrix)
  have hBφ : IsIdempotentElem (Bk.map φ) := hBk.map (φ.mapMatrix)
  exact
    (Matrix.coe_rangeHomEquiv_arrowCongrAddEquiv_ofEq
      hAφ hBφ hAl hBl eA eB (Matrix.rangeHomMap φ hAk hBk g)).trans
      (congrArg Subtype.val
        (Matrix.rangeHomEquiv_rangeHomMap φ hAk hBk hAφ hBφ g))

/-- The existing classifier sends the canonical limit map to entrywise change. -/
theorem rangeHomEquiv_rangeHomToLimit
    (i j : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (k : I) (hik : i ≤ k) (hjk : j ≤ k)
    (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)))
    (hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k)))
    (hAL : IsIdempotentElem (A.map (DirectLimit.Ring.of R f i)))
    (hBL : IsIdempotentElem (B.map (DirectLimit.Ring.of R f j)))
    (g : (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (A.map (f i k hik : R i →+* R k))).range →ₗ[(R k)ᵐᵒᵖ]
      (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
        (B.map (f j k hjk : R j →+* R k))).range) :
    (Matrix.rangeHomEquiv hAL hBL
        (rangeHomToLimit R f i j A B k hik hjk hAk hBk g) :
      Matrix κ ι (DirectLimit R f)) =
      (Matrix.rangeHomEquiv hAk hBk g : Matrix κ ι (R k)).map
        (DirectLimit.Ring.of R f k) := by
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
  have hAφ : IsIdempotentElem (Ak.map φ) := hAk.map (φ.mapMatrix)
  have hBφ : IsIdempotentElem (Bk.map φ) := hBk.map (φ.mapMatrix)
  exact
    (Matrix.coe_rangeHomEquiv_arrowCongrAddEquiv_ofEq
      hAφ hBφ hAL hBL eA eB (Matrix.rangeHomMap φ hAk hBk g)).trans
      (congrArg Subtype.val
        (Matrix.rangeHomEquiv_rangeHomMap φ hAk hBk hAφ hBφ g))

omit [IsDirectedOrder I] [Nonempty I] in
/-- The canonical transition at one stage is the identity additive map. -/
theorem rangeHomTransition_id
    (i j : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (k : I) (hik : i ≤ k) (hjk : j ≤ k)
    (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)))
    (hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k))) :
    rangeHomTransition R f i j A B k k hik hjk hik hjk le_rfl hAk hBk =
      AddMonoidHom.id _ := by
  classical
  have hself (x : R k) : f k k le_rfl x = x := by
    exact DirectedSystem.map_self' f x
  apply AddMonoidHom.ext
  intro g
  apply (Matrix.rangeHomEquiv hAk hBk).injective
  apply Subtype.ext
  exact
    (rangeHomEquiv_rangeHomTransition R f i j A B k k hik hjk hik hjk
      le_rfl hAk hBk hAk hBk g).trans (by
        ext p q
        exact hself _)

omit [IsDirectedOrder I] [Nonempty I] in
/-- Canonical transitions compose as additive maps. -/
theorem rangeHomTransition_comp
    (i j : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (k l m : I) (hik : i ≤ k) (hjk : j ≤ k)
    (hil : i ≤ l) (hjl : j ≤ l) (him : i ≤ m) (hjm : j ≤ m)
    (hkl : k ≤ l) (hlm : l ≤ m)
    (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)))
    (hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k)))
    (hAl : IsIdempotentElem (A.map (f i l hil : R i →+* R l)))
    (hBl : IsIdempotentElem (B.map (f j l hjl : R j →+* R l))) :
    (rangeHomTransition R f i j A B l m hil hjl him hjm hlm hAl hBl).comp
        (rangeHomTransition R f i j A B k l hik hjk hil hjl hkl hAk hBk) =
      rangeHomTransition R f i j A B k m hik hjk him hjm
        (hkl.trans hlm) hAk hBk := by
  classical
  have eA :
      (A.map (f i l hil : R i →+* R l)).map (f l m hlm : R l →+* R m) =
        A.map (f i m him : R i →+* R m) := by
    ext p q
    change f l m hlm (f i l hil (A p q)) = f i m him (A p q)
    exact DirectedSystem.map_map' f hil hlm (A p q)
  have eB :
      (B.map (f j l hjl : R j →+* R l)).map (f l m hlm : R l →+* R m) =
        B.map (f j m hjm : R j →+* R m) := by
    ext p q
    change f l m hlm (f j l hjl (B p q)) = f j m hjm (B p q)
    exact DirectedSystem.map_map' f hjl hlm (B p q)
  have hAm : IsIdempotentElem (A.map (f i m him : R i →+* R m)) := by
    rw [← eA]
    exact hAl.map ((f l m hlm : R l →+* R m).mapMatrix)
  have hBm : IsIdempotentElem (B.map (f j m hjm : R j →+* R m)) := by
    rw [← eB]
    exact hBl.map ((f l m hlm : R l →+* R m).mapMatrix)
  apply AddMonoidHom.ext
  intro g
  apply (Matrix.rangeHomEquiv hAm hBm).injective
  apply Subtype.ext
  change
    (Matrix.rangeHomEquiv hAm hBm
      (rangeHomTransition R f i j A B l m hil hjl him hjm hlm hAl hBl
        (rangeHomTransition R f i j A B k l hik hjk hil hjl hkl hAk hBk g)) :
        Matrix κ ι (R m)) =
      (Matrix.rangeHomEquiv hAm hBm
        (rangeHomTransition R f i j A B k m hik hjk him hjm
          (hkl.trans hlm) hAk hBk g) : Matrix κ ι (R m))
  simp only [rangeHomEquiv_rangeHomTransition]
  ext p q
  exact DirectedSystem.map_map' f hkl hlm _

/-- The canonical limit comparison is compatible with stage transition. -/
theorem rangeHomToLimit_comp_transition
    (i j : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (k l : I) (hik : i ≤ k) (hjk : j ≤ k)
    (hil : i ≤ l) (hjl : j ≤ l) (hkl : k ≤ l)
    (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)))
    (hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k)))
    (hAl : IsIdempotentElem (A.map (f i l hil : R i →+* R l)))
    (hBl : IsIdempotentElem (B.map (f j l hjl : R j →+* R l))) :
    (rangeHomToLimit R f i j A B l hil hjl hAl hBl).comp
        (rangeHomTransition R f i j A B k l hik hjk hil hjl hkl hAk hBk) =
      rangeHomToLimit R f i j A B k hik hjk hAk hBk := by
  classical
  have eA :
      (A.map (f i l hil : R i →+* R l)).map (DirectLimit.Ring.of R f l) =
        A.map (DirectLimit.Ring.of R f i) := by
    ext p q
    change (DirectLimit.Ring.of R f l) (f i l hil (A p q)) =
      (DirectLimit.Ring.of R f i) (A p q)
    simp only [DirectLimit.Ring.of_f]
  have eB :
      (B.map (f j l hjl : R j →+* R l)).map (DirectLimit.Ring.of R f l) =
        B.map (DirectLimit.Ring.of R f j) := by
    ext p q
    change (DirectLimit.Ring.of R f l) (f j l hjl (B p q)) =
      (DirectLimit.Ring.of R f j) (B p q)
    simp only [DirectLimit.Ring.of_f]
  have hAL : IsIdempotentElem (A.map (DirectLimit.Ring.of R f i)) := by
    rw [← eA]
    exact hAl.map ((DirectLimit.Ring.of R f l).mapMatrix)
  have hBL : IsIdempotentElem (B.map (DirectLimit.Ring.of R f j)) := by
    rw [← eB]
    exact hBl.map ((DirectLimit.Ring.of R f l).mapMatrix)
  apply AddMonoidHom.ext
  intro g
  apply (Matrix.rangeHomEquiv hAL hBL).injective
  apply Subtype.ext
  change
    (Matrix.rangeHomEquiv hAL hBL
      (rangeHomToLimit R f i j A B l hil hjl hAl hBl
        (rangeHomTransition R f i j A B k l hik hjk hil hjl hkl hAk hBk g)) :
        Matrix κ ι (DirectLimit R f)) =
      (Matrix.rangeHomEquiv hAL hBL
        (rangeHomToLimit R f i j A B k hik hjk hAk hBk g) :
          Matrix κ ι (DirectLimit R f))
  simp only [rangeHomEquiv_rangeHomToLimit, rangeHomEquiv_rangeHomTransition]
  ext p q
  change (DirectLimit.Ring.of R f l)
      (f k l hkl ((Matrix.rangeHomEquiv hAk hBk g : Matrix κ ι (R k)) p q)) =
    (DirectLimit.Ring.of R f k)
      ((Matrix.rangeHomEquiv hAk hBk g : Matrix κ ι (R k)) p q)
  simp only [DirectLimit.Ring.of_f]

/-- An original map between the prescribed limit ranges is the canonical image
of an original range map at one common upper stage. -/
theorem exists_rangeHom_at_common_stage
    (i j : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B)
    (h :
      (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
        (A.map (DirectLimit.Ring.of R f i))).range →ₗ[(DirectLimit R f)ᵐᵒᵖ]
      (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
        (B.map (DirectLimit.Ring.of R f j))).range) :
    ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
      ∃ (hAk : IsIdempotentElem (A.map (f i k hik : R i →+* R k)))
        (hBk : IsIdempotentElem (B.map (f j k hjk : R j →+* R k)))
        (g : (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
            (A.map (f i k hik : R i →+* R k))).range →ₗ[(R k)ᵐᵒᵖ]
          (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
            (B.map (f j k hjk : R j →+* R k))).range),
        rangeHomToLimit R f i j A B k hik hjk hAk hBk g = h := by
  classical
  have hAL : IsIdempotentElem (A.map (DirectLimit.Ring.of R f i)) :=
    hA.map ((DirectLimit.Ring.of R f i).mapMatrix)
  have hBL : IsIdempotentElem (B.map (DirectLimit.Ring.of R f j)) :=
    hB.map ((DirectLimit.Ring.of R f j).mapMatrix)
  let Y : Matrix κ ι (DirectLimit R f) :=
    (Matrix.rangeHomEquiv hAL hBL h : Matrix κ ι (DirectLimit R f))
  obtain ⟨hBY, hYA⟩ :=
    (Matrix.mem_normalizedHom (A.map (DirectLimit.Ring.of R f i))
      (B.map (DirectLimit.Ring.of R f j)) Y).mp
        (Matrix.rangeHomEquiv hAL hBL h).property
  change B.map (DirectLimit.NonUnitalRing.of R f j) * Y = Y at hBY
  change Y * A.map (DirectLimit.NonUnitalRing.of R f i) = Y at hYA
  obtain ⟨k, hik, hjk, Z, hZ, hBZ, hZA⟩ :=
    DirectLimit.exists_normalized_matrix R f i j A B Y hBY hYA
  let Ak : Matrix ι ι (R k) := A.map (f i k hik : R i →+* R k)
  let Bk : Matrix κ κ (R k) := B.map (f j k hjk : R j →+* R k)
  have hAk : IsIdempotentElem Ak :=
    hA.map ((f i k hik : R i →+* R k).mapMatrix)
  have hBk : IsIdempotentElem Bk :=
    hB.map ((f j k hjk : R j →+* R k).mapMatrix)
  let Zk : Matrix.normalizedHom Ak Bk :=
    ⟨Z, (Matrix.mem_normalizedHom Ak Bk Z).mpr ⟨hBZ, hZA⟩⟩
  let g := Matrix.normalizedHom.toRangeHom Zk
  refine ⟨k, hik, hjk, hAk, hBk, g, ?_⟩
  apply (Matrix.rangeHomEquiv hAL hBL).injective
  apply Subtype.ext
  rw [rangeHomEquiv_rangeHomToLimit R f i j A B k hik hjk
    hAk hBk hAL hBL g]
  have hg : Matrix.rangeHomEquiv hAk hBk g = Zk :=
    Matrix.rangeHomEquiv_toRangeHom hAk hBk Zk
  rw [hg]
  change Z.map (DirectLimit.Ring.of R f k) = Y
  change Z.map (DirectLimit.Ring.of R f k) = Y at hZ
  exact hZ

/-- Original range maps have equal canonical limit maps exactly when their
canonical transitions are equal in one original Hom at a common later stage. -/
theorem rangeHomToLimit_eq_iff_eventually_eq
    (i j : I) (A : Matrix ι ι (R i)) (B : Matrix κ κ (R j))
    (k₁ k₂ : I)
    (hik₁ : i ≤ k₁) (hjk₁ : j ≤ k₁)
    (hik₂ : i ≤ k₂) (hjk₂ : j ≤ k₂)
    (hAk₁ : IsIdempotentElem (A.map (f i k₁ hik₁ : R i →+* R k₁)))
    (hBk₁ : IsIdempotentElem (B.map (f j k₁ hjk₁ : R j →+* R k₁)))
    (hAk₂ : IsIdempotentElem (A.map (f i k₂ hik₂ : R i →+* R k₂)))
    (hBk₂ : IsIdempotentElem (B.map (f j k₂ hjk₂ : R j →+* R k₂)))
    (g₁ :
      (Matrix.mulVecBilin (R k₁) (R k₁)ᵐᵒᵖ
        (A.map (f i k₁ hik₁ : R i →+* R k₁))).range →ₗ[(R k₁)ᵐᵒᵖ]
      (Matrix.mulVecBilin (R k₁) (R k₁)ᵐᵒᵖ
        (B.map (f j k₁ hjk₁ : R j →+* R k₁))).range)
    (g₂ :
      (Matrix.mulVecBilin (R k₂) (R k₂)ᵐᵒᵖ
        (A.map (f i k₂ hik₂ : R i →+* R k₂))).range →ₗ[(R k₂)ᵐᵒᵖ]
      (Matrix.mulVecBilin (R k₂) (R k₂)ᵐᵒᵖ
        (B.map (f j k₂ hjk₂ : R j →+* R k₂))).range) :
    rangeHomToLimit R f i j A B k₁ hik₁ hjk₁ hAk₁ hBk₁ g₁ =
        rangeHomToLimit R f i j A B k₂ hik₂ hjk₂ hAk₂ hBk₂ g₂ ↔
      ∃ (l : I) (hk₁l : k₁ ≤ l) (hk₂l : k₂ ≤ l),
        rangeHomTransition R f i j A B k₁ l hik₁ hjk₁
            (hik₁.trans hk₁l) (hjk₁.trans hk₁l) hk₁l hAk₁ hBk₁ g₁ =
          rangeHomTransition R f i j A B k₂ l hik₂ hjk₂
            (hik₁.trans hk₁l) (hjk₁.trans hk₁l) hk₂l hAk₂ hBk₂ g₂ := by
  classical
  let C₁ : Matrix κ ι (R k₁) :=
    (Matrix.rangeHomEquiv hAk₁ hBk₁ g₁ : Matrix κ ι (R k₁))
  let C₂ : Matrix κ ι (R k₂) :=
    (Matrix.rangeHomEquiv hAk₂ hBk₂ g₂ : Matrix κ ι (R k₂))
  have hAL : IsIdempotentElem (A.map (DirectLimit.Ring.of R f i)) := by
    have eA :
        (A.map (f i k₁ hik₁ : R i →+* R k₁)).map
            (DirectLimit.Ring.of R f k₁) =
          A.map (DirectLimit.Ring.of R f i) := by
      ext p q
      change (DirectLimit.Ring.of R f k₁) (f i k₁ hik₁ (A p q)) =
        (DirectLimit.Ring.of R f i) (A p q)
      simp only [DirectLimit.Ring.of_f]
    rw [← eA]
    exact hAk₁.map ((DirectLimit.Ring.of R f k₁).mapMatrix)
  have hBL : IsIdempotentElem (B.map (DirectLimit.Ring.of R f j)) := by
    have eB :
        (B.map (f j k₁ hjk₁ : R j →+* R k₁)).map
            (DirectLimit.Ring.of R f k₁) =
          B.map (DirectLimit.Ring.of R f j) := by
      ext p q
      change (DirectLimit.Ring.of R f k₁) (f j k₁ hjk₁ (B p q)) =
        (DirectLimit.Ring.of R f j) (B p q)
      simp only [DirectLimit.Ring.of_f]
    rw [← eB]
    exact hBk₁.map ((DirectLimit.Ring.of R f k₁).mapMatrix)
  have hlimit :
      rangeHomToLimit R f i j A B k₁ hik₁ hjk₁ hAk₁ hBk₁ g₁ =
          rangeHomToLimit R f i j A B k₂ hik₂ hjk₂ hAk₂ hBk₂ g₂ ↔
        C₁.map (DirectLimit.Ring.of R f k₁) =
          C₂.map (DirectLimit.Ring.of R f k₂) := by
    constructor
    · intro hmaps
      have hmat := congrArg
        (fun g => (Matrix.rangeHomEquiv hAL hBL g :
          Matrix κ ι (DirectLimit R f))) hmaps
      simpa only [rangeHomEquiv_rangeHomToLimit] using hmat
    · intro hmat
      apply (Matrix.rangeHomEquiv hAL hBL).injective
      apply Subtype.ext
      simpa only [rangeHomEquiv_rangeHomToLimit] using hmat
  have hstage (l : I) (hk₁l : k₁ ≤ l) (hk₂l : k₂ ≤ l) :
      rangeHomTransition R f i j A B k₁ l hik₁ hjk₁
          (hik₁.trans hk₁l) (hjk₁.trans hk₁l) hk₁l hAk₁ hBk₁ g₁ =
        rangeHomTransition R f i j A B k₂ l hik₂ hjk₂
          (hik₁.trans hk₁l) (hjk₁.trans hk₁l) hk₂l hAk₂ hBk₂ g₂ ↔
      C₁.map (f k₁ l hk₁l : R k₁ →+* R l) =
        C₂.map (f k₂ l hk₂l : R k₂ →+* R l) := by
    have hAl : IsIdempotentElem
        (A.map (f i l (hik₁.trans hk₁l) : R i →+* R l)) := by
      have eA :
          (A.map (f i k₁ hik₁ : R i →+* R k₁)).map
              (f k₁ l hk₁l : R k₁ →+* R l) =
            A.map (f i l (hik₁.trans hk₁l) : R i →+* R l) := by
        ext p q
        change f k₁ l hk₁l (f i k₁ hik₁ (A p q)) =
          f i l (hik₁.trans hk₁l) (A p q)
        exact DirectedSystem.map_map' f hik₁ hk₁l (A p q)
      rw [← eA]
      exact hAk₁.map ((f k₁ l hk₁l : R k₁ →+* R l).mapMatrix)
    have hBl : IsIdempotentElem
        (B.map (f j l (hjk₁.trans hk₁l) : R j →+* R l)) := by
      have eB :
          (B.map (f j k₁ hjk₁ : R j →+* R k₁)).map
              (f k₁ l hk₁l : R k₁ →+* R l) =
            B.map (f j l (hjk₁.trans hk₁l) : R j →+* R l) := by
        ext p q
        change f k₁ l hk₁l (f j k₁ hjk₁ (B p q)) =
          f j l (hjk₁.trans hk₁l) (B p q)
        exact DirectedSystem.map_map' f hjk₁ hk₁l (B p q)
      rw [← eB]
      exact hBk₁.map ((f k₁ l hk₁l : R k₁ →+* R l).mapMatrix)
    constructor
    · intro hmaps
      have hmat := congrArg
        (fun g => (Matrix.rangeHomEquiv hAl hBl g : Matrix κ ι (R l))) hmaps
      simpa only [rangeHomEquiv_rangeHomTransition] using hmat
    · intro hmat
      apply (Matrix.rangeHomEquiv hAl hBl).injective
      apply Subtype.ext
      simpa only [rangeHomEquiv_rangeHomTransition] using hmat
  rw [hlimit]
  constructor
  · intro hC
    have hentries : ∀ p : κ × ι,
        (⟦⟨k₁, C₁ p.1 p.2⟩⟧ : DirectLimit R f) = ⟦⟨k₂, C₂ p.1 p.2⟩⟧ := by
      intro p
      change (DirectLimit.Ring.of R f k₁) (C₁ p.1 p.2) =
        (DirectLimit.Ring.of R f k₂) (C₂ p.1 p.2)
      exact congrArg (fun C : Matrix κ ι (DirectLimit R f) => C p.1 p.2) hC
    obtain ⟨l, hk₁l, hk₂l, hl⟩ :=
      (DirectLimit.forall_mk_eq_iff_exists_of_fixed (G := R) f k₁ k₂
        (fun p : κ × ι => C₁ p.1 p.2) (fun p : κ × ι => C₂ p.1 p.2)).mp hentries
    refine ⟨l, hk₁l, hk₂l, (hstage l hk₁l hk₂l).mpr ?_⟩
    ext p q
    exact hl (p, q)
  · rintro ⟨l, hk₁l, hk₂l, hmaps⟩
    have hC := (hstage l hk₁l hk₂l).mp hmaps
    ext p q
    change (DirectLimit.Ring.of R f k₁) (C₁ p q) =
      (DirectLimit.Ring.of R f k₂) (C₂ p q)
    have hof₁ (x : R k₁) :
        (DirectLimit.Ring.of R f l) (f k₁ l hk₁l x) =
          (DirectLimit.Ring.of R f k₁) x := by
      simp only [DirectLimit.Ring.of_f]
    have hof₂ (x : R k₂) :
        (DirectLimit.Ring.of R f l) (f k₂ l hk₂l x) =
          (DirectLimit.Ring.of R f k₂) x := by
      simp only [DirectLimit.Ring.of_f]
    have hentry := congrArg (fun C : Matrix κ ι (R l) => C p q) hC
    change f k₁ l hk₁l (C₁ p q) = f k₂ l hk₂l (C₂ p q) at hentry
    have hentryL := congrArg (DirectLimit.Ring.of R f l) hentry
    exact (hof₁ (C₁ p q)).symm.trans (hentryL.trans (hof₂ (C₂ p q)))

end DirectedRangeHom
end DirectLimit
