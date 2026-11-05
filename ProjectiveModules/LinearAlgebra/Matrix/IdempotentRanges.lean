/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Projection
public import ProjectiveModules.Module.OrthogonalIdempotentRanges
import ProjectiveModules.Module.RightEndomorphismMatrix

/-!
# Idempotent matrix ranges

Rectangular factorizations give and characterize linear equivalences between the
right-column ranges of idempotent matrices. The columns are `R`-valued and the
linear equivalences use the opposite semiring, so scalars act on the right.
Normalized rectangular matrices also describe the right-linear homomorphisms
between these ranges additively.
-/

@[expose] public section

noncomputable section

open scoped Matrix

universe uR uι uκ

namespace Matrix

variable {R : Type uR} [Semiring R]
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]

/-- The equivalence between right-column ranges induced by a rectangular factorization.
The forward map is multiplication by `Y`, and the inverse is multiplication by `X`. -/
noncomputable def rangeEquivOfMulEq
    (A : Matrix ι ι R) (B : Matrix κ κ R)
    (hA : A * A = A) (hB : B * B = B)
    (X : Matrix ι κ R) (Y : Matrix κ ι R)
    (hXY : X * Y = A) (hYX : Y * X = B) :
    LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ A) ≃ₗ[Rᵐᵒᵖ]
      LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ B) := by
  classical
  let p := Matrix.mulVecBilin R Rᵐᵒᵖ A
  let q := Matrix.mulVecBilin R Rᵐᵒᵖ B
  let f := Matrix.mulVecBilin R Rᵐᵒᵖ Y
  let g := Matrix.mulVecBilin R Rᵐᵒᵖ X
  have hfg : f.comp g = q := by
    apply LinearMap.ext
    intro v
    change Y *ᵥ (X *ᵥ v) = B *ᵥ v
    rw [Matrix.mulVec_mulVec, hYX]
  have hgf : g.comp f = p := by
    apply LinearMap.ext
    intro v
    change X *ᵥ (Y *ᵥ v) = A *ᵥ v
    rw [Matrix.mulVec_mulVec, hXY]
  have hp : IsIdempotentElem p := by
    change p.comp p = p
    apply LinearMap.ext
    intro v
    change A *ᵥ (A *ᵥ v) = A *ᵥ v
    rw [Matrix.mulVec_mulVec, hA]
  have hq : IsIdempotentElem q := by
    change q.comp q = q
    apply LinearMap.ext
    intro v
    change B *ᵥ (B *ᵥ v) = B *ᵥ v
    rw [Matrix.mulVec_mulVec, hB]
  have hf : f.comp p = q.comp f := by
    calc
      f.comp p = f.comp (g.comp f) := by rw [hgf]
      _ = (f.comp g).comp f := rfl
      _ = q.comp f := by rw [hfg]
  have hg : g.comp q = p.comp g := by
    calc
      g.comp q = g.comp (f.comp g) := by rw [hfg]
      _ = (g.comp f).comp g := rfl
      _ = p.comp g := by rw [hgf]
  let f' := f.mapRangeOfIntertwines hf
  let g' := g.mapRangeOfIntertwines hg
  refine LinearEquiv.ofLinearMap f' g' ?_ ?_
  · apply LinearMap.ext
    intro w
    apply Subtype.ext
    change ((f.mapRangeOfIntertwines hf)
      ((g.mapRangeOfIntertwines hg) w) : κ → R) = (w : κ → R)
    rw [LinearMap.mapRangeOfIntertwines_apply,
      LinearMap.mapRangeOfIntertwines_apply]
    exact (DFunLike.congr_fun hfg (w : κ → R)).trans
      ((LinearMap.IsIdempotentElem.mem_range_iff hq).mp w.property)
  · apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ((g.mapRangeOfIntertwines hg)
      ((f.mapRangeOfIntertwines hf) v) : ι → R) = (v : ι → R)
    rw [LinearMap.mapRangeOfIntertwines_apply,
      LinearMap.mapRangeOfIntertwines_apply]
    exact (DFunLike.congr_fun hgf (v : ι → R)).trans
      ((LinearMap.IsIdempotentElem.mem_range_iff hp).mp v.property)

/-- The underlying function of the range equivalence is multiplication by `Y`. -/
theorem coe_rangeEquivOfMulEq
    (A : Matrix ι ι R) (B : Matrix κ κ R)
    (hA : A * A = A) (hB : B * B = B)
    (X : Matrix ι κ R) (Y : Matrix κ ι R)
    (hXY : X * Y = A) (hYX : Y * X = B) :
    (fun v : LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ A) =>
      (rangeEquivOfMulEq A B hA hB X Y hXY hYX v : κ → R)) =
    (fun v : LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ A) =>
      Y.mulVec (v : ι → R)) := by
  classical
  funext v
  rw [rangeEquivOfMulEq, LinearEquiv.coe_ofLinearMap,
    LinearMap.mapRangeOfIntertwines_apply, Matrix.mulVecBilin_apply]

/-- The range equivalence acts on columns by multiplication by `Y`. -/
@[simp]
theorem rangeEquivOfMulEq_apply
    (A : Matrix ι ι R) (B : Matrix κ κ R)
    (hA : A * A = A) (hB : B * B = B)
    (X : Matrix ι κ R) (Y : Matrix κ ι R)
    (hXY : X * Y = A) (hYX : Y * X = B)
    (v : LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ A)) :
    (rangeEquivOfMulEq A B hA hB X Y hXY hYX v : κ → R) =
      Y.mulVec (v : ι → R) := by
  exact congrFun (coe_rangeEquivOfMulEq A B hA hB X Y hXY hYX) v

/-- The inverse range equivalence acts on columns by multiplication by `X`. -/
@[simp]
theorem rangeEquivOfMulEq_symm_apply
    (A : Matrix ι ι R) (B : Matrix κ κ R)
    (hA : A * A = A) (hB : B * B = B)
    (X : Matrix ι κ R) (Y : Matrix κ ι R)
    (hXY : X * Y = A) (hYX : Y * X = B)
    (w : LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ B)) :
    ((rangeEquivOfMulEq A B hA hB X Y hXY hYX).symm w : ι → R) =
      X.mulVec (w : κ → R) := by
  classical
  rw [rangeEquivOfMulEq, LinearEquiv.symm_ofLinearMap,
    LinearEquiv.coe_ofLinearMap, LinearMap.mapRangeOfIntertwines_apply,
    Matrix.mulVecBilin_apply]

omit [Fintype κ] in
/-- A linear map from a finite right-coordinate module has a rectangular matrix. -/
private theorem exists_mulVecBilin_eq
    (f : (ι → R) →ₗ[Rᵐᵒᵖ] (κ → R)) :
    ∃ M : Matrix κ ι R, Matrix.mulVecBilin R Rᵐᵒᵖ M = f := by
  classical
  -- Represent each output component on the same finite sum-indexed module.
  let F (k : κ) : Module.End Rᵐᵒᵖ ((ι ⊕ Unit) → R) :=
    { toFun := fun w =>
        Sum.elim (fun _ : ι => 0)
          (fun _ : Unit => f (fun i => w (Sum.inl i)) k)
      map_add' := by
        intro v w
        funext z
        cases z with
        | inl i => simp
        | inr u =>
          change
            f ((fun i => v (Sum.inl i)) + (fun i => w (Sum.inl i))) k =
              (f (fun i => v (Sum.inl i)) + f (fun i => w (Sum.inl i))) k
          rw [map_add]
      map_smul' := by
        intro r v
        funext z
        cases z with
        | inl i => simp
        | inr u =>
          change
            f (r • (fun i => v (Sum.inl i))) k =
              (r • f (fun i => v (Sum.inl i))) k
          rw [map_smul] }
  let C (k : κ) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
    Module.rightEndomorphismMatrixEquiv R (ι ⊕ Unit) (F k)
  let M : Matrix κ ι R := fun k i => C k (Sum.inr ()) (Sum.inl i)
  refine ⟨M, ?_⟩
  apply LinearMap.ext
  intro v
  funext k
  rw [Matrix.mulVecBilin_apply]
  have h := congrFun
    (Module.rightEndomorphismMatrixEquiv_mulVec R (ι ⊕ Unit) (F k)
      (Sum.elim v (fun _ : Unit => 0))) (Sum.inr ())
  change
    (∑ j : ι ⊕ Unit,
      C k (Sum.inr ()) j * Sum.elim v (fun _ : Unit => 0) j) = f v k at h
  change (∑ i : ι, C k (Sum.inr ()) (Sum.inl i) * v i) = f v k
  simpa [Fintype.sum_sum_type] using h

/-- The right-column ranges of two idempotent matrices are isomorphic exactly when
the matrices admit a rectangular factorization. -/
theorem nonempty_rangeEquiv_iff_exists_mul_eq
    (A : Matrix ι ι R) (B : Matrix κ κ R)
    (hA : A * A = A) (hB : B * B = B) :
    Nonempty
      (LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ A) ≃ₗ[Rᵐᵒᵖ]
        LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ B)) ↔
      ∃ (X : Matrix ι κ R) (Y : Matrix κ ι R), X * Y = A ∧ Y * X = B := by
  classical
  constructor
  · rintro ⟨e⟩
    let p : Module.End Rᵐᵒᵖ (ι → R) := Matrix.mulVecBilin R Rᵐᵒᵖ A
    let q : Module.End Rᵐᵒᵖ (κ → R) := Matrix.mulVecBilin R Rᵐᵒᵖ B
    have hp (v : ι → R) : p (p v) = p v := by
      simpa only [p, Matrix.mulVecBilin_apply, hA] using
        (Matrix.mulVec_mulVec v A A)
    have hq (v : κ → R) : q (q v) = q v := by
      simpa only [q, Matrix.mulVecBilin_apply, hB] using
        (Matrix.mulVec_mulVec v B B)
    have hp_range (v : LinearMap.range p) :
        p.rangeRestrict (v : ι → R) = v := by
      apply Subtype.ext
      obtain ⟨w, hw⟩ := v.property
      change p (v : ι → R) = (v : ι → R)
      rw [← hw]
      exact hp w
    have hq_range (v : LinearMap.range q) :
        q.rangeRestrict (v : κ → R) = v := by
      apply Subtype.ext
      obtain ⟨w, hw⟩ := v.property
      change q (v : κ → R) = (v : κ → R)
      rw [← hw]
      exact hq w
    let t : (ι → R) →ₗ[Rᵐᵒᵖ] (κ → R) :=
      (LinearMap.range q).subtype.comp (e.toLinearMap.comp p.rangeRestrict)
    let s : (κ → R) →ₗ[Rᵐᵒᵖ] (ι → R) :=
      (LinearMap.range p).subtype.comp (e.symm.toLinearMap.comp q.rangeRestrict)
    have hst : s.comp t = p := by
      apply LinearMap.ext
      intro v
      change
        ((e.symm (q.rangeRestrict (e (p.rangeRestrict v) : κ → R)) :
          LinearMap.range p) : ι → R) = p v
      rw [hq_range, e.symm_apply_apply]
      rfl
    have hts : t.comp s = q := by
      apply LinearMap.ext
      intro v
      change
        ((e (p.rangeRestrict (e.symm (q.rangeRestrict v) : ι → R)) :
          LinearMap.range q) : κ → R) = q v
      rw [hp_range, e.apply_symm_apply]
      rfl
    obtain ⟨Y, hY⟩ := exists_mulVecBilin_eq t
    obtain ⟨X, hX⟩ := exists_mulVecBilin_eq s
    refine ⟨X, Y, ?_, ?_⟩
    · let E := Module.rightEndomorphismMatrixEquiv R ι
      apply E.symm.injective
      apply LinearMap.ext
      intro v
      calc
        E.symm (X * Y) v = (X * Y).mulVec v := by
          symm
          simpa only [E, RingEquiv.apply_symm_apply] using
            (Module.rightEndomorphismMatrixEquiv_mulVec R ι (E.symm (X * Y)) v)
        _ = A.mulVec v := by
          simpa only [LinearMap.comp_apply, ← hX, ← hY, p,
            Matrix.mulVecBilin_apply, Matrix.mulVec_mulVec] using
            (congrArg (fun f : Module.End Rᵐᵒᵖ (ι → R) => f v) hst)
        _ = E.symm A v := by
          simpa only [E, RingEquiv.apply_symm_apply] using
            (Module.rightEndomorphismMatrixEquiv_mulVec R ι (E.symm A) v)
    · let E := Module.rightEndomorphismMatrixEquiv R κ
      apply E.symm.injective
      apply LinearMap.ext
      intro v
      calc
        E.symm (Y * X) v = (Y * X).mulVec v := by
          symm
          simpa only [E, RingEquiv.apply_symm_apply] using
            (Module.rightEndomorphismMatrixEquiv_mulVec R κ (E.symm (Y * X)) v)
        _ = B.mulVec v := by
          simpa only [LinearMap.comp_apply, ← hX, ← hY, q,
            Matrix.mulVecBilin_apply, Matrix.mulVec_mulVec] using
            (congrArg (fun f : Module.End Rᵐᵒᵖ (κ → R) => f v) hts)
        _ = E.symm B v := by
          simpa only [E, RingEquiv.apply_symm_apply] using
            (Module.rightEndomorphismMatrixEquiv_mulVec R κ (E.symm B) v)
  · rintro ⟨X, Y, hXY, hYX⟩
    exact ⟨rangeEquivOfMulEq A B hA hB X Y hXY hYX⟩

/-- Rectangular matrices fixed by multiplication by the target matrix on the left
and by the source matrix on the right. -/
def normalizedHom (A : Matrix ι ι R) (B : Matrix κ κ R) :
    AddSubmonoid (Matrix κ ι R) where
  carrier := {Y | B * Y = Y ∧ Y * A = Y}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro X Y hX hY
    constructor
    · rw [Matrix.mul_add, hX.1, hY.1]
    · rw [Matrix.add_mul, hX.2, hY.2]

@[simp]
theorem mem_normalizedHom (A : Matrix ι ι R) (B : Matrix κ κ R) (Y : Matrix κ ι R) :
    Y ∈ normalizedHom A B ↔ B * Y = Y ∧ Y * A = Y := Iff.rfl


namespace normalizedHom

variable {A : Matrix ι ι R} {B : Matrix κ κ R}

/-- A normalized matrix is fixed by multiplication by its target matrix. -/
@[simp]
theorem mul_coe (Y : normalizedHom A B) :
    B * (Y : Matrix κ ι R) = (Y : Matrix κ ι R) :=
  ((mem_normalizedHom A B (Y : Matrix κ ι R)).mp Y.property).1

/-- A normalized matrix is fixed by multiplication by its source matrix. -/
@[simp]
theorem coe_mul (Y : normalizedHom A B) :
    (Y : Matrix κ ι R) * A = (Y : Matrix κ ι R) :=
  ((mem_normalizedHom A B (Y : Matrix κ ι R)).mp Y.property).2

/-- Column multiplication by a normalized matrix, restricted to the source range
and with codomain the target range, as an additive map of homomorphism spaces. -/
def toRangeHom :
    normalizedHom A B →+
      ((mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ]
        (mulVecBilin R Rᵐᵒᵖ B).range) where
  toFun Y :=
    ((mulVecBilin R Rᵐᵒᵖ (Y : Matrix κ ι R)).comp
      (mulVecBilin R Rᵐᵒᵖ A).range.subtype).codRestrict
        (mulVecBilin R Rᵐᵒᵖ B).range (by
          intro v
          refine ⟨(Y : Matrix κ ι R) *ᵥ (v : ι → R), ?_⟩
          change B *ᵥ ((Y : Matrix κ ι R) *ᵥ (v : ι → R)) =
            (Y : Matrix κ ι R) *ᵥ (v : ι → R)
          simpa only [mulVec_mulVec] using
            congrArg (fun M : Matrix κ ι R => M *ᵥ (v : ι → R)) (mul_coe Y))
  map_zero' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (0 : Matrix κ ι R) *ᵥ (v : ι → R) = 0
    simp
  map_add' := by
    intro Y Z
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ((Y : Matrix κ ι R) + (Z : Matrix κ ι R)) *ᵥ (v : ι → R) =
      (Y : Matrix κ ι R) *ᵥ (v : ι → R) +
        (Z : Matrix κ ι R) *ᵥ (v : ι → R)
    exact add_mulVec _ _ _

/-- The induced range map is original-valued column multiplication. -/
@[simp]
theorem toRangeHom_apply (Y : normalizedHom A B)
    (v : (mulVecBilin R Rᵐᵒᵖ A).range) :
    (toRangeHom Y v : κ → R) =
      (Y : Matrix κ ι R) *ᵥ (v : ι → R) :=
  rfl

/-- A source-normalized matrix is determined by its action on the source range. -/
theorem toRangeHom_injective :
    Function.Injective (toRangeHom (A := A) (B := B)) := by
  classical
  intro Y Z h
  apply Subtype.ext
  have hmul : (Y : Matrix κ ι R) * A = (Z : Matrix κ ι R) * A := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    let vA : (mulVecBilin R Rᵐᵒᵖ A).range := ⟨A *ᵥ v, ⟨v, rfl⟩⟩
    have hv := congrArg Subtype.val (LinearMap.congr_fun h vA)
    simpa only [toRangeHom_apply, vA, mulVec_mulVec] using hv
  calc
    (Y : Matrix κ ι R) = (Y : Matrix κ ι R) * A := (coe_mul Y).symm
    _ = (Z : Matrix κ ι R) * A := hmul
    _ = (Z : Matrix κ ι R) := coe_mul Z

end normalizedHom

namespace normalizedHom

universe uη

variable {η : Type uη} [Fintype η]
variable {A : Matrix ι ι R} {B : Matrix κ κ R} {C : Matrix η η R}

/-- An idempotent matrix, viewed as a normalized matrix from itself to itself. -/
def id (hA : IsIdempotentElem A) : normalizedHom A A :=
  ⟨A, (mem_normalizedHom A A A).2 ⟨hA, hA⟩⟩

/-- The matrix representing the identity is the source idempotent. -/
@[simp]
theorem coe_id (hA : IsIdempotentElem A) :
    (id hA : Matrix ι ι R) = A :=
  rfl

/-- Composition of normalized matrices is their matrix product. -/
def comp (Z : normalizedHom B C) (Y : normalizedHom A B) : normalizedHom A C :=
  ⟨(Z : Matrix η κ R) * (Y : Matrix κ ι R),
    (mem_normalizedHom A C _).2 (by
      constructor
      · rw [← Matrix.mul_assoc, mul_coe]
      · rw [Matrix.mul_assoc, coe_mul])⟩

/-- The underlying matrix of a composite is the product of the underlying matrices. -/
@[simp]
theorem coe_comp (Z : normalizedHom B C) (Y : normalizedHom A B) :
    (comp Z Y : Matrix η ι R) =
      (Z : Matrix η κ R) * (Y : Matrix κ ι R) :=
  rfl

/-- The range map induced by an idempotent matrix is the identity. -/
@[simp]
theorem toRangeHom_id (hA : IsIdempotentElem A) :
    toRangeHom (id hA) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  simp only [LinearMap.id_apply, toRangeHom_apply, coe_id]
  obtain ⟨w, hw⟩ := v.property
  change A *ᵥ w = (v : ι → R) at hw
  rw [← hw]
  simpa only [mulVec_mulVec] using
    congrArg (fun M : Matrix ι ι R => M *ᵥ w) (show A * A = A from hA)

/-- Multiplication of normalized matrices induces composition of their range maps. -/
@[simp]
theorem toRangeHom_comp (Z : normalizedHom B C) (Y : normalizedHom A B) :
    toRangeHom (comp Z Y) = (toRangeHom Z).comp (toRangeHom Y) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  simp only [LinearMap.comp_apply, toRangeHom_apply, coe_comp, mulVec_mulVec]

end normalizedHom

private theorem isIdempotentElem_mulVecBilin {A : Matrix ι ι R}
    (hA : IsIdempotentElem A) : IsIdempotentElem (mulVecBilin R Rᵐᵒᵖ A) := by
  have hAA : A * A = A := hA
  change (mulVecBilin R Rᵐᵒᵖ A).comp (mulVecBilin R Rᵐᵒᵖ A) =
    mulVecBilin R Rᵐᵒᵖ A
  apply LinearMap.ext
  intro v
  change A *ᵥ (A *ᵥ v) = A *ᵥ v
  rw [Matrix.mulVec_mulVec, hAA]

/-- Every right-linear map between idempotent ranges is induced by a normalized matrix. -/
theorem normalizedHom.toRangeHom_surjective
    {A : Matrix ι ι R} {B : Matrix κ κ R}
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B) :
    Function.Surjective (normalizedHom.toRangeHom (A := A) (B := B)) := by
  let a := mulVecBilin R Rᵐᵒᵖ A
  let b := mulVecBilin R Rᵐᵒᵖ B
  have ha : IsIdempotentElem a := isIdempotentElem_mulVecBilin hA
  have hb : IsIdempotentElem b := isIdempotentElem_mulVecBilin hB
  intro f
  let F : (ι → R) →ₗ[Rᵐᵒᵖ] κ → R :=
    b.range.subtype.comp (f.comp a.rangeRestrict)
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix κ ι R, mulVecBilin R Rᵐᵒᵖ Y = F := by
    exact exists_mulVecBilin_eq F
  have hBF : b.comp F = F :=
    (LinearMap.IsIdempotentElem.comp_eq_right_iff hb F).2 (by
      rintro z ⟨v, rfl⟩
      exact (f (a.rangeRestrict v)).property)
  have hπ : a.rangeRestrict.comp a = a.rangeRestrict := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change a (a v) = a v
    exact congrArg (fun q : Module.End Rᵐᵒᵖ (ι → R) => q v) ha
  have hFA : F.comp a = F := by
    dsimp only [F]
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hπ]
  have hBY : B * Y = Y := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [← Matrix.mulVec_mulVec]
    change b ((mulVecBilin R Rᵐᵒᵖ Y) v) = (mulVecBilin R Rᵐᵒᵖ Y) v
    rw [hY]
    exact congrArg (fun q : (ι → R) →ₗ[Rᵐᵒᵖ] κ → R => q v) hBF
  have hYA : Y * A = Y := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    rw [← Matrix.mulVec_mulVec]
    change (mulVecBilin R Rᵐᵒᵖ Y) (a v) = (mulVecBilin R Rᵐᵒᵖ Y) v
    rw [hY]
    exact congrArg (fun q : (ι → R) →ₗ[Rᵐᵒᵖ] κ → R => q v) hFA
  refine ⟨⟨Y, ⟨hBY, hYA⟩⟩, ?_⟩
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change (mulVecBilin R Rᵐᵒᵖ Y) (v : ι → R) = (f v : κ → R)
  rw [hY]
  have h_on : a.comp a.range.subtype = a.range.subtype :=
    (LinearMap.IsIdempotentElem.comp_eq_right_iff ha a.range.subtype).2 (by
      rintro z ⟨w, rfl⟩
      exact w.property)
  have hfix : a.rangeRestrict (v : ι → R) = v := by
    apply Subtype.ext
    change a (v : ι → R) = (v : ι → R)
    exact congrArg (fun q : a.range →ₗ[Rᵐᵒᵖ] ι → R => q v) h_on
  change (f (a.rangeRestrict (v : ι → R)) : κ → R) = (f v : κ → R)
  rw [hfix]

/-- Homomorphisms between the right ranges of two idempotent matrices correspond
additively to matrices normalized by those idempotents. -/
noncomputable def rangeHomEquiv {A : Matrix ι ι R} {B : Matrix κ κ R}
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B) :
    ((mulVecBilin R Rᵐᵒᵖ A).range →ₗ[Rᵐᵒᵖ] (mulVecBilin R Rᵐᵒᵖ B).range) ≃+
      normalizedHom A B := by
  exact (AddEquiv.ofBijective
    (normalizedHom.toRangeHom (A := A) (B := B))
    ⟨normalizedHom.toRangeHom_injective,
      normalizedHom.toRangeHom_surjective hA hB⟩).symm

end Matrix
