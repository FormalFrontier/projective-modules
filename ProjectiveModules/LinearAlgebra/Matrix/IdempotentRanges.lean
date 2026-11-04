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

end Matrix
