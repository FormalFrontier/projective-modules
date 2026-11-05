/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Matrix.Idempotent
public import ProjectiveModules.LinearAlgebra.Matrix.Projective
public import ProjectiveModules.Module.RightExtension
import AlgebraicDirectLimits.Matrix.ProductDescentSignature
import ProjectiveModules.LinearAlgebra.Matrix.IdempotentRanges
import ProjectiveModules.Module.RightExtensionMatrixRange

/-!
# Descent of finite projective right modules along directed ring limits

A finite projective right module over a nonempty directed limit of unital rings is
linearly equivalent to scalar extension of the range of a finite idempotent matrix
over one of the original rings. The scalar extension uses the canonical stage map
`DirectLimit.Ring.of`. The stage may depend on the module, and transition maps need
not be injective.

The range consists of columns over the stage ring with its canonical right action,
encoded by the opposite ring. It is finite projective by
`Module.finite_projective_iff_exists_equiv_range_idempotent_matrix`.
The index, stage-ring and module-carrier universes are independent; zero rings and
zero-dimensional matrices are allowed.

Prescribed idempotent ranges are compared over the limit and at common upper
stages. The mapped-range comparison allows unital semirings; canonical right
scalar extensions are compared over unital rings. Continuity of K₀ is not addressed.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, the
  finite-idempotent description of projective modules and directed-limit argument.
* Algebraic Direct Limits' finite idempotent-matrix descent and Projective Modules'
  original right-module idempotent-range classification and right scalar extension.
-/

@[expose] public section

universe uι uR uM uκ uν

namespace DirectLimit

/-- Every finite projective right module over a nonempty directed limit of unital
rings is linearly equivalent to extension of an idempotent matrix range from some
stage, along the canonical map from that stage to the limit.

The matrix acts on columns over the original stage ring by left multiplication;
right scalars act through the opposite ring. Its range is finite projective by the
idempotent-range classification. The stage is existential, not prescribed in advance.
No injectivity of the transition maps is required. This is the projective-module
form of the finite-matrix descent argument in Weibel's *The K-book*. -/
theorem exists_rightExtension_range_idempotent_matrix_equiv
    {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (R : ι → Type uR) [∀ i, Ring (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]
    (M : Type uM) [AddCommGroup M] [Module (DirectLimit R f)ᵐᵒᵖ M]
    [Module.Finite (DirectLimit R f)ᵐᵒᵖ M]
    [Module.Projective (DirectLimit R f)ᵐᵒᵖ M] :
    ∃ (i : ι) (n : ℕ) (A : Matrix (Fin n) (Fin n) (R i)),
      IsIdempotentElem A ∧
        Nonempty
          (ModuleCat.RightExtension.Obj (DirectLimit.Ring.of R f i)
            (LinearMap.range (Matrix.mulVecBilin (R i) (R i)ᵐᵒᵖ A)) ≃ₗ[
              (DirectLimit R f)ᵐᵒᵖ] M) := by
  classical
  obtain ⟨n, E, hE, ⟨eM⟩⟩ :=
    Module.Projective.exists_equiv_range_idempotent_matrix
      (R := DirectLimit R f) (P := M)
  obtain ⟨i, A, hA, hmap⟩ := exists_idempotent_matrix R f E hE
  -- The nonunital and unital canonical legs have the same entries in this limit.
  have hmap' : A.map (DirectLimit.Ring.of R f i) = E := by
    ext a b
    simpa only [Matrix.map_apply, Ring.of_apply, NonUnitalRing.of_apply]
      using congrFun (congrFun hmap a) b
  have eA : ModuleCat.RightExtension.Obj (DirectLimit.Ring.of R f i)
      (LinearMap.range (Matrix.mulVecBilin (R i) (R i)ᵐᵒᵖ A)) ≃ₗ[
        (DirectLimit R f)ᵐᵒᵖ]
      LinearMap.range (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ E) := by
    rw [← hmap']
    exact ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv
      (DirectLimit.Ring.of R f i) A hA
  exact ⟨i, n, A, hA, ⟨eA.trans eM.symm⟩⟩

/-- The right-column ranges of two prescribed finite idempotent matrices become
linearly equivalent over the directed limit exactly when their images are linearly
equivalent at some common upper stage of their original stages.

The matrices may have different, possibly empty finite index types. The transition
maps need not be injective. This asserts existence of an equivalence at a later
stage, not a lift of a prescribed equivalence over the limit. -/
theorem nonempty_rangeEquiv_iff_exists_common_stage
    {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (R : ι → Type uR) [∀ i, Semiring (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]
    {κ : Type uκ} [Fintype κ] {ν : Type uν} [Fintype ν]
    (i j : ι) (A : Matrix κ κ (R i)) (B : Matrix ν ν (R j))
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B) :
    Nonempty
      (LinearMap.range (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
        (A.map (DirectLimit.Ring.of R f i))) ≃ₗ[(DirectLimit R f)ᵐᵒᵖ]
        LinearMap.range (Matrix.mulVecBilin (DirectLimit R f) (DirectLimit R f)ᵐᵒᵖ
          (B.map (DirectLimit.Ring.of R f j)))) ↔
      ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
        Nonempty
          (LinearMap.range (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
            (A.map (f i k hik))) ≃ₗ[(R k)ᵐᵒᵖ]
            LinearMap.range (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
              (B.map (f j k hjk)))) := by
  classical
  have hA_lim : IsIdempotentElem (A.map (Ring.of R f i)) := by
    simpa only [RingHom.mapMatrix_apply] using hA.map (Ring.of R f i).mapMatrix
  have hB_lim : IsIdempotentElem (B.map (Ring.of R f j)) := by
    simpa only [RingHom.mapMatrix_apply] using hB.map (Ring.of R f j).mapMatrix
  rw [Matrix.nonempty_rangeEquiv_iff_exists_mul_eq _ _ hA_lim.eq hB_lim.eq]
  constructor
  · rintro ⟨X, Y, hXY, hYX⟩
    -- Both product equations descend with the same rectangular pair.
    obtain ⟨k, hik, hjk, Xk, Yk, _, _, hXkYk, hYkXk⟩ :=
      exists_matrix_products R f i j A B X Y hXY hYX
    have hAk : IsIdempotentElem (A.map (f i k hik)) := by
      simpa only [RingHom.mapMatrix_apply] using hA.map (f i k hik).mapMatrix
    have hBk : IsIdempotentElem (B.map (f j k hjk)) := by
      simpa only [RingHom.mapMatrix_apply] using hB.map (f j k hjk).mapMatrix
    refine ⟨k, hik, hjk, ⟨?_⟩⟩
    exact Matrix.rangeEquivOfMulEq _ _ hAk.eq hBk.eq Xk Yk hXkYk hYkXk
  · rintro ⟨k, hik, hjk, he⟩
    have hAk : IsIdempotentElem (A.map (f i k hik)) := by
      simpa only [RingHom.mapMatrix_apply] using hA.map (f i k hik).mapMatrix
    have hBk : IsIdempotentElem (B.map (f j k hjk)) := by
      simpa only [RingHom.mapMatrix_apply] using hB.map (f j k hjk).mapMatrix
    obtain ⟨X, Y, hXY, hYX⟩ :=
      (Matrix.nonempty_rangeEquiv_iff_exists_mul_eq _ _ hAk.eq hBk.eq).mp he
    refine ⟨X.map (Ring.of R f k), Y.map (Ring.of R f k), ?_, ?_⟩
    · rw [← Matrix.map_mul, hXY]
      ext a b
      exact Ring.of_f (G := R) (f := f) hik (A a b)
    · rw [← Matrix.map_mul, hYX]
      ext a b
      exact Ring.of_f (G := R) (f := f) hjk (B a b)

/-- Canonical right scalar extensions of the original ranges of two prescribed
finite idempotent matrices are linearly equivalent over the limit exactly when
the mapped ranges are linearly equivalent at some common upper stage.

The scalar extensions use `DirectLimit.Ring.of` and the original range modules.
Their comparison with mapped ranges is
`ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv`. The dimensions are
independent and may be empty, and no injectivity of transition maps is required. -/
theorem nonempty_rightExtension_rangeEquiv_iff_exists_common_stage
    {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (R : ι → Type uR) [∀ i, Ring (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]
    {κ : Type uκ} [Fintype κ] {ν : Type uν} [Fintype ν]
    (i j : ι) (A : Matrix κ κ (R i)) (B : Matrix ν ν (R j))
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B) :
    Nonempty
      (ModuleCat.RightExtension.Obj (DirectLimit.Ring.of R f i)
        (LinearMap.range (Matrix.mulVecBilin (R i) (R i)ᵐᵒᵖ A)) ≃ₗ[
          (DirectLimit R f)ᵐᵒᵖ]
        ModuleCat.RightExtension.Obj (DirectLimit.Ring.of R f j)
          (LinearMap.range (Matrix.mulVecBilin (R j) (R j)ᵐᵒᵖ B))) ↔
      ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
        Nonempty
          (LinearMap.range (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
            (A.map (f i k hik))) ≃ₗ[(R k)ᵐᵒᵖ]
            LinearMap.range (Matrix.mulVecBilin (R k) (R k)ᵐᵒᵖ
              (B.map (f j k hjk)))) := by
  let eA := ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv
    (DirectLimit.Ring.of R f i) A hA
  let eB := ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv
    (DirectLimit.Ring.of R f j) B hB
  refine Iff.trans ?_ (nonempty_rangeEquiv_iff_exists_common_stage R f i j A B hA hB)
  constructor
  · rintro ⟨e⟩
    exact ⟨eA.symm.trans (e.trans eB)⟩
  · rintro ⟨e⟩
    exact ⟨eA.trans (e.trans eB.symm)⟩

end DirectLimit
