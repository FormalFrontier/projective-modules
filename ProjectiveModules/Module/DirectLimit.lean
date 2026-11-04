/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Matrix.Idempotent
public import ProjectiveModules.LinearAlgebra.Matrix.Projective
public import ProjectiveModules.Module.RightExtension
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

This module concerns existence of descent, not eventual equivalence of two descended
modules or continuity of K₀.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, the
  finite-idempotent description of projective modules and directed-limit argument.
* Algebraic Direct Limits' finite idempotent-matrix descent and Projective Modules'
  original right-module idempotent-range classification and right scalar extension.
-/

@[expose] public section

universe uι uR uM

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

end DirectLimit
