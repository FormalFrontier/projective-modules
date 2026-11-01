/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Finiteness.Projective
import ProjectiveModules.Module.ProjectiveKernel
import ProjectiveModules.Module.RightEndomorphismMatrix
import ProjectiveModules.Module.RightRegular

/-!
# Finite projective right semimodules as idempotent matrix images

A right semimodule over a semiring is finite and projective if and only if it is linearly
equivalent to the range of an idempotent finite matrix acting on column vectors by left
multiplication. Right scalar multiplication is encoded by the canonical action of the
opposite semiring.

The forward construction uses a retract of a finite free semimodule and preserves the
original `R`-valued column vectors and their pointwise right action. The converse uses
the projection onto the same range. The matrix size may be zero.

## References

The classical description of finite projective right modules by idempotent matrices is
presented in C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*.
The classification here generalizes the ring formulation to semirings.

The construction uses Mathlib's finite-free retract theorem
`Module.Finite.exists_comp_eq_id_of_projective`, the canonical right-free coordinate
equivalence `Module.rightFreeCoordEquiv`, and the right-endomorphism matrix equivalence
`Module.rightEndomorphismMatrixEquiv`. The converse uses
`Module.Projective.range_of_isIdempotentElem`, which applies Mathlib's projection and
direct-summand APIs to the original linear-map range.
-/

@[expose] public section

universe u v

/-- Every finite projective right semimodule over a semiring is linearly equivalent to
the range of an idempotent matrix acting on column vectors by left multiplication.

The ambient vectors have the pointwise right action of `R`, encoded by `Rᵐᵒᵖ`.
The ambient size may be zero. -/
theorem Module.Projective.exists_equiv_range_idempotent_matrix
    {R : Type u} [Semiring R] {P : Type v} [AddCommMonoid P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P] :
    ∃ (n : ℕ) (e : Matrix (Fin n) (Fin n) R),
      e * e = e ∧ Nonempty (P ≃ₗ[Rᵐᵒᵖ] LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ e)) := by
  classical
  obtain ⟨n, f, g, hf, hg, hfg⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective Rᵐᵒᵖ P
  let c : (Fin n → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (Fin n → R) :=
    Module.rightFreeCoordEquiv R (Fin n)
  let f' : (Fin n → R) →ₗ[Rᵐᵒᵖ] P := f.comp c.symm.toLinearMap
  let g' : P →ₗ[Rᵐᵒᵖ] (Fin n → R) := c.toLinearMap.comp g
  have hfg' (x : P) : f' (g' x) = x := by
    change f (c.symm (c (g x))) = x
    rw [c.symm_apply_apply]
    exact congrArg (fun h : P →ₗ[Rᵐᵒᵖ] P => h x) hfg
  let F : Module.End Rᵐᵒᵖ (Fin n → R) := g'.comp f'
  have hF : F * F = F := by
    apply LinearMap.ext
    intro x
    change g' (f' (g' (f' x))) = g' (f' x)
    exact congrArg g' (hfg' (f' x))
  -- Endomorphism entries act by left multiplication, preserving the order of products.
  let E : Module.End Rᵐᵒᵖ (Fin n → R) ≃+* Matrix (Fin n) (Fin n) R :=
    Module.rightEndomorphismMatrixEquiv R (Fin n)
  let e := E F
  refine ⟨n, e, ?_, ?_⟩
  · calc
      e * e = E (F * F) := (E.map_mul F F).symm
      _ = e := congrArg E hF
  · have hmulVec : Matrix.mulVecBilin R Rᵐᵒᵖ e = F := by
      apply LinearMap.ext
      intro x
      exact Module.rightEndomorphismMatrixEquiv_mulVec R (Fin n) F x
    have hrange : LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ e) =
        LinearMap.range g' := by
      rw [hmulVec]
      exact LinearMap.range_comp_of_range_eq_top g'
        (LinearMap.range_eq_top.mpr (hf.comp c.symm.surjective))
    exact ⟨(LinearEquiv.ofInjective g' (c.injective.comp hg)).trans
      (LinearEquiv.ofEq _ _ hrange.symm)⟩

/-- An additive commutative monoid with a right semimodule structure over a semiring is
finitely generated and projective if and only if it is linearly equivalent to the range
of an idempotent finite matrix acting on column vectors by left multiplication.

This generalizes the classical ring description in C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory* to semirings.
The range consists of `R`-valued columns with the canonical right action
`(MulOpposite.op a • x) i = x i * a`, encoded by `Rᵐᵒᵖ`.
Scalar and carrier universes are independent. The matrix size may be zero, and zero
semirings and the zero semimodule are allowed. -/
theorem Module.finite_projective_iff_exists_equiv_range_idempotent_matrix
    {R : Type u} [Semiring R] {P : Type v} [AddCommMonoid P] [Module Rᵐᵒᵖ P] :
    (Module.Finite Rᵐᵒᵖ P ∧ Module.Projective Rᵐᵒᵖ P) ↔
      ∃ (n : ℕ) (e : Matrix (Fin n) (Fin n) R), e * e = e ∧
        Nonempty (P ≃ₗ[Rᵐᵒᵖ] LinearMap.range (Matrix.mulVecBilin R Rᵐᵒᵖ e)) := by
  constructor
  · rintro ⟨hfin, hproj⟩
    let := hfin
    let := hproj
    exact Module.Projective.exists_equiv_range_idempotent_matrix
  · rintro ⟨n, e, he, ⟨f⟩⟩
    let L : Module.End Rᵐᵒᵖ (Fin n → R) := Matrix.mulVecBilin R Rᵐᵒᵖ e
    have hL : IsIdempotentElem L := by
      apply LinearMap.ext
      intro x
      change Matrix.mulVec e (Matrix.mulVec e x) = Matrix.mulVec e x
      rw [Matrix.mulVec_mulVec, he]
    have : Module.Projective Rᵐᵒᵖ L.range :=
      Module.Projective.range_of_isIdempotentElem L hL
    exact ⟨Module.Finite.equiv f.symm, Module.Projective.of_equiv' f.symm⟩
