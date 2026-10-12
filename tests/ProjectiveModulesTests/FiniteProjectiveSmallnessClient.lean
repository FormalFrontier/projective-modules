/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.FiniteProjectiveSmallness
public import ProjectiveModules.Category.FiniteModuleDimension
public import Mathlib.Algebra.Field.Opposite
import Mathlib.Algebra.Ring.PUnit
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite projective smallness and representation clients

These clients use the derived small model with independent universes, normalize
regular and lifted inputs in the ring-universe reference category, and compare
zero-module and zero-ring classes. Over a division ring, the reference classes
of finite-dimensional right vector spaces are classified by the existing
finite-rank linear-equivalence theorem. In particular, coordinate spaces of
ranks zero and one have different classes.
-/

@[expose] public section

universe u v w

open CategoryTheory ModuleCat

namespace ProjectiveModulesTests.FiniteProjectiveSmallnessClient

-- Essential smallness is used to obtain a ring-universe small model and its
-- equivalence, rather than assumed in the hypotheses.
example (R : Type u) [Ring R] (X : FiniteProjective.{u, v} R) :
    Nonempty (((equivSmallModel.{u} (FiniteProjective.{u, v} R)).inverse.obj
      ((equivSmallModel.{u} (FiniteProjective.{u, v} R)).functor.obj X)) ≅ X) :=
  ⟨((equivSmallModel.{u} (FiniteProjective.{u, v} R)).unitIso.app X).symm⟩

-- The regular right module is present in the reference category, and a larger
-- input carrier yields the same class in that one reference skeleton.
example (R : Type u) [Ring R] :
    FiniteProjective.isoClass Rᵐᵒᵖ (ULift.{v} Rᵐᵒᵖ) =
      toSkeleton (FiniteProjective.of Rᵐᵒᵖ Rᵐᵒᵖ) := by
  rw [FiniteProjective.isoClass_ulift]
  exact FiniteProjective.isoClass_of Rᵐᵒᵖ (FiniteProjective.of Rᵐᵒᵖ Rᵐᵒᵖ)

-- Evaluation through the lift comparison recovers the represented element.
example (R : Type u) [Ring R] (x : R) :
    FiniteProjective.homLinearEquiv R _ _
      (FiniteProjective.reprULiftIso.{u, u, v} R R).hom
      ((FiniteProjective.reprEquiv R (ULift.{v} R)).symm ⟨x⟩) =
        (FiniteProjective.reprEquiv R R).symm x := by
  simp only [FiniteProjective.reprULiftIso_hom_apply, LinearEquiv.apply_symm_apply]

example (R : Type u) [Ring R] :
    FiniteProjective.isoClass Rᵐᵒᵖ (ULift.{v} PUnit.{1}) =
      toSkeleton (FiniteProjective.of Rᵐᵒᵖ PUnit.{u + 1}) :=
  FiniteProjective.isoClass_zero Rᵐᵒᵖ (ULift.{v} PUnit.{1})

-- All finite projective right modules collapse to one class over the zero
-- ring; no module-rank calculation is used.
example (R : Type u) [Ring R] [Subsingleton R]
    (X : FiniteProjective.{u, v} Rᵐᵒᵖ) (Y : FiniteProjective.{u, w} Rᵐᵒᵖ) :
    FiniteProjective.isoClass Rᵐᵒᵖ X = FiniteProjective.isoClass Rᵐᵒᵖ Y := by
  let : Subsingleton X := Module.subsingleton Rᵐᵒᵖ X
  let : Subsingleton Y := Module.subsingleton Rᵐᵒᵖ Y
  exact (FiniteProjective.isoClass_eq_iff Rᵐᵒᵖ X Y).2
    ⟨LinearEquiv.ofSubsingleton X Y⟩

example (n m : ℕ) :
    FiniteProjective.isoClass PUnit.{1} (Fin n → PUnit.{1}) =
      FiniteProjective.isoClass PUnit.{1} (Fin m → PUnit.{1}) :=
  (FiniteProjective.isoClass_eq_iff PUnit.{1} _ _).2
    ⟨LinearEquiv.ofSubsingleton _ _⟩

/-- Two finite-dimensional right vector spaces over a division ring have the
same class in the ring-universe reference skeleton exactly when their finite
dimensions agree, even for independent carrier universes. -/
theorem isoClass_eq_iff_finrank_eq (K : Type u) [DivisionRing K]
    (M : Type v) [AddCommGroup M] [Module Kᵐᵒᵖ M] [Module.Finite Kᵐᵒᵖ M]
    (N : Type w) [AddCommGroup N] [Module Kᵐᵒᵖ N] [Module.Finite Kᵐᵒᵖ N] :
    FiniteProjective.isoClass Kᵐᵒᵖ M = FiniteProjective.isoClass Kᵐᵒᵖ N ↔
      Module.finrank Kᵐᵒᵖ M = Module.finrank Kᵐᵒᵖ N := by
  rw [FiniteProjective.isoClass_eq_iff]
  constructor
  · rintro ⟨e⟩
    exact e.finrank_eq
  · intro h
    have hrepr : Module.finrank Kᵐᵒᵖ (Module.Finite.repr Kᵐᵒᵖ M) =
        Module.finrank Kᵐᵒᵖ (Module.Finite.repr Kᵐᵒᵖ N) := by
      simpa only [Module.Finite.finrank_repr] using h
    obtain ⟨e⟩ := (ModuleCat.nonempty_iso_iff_finrank_eq
      (X := ModuleCat.of Kᵐᵒᵖ (Module.Finite.repr Kᵐᵒᵖ M))
      (Y := ModuleCat.of Kᵐᵒᵖ (Module.Finite.repr Kᵐᵒᵖ N))).2 hrepr
    exact ⟨(Module.Finite.reprEquiv Kᵐᵒᵖ M).symm.trans
      (e.toLinearEquiv.trans (Module.Finite.reprEquiv Kᵐᵒᵖ N))⟩

private theorem rightFreeClasses (K : Type u) [DivisionRing K] (n m : ℕ) :
    FiniteProjective.isoClass Kᵐᵒᵖ (Fin n → Kᵐᵒᵖ) =
      FiniteProjective.isoClass Kᵐᵒᵖ (Fin m → Kᵐᵒᵖ) ↔ n = m := by
  rw [isoClass_eq_iff_finrank_eq]
  simp only [Module.finrank_fin_fun]

example (K : Type u) [DivisionRing K] :
    FiniteProjective.isoClass Kᵐᵒᵖ (Fin 1 → Kᵐᵒᵖ) ≠
      FiniteProjective.isoClass Kᵐᵒᵖ (Fin 0 → Kᵐᵒᵖ) := by
  intro h
  have hn := (rightFreeClasses K 1 0).1 h
  simp at hn

-- Product comparison is used to compute the dimension of the represented
-- direct sum, not to install a monoidal structure.
example (K : Type u) [DivisionRing K]
    (M : Type v) [AddCommGroup M] [Module Kᵐᵒᵖ M] [Module.Finite Kᵐᵒᵖ M]
    (N : Type w) [AddCommGroup N] [Module Kᵐᵒᵖ N] [Module.Finite Kᵐᵒᵖ N] :
    Module.finrank Kᵐᵒᵖ (FiniteProjective.repr Kᵐᵒᵖ (M × N)) =
      Module.finrank Kᵐᵒᵖ M + Module.finrank Kᵐᵒᵖ N := by
  rw [(FiniteProjective.isoToLinearEquiv
    (FiniteProjective.reprProdIso Kᵐᵒᵖ M N)).finrank_eq]
  rw [Module.finrank_prod, (FiniteProjective.reprEquiv Kᵐᵒᵖ M).finrank_eq,
    (FiniteProjective.reprEquiv Kᵐᵒᵖ N).finrank_eq]

end ProjectiveModulesTests.FiniteProjectiveSmallnessClient
