/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
import ProjectiveModules.KTheory.InvariantBasisNumber
import ProjectiveModules.Module.LocallyConstantRank
import ProjectiveModules.Module.RightExtension
import ProjectiveModules.Module.RightRegular
public import Mathlib.Algebra.Field.Opposite
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Ring.PUnit
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Clients of the right-module K₀ construction

The constructions below use regular right modules, zero modules, independently
lifted carriers, and complementary idempotent summands over two fields. They
calculate direct-sum relations and evaluate the group-completion universal map.

The product examples give module decompositions. Detecting the corresponding
classes after group completion requires compatible additive invariants;
module nonfreeness alone is not a group-completion calculation.
-/

@[expose] public section

universe u v w

open CategoryTheory KTheory ModuleCat

namespace ProjectiveModulesTests.K0Client

-- Splitting a finite rank into two ranks splits its K₀ class additively.
example (R : Type u) [Ring R] (m n : ℕ) :
    K0.of R (Fin (m + n) → Rᵐᵒᵖ) =
      K0.of R (Fin m → Rᵐᵒᵖ) + K0.of R (Fin n → Rᵐᵒᵖ) := by
  simp only [K0.of_fin_fun_eq_nsmul, add_nsmul]

-- Opposite-ring IBN changes only the criterion, not the cyclic map into K₀(R).
example (R : Type u) [Ring R] :
    Function.Injective (zmultiplesHom (K0 R) (K0.of R Rᵐᵒᵖ)) ↔
      InvariantBasisNumber Rᵐᵒᵖ :=
  (K0.invariantBasisNumber_iff_injective_zmultiplesHom R).symm.trans
    MulOpposite.invariantBasisNumber_iff.symm

-- The ordinary regular right-module carrier and its scalar-self presentation
-- give the same generator even after an independent carrier lift and a zero sum.
example (R : Type u) [Ring R] :
    K0.of R (ULift.{v} R × PUnit.{w + 1}) = K0.of R Rᵐᵒᵖ := by
  rw [K0.of_prod, K0.of_ulift, K0.of_zero R (PUnit.{w + 1}), add_zero]
  exact K0.of_eq_of_equiv R R (MulOpposite.opLinearEquiv Rᵐᵒᵖ)

example (R : Type u) [Ring R] :
    ProjectiveClass.of R (PUnit.{v + 1} × ULift.{w} R) =
      ProjectiveClass.of R Rᵐᵒᵖ := by
  rw [ProjectiveClass.of_prod, ProjectiveClass.of_zero, ProjectiveClass.of_ulift, zero_add]
  exact ProjectiveClass.of_eq_of_equiv R R (MulOpposite.opLinearEquiv Rᵐᵒᵖ)

-- The output stays in the ring universe although these inputs need not.
private noncomputable def liftedRegularDifference (R : Type u) [Ring R] : K0 R :=
  K0.of R (ULift.{v} R × ULift.{w} R) - K0.of R R

example (R : Type u) [Ring R] :
    liftedRegularDifference.{u, v, w} R = K0.of R R := by
  simp only [liftedRegularDifference, K0.of_prod, K0.of_ulift, add_sub_cancel_right]

-- Over a zero ring all unital modules are subsingleton. No rank calculation
-- (which has a different zero-ring convention) is used here.
example (R : Type u) [Ring R] [Subsingleton R] :
    liftedRegularDifference.{u, v, w} R = 0 := by
  let : Subsingleton Rᵐᵒᵖ := inferInstance
  let : Subsingleton (ULift.{v} R × ULift.{w} R) :=
    Module.subsingleton Rᵐᵒᵖ (ULift.{v} R × ULift.{w} R)
  simp only [liftedRegularDifference, K0.of_zero, sub_zero]

example : K0.of PUnit.{1} (Fin 3 → PUnit.{1}) = 0 :=
  K0.of_zero PUnit.{1} (Fin 3 → PUnit.{1})

-- Extensionality and evaluation recover the identity homomorphism from its
-- restriction to the direct-sum class monoid.
example (R : Type u) [Ring R] :
    K0.lift R (K0.ofClass R) = AddMonoidHom.id (K0 R) := by
  apply K0.hom_ext R
  intro X
  simp only [K0.lift_of, K0.ofClass_of, AddMonoidHom.id_apply]

example (R : Type u) [Ring R] :
    K0.lift R (K0.ofClass R)
      (K0.of R (Rᵐᵒᵖ × ULift.{v} PUnit.{1})) = K0.of R Rᵐᵒᵖ := by
  simp only [K0.lift_of, ProjectiveClass.of_prod, ProjectiveClass.of_zero,
    add_zero, K0.ofClass_of]

-- Class elimination gives a representative even after adjoining a zero
-- module in an independent carrier universe.
example (R : Type u) [Ring R] (a : ProjectiveClass R) :
    ∃ X : FiniteProjective.{u, u} Rᵐᵒᵖ,
      ProjectiveClass.of R (X × PUnit.{v + 1}) = a := by
  refine ProjectiveClass.induction_on R a ?_
  intro X
  refine ⟨X, ?_⟩
  simp only [ProjectiveClass.of_prod, ProjectiveClass.of_zero, add_zero]

example (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (A : Type w) [AddZero A] (F : ProjectiveClass R →+ A) :
    F (ProjectiveClass.of R (FiniteProjective.repr Rᵐᵒᵖ M × PUnit.{w + 1})) =
      F (ProjectiveClass.of R M) := by
  simp only [ProjectiveClass.of_prod, ProjectiveClass.of_zero, add_zero,
    ProjectiveClass.of_repr]

-- The extension restricts back to the original class map, determined through
-- generator extensionality rather than a description of the resized quotient.
example (R : Type u) [Ring R] :
    (K0.lift R (K0.ofClass R)).comp (K0.ofClass R) = K0.ofClass R := by
  apply ProjectiveClass.addHom_ext R
  intro X
  simp only [AddMonoidHom.comp_apply, K0.lift_ofClass]

-- Reference-module evaluation has the supplied object function as its simp
-- normal form, even when that function is abstract and not repr-normalized.
example (R : Type u) [Ring R] (A : Type w) [AddZero A]
    (f : FiniteProjective.{u, u} Rᵐᵒᵖ → A)
    (hiso : ∀ {X Y : FiniteProjective.{u, u} Rᵐᵒᵖ}, (X ≅ Y) → f X = f Y)
    (hzero : f (FiniteProjective.of Rᵐᵒᵖ PUnit.{u + 1}) = 0)
    (hprod : ∀ X Y : FiniteProjective.{u, u} Rᵐᵒᵖ,
      f (FiniteProjective.of Rᵐᵒᵖ (X × Y)) = f X + f Y)
    (X : FiniteProjective.{u, u} Rᵐᵒᵖ) :
    ProjectiveClass.lift R f hiso hzero hprod (ProjectiveClass.of R X) = f X := by
  simp

-- Descending the module generator function recovers the canonical completion
-- map, using its zero/direct-sum/isomorphism laws as actual input data.
private theorem completionClassIso (R : Type u) [Ring R]
    {X Y : FiniteProjective.{u, u} Rᵐᵒᵖ} (e : X ≅ Y) :
    K0.of R X = K0.of R Y :=
  K0.of_eq_of_equiv R X (N := Y) (FiniteProjective.isoToLinearEquiv e)

private noncomputable def completionClassLift (R : Type u) [Ring R] :
    ProjectiveClass R →+ K0 R :=
  ProjectiveClass.lift R
    (fun X : FiniteProjective.{u, u} Rᵐᵒᵖ ↦ K0.of R X)
    (completionClassIso R)
    (K0.of_zero R PUnit.{u + 1})
    (fun X Y ↦ K0.of_prod R X Y)

example (R : Type u) [Ring R] : completionClassLift R = K0.ofClass R := by
  symm
  exact ProjectiveClass.lift_unique (R := R)
    (f := fun X : FiniteProjective.{u, u} Rᵐᵒᵖ ↦ K0.of R X)
    (hiso := completionClassIso R)
    (hzero := K0.of_zero R PUnit.{u + 1})
    (hadd := fun X Y ↦ K0.of_prod R X Y)
    (F := K0.ofClass R) (h := fun X ↦ K0.ofClass_of R X)

example (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    completionClassLift R (ProjectiveClass.of R M) = K0.of R M := by
  calc
    completionClassLift R (ProjectiveClass.of R M) =
        K0.of R (FiniteProjective.repr Rᵐᵒᵖ M) :=
      ProjectiveClass.lift_of_module (R := R) (M := M)
        (f := fun X : FiniteProjective.{u, u} Rᵐᵒᵖ ↦ K0.of R X)
        (hiso := completionClassIso R)
        (hzero := K0.of_zero R PUnit.{u + 1})
        (hadd := fun X Y ↦ K0.of_prod R X Y)
    _ = K0.of R M :=
      K0.of_eq_of_equiv R _ (FiniteProjective.reprEquiv Rᵐᵒᵖ M)

-- These are existing vector-space computations, independent of descent to
-- K₀. They distinguish a zero space, a line, and a plane.
example (K : Type u) [DivisionRing K] :
    Module.finrank Kᵐᵒᵖ (Fin 0 → Kᵐᵒᵖ) = 0 ∧
      Module.finrank Kᵐᵒᵖ (Fin 1 → Kᵐᵒᵖ) = 1 ∧
      Module.finrank Kᵐᵒᵖ (Fin 2 → Kᵐᵒᵖ) = 2 := by
  simp

example (K : Type u) [DivisionRing K] :
    Module.finrank Kᵐᵒᵖ (ULift.{v} Kᵐᵒᵖ × PUnit.{w + 1}) = 1 := by
  rw [Module.finrank_prod, finrank_ulift, Module.finrank_self,
    Module.finrank_zero_of_subsingleton, add_zero]

-- A line is not the zero *isomorphism class*. This uses module isomorphism
-- and finite dimension, not injectivity of the group-completion map.
/-- The regular right module over a division ring has nonzero isomorphism
class, as witnessed by its dimension one. -/
theorem regular_class_ne_zero (K : Type u) [DivisionRing K] :
    ProjectiveClass.of K Kᵐᵒᵖ ≠ (0 : ProjectiveClass K) := by
  intro h
  obtain ⟨e⟩ := (ProjectiveClass.of_eq_iff K Kᵐᵒᵖ PUnit.{u + 1}).1
    (h.trans (ProjectiveClass.of_zero K PUnit.{u + 1}).symm)
  have he := e.finrank_eq
  rw [Module.finrank_self, Module.finrank_zero_of_subsingleton] at he
  exact Nat.one_ne_zero he

section ProductFields

variable (K : Type u) (L : Type v) [Field K] [Field L]

private def productIdempotent : (K × L)ᵐᵒᵖ := MulOpposite.op (1, 0)

private theorem productIdempotent_isIdempotent : IsIdempotentElem (productIdempotent K L) := by
  simp [IsIdempotentElem, productIdempotent, ← MulOpposite.op_mul]

private noncomputable def firstSummand : FiniteProjective.{max u v, max u v} (K × L)ᵐᵒᵖ := by
  letI : Module.Finite (K × L)ᵐᵒᵖ (Ideal.span {productIdempotent K L}) :=
    Module.Finite.span_singleton _ _
  letI : Module.Projective (K × L)ᵐᵒᵖ (Ideal.span {productIdempotent K L}) :=
    (productIdempotent_isIdempotent K L).projective_span
  exact FiniteProjective.of (K × L)ᵐᵒᵖ (Ideal.span {productIdempotent K L})

private noncomputable def secondSummand : FiniteProjective.{max u v, max u v} (K × L)ᵐᵒᵖ := by
  letI : Module.Finite (K × L)ᵐᵒᵖ (Ideal.span {1 - productIdempotent K L}) :=
    Module.Finite.span_singleton _ _
  letI : Module.Projective (K × L)ᵐᵒᵖ (Ideal.span {1 - productIdempotent K L}) :=
    (productIdempotent_isIdempotent K L).one_sub.projective_span
  exact FiniteProjective.of (K × L)ᵐᵒᵖ (Ideal.span {1 - productIdempotent K L})

-- These are constructed finite projectives, not hypotheses supplied by the client.
example :
    K0.of (K × L) (firstSummand K L) + K0.of (K × L) (secondSummand K L) =
      K0.of (K × L) (K × L)ᵐᵒᵖ := by
  rw [← K0.of_prod]
  exact K0.of_eq_of_equiv (K × L) _
    (productIdempotent_isIdempotent K L).spanProdEquiv

end ProductFields

end ProjectiveModulesTests.K0Client
