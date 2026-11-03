/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine.Endomorphism.Product
public import ProjectiveModules.Module.ProjectivePi
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option
public import Mathlib.LinearAlgebra.Pi

/-!
# Determinants of finite dependent products

The scalar determinant of a componentwise endomorphism of a finite dependent
product of finite projective modules is the product of the scalar determinants
of its components. The index type only needs to be finite, and its universe is
independent of the scalar and factor universes.
For constant finite free factors, `Module.determinant_piMap` generalizes
Mathlib's `LinearMap.det_pi`.

The proof uses finite empty/option induction. Reindexing preserves determinants
by intertwining, and the option step reduces to the binary product formula.
Neither the ring nor the factors need to be nontrivial.
-/

@[expose] public section

open scoped BigOperators

universe u w v

namespace Module

variable (R : Type u) [CommRing R]

/-- Scalar determinants multiply under finite dependent products of finite
projective modules, without any constant-rank or freeness hypothesis. -/
theorem determinant_piMap
    {I : Type w} [_root_.Finite I] (P : I → Type v)
    [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
    [∀ i, Module.Finite R (P i)] [∀ i, Module.Projective R (P i)]
    (f : ∀ i, Module.End R (P i)) :
    Module.determinant R (∀ i, P i) (LinearMap.piMap f) =
      ∏ᶠ i, Module.determinant R (P i) (f i) := by
  classical
  let statement : Type w → Prop := fun J =>
    ∀ [_root_.Finite J] (Q : J → Type v)
      [∀ j, AddCommGroup (Q j)] [∀ j, Module R (Q j)]
      [∀ j, Module.Finite R (Q j)] [∀ j, Module.Projective R (Q j)]
      (g : ∀ j, Module.End R (Q j)),
      Module.determinant R (∀ j, Q j) (LinearMap.piMap g) =
        ∏ᶠ j, Module.determinant R (Q j) (g j)
  have h : statement I := by
    refine _root_.Finite.induction_empty_option (P := statement) ?_ ?_ ?_ I
    · intro α β e ih
      dsimp only [statement] at ih ⊢
      intro _ Q _ _ _ _ g
      let : Fintype β := Fintype.ofFinite β
      let : Fintype α := Fintype.ofEquiv β e.symm
      let E : (∀ b, Q b) ≃ₗ[R] (∀ a, Q (e a)) :=
        (LinearEquiv.piCongrLeft R Q e).symm
      have he :
          E.toLinearMap.comp (LinearMap.piMap g) =
            (LinearMap.piMap (fun a => g (e a))).comp E.toLinearMap := by
        apply LinearMap.ext
        intro x
        funext a
        rfl
      calc
        Module.determinant R (∀ b, Q b) (LinearMap.piMap g) =
            Module.determinant R (∀ a, Q (e a))
              (LinearMap.piMap (fun a => g (e a))) :=
          Module.determinant_eq_of_intertwining R _ _ E _ _ he
        _ = ∏ᶠ a, Module.determinant R (Q (e a)) (g (e a)) :=
          ih (fun a => Q (e a)) (fun a => g (e a))
        _ = ∏ᶠ b, Module.determinant R (Q b) (g b) := by
          simpa only [finprod_eq_prod_of_fintype] using
            e.prod_comp (fun b => Module.determinant R (Q b) (g b))
    · dsimp only [statement]
      intro _ Q _ _ _ _ g
      have hg : LinearMap.piMap g =
          (LinearMap.id : Module.End R (∀ i, Q i)) :=
        Subsingleton.elim _ _
      rw [hg, Module.determinant_id]
      simp [finprod_eq_prod_of_fintype]
    · intro α _ ih
      dsimp only [statement] at ih ⊢
      intro _ Q _ _ _ _ g
      let E : (∀ o, Q o) ≃ₗ[R] Q none × (∀ a, Q (some a)) :=
        LinearEquiv.piOptionEquivProd R
      have he :
          E.toLinearMap.comp (LinearMap.piMap g) =
            ((g none).prodMap (LinearMap.piMap (fun a => g (some a)))).comp
              E.toLinearMap := by
        apply LinearMap.ext
        intro x
        apply Prod.ext
        · rfl
        · rfl
      calc
        Module.determinant R (∀ o, Q o) (LinearMap.piMap g) =
            Module.determinant R (Q none × (∀ a, Q (some a)))
              ((g none).prodMap (LinearMap.piMap (fun a => g (some a)))) :=
          Module.determinant_eq_of_intertwining R _ _ E _ _ he
        _ = Module.determinant R (Q none) (g none) *
            Module.determinant R (∀ a, Q (some a))
              (LinearMap.piMap (fun a => g (some a))) :=
          Module.determinant_prodMap R _ _ _ _
        _ = Module.determinant R (Q none) (g none) *
            ∏ᶠ a, Module.determinant R (Q (some a)) (g (some a)) := by
          rw [ih (fun a => Q (some a)) (fun a => g (some a))]
        _ = ∏ᶠ o, Module.determinant R (Q o) (g o) := by
          simp only [finprod_eq_prod_of_fintype, Fintype.prod_option]
  exact h P f

end Module
