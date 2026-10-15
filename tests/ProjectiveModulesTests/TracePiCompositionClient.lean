/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.Trace.Pi
import ProjectiveModules.Module.Trace.Comparison
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

import Mathlib.Tactic.NormNum

/-!
# Rectangular coordinate paths through a function module

Two linear maps connect `Fin 2 → ℕ` with the dependent product whose `false`
factor is `ℕ` and whose `true` factor is `ℕ → ℕ`. The forward map has coordinates
`2 * x 0 + x 1` and the constant function with value `x 0 + 3 * x 1`. The reverse
map uses the scalar coordinate and evaluation at zero, with respective weights
`(4, 1)` and `(1, 5)`.

The rectangular-coordinate composition formula computes the finite-projective
trace of the composite as `25`. The four paths contribute `8`, `1`, `1`, and
`15`; their traces are computed on the regular module using comparison with the
finite-basis trace. Both off-diagonal coordinate maps of the composite send `1`
to `7`. All scalar actions are the canonical left actions of `ℕ`, and no
finite-generation or projectivity assumption is placed on either target factor.

## References

Coordinate maps follow the Mathlib formalization by Johannes Hölzl, Mario
Carneiro, Kevin Buzzard, Yury Kudryashov and Eric Wieser. Finite sums without
an enumeration follow the formalization by Kexing Ying, Kevin Buzzard and
Yury Kudryashov. The finite-basis trace interface is due to Johannes Hölzl,
Patrick Massot, Casper Putz, Anne Baanen and Antoine Labelle; the contraction
approach underlying finite-projective trace is due to Oliver Nash and
Antoine Labelle.
-/

noncomputable section

namespace ProjectiveModulesTests.TracePiCompositionClient

private abbrev P := Fin 2 → ℕ

private abbrev N : Bool → Type := Bool.rec ℕ (ℕ → ℕ)

private abbrev targetAddCommMonoid : ∀ j, AddCommMonoid (N j) :=
  Bool.rec (motive := fun j => AddCommMonoid (N j))
    (inferInstanceAs (AddCommMonoid ℕ))
    (Pi.addCommMonoid : AddCommMonoid (ℕ → ℕ))

attribute [local instance] targetAddCommMonoid

private abbrev targetModule : ∀ j, Module ℕ (N j) :=
  Bool.rec (motive := fun j => Module ℕ (N j))
    (inferInstanceAs (Module ℕ ℕ))
    (Pi.module ℕ (fun _ => ℕ) ℕ)

attribute [local instance] targetModule

private abbrev Q := ∀ j, N j

-- Select the existing pointwise structures, rather than the generic natural-number action.
private abbrev sourceModule : Module ℕ P := Pi.module (Fin 2) (fun _ => ℕ) ℕ
private abbrev functionModule : Module ℕ (ℕ → ℕ) := Pi.module ℕ (fun _ => ℕ) ℕ
private abbrev productModule : Module ℕ Q := Pi.module Bool N ℕ

attribute [local instance] sourceModule functionModule productModule

private def f : P →ₗ[ℕ] Q :=
  LinearMap.pi (R := ℕ) (φ := N)
    (Bool.rec (motive := fun j => P →ₗ[ℕ] N j)
      ((2 : ℕ) • (LinearMap.proj 0 : P →ₗ[ℕ] ℕ) + LinearMap.proj 1)
      ((LinearMap.pi fun _ : ℕ => (LinearMap.id : ℕ →ₗ[ℕ] ℕ)).comp
        ((LinearMap.proj 0 : P →ₗ[ℕ] ℕ) + (3 : ℕ) • LinearMap.proj 1)))

private def g : Q →ₗ[ℕ] P :=
  LinearMap.pi (R := ℕ) (φ := fun _ : Fin 2 => ℕ) fun i => if i = 0 then
    (4 : ℕ) • (LinearMap.proj false : Q →ₗ[ℕ] ℕ) +
      (LinearMap.proj (R := ℕ) (φ := fun _ : ℕ => ℕ) 0).comp
        (LinearMap.proj true : Q →ₗ[ℕ] (ℕ → ℕ))
  else
    (LinearMap.proj false : Q →ₗ[ℕ] ℕ) + (5 : ℕ) •
      (LinearMap.proj (R := ℕ) (φ := fun _ : ℕ => ℕ) 0).comp
        (LinearMap.proj true : Q →ₗ[ℕ] (ℕ → ℕ))

private theorem f_false_apply (x : P) : f x false = 2 * x 0 + x 1 := by
  simp [f, LinearMap.proj_apply, smul_eq_mul]

private theorem f_true_apply (x : P) (n : ℕ) : f x true n = x 0 + 3 * x 1 := by
  simp [f]

private theorem g_zero_apply (y : Q) : g y 0 = 4 * y false + y true 0 := by
  simp [g, LinearMap.proj_apply, smul_eq_mul]

private theorem g_one_apply (y : Q) : g y 1 = y false + 5 * y true 0 := by
  simp [g, LinearMap.proj_apply, smul_eq_mul]

private def path (i : Fin 2) (j : Bool) : ℕ →ₗ[ℕ] ℕ :=
  ((LinearMap.proj i : P →ₗ[ℕ] ℕ).comp
      (g.comp (@LinearMap.single ℕ Bool _ N _ _ (Classical.decEq Bool) j))).comp
    ((LinearMap.proj (R := ℕ) (φ := N) j).comp
      (f.comp (@LinearMap.single ℕ (Fin 2) _ (fun _ => ℕ) _ _
        (Classical.decEq (Fin 2)) i)))

private theorem path_zero_false :
    path 0 false = (8 : ℕ) • (LinearMap.id : ℕ →ₗ[ℕ] ℕ) := by
  let : DecidableEq (Fin 2) := Classical.decEq (Fin 2)
  let : DecidableEq Bool := Classical.decEq Bool
  apply LinearMap.ext
  intro n
  norm_num [path, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply,
    g_zero_apply, f_false_apply, smul_eq_mul, ← Nat.mul_assoc]

private theorem path_zero_true :
    path 0 true = (1 : ℕ) • (LinearMap.id : ℕ →ₗ[ℕ] ℕ) := by
  let : DecidableEq (Fin 2) := Classical.decEq (Fin 2)
  let : DecidableEq Bool := Classical.decEq Bool
  apply LinearMap.ext
  intro n
  simp [path, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply,
    g_zero_apply, f_true_apply]

private theorem path_one_false :
    path 1 false = (1 : ℕ) • (LinearMap.id : ℕ →ₗ[ℕ] ℕ) := by
  let : DecidableEq (Fin 2) := Classical.decEq (Fin 2)
  let : DecidableEq Bool := Classical.decEq Bool
  apply LinearMap.ext
  intro n
  simp [path, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply,
    g_one_apply, f_false_apply]

private theorem path_one_true :
    path 1 true = (15 : ℕ) • (LinearMap.id : ℕ →ₗ[ℕ] ℕ) := by
  let : DecidableEq (Fin 2) := Classical.decEq (Fin 2)
  let : DecidableEq Bool := Classical.decEq Bool
  apply LinearMap.ext
  intro n
  norm_num [path, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply,
    g_one_apply, f_true_apply, smul_eq_mul, ← Nat.mul_assoc]

private theorem trace_scalar (c : ℕ) :
    LinearMap.traceOfFiniteProjective ℕ ℕ (c • (LinearMap.id : ℕ →ₗ[ℕ] ℕ)) = c := by
  rw [LinearMap.traceOfFiniteProjective_eq_trace,
    LinearMap.trace_eq_matrix_trace ℕ (Module.Basis.singleton Unit ℕ)]
  simp [Matrix.trace, LinearMap.toMatrix_apply, smul_eq_mul]

private theorem trace_path_zero_false :
    LinearMap.traceOfFiniteProjective ℕ ℕ (path 0 false) = 8 := by
  rw [path_zero_false, trace_scalar]

private theorem trace_path_zero_true :
    LinearMap.traceOfFiniteProjective ℕ ℕ (path 0 true) = 1 := by
  rw [path_zero_true, trace_scalar]

private theorem trace_path_one_false :
    LinearMap.traceOfFiniteProjective ℕ ℕ (path 1 false) = 1 := by
  rw [path_one_false, trace_scalar]

private theorem trace_path_one_true :
    LinearMap.traceOfFiniteProjective ℕ ℕ (path 1 true) = 15 := by
  rw [path_one_true, trace_scalar]

/-- Summing the four rectangular path traces gives the trace of the composite. -/
private theorem trace_g_comp_f :
    LinearMap.traceOfFiniteProjective ℕ P (g.comp f) = 25 := by
  calc
    LinearMap.traceOfFiniteProjective ℕ P (g.comp f) =
        ∑ᶠ i : Fin 2, ∑ᶠ j : Bool,
          LinearMap.traceOfFiniteProjective ℕ ℕ (path i j) :=
      LinearMap.traceOfFiniteProjective_pi_comp ℕ (fun _ : Fin 2 => ℕ) N f g
    _ = 25 := by
      simp only [finsum_eq_sum_of_fintype, Fin.sum_univ_two, Fintype.sum_bool,
        trace_path_zero_false, trace_path_zero_true, trace_path_one_false, trace_path_one_true]
      norm_num

private theorem composite_zero_one_apply_one :
    ((LinearMap.proj (0 : Fin 2) : P →ₗ[ℕ] ℕ).comp
      ((g.comp f).comp (@LinearMap.single ℕ (Fin 2) _ (fun _ => ℕ) _ _
        (Classical.decEq (Fin 2)) 1))) 1 = 7 := by
  let : DecidableEq (Fin 2) := Classical.decEq (Fin 2)
  norm_num [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply,
    g_zero_apply, f_false_apply, f_true_apply]

private theorem composite_one_zero_apply_one :
    ((LinearMap.proj (1 : Fin 2) : P →ₗ[ℕ] ℕ).comp
      ((g.comp f).comp (@LinearMap.single ℕ (Fin 2) _ (fun _ => ℕ) _ _
        (Classical.decEq (Fin 2)) 0))) 1 = 7 := by
  let : DecidableEq (Fin 2) := Classical.decEq (Fin 2)
  norm_num [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply,
    g_one_apply, f_false_apply, f_true_apply]

example : LinearMap.traceOfFiniteProjective ℕ P (g.comp f) = 25 := trace_g_comp_f

example :
    ((LinearMap.proj (0 : Fin 2) : P →ₗ[ℕ] ℕ).comp
      ((g.comp f).comp (@LinearMap.single ℕ (Fin 2) _ (fun _ => ℕ) _ _
        (Classical.decEq (Fin 2)) 1))) 1 = 7 := composite_zero_one_apply_one

example :
    ((LinearMap.proj (1 : Fin 2) : P →ₗ[ℕ] ℕ).comp
      ((g.comp f).comp (@LinearMap.single ℕ (Fin 2) _ (fun _ => ℕ) _ _
        (Classical.decEq (Fin 2)) 0))) 1 = 7 := composite_one_zero_apply_one

end ProjectiveModulesTests.TracePiCompositionClient
