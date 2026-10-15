/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.Trace.Pi
import ProjectiveModules.Module.Trace.Comparison

/-!
# Rectangular composites and finite-projective trace

A one-coordinate natural-number module maps into a two-coordinate dependent product.
One target factor is the full function module `ℕ → ℕ`; the return map evaluates that
factor at zero. Both coordinate paths return the identity, while the composite is
twice the identity and has trace two. No finiteness or projectivity is imposed on
the target factors.

The trace computations use the finite-product trace formula, its linearity, and
the rank-one trace formula. Empty intermediate and source products supply the zero
boundary cases.

## References

The coordinate maps are from Mathlib's `LinearAlgebra.Pi`. The rank-one trace
formula is from `ProjectiveModules.Module.Trace.Basic`.
-/

universe uR uι uκ uM uN

section Rectangular

variable (R : Type uR) [CommSemiring R]
variable {ι : Type uι} [Finite ι] {κ : Type uκ} [hκ : Finite κ]
variable (M : ι → Type uM) (N : κ → Type uN)
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable [∀ i, Module.Finite R (M i)] [∀ i, Module.Projective R (M i)]
variable [∀ k, AddCommMonoid (N k)] [∀ k, Module R (N k)]

include hκ in
example (f : (∀ i, M i) →ₗ[R] (∀ k, N k))
    (g : (∀ k, N k) →ₗ[R] (∀ i, M i)) :
    LinearMap.traceOfFiniteProjective R (∀ i, M i) (g.comp f) =
      ∑ᶠ i : ι, LinearMap.traceOfFiniteProjective R (M i)
        ((LinearMap.proj (R := R) (φ := M) i).comp
          ((g.comp f).comp
            (@LinearMap.single R ι _ M _ _ (Classical.decEq ι) i))) :=
  LinearMap.traceOfFiniteProjective_pi R M (g.comp f)

end Rectangular

namespace RectangularNat

private abbrev Source := Unit → ℕ

private abbrev TargetFactor : Bool → Type
  | false => ℕ
  | true => ℕ → ℕ

-- Use the pointwise structures on function spaces, as in the coordinate-map constructors.
local instance : AddCommMonoid Source := Pi.addCommMonoid

local instance : Module ℕ Source := Pi.module Unit (fun _ => ℕ) ℕ

local instance : AddCommMonoid (ℕ → ℕ) := Pi.addCommMonoid

local instance : Module ℕ (ℕ → ℕ) := Pi.module ℕ (fun _ => ℕ) ℕ

local instance (b : Bool) : AddCommMonoid (TargetFactor b) :=
  match b with
  | false => inferInstanceAs (AddCommMonoid ℕ)
  | true => Pi.addCommMonoid

local instance (b : Bool) : Module ℕ (TargetFactor b) :=
  match b with
  | false => inferInstanceAs (Module ℕ ℕ)
  | true => Pi.module ℕ (fun _ => ℕ) ℕ

local instance : AddCommMonoid (∀ b, TargetFactor b) := Pi.addCommMonoid

local instance : Module ℕ (∀ b, TargetFactor b) := Pi.module Bool TargetFactor ℕ

private def forward : Source →ₗ[ℕ] (∀ b, TargetFactor b) :=
  LinearMap.pi (R := ℕ) (φ := TargetFactor) fun b =>
    match b with
    | false => LinearMap.proj (R := ℕ) (φ := fun _ : Unit => ℕ) ()
    | true => LinearMap.pi (R := ℕ) (φ := fun _ : ℕ => ℕ) fun _ =>
        LinearMap.proj (R := ℕ) (φ := fun _ : Unit => ℕ) ()

private def backward : (∀ b, TargetFactor b) →ₗ[ℕ] Source :=
  LinearMap.pi (R := ℕ) (φ := fun _ : Unit => ℕ) fun _ =>
    (LinearMap.proj (R := ℕ) (φ := TargetFactor) false) +
      (LinearMap.proj (R := ℕ) (φ := fun _ : ℕ => ℕ) 0).comp
        (LinearMap.proj (R := ℕ) (φ := TargetFactor) true)

private theorem forward_false (x : Source) : forward x false = x () := rfl

private theorem forward_true (x : Source) (n : ℕ) : forward x true n = x () := rfl

private theorem backward_apply (y : ∀ b, TargetFactor b) (u : Unit) :
    backward y u = y false + y true 0 := rfl

private noncomputable def outward (b : Bool) : ℕ →ₗ[ℕ] TargetFactor b :=
  (LinearMap.proj (R := ℕ) (φ := TargetFactor) b).comp
    (forward.comp
      (@LinearMap.single ℕ Unit _ (fun _ => ℕ) _ _ (Classical.decEq Unit) ()))

private noncomputable def inward (b : Bool) : TargetFactor b →ₗ[ℕ] ℕ :=
  (LinearMap.proj (R := ℕ) (φ := fun _ : Unit => ℕ) ()).comp
    (backward.comp
      (@LinearMap.single ℕ Bool _ TargetFactor _ _ (Classical.decEq Bool) b))

private theorem outward_false_apply (x : ℕ) : outward false x = x := by
  let : DecidableEq Unit := Classical.decEq Unit
  simp [outward, LinearMap.comp_apply, LinearMap.proj_apply, forward_false,
    LinearMap.single_apply]

private theorem outward_true_apply (x n : ℕ) : outward true x n = x := by
  let : DecidableEq Unit := Classical.decEq Unit
  simp [outward, LinearMap.comp_apply, LinearMap.proj_apply, forward_true,
    LinearMap.single_apply]

private theorem inward_false_apply (x : ℕ) : inward false x = x := by
  let : DecidableEq Bool := Classical.decEq Bool
  simp [inward, LinearMap.comp_apply, LinearMap.proj_apply, backward_apply,
    LinearMap.single_apply]

private theorem inward_true_apply (h : ℕ → ℕ) : inward true h = h 0 := by
  let : DecidableEq Bool := Classical.decEq Bool
  simp [inward, LinearMap.comp_apply, LinearMap.proj_apply, backward_apply,
    LinearMap.single_apply]

private theorem false_path : (inward false).comp (outward false) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact (inward_false_apply (outward false x)).trans (outward_false_apply x)

private theorem true_path : (inward true).comp (outward true) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact (inward_true_apply (outward true x)).trans (outward_true_apply x 0)

private theorem composite_eq_two_smul_id :
    backward.comp forward = (2 : ℕ) • (LinearMap.id : Source →ₗ[ℕ] Source) := by
  rw [two_smul]
  apply LinearMap.ext
  intro x
  funext u
  cases u
  simp only [LinearMap.comp_apply, backward_apply, forward_false, forward_true,
    LinearMap.add_apply, LinearMap.id_apply, Pi.add_apply]

private theorem trace_nat_id :
    LinearMap.traceOfFiniteProjective ℕ ℕ (LinearMap.id : ℕ →ₗ[ℕ] ℕ) = 1 := by
  have hid : (LinearMap.id : ℕ →ₗ[ℕ] ℕ) =
      (LinearMap.id : ℕ →ₗ[ℕ] ℕ).smulRight (1 : ℕ) := by
    apply LinearMap.ext
    intro x
    simp [smul_eq_mul]
  rw [hid, LinearMap.traceOfFiniteProjective_smulRight, LinearMap.id_apply]

private theorem source_id_block :
    (LinearMap.proj (R := ℕ) (φ := fun _ : Unit => ℕ) ()).comp
        ((LinearMap.id : Source →ₗ[ℕ] Source).comp
          (@LinearMap.single ℕ Unit _ (fun _ => ℕ) _ _ (Classical.decEq Unit) ())) =
      LinearMap.id := by
  let : DecidableEq Unit := Classical.decEq Unit
  simpa only [LinearMap.id_comp] using
    (LinearMap.proj_comp_single_same (R := ℕ) (φ := fun _ : Unit => ℕ) ())

private theorem trace_source_id :
    LinearMap.traceOfFiniteProjective ℕ Source (LinearMap.id : Source →ₗ[ℕ] Source) =
      1 := by
  rw [LinearMap.traceOfFiniteProjective_pi ℕ (fun _ : Unit => ℕ),
    finsum_eq_sum_of_fintype]
  simpa only [Fintype.sum_unique, show (default : Unit) = () from rfl,
    source_id_block] using trace_nat_id

private theorem trace_composite :
    LinearMap.traceOfFiniteProjective ℕ Source (backward.comp forward) = 2 := by
  rw [composite_eq_two_smul_id, map_smul, trace_source_id]
  rfl

private theorem trace_false_path :
    LinearMap.traceOfFiniteProjective ℕ ℕ ((inward false).comp (outward false)) = 1 := by
  rw [false_path, trace_nat_id]

private theorem trace_true_path :
    LinearMap.traceOfFiniteProjective ℕ ℕ ((inward true).comp (outward true)) = 1 := by
  rw [true_path, trace_nat_id]

example : backward.comp forward ≠ 0 := by
  intro h
  have hv := congrArg (fun F : Source →ₗ[ℕ] Source => F (fun _ => 1) ()) h
  simp [LinearMap.comp_apply, backward_apply, forward_false, forward_true] at hv

example :
    LinearMap.traceOfFiniteProjective ℕ Source (backward.comp forward) = 2 ∧
      LinearMap.traceOfFiniteProjective ℕ ℕ
          ((inward false).comp (outward false)) = 1 ∧
      LinearMap.traceOfFiniteProjective ℕ ℕ
          ((inward true).comp (outward true)) = 1 :=
  ⟨trace_composite, trace_false_path, trace_true_path⟩

example :
    LinearMap.traceOfFiniteProjective ℕ Source (backward.comp forward) =
      LinearMap.traceOfFiniteProjective ℕ ℕ ((inward false).comp (outward false)) +
        LinearMap.traceOfFiniteProjective ℕ ℕ ((inward true).comp (outward true)) := by
  rw [trace_composite, trace_false_path, trace_true_path]

example (h : ℕ → ℕ) :
    backward
        (@LinearMap.single ℕ Bool _ TargetFactor _ _ (Classical.decEq Bool) true h) () =
      h 0 := by
  simpa only [inward, LinearMap.comp_apply, LinearMap.proj_apply] using
    inward_true_apply h

example : inward true = LinearMap.proj (R := ℕ) (φ := fun _ : ℕ => ℕ) 0 := by
  apply LinearMap.ext
  intro h
  exact inward_true_apply h

example : inward true ≠ 0 := by
  intro h
  have hv := congrArg (fun F : (ℕ → ℕ) →ₗ[ℕ] ℕ => F (fun _ => 1)) h
  simp only [LinearMap.zero_apply] at hv
  exact Nat.one_ne_zero ((inward_true_apply (fun _ => 1)).symm.trans hv)

example :
    backward
        (@LinearMap.single ℕ Bool _ TargetFactor _ _ (Classical.decEq Bool) true
          (fun n => match n with | 0 => 1 | _ + 1 => 0)) () = 1 := by
  simpa only [inward, LinearMap.comp_apply, LinearMap.proj_apply] using
    inward_true_apply (fun n => match n with | 0 => 1 | _ + 1 => 0)

example :
    backward
        (@LinearMap.single ℕ Bool _ TargetFactor _ _ (Classical.decEq Bool) true
          (fun n => match n with | 0 => 0 | _ + 1 => 1)) () = 0 := by
  simpa only [inward, LinearMap.comp_apply, LinearMap.proj_apply] using
    inward_true_apply (fun n => match n with | 0 => 0 | _ + 1 => 1)

end RectangularNat

section EmptyIntermediate

variable (R : Type uR) [CommSemiring R]
variable (N : Empty → Type uN)
variable [∀ e, AddCommMonoid (N e)] [∀ e, Module R (N e)]

private theorem comp_through_empty
    {P : Type uM} [AddCommMonoid P] [Module R P]
    (f : P →ₗ[R] (∀ e, N e)) (g : (∀ e, N e) →ₗ[R] P) : g.comp f = 0 := by
  apply LinearMap.ext
  intro x
  have hf : f x = 0 := funext fun e => Empty.elim e
  simp only [LinearMap.comp_apply, hf, map_zero, LinearMap.zero_apply]

example (f : (Unit → ℕ) →ₗ[ℕ] (∀ e, N e))
    (g : (∀ e, N e) →ₗ[ℕ] (Unit → ℕ)) :
    g.comp f = 0 ∧
      LinearMap.traceOfFiniteProjective ℕ (Unit → ℕ) (g.comp f) = 0 := by
  have h := comp_through_empty ℕ N f g
  refine ⟨h, ?_⟩
  rw [h]
  exact map_zero (LinearMap.traceOfFiniteProjective ℕ (Unit → ℕ))

end EmptyIntermediate

section EmptySource

variable (R : Type uR) [CommSemiring R]
variable {κ : Type uκ} [hκ : Finite κ] (N : κ → Type uN)
variable [∀ k, AddCommMonoid (N k)] [∀ k, Module R (N k)]

include hκ in
example (f : (Empty → R) →ₗ[R] (∀ k, N k))
    (g : (∀ k, N k) →ₗ[R] (Empty → R)) :
    g.comp f = 0 ∧
      LinearMap.traceOfFiniteProjective R (Empty → R) (g.comp f) = 0 := by
  have h : g.comp f = 0 := by
    apply LinearMap.ext
    intro x
    exact funext fun e => Empty.elim e
  refine ⟨h, ?_⟩
  rw [h]
  exact map_zero (LinearMap.traceOfFiniteProjective R (Empty → R))

end EmptySource
