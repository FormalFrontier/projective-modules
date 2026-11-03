/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Abel

/-!
# Units from compositions of linear maps

For linear maps between two possibly different modules, the identity minus one
composition is a unit exactly when the identity minus the opposite composition
is a unit. If `V` is a two-sided inverse of `1 - r.comp i`, the inverse of
`1 - i.comp r` is `1 + i.comp (V.comp r)`.

Only additive-group module structures over a semiring are required.

## References

The proof uses Mathlib's two-sided unit criterion and endomorphism-ring interfaces.
-/

@[expose] public section

universe u v w

private theorem isUnit_one_sub_comp
    {R : Type u} [Semiring R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (i : N →ₗ[R] M) (r : M →ₗ[R] N)
    (h : IsUnit ((1 : Module.End R N) - r.comp i)) :
    IsUnit ((1 : Module.End R M) - i.comp r) := by
  obtain ⟨V, hleft, hright⟩ := isUnit_iff_exists.mp h
  refine isUnit_iff_exists.mpr ⟨1 + i.comp (V.comp r), ?_, ?_⟩
  · ext x
    have hx := congrArg (fun f : Module.End R N => i (f (r x))) hleft
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.comp_apply, map_sub] at hx
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.add_apply, LinearMap.comp_apply, map_add]
    calc
      x - i (r x) + (i (V (r x)) - i (r (i (V (r x))))) =
          x + (i (V (r x)) - i (r (i (V (r x)))) - i (r x)) := by abel
      _ = x := by rw [hx]; simp
  · ext x
    have hx := congrArg (fun f : Module.End R N => i (f (r x))) hright
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.comp_apply, map_sub] at hx
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.add_apply, LinearMap.comp_apply, map_sub]
    calc
      x + i (V (r x)) - (i (r x) + i (V (r (i (r x))))) =
          x + (i (V (r x)) - i (V (r (i (r x)))) - i (r x)) := by abel
      _ = x := by rw [hx]; simp

/-- The identity minus a composition of two linear maps is a unit if and only if
this holds for their composition in the opposite order, on the other module. -/
theorem LinearMap.isUnit_one_sub_comp_iff
    {R : Type u} [Semiring R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (i : N →ₗ[R] M) (r : M →ₗ[R] N) :
    IsUnit ((1 : Module.End R M) - i.comp r) ↔
      IsUnit ((1 : Module.End R N) - r.comp i) :=
  ⟨isUnit_one_sub_comp r i, isUnit_one_sub_comp i r⟩
