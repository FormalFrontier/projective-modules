/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Pairing.Regulator.Basic

/-!
# Evaluating a pairing regulator on subgroup bases

Given full-rank free subgroups of two finitely generated abelian groups, bases of the
subgroups evaluate the normalized regulator of the original real-valued integer-bilinear
pairing. The denominators are the indices of the given subgroups in the whole original
groups, including torsion. Neither original group is assumed free.

## Main result

* `LinearMap.pairingRegulator_eq_of_subgroup_bases` gives the normalized determinant
  formula for bases of given subgroups, with both bases indexed by the common rank.

## References

This specializes the normalized determinant identity to the given-subgroup formulation in
J. S. Milne, *Abelian Varieties*, Version 2.0, Introduction, Exercise 0.2. The source's
nondegeneracy assumption is not used in this identity, so a zero pairing determinant and
rank zero are included. The original groups and pairing are data; no group of rational
points or height pairing is constructed here.

The formalization uses Mathlib's `Module.Basis.linearIndependent` and
`LinearIndependent.map_injOn` for the coerced bases, and `Module.Basis.span_eq`,
`Submodule.map_span`, and `Submodule.range_subtype` to identify their spans with the given
subgroups before applying `LinearMap.pairingRegulator_eq`.
-/

@[expose] public section

universe u v w

open Module

namespace LinearMap

private theorem pairingRegulator_span_subgroup_basis
    {M : Type u} [AddCommGroup M] {ι : Type w}
    (E : AddSubgroup M) (b : Basis ι ℤ E) :
    (Submodule.span ℤ (Set.range (fun i => (b i : M)))).toAddSubgroup = E := by
  have hspan : Submodule.span ℤ (Set.range (fun i => (b i : M))) =
      E.toIntSubmodule := by
    calc
      Submodule.span ℤ (Set.range (fun i => (b i : M))) =
          (Submodule.span ℤ (Set.range b)).map E.subtype.toIntLinearMap := by
        rw [Submodule.map_span, ← Set.range_comp, AddMonoidHom.coe_toIntLinearMap,
          AddSubgroup.coe_subtype]
        rfl
      _ = E.toIntSubmodule := by
        rw [b.span_eq, Submodule.map_top]
        exact Submodule.range_subtype E.toIntSubmodule
  rw [hspan, AddSubgroup.toIntSubmodule_toAddSubgroup]

/-- Evaluate the regulator on bases of given full-rank free subgroups of the original
finitely generated abelian groups. Both denominator factors are full-group indices,
including torsion. No nondegeneracy, nonzero determinant, or positive-rank assumption is
needed, and freeness is required only through the supplied subgroup bases. This is the
subgroup-basis form of the identity in J. S. Milne, *Abelian Varieties*, Version 2.0,
Introduction, Exercise 0.2. -/
theorem pairingRegulator_eq_of_subgroup_bases
    {M : Type u} {N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module.Finite ℤ M] [Module.Finite ℤ N]
    (B : M →ₗ[ℤ] N →ₗ[ℤ] ℝ)
    (h : Module.finrank ℤ M = Module.finrank ℤ N)
    (E : AddSubgroup M) (F : AddSubgroup N)
    (bE : Basis (Fin (Module.finrank ℤ M)) ℤ E)
    (bF : Basis (Fin (Module.finrank ℤ M)) ℤ F) :
    B.pairingRegulator h =
      |(toMatrix₂Aux ℤ (fun i => (bE i : M)) (fun i => (bF i : N)) B).det| /
        ((E.index : ℝ) * (F.index : ℝ)) := by
  have he : LinearIndependent ℤ (fun i => (bE i : M)) :=
    bE.linearIndependent.map_injOn E.subtype.toIntLinearMap E.subtype_injective.injOn
  have hf : LinearIndependent ℤ (fun i => (bF i : N)) :=
    bF.linearIndependent.map_injOn F.subtype.toIntLinearMap F.subtype_injective.injOn
  simpa only [pairingRegulator_span_subgroup_basis E bE,
    pairingRegulator_span_subgroup_basis F bF] using
    (pairingRegulator_eq B h (fun i => (bE i : M)) (fun i => (bF i : N)) he hf)

end LinearMap
