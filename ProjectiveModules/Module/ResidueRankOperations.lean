/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Cardinal ranks of residue-field fibres

At each prime of a commutative ring, the cardinal rank of a tensor-product fibre is the
product of the cardinal ranks of the two fibres, with universe lifts as needed. The cardinal
rank of the fibre of an arbitrary algebraic direct sum is the sum of the fibre ranks.

## Implementation notes

The proofs compose Mathlib's residue-field-linear tensor distribution equivalences with
`rank_tensorProduct` and `rank_directSum`. Freeness is used only for vector spaces over the
residue field; the original modules need not be free, flat or finitely generated.
-/

@[expose] public section

open scoped TensorProduct

universe uR vM vN wI

namespace Module

/-- The cardinal rank of a tensor-product fibre is the product of the cardinal ranks of its
factors' fibres. The lifts allow the two modules to lie in independent universes. -/
theorem rank_residueField_tensor_tensorProduct
    {R : Type uR} [CommRing R]
    {M : Type vM} [AddCommMonoid M] [Module R M]
    {N : Type vN} [AddCommMonoid N] [Module R N] (p : PrimeSpectrum R) :
    Module.rank p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] (M ⊗[R] N)) =
    Cardinal.lift.{vN}
        (Module.rank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) *
      Cardinal.lift.{vM}
        (Module.rank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] N)) := by
  calc
    _ = Module.rank p.asIdeal.ResidueField
        ((p.asIdeal.ResidueField ⊗[R] M) ⊗[p.asIdeal.ResidueField]
          (p.asIdeal.ResidueField ⊗[R] N)) :=
      (TensorProduct.AlgebraTensorModule.distribBaseChange
        (R := R) (A := p.asIdeal.ResidueField) (N := M) (Q := N)).rank_eq
    _ = _ := by
      -- Enlarging each lift by its source universe absorbs the residue-field universe.
      simpa only [← Cardinal.lift_umax] using
        (_root_.rank_tensorProduct (R := p.asIdeal.ResidueField)
          (S := p.asIdeal.ResidueField)
          (M := p.asIdeal.ResidueField ⊗[R] M)
          (M' := p.asIdeal.ResidueField ⊗[R] N))

/-- The cardinal rank of the residue-field fibre of an arbitrary direct sum is the cardinal
sum of the ranks of the summands' fibres. -/
theorem rank_residueField_tensor_directSum
    {R : Type uR} [CommRing R] {ι : Type wI}
    (P : ι → Type vM) [∀ i, AddCommMonoid (P i)]
    [∀ i, Module R (P i)] (p : PrimeSpectrum R) :
    Module.rank p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] DirectSum ι P) =
    Cardinal.sum (fun i => Module.rank p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] P i)) := by
  classical
  exact
    (TensorProduct.directSumRight R p.asIdeal.ResidueField p.asIdeal.ResidueField P).rank_eq.trans
      (_root_.rank_directSum (R := p.asIdeal.ResidueField)
        (fun i => p.asIdeal.ResidueField ⊗[R] P i))

end Module
