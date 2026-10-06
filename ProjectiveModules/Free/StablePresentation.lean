/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finite stable presentations and their integer rank

A finite stable presentation identifies the product of a module with a finite
coordinate module with another finite coordinate module. Its existence is
equivalent to finite generation together with Mathlib's `Module.IsStablyFree`;
stable freeness by itself does not require finite generation. Under invariant
basis number, any two presentations give the same integer difference of the
numbers of coordinates. The cross-sum comparison works for arbitrary finite
index types over semirings, without requiring the presented module to be free.
This is distinct from the usual `Module.FinitePresentation` condition on
generators and relations.

Weibel formulates finite stable presentations for right modules over rings.
Applying these left-module results to opposite scalars recovers that setting;
the numerical statements also apply to semirings. The cross-sum construction
generalizes Prism's earlier finite-coordinate Lean formalization in Formal
Frontier's Weibel K-book research. It uses Mathlib's stable-free, finite-basis and
invariant-basis-number APIs rather than introducing a separate rank class.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Definition I.1.2.
* Mathlib, `Mathlib.Algebra.Module.StablyFree.Basic` and
  `Mathlib.LinearAlgebra.InvariantBasisNumber`.
* Prism (Formal Frontier), earlier Lean formalization of the finite-coordinate
  comparison and cross-sum argument for Weibel's definition.
-/

@[expose] public section

universe uR uP uι uκ uι' uκ'

namespace Module

/-- A module over an arbitrary ring has a finite stable presentation precisely
when it is finitely generated and stably free. In particular, stable freeness
alone permits free modules of infinite rank. This is the finite-coordinate
formulation of Weibel, *The K-book*, Definition I.1.2, for left modules. -/
theorem exists_fin_prod_linearEquiv_iff_finite_isStablyFree
    (R : Type uR) [Ring R] (P : Type uP) [AddCommGroup P] [Module R P] :
    (∃ m n : ℕ, Nonempty ((P × (Fin m → R)) ≃ₗ[R] (Fin n → R))) ↔
      Module.Finite R P ∧ Module.IsStablyFree R P := by
  classical
  constructor
  · rintro ⟨m, n, ⟨e⟩⟩
    let : Module.Finite R (P × (Fin m → R)) := Module.Finite.equiv e.symm
    have hfinite : Module.Finite R P :=
      Module.Finite.of_surjective (LinearMap.fst R P (Fin m → R))
        fun p ↦ ⟨(p, 0), rfl⟩
    let : Module.Free R (P × (Fin m → R)) := Module.Free.of_equiv e.symm
    exact ⟨hfinite, Module.IsStablyFree.of_free_prod R P (Fin m → R)⟩
  · rintro ⟨hfinite, hstable⟩
    let : Module.Finite R P := hfinite
    let : Module.IsStablyFree R P := hstable
    obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod R P
    let : Module.Finite R (P × N) := inferInstance
    let m := Fintype.card (Module.Free.ChooseBasisIndex R N)
    let n := Fintype.card (Module.Free.ChooseBasisIndex R (P × N))
    let bN := (Module.Free.chooseBasis R N).reindex
      (Fintype.equivFin (Module.Free.ChooseBasisIndex R N))
    let bPN := (Module.Free.chooseBasis R (P × N)).reindex
      (Fintype.equivFin (Module.Free.ChooseBasisIndex R (P × N)))
    exact ⟨m, n, ⟨((LinearEquiv.refl R P).prodCongr bN.equivFun).symm.trans
      bPN.equivFun⟩⟩

/-- Under invariant basis number, stabilizing two presentations by each
other's finite complement gives the cross-sum equality. This extends the
finite-coordinate argument for Weibel, *The K-book*, Definition I.1.2 to
semirings and arbitrary finite index types. -/
theorem card_add_card_eq_of_prod_linearEquiv
    (R : Type uR) [Semiring R] [InvariantBasisNumber R]
    (P : Type uP) [AddCommMonoid P] [Module R P]
    {ι : Type uι} {κ : Type uκ} {ι' : Type uι'} {κ' : Type uκ'}
    [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (e : (P × (ι → R)) ≃ₗ[R] (κ → R))
    (e' : (P × (ι' → R)) ≃ₗ[R] (κ' → R)) :
    Fintype.card κ + Fintype.card ι' = Fintype.card κ' + Fintype.card ι := by
  let comparison : ((κ ⊕ ι') → R) ≃ₗ[R] ((κ' ⊕ ι) → R) :=
    (LinearEquiv.sumArrowLequivProdArrow κ ι' R R) |>.trans
      (e.symm.prodCongr (LinearEquiv.refl R (ι' → R))) |>.trans
      (LinearEquiv.prodAssoc R P (ι → R) (ι' → R)) |>.trans
      ((LinearEquiv.refl R P).prodCongr
        (LinearEquiv.prodComm R (ι → R) (ι' → R))) |>.trans
      (LinearEquiv.prodAssoc R P (ι' → R) (ι → R)).symm |>.trans
      (e'.prodCongr (LinearEquiv.refl R (ι → R))) |>.trans
      (LinearEquiv.sumArrowLequivProdArrow κ' ι R R).symm
  simpa only [Fintype.card_sum] using
    card_eq_of_linearEquiv R comparison

/-- The integer ranks assigned by two finite stable presentations agree under
invariant basis number, without a rank-condition or size inequality. Integer
subtraction is essential: the complement need not have fewer coordinates than
the free module under this hypothesis. -/
theorem int_card_sub_eq_of_prod_linearEquiv
    (R : Type uR) [Semiring R] [InvariantBasisNumber R]
    (P : Type uP) [AddCommMonoid P] [Module R P]
    {ι : Type uι} {κ : Type uκ} {ι' : Type uι'} {κ' : Type uκ'}
    [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (e : (P × (ι → R)) ≃ₗ[R] (κ → R))
    (e' : (P × (ι' → R)) ≃ₗ[R] (κ' → R)) :
    (Fintype.card κ : ℤ) - Fintype.card ι =
      (Fintype.card κ' : ℤ) - Fintype.card ι' := by
  have h := card_add_card_eq_of_prod_linearEquiv R P e e'
  omega

end Module
