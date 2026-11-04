/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Pairing.Regulator.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Projection

/-!
# Pairing regulators from bases modulo torsion

Lifts of a basis of the quotient by torsion form an independent integer frame. Its span
is complementary to the torsion submodule, so the index of that span in the original
group is the cardinality of the torsion submodule. Consequently, the pairing regulator
is the absolute determinant on any such lifts divided by the product of the two torsion
cardinalities.

No freeness of the original groups or nondegeneracy of the pairing is required. Empty
bases are included.

## References

* J. S. Milne, *Abelian Varieties*, Version 2.0, Introduction, Exercise 0.2, for the
  normalized pairing discriminant.
* Mathlib's quotient, basis, and subgroup-index APIs, in particular
  `Submodule.range_ker_disjoint`, `Submodule.map_mkQ_eq_top`, and
  `Submodule.quotientEquivOfIsCompl`.
-/

@[expose] public section

universe u v w

open Module

namespace LinearMap

private theorem linearIndependent_and_index_span_eq_card_of_quotient_basis
    {M : Type u} [AddCommGroup M] {ι : Type w}
    (P : Submodule ℤ M) (b : Basis ι ℤ (M ⧸ P)) (e : ι → M)
    (he : ∀ i, P.mkQ (e i) = b i) :
    LinearIndependent ℤ e ∧
      (Submodule.span ℤ (Set.range e)).toAddSubgroup.index = Nat.card P := by
  let E : Submodule ℤ M := Submodule.span ℤ (Set.range e)
  have hcomp : P.mkQ ∘ e = b := funext he
  have hLI : LinearIndependent ℤ (P.mkQ ∘ e) := by
    rw [hcomp]
    exact b.linearIndependent
  have hdisj : Disjoint E P := by
    simpa only [Submodule.ker_mkQ] using
      (Submodule.range_ker_disjoint (f := P.mkQ) (v := e) hLI)
  have hmap : (Submodule.span ℤ (Set.range e)).map P.mkQ = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp, hcomp, b.span_eq]
  have hcompl : IsCompl E P :=
    IsCompl.of_eq hdisj.eq_bot (by
      simpa only [sup_comm] using (P.map_mkQ_eq_top E).mp hmap)
  refine ⟨LinearIndependent.of_comp P.mkQ hLI, ?_⟩
  change Nat.card (M ⧸ E) = Nat.card P
  exact Nat.card_congr (E.quotientEquivOfIsCompl P hcompl).toEquiv

/-- Evaluate the pairing regulator on arbitrary lifts of bases modulo torsion.

The denominator uses torsion cardinalities in the original groups. The lift equations
imply both independence of the lifts and the required full-group index identities; no
additional assumptions on the frames or the determinant are needed. This is the
quotient-basis form of the normalized discriminant in Milne, *Abelian Varieties*,
Version 2.0, Introduction, Exercise 0.2. -/
theorem pairingRegulator_eq_of_torsion_quotient_bases
    {M : Type u} {N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module.Finite ℤ M] [Module.Finite ℤ N]
    (B : M →ₗ[ℤ] N →ₗ[ℤ] ℝ)
    (h : Module.finrank ℤ M = Module.finrank ℤ N)
    (bM : Basis (Fin (Module.finrank ℤ M)) ℤ (M ⧸ Submodule.torsion ℤ M))
    (bN : Basis (Fin (Module.finrank ℤ M)) ℤ (N ⧸ Submodule.torsion ℤ N))
    (e : Fin (Module.finrank ℤ M) → M) (f : Fin (Module.finrank ℤ M) → N)
    (he : ∀ i, (Submodule.torsion ℤ M).mkQ (e i) = bM i)
    (hf : ∀ i, (Submodule.torsion ℤ N).mkQ (f i) = bN i) :
    B.pairingRegulator h =
      |(toMatrix₂Aux ℤ e f B).det| /
        ((Nat.card (Submodule.torsion ℤ M) : ℝ) *
          (Nat.card (Submodule.torsion ℤ N) : ℝ)) := by
  obtain ⟨he', hindexM⟩ :=
    linearIndependent_and_index_span_eq_card_of_quotient_basis
      (Submodule.torsion ℤ M) bM e he
  obtain ⟨hf', hindexN⟩ :=
    linearIndependent_and_index_span_eq_card_of_quotient_basis
      (Submodule.torsion ℤ N) bN f hf
  rw [pairingRegulator_eq B h e f he' hf', hindexM, hindexN]

end LinearMap
