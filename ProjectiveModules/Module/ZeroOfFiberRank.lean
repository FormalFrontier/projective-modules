/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.LocalFiberBasis
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Vanishing from residue-fiber rank zero

For projective modules, zero cardinal rank at every maximal residue field implies that
the module is subsingleton. The proof uses an empty basis after localization and the
local criterion for surjectivity of the zero endomorphism.

## References

* Charles A. Weibel, *The K-book*, Chapter I, §2.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Module.Projective

/-- Zero cardinal rank of every maximal residue fiber forces a projective module to vanish. -/
theorem subsingleton_of_residue_rank_eq_zero
    {R : Type u} [CommRing R]
    {P : Type v} [AddCommMonoid P] [Module R P] [Module.Projective R P]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Module.rank (R ⧸ m) ((R ⧸ m) ⊗[R] P) = 0) : Subsingleton P := by
  have hsurj : Function.Surjective (0 : P →ₗ[R] P) := by
    apply surjective_of_localized_maximal
    intro m hm z
    obtain ⟨b⟩ := nonempty_basis_atPrime_of_residue_rank_eq m 0 (by simpa using h m)
    refine ⟨0, ?_⟩
    apply (LocalizedModule.equivTensorProduct m.primeCompl P).injective
    apply b.ext_elem_iff.mpr
    intro i
    exact Fin.elim0 i
  constructor
  intro x y
  obtain ⟨a, ha⟩ := hsurj x
  obtain ⟨b, hb⟩ := hsurj y
  exact ha.symm.trans hb

end Module.Projective
