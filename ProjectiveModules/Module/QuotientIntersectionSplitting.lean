/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import ProjectiveModules.Module.QuotientIntersection
import ProjectiveModules.Module.ProjectiveKernel
import Mathlib.Algebra.Exact.Basic
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finite and projective intersection quotients

When the quotient by `U ⊔ V` is projective, the canonical quotient sequence splits.
Consequently, the quotient by `U ⊓ V` is finitely generated or projective exactly
when both individual quotients have the corresponding property.

Finite generation passes from the intersection quotient to each individual quotient
by surjectivity of the quotient factor maps. The converse uses the existing
split-kernel finite-generation theorem. Projectivity in both directions uses the
split sequence: the middle product is isomorphic to the product of the kernel and
the sum quotient, and each individual quotient is a retract of the middle product.
No finiteness or projectivity hypothesis on the ambient module is needed.

## References

* Mathlib's projective lifting, retract, and equivalence theorems in
  `Mathlib.Algebra.Module.Projective`.
* The split-kernel closure theorems in `ProjectiveModules.Module.ProjectiveKernel`.
* The supplied-section kernel-product equivalence in
  `StableRange.Module.SplitSurjective`.
-/

@[expose] public section

universe uS uM

namespace Submodule.QuotientIntersection

variable {S : Type uS} [Ring S]
variable {M : Type uM} [AddCommGroup M] [Module S M]

private noncomputable def diagonalEquivKer (U V : Submodule S M) :
    (M ⧸ (U ⊓ V)) ≃ₗ[S] LinearMap.ker (difference U V) :=
  (LinearEquiv.ofInjective (diagonal U V) (diagonal_injective U V)).trans
    (LinearEquiv.ofEq _ _ (exact_diagonal_difference U V).linearMap_ker_eq.symm)

/-- If the sum quotient is projective, the intersection quotient is finitely generated
exactly when both individual quotients are finitely generated. -/
theorem finite_iff (U V : Submodule S M) [Module.Projective S (M ⧸ (U ⊔ V))] :
    Module.Finite S (M ⧸ (U ⊓ V)) ↔
      Module.Finite S (M ⧸ U) ∧ Module.Finite S (M ⧸ V) := by
  constructor
  · intro hI
    let := hI
    exact ⟨Module.Finite.of_surjective
        (Submodule.factor (show U ⊓ V ≤ U from inf_le_left))
        (Submodule.factor_surjective _),
      Module.Finite.of_surjective
        (Submodule.factor (show U ⊓ V ≤ V from inf_le_right))
        (Submodule.factor_surjective _)⟩
  · rintro ⟨hU, hV⟩
    let := hU
    let := hV
    obtain ⟨s, hs⟩ := Module.projective_lifting_property
      (difference U V) LinearMap.id (difference_surjective U V)
    let := LinearMap.finite_splitKernel s (difference U V) hs
    exact Module.Finite.equiv (diagonalEquivKer U V).symm

/-- If the sum quotient is projective, the intersection quotient is projective
exactly when both individual quotients are projective. -/
theorem projective_iff (U V : Submodule S M) [Module.Projective S (M ⧸ (U ⊔ V))] :
    Module.Projective S (M ⧸ (U ⊓ V)) ↔
      Module.Projective S (M ⧸ U) ∧ Module.Projective S (M ⧸ V) := by
  constructor
  · intro hI
    let := hI
    let := Module.Projective.of_equiv' (diagonalEquivKer U V)
    obtain ⟨s, hs⟩ := Module.projective_lifting_property
      (difference U V) LinearMap.id (difference_surjective U V)
    let := Module.Projective.of_equiv'
      (LinearMap.kerProdEquivOfRightInverse (difference U V) s hs)
    exact ⟨Module.Projective.of_split
        (LinearMap.inl S (M ⧸ U) (M ⧸ V))
        (LinearMap.fst S (M ⧸ U) (M ⧸ V)) (by ext x; rfl),
      Module.Projective.of_split
        (LinearMap.inr S (M ⧸ U) (M ⧸ V))
        (LinearMap.snd S (M ⧸ U) (M ⧸ V)) (by ext x; rfl)⟩
  · rintro ⟨hU, hV⟩
    let := hU
    let := hV
    obtain ⟨s, hs⟩ := Module.projective_lifting_property
      (difference U V) LinearMap.id (difference_surjective U V)
    let := LinearMap.projective_splitKernel s (difference U V) hs
    exact Module.Projective.of_equiv' (diagonalEquivKer U V).symm

end Submodule.QuotientIntersection
