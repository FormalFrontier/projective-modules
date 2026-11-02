/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import ProjectiveModules.RingTheory.IdempotentConjugation

/-!
# Naturality of finite idempotent conjugation constructions

The specified finite-family coefficient commutes with unital ring homomorphisms and is
unchanged by joint equivalence reindexing. The constructed stock unit has the same transport
properties. For ring-homomorphism transport of the unit, the target construction uses its own
two-sided ideal in the Jacobson radical and its own pointwise image-family congruence data.
No preservation of Jacobson radicals by an arbitrary ring homomorphism is assumed.

The coefficient identities require no orthogonality. The unit identities require only the
first family's orthogonality, not idempotence or orthogonality of the second family. They
assert transport of the constructions, not simultaneous conjugacy in that generality.
Neither family has to sum to one. Rings may be noncommutative or zero, finite index types
may be empty, and the scalar and both index universes are independent.

The statements reuse the existing coefficient and unit constructions, Mathlib's
orthogonal-idempotent transport, and the canonical `Units.map`.
-/

@[expose] public section

universe uR vS wι xκ

namespace RingHom

variable {R : Type uR} {S : Type vS} [Ring R] [Ring S]
variable {ι : Type wι} [Fintype ι]

/-- Unital ring homomorphisms preserve the specified finite-family coefficient. -/
@[simp]
theorem map_conjugationCoeff (f : R →+* S) (a b : ι → R) :
    f (OrthogonalIdempotents.conjugationCoeff a b) =
      OrthogonalIdempotents.conjugationCoeff (f ∘ a) (f ∘ b) := by
  classical
  simp [OrthogonalIdempotents.conjugationCoeff_eq]

end RingHom

namespace OrthogonalIdempotents

variable {R : Type uR} [Ring R] {ι : Type wι} [Fintype ι]

section Map

variable {S : Type vS} [Ring S] {a b : ι → R}

/-- Mapping the constructed stock unit agrees with the target construction using its own
radical-ideal bound and pointwise congruence data. -/
theorem map_conjugatingUnit (ha : OrthogonalIdempotents a) (f : R →+* S)
    (I : Ideal R) [I.IsTwoSided] (hI : I ≤ Ring.jacobson R)
    (hab : ∀ i, b i - a i ∈ I)
    (J : Ideal S) [J.IsTwoSided] (hJ : J ≤ Ring.jacobson S)
    (habS : ∀ i, f (b i) - f (a i) ∈ J) :
    Units.map f.toMonoidHom (conjugatingUnit ha I hI hab) =
      conjugatingUnit (OrthogonalIdempotents.map f ha) J hJ habS := by
  ext
  simp
  rfl

end Map

section Reindex

variable {κ : Type xκ} [Fintype κ]

/-- Joint equivalence reindexing leaves the specified finite-family coefficient unchanged. -/
@[simp]
theorem conjugationCoeff_comp_equiv (a b : ι → R) (e : κ ≃ ι) :
    conjugationCoeff (a ∘ e) (b ∘ e) = conjugationCoeff a b := by
  classical
  have hsum (g : ι → R) : (∑ k, g (e k)) = ∑ i, g i := by
    simpa using congrArg (fun x : Multiplicative R => Multiplicative.toAdd x)
      (Finset.prod_comp_equiv (M := Multiplicative R) (s := Finset.univ)
        (f := fun i => Multiplicative.ofAdd (g i)) e)
  have h :
      (∑ k, b (e k) * a (e k)) + (1 - ∑ k, b (e k)) * (1 - ∑ k, a (e k)) =
        (∑ i, b i * a i) + (1 - ∑ i, b i) * (1 - ∑ i, a i) := by
    rw [hsum (fun i => b i * a i), hsum b, hsum a]
  simpa [conjugationCoeff_eq] using h

variable {a b : ι → R}

/-- Joint equivalence reindexing leaves the constructed stock unit unchanged. -/
theorem conjugatingUnit_comp_equiv (ha : OrthogonalIdempotents a) (e : κ ≃ ι)
    (I : Ideal R) [I.IsTwoSided] (hI : I ≤ Ring.jacobson R)
    (hab : ∀ i, b i - a i ∈ I) :
    conjugatingUnit ((OrthogonalIdempotents.equiv e).mpr ha) I hI
        (fun k => hab (e k)) =
      conjugatingUnit ha I hI hab := by
  ext
  simp only [coe_conjugatingUnit]
  exact conjugationCoeff_comp_equiv a b e

end Reindex

end OrthogonalIdempotents
