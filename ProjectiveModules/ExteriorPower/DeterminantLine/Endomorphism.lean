/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine.Endomorphism.Product
import ProjectiveModules.ExteriorPower.ProdPairing

/-!
# Scalar determinants of finite projective endomorphisms

Endomorphisms act on the invertible determinant line, and their scalar determinants
multiply under composition and direct products. The modules need not have constant
stalk rank, and the endomorphisms need not be invertible.

The unrestricted product formula uses finite-free split presentations and their
block-diagonal stabilizations. The constant-rank formula below uses the ordered
top exterior-product pairing.

## References

For determinants of finite projective modules, see C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w

namespace Module

variable (R : Type u) [CommRing R]
variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

/-- The product formula for finite projective modules with constant stalk rank.
The endomorphisms need not be invertible, and the coefficient ring may be trivial. -/
theorem determinant_prodMap_of_rankAtStalk_eq
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q]
    {n m : ℕ}
    (hP : ∀ p : PrimeSpectrum R, rankAtStalk (R := R) P p = n)
    (hQ : ∀ p : PrimeSpectrum R, rankAtStalk (R := R) Q p = m)
    (f : Module.End R P) (g : Module.End R Q) :
    determinant R (P × Q) (f.prodMap g) = determinant R P f * determinant R Q g := by
  have hP' : rankAtStalk (R := R) P = fun _ ↦ n := funext hP
  have hQ' : rankAtStalk (R := R) Q = fun _ ↦ m := funext hQ
  have hPQ : rankAtStalk (R := R) (P × Q) = fun _ ↦ n + m := by
    ext p
    simp only [rankAtStalk_prod, Pi.add_apply, hP, hQ]
  let := exteriorPower.invertible_of_rankAtStalk_eq n hP'
  let := exteriorPower.invertible_of_rankAtStalk_eq m hQ'
  let := exteriorPower.invertible_of_rankAtStalk_eq (n + m) hPQ
  rw [determinant_eq_exteriorPower_determinant R (P × Q) (n + m) hPQ,
    determinant_eq_exteriorPower_determinant R P n hP',
    determinant_eq_exteriorPower_determinant R Q m hQ']
  apply (exteriorPower.determinant_eq_iff_map_eq_smul R (P × Q) (n + m) _ _).2
  have htensor :
      TensorProduct.map (exteriorPower.map n f) (exteriorPower.map m g) =
        (exteriorPower.determinant R P n f * exteriorPower.determinant R Q m g) •
          (LinearMap.id : Module.End R ((⋀[R]^n P) ⊗[R] (⋀[R]^m Q))) := by
    apply TensorProduct.ext'
    intro a b
    simp only [TensorProduct.map_tmul, exteriorPower.map_eq_smul_determinant,
      LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.smul_tmul_smul]
  intro z
  obtain ⟨x, rfl⟩ :=
    (exteriorPower.prodPairingEquiv R P Q n m hP' hQ').surjective z
  change exteriorPower.map (n + m) (f.prodMap g)
      (exteriorPower.prodPairing R P Q n m x) = _
  have h := LinearMap.congr_fun (exteriorPower.prodPairing_naturality R P Q n m f g) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, htensor,
    LinearMap.smul_apply, LinearMap.id_apply, map_smul] at h
  exact h

end Module
