/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import ProjectiveModules.ExteriorPower.Projective

/-!
# Antisymmetrization for exterior powers

Naturality and injectivity of the alternating map from exterior powers to tensor powers.
-/

@[expose] public section

universe u v w

namespace exteriorPower

variable {R : Type u} [CommRing R] {M : Type v}
  [AddCommGroup M] [Module R M] {n : ℕ}

/-- Pairing with a wedge of forms factors through antisymmetrization. -/
lemma pairingDual_ιMulti_apply (f : Fin n → Module.Dual R M)
    (x : ⋀[R]^n M) :
    pairingDual R M n (ιMulti R n f) x =
      TensorPower.multilinearMapToDual R M n f (toTensorPower R M n x) := by
  rw [pairingDual, alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- Antisymmetrization is injective for a module equipped with any basis. -/
theorem toTensorPower_injective_of_basis {ι : Type w}
    (b : Module.Basis ι R M) :
    Function.Injective (toTensorPower R M n) := by
  classical
  let : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  intro x y h
  apply (b.exteriorPower n).repr.injective
  ext s
  simp only [basis_repr_apply, ιMultiDual, ιMulti_family,
    pairingDual_ιMulti_apply]
  rw [h]

/-- Antisymmetrization commutes with every linear map. -/
theorem toTensorPower_naturality (R : Type u) [CommRing R]
    (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (n : Nat) (f : M →ₗ[R] N) :
    (PiTensorProduct.map (fun _ : Fin n => f)).comp
        (toTensorPower R M n) =
      (toTensorPower R N n).comp (map n f) := by
  classical
  apply linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    map_apply_ιMulti, toTensorPower_apply_ιMulti, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Units.smul_def, map_zsmul,
    PiTensorProduct.map_tprod, Function.comp_apply]

/-- Antisymmetrization is injective on every projective module. -/
theorem toTensorPower_injective (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Projective R M] (n : Nat) :
    Function.Injective (toTensorPower R M n) := by
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := R) (P := M)).mp inferInstance
  have he : Function.Injective (map n s) :=
    map_injective (n := n) (Finsupp.linearCombination R id) hs
  have hF : Function.Injective (toTensorPower R (M →₀ R) n) :=
    toTensorPower_injective_of_basis (n := n)
      (Finsupp.basisSingleOne : Module.Basis M R (M →₀ R))
  intro x y h
  apply he
  apply hF
  have hn := toTensorPower_naturality R M (M →₀ R) n s
  have hx := DFunLike.congr_fun hn x
  have hy := DFunLike.congr_fun hn y
  simp only [LinearMap.comp_apply] at hx hy
  rw [← hx, ← hy, h]

end exteriorPower
