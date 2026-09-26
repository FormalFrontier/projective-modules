/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.StdBasis
public import ProjectiveModules.ExteriorPower.Determinant

/-!
# Top exterior powers and ordinary determinants

A basis indexed by `Fin n` canonically identifies the `n`th exterior power
with the base ring: the coordinate of an exterior product is its determinant
in that basis. Under this identification, the exterior-power action of an
endomorphism is multiplication by `LinearMap.det`.

For the standard basis of `Fin n → R`, this identifies the conditional
`exteriorPower.determinant` with `LinearMap.det` and, for `Matrix.toLin'`, with
`Matrix.det`. All results include degree zero and the zero ring.
-/

@[expose] public section

noncomputable section

universe u v

namespace Module.Basis

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {n : ℕ} (b : Basis (Fin n) R M)

/-- The ordered exterior product of a basis indexed by `Fin n`. -/
def topExteriorWedge : ⋀[R]^n M :=
  exteriorPower.ιMulti R n b

/-- The determinant coordinate on the top exterior power. -/
def topExteriorCoordinate : (⋀[R]^n M) →ₗ[R] R :=
  exteriorPower.alternatingMapLinearEquiv b.det

@[simp]
theorem topExteriorCoordinate_wedge :
    b.topExteriorCoordinate b.topExteriorWedge = 1 := by
  rw [topExteriorCoordinate, topExteriorWedge,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact b.det_self

/-- Multiply the ordered top wedge by a scalar. -/
def topExteriorInverse : R →ₗ[R] ⋀[R]^n M :=
  (LinearMap.id : R →ₗ[R] R).smulRight b.topExteriorWedge

/-- Every top exterior product is its determinant times the ordered basis wedge. -/
theorem iMulti_eq_det_smul_topExteriorWedge (x : Fin n → M) :
    exteriorPower.ιMulti R n x = b.det x • b.topExteriorWedge := by
  have h :
      exteriorPower.ιMulti R n = b.det.smulRight b.topExteriorWedge := by
    refine Module.Basis.ext_alternating b fun i hi ↦ ?_
    let σ : Equiv.Perm (Fin n) :=
      Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change exteriorPower.ιMulti R n (b ∘ σ) =
      b.det (b ∘ σ) • exteriorPower.ιMulti R n b
    simp [AlternatingMap.map_perm, Module.Basis.det_self]
  exact DFunLike.congr_fun h x

/-- Multiplying the top wedge is a left inverse to taking its determinant coordinate. -/
theorem topExteriorInverse_comp_coordinate :
    b.topExteriorInverse.comp b.topExteriorCoordinate = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    topExteriorCoordinate,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    topExteriorInverse, LinearMap.smulRight_apply, LinearMap.id_apply]
  exact (b.iMulti_eq_det_smul_topExteriorWedge x).symm

/-- Taking the determinant coordinate is a left inverse to multiplying the top wedge. -/
theorem topExteriorCoordinate_comp_inverse :
    b.topExteriorCoordinate.comp b.topExteriorInverse = LinearMap.id := by
  apply LinearMap.ext
  intro r
  change b.topExteriorCoordinate (r • b.topExteriorWedge) = r
  rw [map_smul, topExteriorCoordinate_wedge, smul_eq_mul, mul_one]

/-- A basis indexed by `Fin n` identifies its `n`th exterior power with the ring. -/
def topExteriorEquiv : (⋀[R]^n M) ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap b.topExteriorCoordinate b.topExteriorInverse
    b.topExteriorCoordinate_comp_inverse b.topExteriorInverse_comp_coordinate

@[simp]
theorem topExteriorEquiv_apply (x : ⋀[R]^n M) :
    b.topExteriorEquiv x = b.topExteriorCoordinate x :=
  rfl

@[simp]
theorem topExteriorEquiv_wedge :
    b.topExteriorEquiv b.topExteriorWedge = 1 :=
  b.topExteriorCoordinate_wedge

@[simp]
theorem topExteriorEquiv_symm_apply (r : R) :
    b.topExteriorEquiv.symm r = r • b.topExteriorWedge :=
  rfl

/-- The top exterior coordinate intertwines an endomorphism with its determinant. -/
theorem topExteriorEquiv_map (f : Module.End R M) (x : ⋀[R]^n M) :
    b.topExteriorEquiv (exteriorPower.map n f x) =
      LinearMap.det f * b.topExteriorEquiv x := by
  let h :
      b.topExteriorCoordinate.comp (exteriorPower.map n f) =
        (LinearMap.lsmul R R (LinearMap.det f)).comp b.topExteriorCoordinate := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro y
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, topExteriorCoordinate,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      LinearMap.lsmul_apply, smul_eq_mul]
    exact b.det_comp f y
  exact DFunLike.congr_fun h x

/-- A basis indexed by `Fin n` proves that the top exterior power is invertible. -/
theorem topExteriorInvertible (b : Basis (Fin n) R M) :
    Module.Invertible R (⋀[R]^n M) :=
  Module.Invertible.congr (b.topExteriorEquiv).symm

/-- The determinant defined through an invertible top exterior power agrees
with the ordinary finite-free determinant. -/
theorem exteriorPower_determinant_eq_det (b : Basis (Fin n) R M)
    [Module.Invertible R (⋀[R]^n M)] (f : Module.End R M) :
    exteriorPower.determinant R M n f = LinearMap.det f := by
  rw [exteriorPower.determinant_eq_iff_map_eq_smul]
  intro x
  apply (b.topExteriorEquiv).injective
  rw [b.topExteriorEquiv_map, map_smul]
  rfl

end Module.Basis

namespace exteriorPower

variable (R : Type u) [CommRing R]

/-- The standard coordinate equivalence on the top exterior power of `R^n`. -/
def standardTopEquiv (n : ℕ) : (⋀[R]^n (Fin n → R)) ≃ₗ[R] R :=
  (Pi.basisFun R (Fin n)).topExteriorEquiv

/-- The standard top exterior power of `R^n` is invertible. -/
instance instInvertiblePiTop (n : ℕ) :
    Module.Invertible R (⋀[R]^n (Fin n → R)) :=
  (Pi.basisFun R (Fin n)).topExteriorInvertible

@[simp]
theorem standardTopEquiv_map (n : ℕ)
    (f : Module.End R (Fin n → R)) (x : ⋀[R]^n (Fin n → R)) :
    standardTopEquiv R n (map n f x) =
      LinearMap.det f * standardTopEquiv R n x :=
  (Pi.basisFun R (Fin n)).topExteriorEquiv_map f x

/-- On the standard free module, the exterior-power determinant is
`LinearMap.det`. -/
theorem determinant_pi_eq_det (n : ℕ) (f : Module.End R (Fin n → R)) :
    determinant R (Fin n → R) n f = LinearMap.det f :=
  (Pi.basisFun R (Fin n)).exteriorPower_determinant_eq_det f

/-- On a matrix endomorphism, the exterior-power determinant is `Matrix.det`. -/
theorem determinant_toLin' (n : ℕ) (g : Matrix (Fin n) (Fin n) R) :
    determinant R (Fin n → R) n (Matrix.toLin' g) = Matrix.det g := by
  rw [determinant_pi_eq_det, LinearMap.det_toLin']

end exteriorPower
