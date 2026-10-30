/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorAlgebra.ContractionSplitting

/-!
# Naturality of the left-contraction splitting

A quadratic-form-preserving linear map induces a linear map on contraction kernels when the
source covector is pulled back from the target. These cycle maps respect identities and
composition, and commute with the cycle lift for every covector and vector.

If the target covector pairs to one with the image of a vector, the existing contraction
splittings commute with the Clifford map. In splitting coordinates this is the product of
the induced cycle map with itself. No injectivity, surjectivity, or restriction on the
quadratic forms is required.

The cycle map uses Mathlib's `LinearMap.restrict`, with membership supplied by
`CliffordAlgebra.map_contractLeft`. The splitting and its inverse are those of
`ProjectiveModules.ExteriorAlgebra.ContractionSplitting`; no additional splitting is
constructed.

## References

The proofs reuse Mathlib's restriction and product maps and Eric Wieser's Clifford-algebra
formalization, together with the contraction naturality and kernel splitting in
`ProjectiveModules.ExteriorAlgebra.Contraction` and
`ProjectiveModules.ExteriorAlgebra.ContractionSplitting`. The latter splitting uses
Antoine Chambert-Loir's `Function.Exact.splitSurjectiveEquiv` from Mathlib.
-/

@[expose] public section

noncomputable section

universe u v w z

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type z} [AddCommGroup P] [Module R P]
variable {Q : QuadraticForm R M} {Q' : QuadraticForm R N}
variable {Q'' : QuadraticForm R P}

namespace CliffordAlgebra

/-- The Clifford map restricted to the original contraction kernels, with the source
covector pulled back along the quadratic-form-preserving linear map. -/
def contractLeftKerMap (f : Q →qᵢ Q') (ν : Module.Dual R N) :
    LinearMap.ker (contractLeft (Q := Q) (ν.comp f.toLinearMap)) →ₗ[R]
      LinearMap.ker (contractLeft (Q := Q') ν) :=
  (CliffordAlgebra.map f).toLinearMap.restrict (by
    intro x hx
    change contractLeft ν (map f x) = 0
    rw [← map_contractLeft f ν x, LinearMap.mem_ker.mp hx, map_zero])

/-- The underlying function on cycles is the Clifford map. -/
theorem contractLeftKerMap_coe (f : Q →qᵢ Q') (ν : Module.Dual R N) :
    (fun x : LinearMap.ker (contractLeft (Q := Q) (ν.comp f.toLinearMap)) =>
      (contractLeftKerMap f ν x : CliffordAlgebra Q')) =
      fun x : LinearMap.ker (contractLeft (Q := Q) (ν.comp f.toLinearMap)) =>
        map f (x : CliffordAlgebra Q) :=
  rfl

/-- Evaluating the cycle map agrees with evaluating the Clifford map. -/
@[simp]
theorem contractLeftKerMap_apply (f : Q →qᵢ Q') (ν : Module.Dual R N)
    (x : LinearMap.ker (contractLeft (Q := Q) (ν.comp f.toLinearMap))) :
    (contractLeftKerMap f ν x : CliffordAlgebra Q') = map f (x : CliffordAlgebra Q) :=
  rfl

/-- The identity isometry induces the identity on contraction cycles. -/
@[simp]
theorem contractLeftKerMap_id (μ : Module.Dual R M) :
    contractLeftKerMap (QuadraticMap.Isometry.id Q) μ =
      (LinearMap.id : LinearMap.ker (contractLeft (Q := Q) μ) →ₗ[R]
        LinearMap.ker (contractLeft (Q := Q) μ)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [contractLeftKerMap_apply, map_id, AlgHom.id_apply]
  rfl

/-- The induced cycle maps respect composition of isometries. -/
theorem contractLeftKerMap_comp (f : Q →qᵢ Q') (g : Q' →qᵢ Q'')
    (ξ : Module.Dual R P) :
    (contractLeftKerMap g ξ).comp (contractLeftKerMap f (ξ.comp g.toLinearMap)) =
      contractLeftKerMap (g.comp f) ξ := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.comp_apply, contractLeftKerMap_apply]
  exact DFunLike.congr_fun (map_comp_map g f) (x : CliffordAlgebra Q)

/-- The cycle lift commutes with the induced Clifford map for every covector and vector. -/
theorem map_contractLeftKerLift (f : Q →qᵢ Q') (ν : Module.Dual R N) (m : M) :
    (map f).toLinearMap.comp
        (contractLeftKerLift (Q := Q) (ν.comp f.toLinearMap) m) =
      (contractLeftKerLift (Q := Q') ν (f m)).comp (contractLeftKerMap f ν) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, contractLeftKerLift_apply,
    contractLeftKerMap_apply, map_mul, map_apply_ι]

/-- The contraction splittings commute with the Clifford map. The single unit-pairing
hypothesis supplies both splittings, and the same cycle map acts on both product factors. -/
theorem contractLeftKerProdEquiv_map (f : Q →qᵢ Q') (ν : Module.Dual R N)
    (m : M) (h : ν (f m) = 1) :
    (contractLeftKerProdEquiv (Q := Q') ν (f m) h).toLinearMap.comp
        (map f).toLinearMap =
      ((contractLeftKerMap f ν).prodMap (contractLeftKerMap f ν)).comp
        (contractLeftKerProdEquiv (Q := Q) (ν.comp f.toLinearMap) m
          (show (ν.comp f.toLinearMap) m = 1 from h)).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · apply Subtype.ext
    simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      LinearEquiv.coe_toLinearMap, LinearMap.prodMap_apply, contractLeftKerMap_apply,
      contractLeftKerProdEquiv_apply_fst, map_mul, map_apply_ι] using
      (map_contractLeft f ν (ι Q m * x)).symm
  · apply Subtype.ext
    simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      LinearEquiv.coe_toLinearMap, LinearMap.prodMap_apply, contractLeftKerMap_apply,
      contractLeftKerProdEquiv_apply_snd] using (map_contractLeft f ν x).symm

/-- In splitting coordinates, the Clifford map is the same induced cycle map in both
factors, using the inverse of the source contraction splitting. -/
theorem map_conj_contractLeftKerProdEquiv (f : Q →qᵢ Q') (ν : Module.Dual R N)
    (m : M) (h : ν (f m) = 1) :
    ((contractLeftKerProdEquiv (Q := Q') ν (f m) h).toLinearMap.comp
        (map f).toLinearMap).comp
      (contractLeftKerProdEquiv (Q := Q) (ν.comp f.toLinearMap) m
        (show (ν.comp f.toLinearMap) m = 1 from h)).symm.toLinearMap =
      (contractLeftKerMap f ν).prodMap (contractLeftKerMap f ν) := by
  rw [contractLeftKerProdEquiv_map]
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]

end CliffordAlgebra
