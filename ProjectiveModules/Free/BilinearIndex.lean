/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import ProjectiveModules.Free.BilinearMatrix

/-!
# Subgroup indices and pairing determinants

Restricting an integer-bilinear pairing valued in a linearly ordered commutative ring
to free subgroups of the same finite rank scales its absolute determinant by their
relative indices. For restriction in just one variable, the family in the other
variable can be arbitrary.

The ambient additive groups need not be free or finitely generated, and the pairing
need not be nondegenerate. The statements include the empty-index case. The target
ring needs only `CommRing`, `LinearOrder` and `IsOrderedRing`; in particular, integer-,
rational- and real-valued pairings are special cases.

## References

The finite free basis calculation uses Mathlib's
`AddSubgroup.relIndex_eq_natAbs_det`, together with the algebra-valued matrix composition
formula `LinearMap.toMatrix₂_compl₁₂_algebra`. The latter follows Mathlib's
`LinearMap.sum_repr_mul_repr_mul` basis-coefficient expansion. The determinant identities
are multiplied and absolute values taken, without cancelling a pairing determinant.
-/

@[expose] public section

open Module
open scoped Matrix

universe u v w wι

namespace LinearMap

variable {K : Type w} [CommRing K] [LinearOrder K] [IsOrderedRing K]

private theorem abs_det_map_toMatrix_inclusion
    {M : Type u} [AddCommGroup M]
    {ι : Type wι} [Fintype ι] [DecidableEq ι]
    {E' E : AddSubgroup M} (hE : E' ≤ E)
    (bE' : Basis ι ℤ E') (bE : Basis ι ℤ E) :
    |((toMatrix bE' bE (AddSubgroup.inclusion hE).toIntLinearMap).map
        (algebraMap ℤ K)).det| = (E'.relIndex E : K) := by
  have hmatrix :
      bE.toMatrix (fun i => (⟨(bE' i : M), hE (bE' i).property⟩ : E)) =
        toMatrix bE' bE (AddSubgroup.inclusion hE).toIntLinearMap := by
    ext i j
    rw [Basis.toMatrix_apply, toMatrix_apply]
    rfl
  have hindex := AddSubgroup.relIndex_eq_natAbs_det E' E hE bE' bE
  change E'.relIndex E =
    (bE.toMatrix (fun i => (⟨(bE' i : M), hE (bE' i).property⟩ : E))).det.natAbs at hindex
  rw [hmatrix] at hindex
  have habs (z : ℤ) : (↑|z| : K) = |(z : K)| := by
    simpa only [abs_eq_max_neg, Int.cast_neg] using
      (Int.cast_mono (R := K)).map_max (a := z) (b := -z)
  change |((toMatrix bE' bE (AddSubgroup.inclusion hE).toIntLinearMap).map
    (fun z : ℤ => (z : K))).det| = _
  rw [← Int.cast_det, hindex, Nat.cast_natAbs, habs]

/-- Restricting both free subgroups multiplies the absolute pairing determinant by the
product of their relative indices. -/
theorem abs_det_toMatrix₂Aux_eq_relIndex_mul
    {M : Type u} {N : Type v} [AddCommGroup M] [AddCommGroup N]
    {ι : Type wι} [Fintype ι] [DecidableEq ι]
    (B : M →ₗ[ℤ] N →ₗ[ℤ] K)
    {E' E : AddSubgroup M} {F' F : AddSubgroup N}
    (hE : E' ≤ E) (hF : F' ≤ F)
    (bE' : Basis ι ℤ E') (bE : Basis ι ℤ E)
    (bF' : Basis ι ℤ F') (bF : Basis ι ℤ F) :
    |(toMatrix₂Aux ℤ (fun i => (bE' i : M)) (fun i => (bF' i : N)) B).det| =
      (E'.relIndex E : K) * (F'.relIndex F : K) *
        |(toMatrix₂Aux ℤ (fun i => (bE i : M)) (fun i => (bF i : N)) B).det| := by
  let l : E' →ₗ[ℤ] E := (AddSubgroup.inclusion hE).toIntLinearMap
  let r : F' →ₗ[ℤ] F := (AddSubgroup.inclusion hF).toIntLinearMap
  let P : E →ₗ[ℤ] F →ₗ[ℤ] K :=
    B.compl₁₂ E.subtype.toIntLinearMap F.subtype.toIntLinearMap
  have hlarge : toMatrix₂ bE bF P =
      toMatrix₂Aux ℤ (fun i => (bE i : M)) (fun i => (bF i : N)) B := by
    ext i j
    simp [P]
  have hsmall : toMatrix₂ bE' bF' (P.compl₁₂ l r) =
      toMatrix₂Aux ℤ (fun i => (bE' i : M)) (fun i => (bF' i : N)) B := by
    ext i j
    simp [P, l, r]
  have hmatrix := toMatrix₂_compl₁₂_algebra bE bF bE' bF' P l r
  rw [hlarge, hsmall] at hmatrix
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, abs_mul, abs_mul,
    abs_det_map_toMatrix_inclusion hE bE' bE,
    abs_det_map_toMatrix_inclusion hF bF' bF]
  ac_rfl

/-- Restricting the left free subgroup multiplies the absolute pairing determinant by
its relative index. The family in the right variable need not be independent. -/
theorem abs_det_toMatrix₂Aux_eq_relIndex_mul_left
    {M : Type u} {N : Type v} [AddCommGroup M] [AddCommGroup N]
    {ι : Type wι} [Fintype ι] [DecidableEq ι]
    (B : M →ₗ[ℤ] N →ₗ[ℤ] K)
    {E' E : AddSubgroup M} (hE : E' ≤ E)
    (bE' : Basis ι ℤ E') (bE : Basis ι ℤ E) (f : ι → N) :
    |(toMatrix₂Aux ℤ (fun i => (bE' i : M)) f B).det| =
      (E'.relIndex E : K) *
        |(toMatrix₂Aux ℤ (fun i => (bE i : M)) f B).det| := by
  let c : Basis ι ℤ (ι → ℤ) := Pi.basisFun ℤ ι
  let t : (ι → ℤ) →ₗ[ℤ] N := c.constr ℤ f
  let l : E' →ₗ[ℤ] E := (AddSubgroup.inclusion hE).toIntLinearMap
  let P : E →ₗ[ℤ] (ι → ℤ) →ₗ[ℤ] K :=
    B.compl₁₂ E.subtype.toIntLinearMap t
  have hlarge : toMatrix₂ bE c P =
      toMatrix₂Aux ℤ (fun i => (bE i : M)) f B := by
    ext i j
    simp [P, t]
  have hsmall : toMatrix₂ bE' c (P.compl₁₂ l LinearMap.id) =
      toMatrix₂Aux ℤ (fun i => (bE' i : M)) f B := by
    ext i j
    simp [P, t, l]
  have hid : (toMatrix c c (LinearMap.id : (ι → ℤ) →ₗ[ℤ] (ι → ℤ))).map
      (algebraMap ℤ K) = 1 := by
    rw [toMatrix_id]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hmatrix := toMatrix₂_compl₁₂_algebra bE c bE' c P l LinearMap.id
  rw [hlarge, hsmall, hid, Matrix.mul_one] at hmatrix
  rw [hmatrix, Matrix.det_mul, Matrix.det_transpose, abs_mul,
    abs_det_map_toMatrix_inclusion hE bE' bE]

/-- Restricting the right free subgroup multiplies the absolute pairing determinant by
its relative index. The family in the left variable need not be independent. -/
theorem abs_det_toMatrix₂Aux_eq_relIndex_mul_right
    {M : Type u} {N : Type v} [AddCommGroup M] [AddCommGroup N]
    {ι : Type wι} [Fintype ι] [DecidableEq ι]
    (B : M →ₗ[ℤ] N →ₗ[ℤ] K) (e : ι → M)
    {F' F : AddSubgroup N} (hF : F' ≤ F)
    (bF' : Basis ι ℤ F') (bF : Basis ι ℤ F) :
    |(toMatrix₂Aux ℤ e (fun i => (bF' i : N)) B).det| =
      (F'.relIndex F : K) *
        |(toMatrix₂Aux ℤ e (fun i => (bF i : N)) B).det| := by
  have htranspose (f : ι → N) :
      toMatrix₂Aux ℤ f e B.flip = (toMatrix₂Aux ℤ e f B)ᵀ := by
    ext i j
    rfl
  simpa only [htranspose, Matrix.det_transpose] using
    (abs_det_toMatrix₂Aux_eq_relIndex_mul_left B.flip hF bF' bF e)

end LinearMap
