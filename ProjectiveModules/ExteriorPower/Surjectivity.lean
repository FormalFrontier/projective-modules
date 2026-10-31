/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveModules.ExteriorPower.Top
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Surjectivity detected by the top exterior power

For a linear map into a free module with a basis indexed by `Fin r`, surjectivity
is equivalent to surjectivity of the induced map on `r`th exterior powers. The
source module is arbitrary.

Cramer's identity puts each determinant multiple of a target vector in the range.
Pure wedges span the exterior power, so a preimage of the target's top basis wedge
then puts every target vector in the range. No single determinant need be a unit.
-/

@[expose] public section

noncomputable section

universe uR uM uN

namespace exteriorPower

open Matrix

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]
variable {r : ℕ}

private theorem det_smul_mem_range (b : Module.Basis (Fin r) R N)
    (f : M →ₗ[R] N) (v : Fin r → M) (y : N) :
    b.det (f ∘ v) • y ∈ LinearMap.range f := by
  classical
  let A : Matrix (Fin r) (Fin r) R := b.toMatrix (f ∘ v)
  let c : Fin r → R := Matrix.cramer A (b.equivFun y)
  have hc : A *ᵥ c = A.det • b.equivFun y :=
    Matrix.mulVec_cramer A (b.equivFun y)
  refine LinearMap.mem_range.mpr ⟨∑ j, c j • v j, ?_⟩
  apply b.equivFun.injective
  ext i
  have hi := congrFun hc i
  simp only [Matrix.mulVec_apply_eq_sum, Pi.smul_apply, smul_eq_mul] at hi
  calc
    b.equivFun (f (∑ j, c j • v j)) i = ∑ j, c j * A i j := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        A, Module.Basis.toMatrix_apply, Module.Basis.equivFun_apply, Function.comp_apply]
    _ = A.det * b.equivFun y i := by simpa only [mul_comm] using hi
    _ = b.equivFun (b.det (f ∘ v) • y) i := by
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.det_apply, A]

/-- A linear map to a free module with a basis indexed by `Fin r` is surjective
if and only if its `r`th exterior power is surjective. No finiteness assumption
on the source is required. This includes `r = 0` and the zero ring. -/
theorem map_surjective_iff_of_basis (b : Module.Basis (Fin r) R N) (f : M →ₗ[R] N) :
    Function.Surjective (map r f) ↔ Function.Surjective f := by
  constructor
  · intro hf y
    -- For fixed y, the wedges whose coordinates send y into the range form a submodule.
    let q : Submodule R (⋀[R]^r M) :=
      Submodule.comap
        ((LinearMap.toSpanSingleton R N y).comp (b.topExteriorCoordinate.comp (map r f)))
        (LinearMap.range f)
    have hspan : Submodule.span R (Set.range (ιMulti R r)) ≤ q := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, rfl⟩
      change (LinearMap.toSpanSingleton R N y)
        (b.topExteriorCoordinate (map r f (ιMulti R r v))) ∈ LinearMap.range f
      rw [map_apply_ιMulti, Module.Basis.iMulti_eq_det_smul_topExteriorWedge,
        map_smul, Module.Basis.topExteriorCoordinate_wedge, map_smul,
        LinearMap.toSpanSingleton_apply_one]
      exact det_smul_mem_range b f v y
    have htop : (⊤ : Submodule R (⋀[R]^r M)) ≤ q := by
      rw [← ιMulti_span R r M]
      exact hspan
    obtain ⟨w, hw⟩ := hf b.topExteriorWedge
    have hwq : w ∈ q := htop (by trivial)
    change (LinearMap.toSpanSingleton R N y)
      (b.topExteriorCoordinate (map r f w)) ∈ LinearMap.range f at hwq
    rw [hw, Module.Basis.topExteriorCoordinate_wedge,
      LinearMap.toSpanSingleton_apply_one] at hwq
    exact LinearMap.mem_range.mp hwq
  · exact fun hf => map_surjective hf

end exteriorPower
