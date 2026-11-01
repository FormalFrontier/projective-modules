/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Abel

/-!
# Determinants of finite-free stabilizations

The rectangular identity `det (1 + AB) = det (1 + BA)` gives a comparison
for compositions between two finite free modules, which need not have the
same rank. It implies that the determinant of an endomorphism extended by
the identity along a split retraction is independent of the retraction and
of the finite free ambient module.

The retract itself need not be free or have constant rank. These results
compare ordinary finite-free determinants; they do not identify them with
the scalar action on a determinant line.

## References

The finite-free comparison uses Mathlib's `Matrix.det_one_add_mul_comm`,
the Weinstein–Aronszajn identity in
`Mathlib.LinearAlgebra.Matrix.SchurComplement`.
-/

@[expose] public section

namespace LinearMap

universe u v w z

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- The rectangular determinant identity for maps between finite free modules.
The two identity maps may act on modules of different ranks. -/
theorem det_id_add_comp_comm [Module.Free R M] [Module.Finite R M]
    [Module.Free R N] [Module.Finite R N]
    (a : N →ₗ[R] M) (b : M →ₗ[R] N) :
    LinearMap.det (id + a.comp b) = LinearMap.det (id + b.comp a) := by
  classical
  let c := Module.Free.chooseBasis R M
  let d := Module.Free.chooseBasis R N
  rw [← det_toMatrix c, ← det_toMatrix d, map_add, map_add,
    toMatrix_id, toMatrix_id, toMatrix_comp c d c, toMatrix_comp d c d]
  exact Matrix.det_one_add_mul_comm _ _

/-- Extending an endomorphism by the identity along a split retraction has
an ordinary determinant independent of the finite free presentation.
No freeness or constant-rank assumption is required on the retract. -/
theorem det_stabilization_eq_of_retractions
    [Module.Free R M] [Module.Finite R M]
    [Module.Free R N] [Module.Finite R N]
    {P : Type z} [AddCommGroup P] [Module R P] (f : Module.End R P)
    (p₁ : M →ₗ[R] P) (j₁ : P →ₗ[R] M) (hp₁ : p₁.comp j₁ = id)
    (p₂ : N →ₗ[R] P) (j₂ : P →ₗ[R] N) (hp₂ : p₂.comp j₂ = id) :
    LinearMap.det (j₁.comp (f.comp p₁) + (id - j₁.comp p₁)) =
      LinearMap.det (j₂.comp (f.comp p₂) + (id - j₂.comp p₂)) := by
  have h₁ (x : P) : p₁ (j₁ x) = x := DFunLike.congr_fun hp₁ x
  have h₂ (x : P) : p₂ (j₂ x) = x := DFunLike.congr_fun hp₂ x
  let a := j₁.comp ((f - id).comp p₂)
  let b := j₂.comp p₁
  have ha : id + a.comp b = j₁.comp (f.comp p₁) + (id - j₁.comp p₁) := by
    ext x
    simp only [a, b, add_apply, comp_apply, sub_apply, id_apply, h₂, map_sub]
    abel
  have hb : id + b.comp a = j₂.comp (f.comp p₂) + (id - j₂.comp p₂) := by
    ext x
    simp only [a, b, add_apply, comp_apply, sub_apply, id_apply, h₁, map_sub]
    abel
  rw [← ha, ← hb]
  exact det_id_add_comp_comm a b

end LinearMap
