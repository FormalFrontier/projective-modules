/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine.Endomorphism.Basic
import ProjectiveModules.ExteriorPower.DeterminantLine.Stabilization
import ProjectiveModules.LinearAlgebra.Determinant
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.Tactic.Abel

/-!
# The rectangular determinant identity

For maps between finite projective modules, the scalar determinants of
`1 + g.comp f` and `1 + f.comp g` agree. Independent finite-free split
presentations reduce the assertion to the rectangular matrix identity;
the modules need not have the same rank, or constant stalk rank.

## References

The finite-free comparison reuses `LinearMap.det_id_add_comp_comm` in
`ProjectiveModules.LinearAlgebra.Determinant`, which applies Mathlib's
`Matrix.det_one_add_mul_comm` from
`Mathlib.LinearAlgebra.Matrix.SchurComplement`.
-/

@[expose] public section

universe u v w

namespace Module

variable (R : Type u) [CommRing R]
variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
variable (Q : Type w) [AddCommGroup Q] [Module R Q]
  [Module.Finite R Q] [Module.Projective R Q]

/-- The rectangular determinant identity for finite projective modules,
extending Mathlib's `Matrix.det_one_add_mul_comm`. Neither freeness nor
constant stalk rank nor invertibility of either endomorphism is required. -/
theorem determinant_one_add_comp_comm (f : P →ₗ[R] Q) (g : Q →ₗ[R] P) :
    determinant R P (1 + g.comp f) = determinant R Q (1 + f.comp g) := by
  change determinant R P (LinearMap.id + g.comp f) =
    determinant R Q (LinearMap.id + f.comp g)
  obtain ⟨m, pP, iP, _, _, hpP⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R P
  obtain ⟨n, pQ, iQ, _, _, hpQ⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R Q
  have hP (x : P) : pP (iP x) = x := DFunLike.congr_fun hpP x
  have hQ (x : Q) : pQ (iQ x) = x := DFunLike.congr_fun hpQ x
  let F := iQ.comp (f.comp pP)
  let G := iP.comp (g.comp pQ)
  have hGP : LinearMap.id + G.comp F =
      iP.comp ((LinearMap.id + g.comp f).comp pP) +
        (LinearMap.id - iP.comp pP) := by
    apply LinearMap.ext
    intro x
    simp only [F, G, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.id_apply, hQ, map_add]
    abel
  have hFG : LinearMap.id + F.comp G =
      iQ.comp ((LinearMap.id + f.comp g).comp pQ) +
        (LinearMap.id - iQ.comp pQ) := by
    apply LinearMap.ext
    intro x
    simp only [F, G, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.id_apply, hP, map_add]
    abel
  rw [determinant_eq_det_stabilization R P (Fin m → R)
      (LinearMap.id + g.comp f) pP iP hpP,
    determinant_eq_det_stabilization R Q (Fin n → R)
      (LinearMap.id + f.comp g) pQ iQ hpQ, ← hGP, ← hFG]
  exact LinearMap.det_id_add_comp_comm G F

end Module
