/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine.Stabilization
import Mathlib.RingTheory.Finiteness.Projective

/-!
# Determinants of product endomorphisms

The scalar determinant of a product endomorphism is the product of the scalar
determinants, even when the finite projective factors have varying stalk ranks.
The coefficient ring may be trivial, and the endomorphisms may be noninvertible.

The proof uses Mathlib's finite-free split presentations, the scalar comparison
with their stabilizations, and `LinearMap.det_prodMap` on the free ambient modules.

## References

For determinants of finite projective modules, see C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Module

variable (R : Type u) [CommRing R]
variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
variable (Q : Type w) [AddCommGroup Q] [Module R Q]
  [Module.Finite R Q] [Module.Projective R Q]

/-- Scalar determinants of arbitrary finite projective endomorphisms multiply
under direct products, with no constant-rank or freeness hypothesis on the factors. -/
theorem determinant_prodMap
    (f : Module.End R P) (g : Module.End R Q) :
    Module.determinant R (P × Q) (f.prodMap g) =
      Module.determinant R P f * Module.determinant R Q g := by
  obtain ⟨n, pP, jP, _, _, hpP⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R P
  obtain ⟨m, pQ, jQ, _, _, hpQ⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R Q
  have hpjProd : (pP.prodMap pQ).comp (jP.prodMap jQ) =
      (LinearMap.id : Module.End R (P × Q)) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · simpa only [LinearMap.comp_apply, LinearMap.prodMap_apply,
        LinearMap.id_apply] using DFunLike.congr_fun hpP x.1
    · simpa only [LinearMap.comp_apply, LinearMap.prodMap_apply,
        LinearMap.id_apply] using DFunLike.congr_fun hpQ x.2
  have hblock :
      (jP.prodMap jQ).comp ((f.prodMap g).comp (pP.prodMap pQ)) +
        (LinearMap.id - (jP.prodMap jQ).comp (pP.prodMap pQ)) =
      (jP.comp (f.comp pP) + (LinearMap.id - jP.comp pP)).prodMap
        (jQ.comp (g.comp pQ) + (LinearMap.id - jQ.comp pQ)) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;>
      simp [LinearMap.prodMap_apply, LinearMap.comp_apply,
        LinearMap.id_apply, LinearMap.add_apply, LinearMap.sub_apply]
  have hPQ := Module.determinant_eq_det_stabilization R (P × Q)
    ((Fin n → R) × (Fin m → R)) (f.prodMap g)
    (pP.prodMap pQ) (jP.prodMap jQ) hpjProd
  have hP := Module.determinant_eq_det_stabilization R P (Fin n → R)
    f pP jP hpP
  have hQ := Module.determinant_eq_det_stabilization R Q (Fin m → R)
    g pQ jQ hpQ
  rw [hPQ, hblock, LinearMap.det_prodMap, ← hP, ← hQ]

end Module
