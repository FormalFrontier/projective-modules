/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine.Stabilization
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Determinants and linear duality

Linear duality preserves the scalar determinant of every endomorphism of a finite
projective module. The module need not be free, faithful, or of constant stalk rank,
and the endomorphism need not be invertible.

Dualizing a split finite-free presentation reverses its retraction and section.
The extension by the identity for this dual presentation is the dual of the
original extension by the identity.

## References

The finite-free identity is Mathlib's `LinearMap.det_dualMap`. The comparison with
an arbitrary finite-free split presentation is
`Module.determinant_eq_det_stabilization`. For background on determinants and
finite projective modules, see C. A. Weibel, *The K-book: An Introduction to
Algebraic K-theory*.
-/

@[expose] public section

noncomputable section

universe u v

namespace Module

variable (R : Type u) [CommRing R]
variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

/-- Linear duality preserves the scalar determinant of an endomorphism of a finite
projective module. This extends Mathlib's finite-free `LinearMap.det_dualMap`. -/
theorem determinant_dualMap (f : Module.End R P) :
    determinant R (Module.Dual R P) f.dualMap = determinant R P f := by
  obtain ⟨n, p, j, _, _, hpj⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R P
  have hdual : j.dualMap.comp p.dualMap = LinearMap.id := by
    rw [LinearMap.dualMap_comp_dualMap, hpj, LinearMap.dualMap_id]
  rw [determinant_eq_det_stabilization R (Module.Dual R P)
      (Module.Dual R (Fin n → R)) f.dualMap j.dualMap p.dualMap hdual,
    determinant_eq_det_stabilization R P (Fin n → R) f p j hpj]
  calc
    _ = LinearMap.det
        (j.comp (f.comp p) + (LinearMap.id - j.comp p)).dualMap := by
      congr 1
      ext φ x
      simp
    _ = _ := LinearMap.det_dualMap _

end Module
