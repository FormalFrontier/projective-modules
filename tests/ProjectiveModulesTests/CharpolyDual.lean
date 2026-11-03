/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly

/-!
# Scalar pencils on the algebraic dual

The original characteristic polynomial also computes the determinants of scalar
pencils on the dual module, without choosing a self-duality equivalence.
-/

@[expose] public section

universe u v

variable (R : Type u) [CommRing R]
variable (P : Type v) [AddCommGroup P] [Module R P]
variable [Module.Finite R P] [Module.Projective R P]

example (f : Module.End R P) (r : R) :
    (Module.charpoly R P f).eval r =
      Module.determinant R (Module.Dual R P)
        (r • (LinearMap.id : Module.End R (Module.Dual R P)) - f.dualMap) := by
  rw [← Module.charpoly_dualMap R P f]
  exact Module.eval_charpoly R (Module.Dual R P) f.dualMap r
