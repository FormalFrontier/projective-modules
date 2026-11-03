/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly

/-!
# Scalar evaluation in an invariant short exact sequence

Evaluating the original middle characteristic polynomial gives the product of
the scalar-pencil determinants on the submodule and quotient, without choosing
an equivariant splitting.
-/

@[expose] public section

universe uR uP uM uQ

variable (R : Type uR) [CommRing R]
variable (P : Type uP) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
variable (M : Type uM) [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]
variable (Q : Type uQ) [AddCommGroup Q] [Module R Q]
  [Module.Finite R Q] [Module.Projective R Q]

example (i : P →ₗ[R] M) (q : M →ₗ[R] Q)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hex : LinearMap.range i = LinearMap.ker q)
    (fp : Module.End R P) (fm : Module.End R M) (fq : Module.End R Q)
    (hp : fm.comp i = i.comp fp) (hfq : q.comp fm = fq.comp q) (r : R) :
    (Module.charpoly R M fm).eval r =
      Module.determinant R P (r • (LinearMap.id : Module.End R P) - fp) *
        Module.determinant R Q (r • (LinearMap.id : Module.End R Q) - fq) := by
  rw [Module.charpoly_eq_mul_of_exact R P M Q i q hi hq hex fp fm fq hp hfq,
    Polynomial.eval_mul, Module.eval_charpoly, Module.eval_charpoly]
