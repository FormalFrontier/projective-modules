/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly
public import ProjectiveModules.ExteriorPower.DeterminantLine.Endomorphism.Units
public import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Characteristic polynomials, units, and spectra

For an endomorphism of a finite projective module over a commutative ring, evaluation of its
intrinsic characteristic polynomial at a scalar is a unit exactly when the corresponding scalar
pencil is a unit. Consequently, the spectrum consists of the scalars at which the characteristic
polynomial has nonunit value. Over a general commutative ring, nonunit values need not be zero.
Evaluation at zero also characterizes invertibility by the constant coefficient, without a
constant-rank hypothesis or a sign formula.

The proofs use `Module.eval_charpoly`, `Module.isUnit_iff_isUnit_determinant`, and the standard
algebraic-spectrum interface `spectrum.mem_iff`. For finite free modules,
`Module.charpoly_eq_charpoly` and `LinearMap.charpoly_def` identify the intrinsic polynomial with
the characteristic polynomial of a basis matrix. Together with the usual transport of units and
spectra along basis algebra equivalences, these are the comparison with the matrix theory.

## References

* Mathlib's `Matrix.mem_spectrum_iff_not_isUnit_eval_charpoly` in
  `Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs` gives the corresponding criterion for matrices
  over commutative rings.
* Mathlib's `Mathlib.Algebra.Algebra.Spectrum.Basic` supplies the algebraic spectrum interface.
-/

@[expose] public section

universe u v

namespace Module

/-- The intrinsic characteristic polynomial has unit value at `r` exactly when `r • 1 - f` is a
unit. This is the finite-projective unit criterion underlying the characteristic-polynomial
spectral criterion formalized for matrices in Mathlib. -/
theorem isUnit_eval_charpoly_iff (R : Type u) (P : Type v) [CommRing R] [AddCommGroup P]
    [Module R P] [Module.Finite R P] [Module.Projective R P] (f : Module.End R P) (r : R) :
    IsUnit ((Module.charpoly R P f).eval r) ↔ IsUnit (r • (1 : Module.End R P) - f) := by
  rw [eval_charpoly R P f r]
  exact (isUnit_iff_isUnit_determinant R P (r • (1 : Module.End R P) - f)).symm

/-- A scalar belongs to the spectrum exactly when the intrinsic characteristic polynomial has
nonunit value there. This uses the algebraic spectrum, so over a general commutative ring the
condition is not the vanishing of the polynomial. -/
theorem mem_spectrum_iff_not_isUnit_eval_charpoly (R : Type u) (P : Type v) [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P) (r : R) :
    r ∈ spectrum R f ↔ ¬IsUnit ((Module.charpoly R P f).eval r) := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one,
    ← isUnit_eval_charpoly_iff R P f r]

/-- An endomorphism of a finite projective module is a unit exactly when the constant coefficient
of its intrinsic characteristic polynomial is a unit, by the evaluation criterion at zero. -/
theorem isUnit_iff_isUnit_charpoly_coeff_zero (R : Type u) (P : Type v) [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P) :
    IsUnit f ↔ IsUnit ((Module.charpoly R P f).coeff 0) := by
  have h0 : (Module.charpoly R P f).eval (0 : R) = (Module.charpoly R P f).coeff 0 :=
    Polynomial.eval₂_at_zero (p := Module.charpoly R P f) (RingHom.id R)
  rw [← h0]
  simpa using (isUnit_eval_charpoly_iff R P f (0 : R)).symm

end Module
