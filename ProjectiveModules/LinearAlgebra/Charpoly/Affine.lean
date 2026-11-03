/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly
public import ProjectiveModules.ExteriorPower.DeterminantLine.Scalar

/-!
# Affine changes of projective characteristic polynomials

For a finite projective module, substitution of `a * X + b` in the characteristic
polynomial of `a • f + b • 1` multiplies the characteristic polynomial of `f` by
the determinant of the scalar endomorphism `a • 1`. No invertibility assumption
on `a` is needed, and the module need not have constant rank.

The homothety formula follows from the characteristic pencil and the scalar law
for determinants. Translation is supplied by `Module.charpoly_sub_smul`.
-/

@[expose] public section

open scoped TensorProduct

universe uR uP

/-- Substituting `a * X` in the characteristic polynomial of `a • f` multiplies
`charpoly f` by the determinant of the scalar endomorphism `a • 1`. -/
theorem Module.charpoly_smul_comp
    (R : Type uR) [CommRing R]
    (P : Type uP) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P) (a : R) :
    (Module.charpoly R P (a • f)).comp (Polynomial.C a * Polynomial.X) =
      Polynomial.C (Module.determinant R P (a • (1 : Module.End R P))) *
        Module.charpoly R P f := by
  have : Module.Projective (Polynomial R) ((Polynomial R) ⊗[R] P) :=
    inferInstance
  have hscalar :
      Module.determinant (Polynomial R) ((Polynomial R) ⊗[R] P)
          (Polynomial.C a •
            (LinearMap.id : Module.End (Polynomial R) ((Polynomial R) ⊗[R] P))) =
        Polynomial.C (Module.determinant R P (a • (1 : Module.End R P))) := by
    calc
      _ = Module.determinant (Polynomial R) ((Polynomial R) ⊗[R] P)
          ((a • (1 : Module.End R P)).baseChange (Polynomial R)) := by
        congr 1
        rw [LinearMap.baseChange_smul, LinearMap.baseChange_one,
          Module.End.one_eq_id, Polynomial.C_eq_algebraMap,
          IsScalarTower.algebraMap_smul]
      _ = Polynomial.C (Module.determinant R P (a • (1 : Module.End R P))) := by
        simpa only [Polynomial.algebraMap_eq] using
          (Module.determinant_baseChange R P (Polynomial R)
            (a • (1 : Module.End R P)))
  calc
    (Module.charpoly R P (a • f)).comp (Polynomial.C a * Polynomial.X) =
        Polynomial.eval₂ (algebraMap R (Polynomial R))
          (Polynomial.C a * Polynomial.X) (Module.charpoly R P (a • f)) := rfl
    _ = Module.determinant (Polynomial R) ((Polynomial R) ⊗[R] P)
          ((Polynomial.C a * Polynomial.X) •
              (LinearMap.id : Module.End (Polynomial R) ((Polynomial R) ⊗[R] P)) -
            (a • f).baseChange (Polynomial R)) :=
      Module.eval₂_charpoly R P (a • f) (Polynomial R) (Polynomial.C a * Polynomial.X)
    _ = Module.determinant (Polynomial R) ((Polynomial R) ⊗[R] P)
          (Polynomial.C a •
            ((Polynomial.X : Polynomial R) •
                (LinearMap.id : Module.End (Polynomial R) ((Polynomial R) ⊗[R] P)) -
              f.baseChange (Polynomial R))) := by
      congr 1
      rw [smul_sub (Polynomial.C a)
          ((Polynomial.X : Polynomial R) •
            (LinearMap.id : Module.End (Polynomial R) ((Polynomial R) ⊗[R] P)))
          (f.baseChange (Polynomial R)),
        smul_smul, LinearMap.baseChange_smul,
        Polynomial.C_eq_algebraMap, IsScalarTower.algebraMap_smul]
    _ = Module.determinant (Polynomial R) ((Polynomial R) ⊗[R] P)
          (Polynomial.C a •
            (LinearMap.id : Module.End (Polynomial R) ((Polynomial R) ⊗[R] P))) *
        Module.determinant (Polynomial R) ((Polynomial R) ⊗[R] P)
          ((Polynomial.X : Polynomial R) •
              (LinearMap.id : Module.End (Polynomial R) ((Polynomial R) ⊗[R] P)) -
            f.baseChange (Polynomial R)) := by
      rw [Module.determinant_smul, Module.determinant_smul_id]
    _ = Polynomial.C (Module.determinant R P (a • (1 : Module.End R P))) *
        Module.charpoly R P f := by
      rw [hscalar, ← Module.charpoly_def R P f]

/-- Affine substitution in the characteristic polynomial of `a • f + b • 1`
scales `charpoly f` by the intrinsic determinant of `a • 1`, even when `a` is not
regular and the finite projective module does not have constant rank. -/
theorem Module.charpoly_smul_add_smul_comp
    (R : Type uR) [CommRing R]
    (P : Type uP) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P) (a b : R) :
    (Module.charpoly R P (a • f + b • (1 : Module.End R P))).comp
        (Polynomial.C a * Polynomial.X + Polynomial.C b) =
      Polynomial.C (Module.determinant R P (a • (1 : Module.End R P))) *
        Module.charpoly R P f := by
  have htranslate :
      Module.charpoly R P (a • f + b • (1 : Module.End R P)) =
        (Module.charpoly R P (a • f)).comp (Polynomial.X + Polynomial.C (-b)) := by
    simpa only [neg_smul, sub_neg_eq_add] using
      (Module.charpoly_sub_smul R P (a • f) (-b))
  have hcomp :
      (Polynomial.X + Polynomial.C (-b)).comp
          (Polynomial.C a * Polynomial.X + Polynomial.C b) =
        Polynomial.C a * Polynomial.X := by
    simp
  rw [htranslate, Polynomial.comp_assoc, hcomp]
  exact Module.charpoly_smul_comp R P f a
