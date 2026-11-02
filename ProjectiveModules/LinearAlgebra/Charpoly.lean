/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine.Stabilization
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import ProjectiveModules.ExteriorPower.DeterminantLine.Endomorphism.Product
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Characteristic polynomials of finite projective modules

The characteristic polynomial of an endomorphism of a finite projective module
is the determinant of its universal scalar pencil over the polynomial ring.
The scalar determinant is the one induced on the determinant line, so neither
freeness nor constant rank is required.

`Module.eval₂_charpoly` characterizes evaluation in every commutative algebra.
It gives ordinary scalar evaluation and compatibility with arbitrary scalar
extension. For finite free modules, `Module.charpoly_eq_charpoly` identifies this
construction with Mathlib's characteristic polynomial. Characteristic polynomials
multiply under binary products of finite projective modules.
`Module.charpoly_eq_of_intertwining` gives invariance under linear equivalences,
and `Module.charpoly_conj` specializes it to conjugation.

## References

* Mathlib's finite-free characteristic polynomials and their scalar-extension API.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

open Polynomial

namespace Module

variable (R : Type u) [CommRing R]
variable (P : Type v) [AddCommGroup P] [Module R P]

section FiniteProjective

variable [Module.Finite R P] [Module.Projective R P]

/-- The characteristic polynomial of an endomorphism of a finite projective
module, defined by the determinant of its universal scalar pencil. -/
noncomputable def charpoly (f : Module.End R P) : R[X] :=
  Module.determinant R[X] (R[X] ⊗[R] P)
    ((Polynomial.X : R[X]) •
      (LinearMap.id : Module.End R[X] (R[X] ⊗[R] P)) - f.baseChange R[X])

/-- The characteristic polynomial is the determinant of the universal scalar
pencil on the polynomial scalar extension. -/
theorem charpoly_def (f : Module.End R P) :
    charpoly R P f = Module.determinant R[X] (R[X] ⊗[R] P)
      ((Polynomial.X : R[X]) •
        (LinearMap.id : Module.End R[X] (R[X] ⊗[R] P)) - f.baseChange R[X]) :=
  rfl

/-- Endomorphisms intertwined by a linear equivalence have the same
characteristic polynomial. -/
theorem charpoly_eq_of_intertwining
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q]
    (f : Module.End R P) (g : Module.End R Q) (e : P ≃ₗ[R] Q)
    (h : e.toLinearMap.comp f = g.comp e.toLinearMap) :
    charpoly R P f = charpoly R Q g := by
  have hbase : (e.toLinearMap.baseChange R[X]).comp (f.baseChange R[X]) =
      (g.baseChange R[X]).comp (e.toLinearMap.baseChange R[X]) := by
    simpa only [LinearMap.baseChange_comp] using
      congrArg (fun k : P →ₗ[R] Q => k.baseChange R[X]) h
  rw [charpoly_def, charpoly_def]
  apply determinant_eq_of_intertwining (e := e.baseChange R R[X] P Q)
  simp only [LinearEquiv.coe_baseChange]
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_sub, map_smul] using
    congrArg (fun k : R[X] ⊗[R] P →ₗ[R[X]] R[X] ⊗[R] Q =>
      (Polynomial.X : R[X]) • (e.toLinearMap.baseChange R[X]) x - k x) hbase

/-- Characteristic polynomials are unchanged by conjugation along a linear
equivalence. -/
theorem charpoly_conj
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q]
    (f : Module.End R P) (e : P ≃ₗ[R] Q) :
    charpoly R Q (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) =
      charpoly R P f := by
  symm
  apply charpoly_eq_of_intertwining R P Q f _ e
  ext x
  simp

/-- Evaluating the characteristic polynomial at an element of any commutative
algebra gives the determinant of the corresponding scalar pencil after base
change. -/
theorem eval₂_charpoly (f : Module.End R P)
    (S : Type w) [CommRing S] [Algebra R S] (s : S) :
    Polynomial.eval₂ (algebraMap R S) s (charpoly R P f) =
      Module.determinant S (S ⊗[R] P)
        (s • (LinearMap.id : Module.End S (S ⊗[R] P)) - f.baseChange S) := by
  let : Algebra R[X] S := (Polynomial.aeval (R := R) s).toRingHom.toAlgebra
  let : IsScalarTower R R[X] S :=
    IsScalarTower.of_algebraMap_eq fun r =>
      ((Polynomial.aeval (R := R) s).commutes r).symm
  have hX : algebraMap R[X] S (Polynomial.X : R[X]) = s := Polynomial.aeval_X s
  calc
    Polynomial.eval₂ (algebraMap R S) s (charpoly R P f) =
        algebraMap R[X] S (charpoly R P f) := by
      rw [← Polynomial.aeval_def]
      rfl
    _ = Module.determinant S (S ⊗[R[X]] (R[X] ⊗[R] P))
        (((Polynomial.X : R[X]) •
          (LinearMap.id : Module.End R[X] (R[X] ⊗[R] P)) -
            f.baseChange R[X]).baseChange S) := by
      rw [charpoly_def, determinant_baseChange]
    _ = Module.determinant S (S ⊗[R] P)
        (s • (LinearMap.id : Module.End S (S ⊗[R] P)) - f.baseChange S) := by
      apply determinant_eq_of_intertwining
        (e := TensorProduct.AlgebraTensorModule.cancelBaseChange R R[X] S S P)
      apply TensorProduct.AlgebraTensorModule.ext
      intro a y
      induction y using TensorProduct.inductionOn with
      | tmul p x =>
          simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            TensorProduct.smul_tmul', Algebra.smul_def, hX,
            mul_left_comm, mul_comm]
      | add y z hy hz =>
          simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hy hz

/-- Evaluating the characteristic polynomial at a scalar gives the determinant
of the scalar pencil on the original module. -/
theorem eval_charpoly (f : Module.End R P) (r : R) :
    (charpoly R P f).eval r =
      Module.determinant R P (r • (LinearMap.id : Module.End R P) - f) := by
  calc
    (charpoly R P f).eval r = Polynomial.aeval r (charpoly R P f) :=
      (congrFun (Polynomial.coe_aeval_eq_eval r) (charpoly R P f)).symm
    _ = Module.determinant R (R ⊗[R] P)
        (r • (LinearMap.id : Module.End R (R ⊗[R] P)) - f.baseChange R) := by
      rw [Polynomial.aeval_def]
      exact eval₂_charpoly R P f R r
    _ = Module.determinant R P (r • (LinearMap.id : Module.End R P) - f) := by
      apply determinant_eq_of_intertwining (e := TensorProduct.lid R P)
      ext a
      simp

/-- Characteristic polynomials of finite projective modules commute with
arbitrary commutative algebra scalar extension. -/
theorem charpoly_baseChange (f : Module.End R P)
    (S : Type w) [CommRing S] [Algebra R S] :
    charpoly S (S ⊗[R] P) (f.baseChange S) =
      Polynomial.map (algebraMap R S) (charpoly R P f) := by
  calc
    charpoly S (S ⊗[R] P) (f.baseChange S) =
        Module.determinant S[X] (S[X] ⊗[S] (S ⊗[R] P))
          ((Polynomial.X : S[X]) •
            (LinearMap.id : Module.End S[X] (S[X] ⊗[S] (S ⊗[R] P))) -
              (f.baseChange S).baseChange S[X]) :=
      charpoly_def S (S ⊗[R] P) (f.baseChange S)
    _ = Module.determinant S[X] (S[X] ⊗[R] P)
        ((Polynomial.X : S[X]) •
          (LinearMap.id : Module.End S[X] (S[X] ⊗[R] P)) - f.baseChange S[X]) := by
      let e := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S[X] S[X] P
      apply determinant_eq_of_intertwining (e := e)
      rw [LinearMap.baseChange_baseChange]
      apply LinearMap.ext
      intro x
      change e ((Polynomial.X : S[X]) • x -
          e.symm ((f.baseChange S[X]) (e x))) =
        (Polynomial.X : S[X]) • e x - (f.baseChange S[X]) (e x)
      rw [map_sub, map_smul, e.apply_symm_apply]
    _ = Polynomial.eval₂ (algebraMap R S[X]) (Polynomial.X : S[X])
        (charpoly R P f) :=
      (eval₂_charpoly R P f S[X] (Polynomial.X : S[X])).symm
    _ = Polynomial.map (algebraMap R S) (charpoly R P f) := by
      rw [← Polynomial.aeval_def, Polynomial.aeval_X_left_eq_map]

/-- The characteristic polynomial of a product endomorphism is the product of
its characteristic polynomials. -/
theorem charpoly_prodMap
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q]
    (f : Module.End R P) (g : Module.End R Q) :
    charpoly R (P × Q) (f.prodMap g) = charpoly R P f * charpoly R Q g := by
  calc
    charpoly R (P × Q) (f.prodMap g) =
        Module.determinant R[X] ((R[X] ⊗[R] P) × (R[X] ⊗[R] Q))
          (((Polynomial.X : R[X]) •
              (LinearMap.id : Module.End R[X] (R[X] ⊗[R] P)) -
                f.baseChange R[X]).prodMap
            ((Polynomial.X : R[X]) •
              (LinearMap.id : Module.End R[X] (R[X] ⊗[R] Q)) -
                g.baseChange R[X])) := by
      rw [charpoly_def]
      apply determinant_eq_of_intertwining
        (e := TensorProduct.prodRight R R[X] R[X] P Q)
      apply TensorProduct.AlgebraTensorModule.ext
      intro a x
      rcases x with ⟨p, q⟩
      simp [TensorProduct.prodRight_tmul]
    _ = charpoly R P f * charpoly R Q g := by
      rw [determinant_prodMap, ← charpoly_def, ← charpoly_def]

/-- The characteristic polynomial of an endomorphism of a zero module is one. -/
@[simp] theorem charpoly_of_subsingleton [Subsingleton P] (f : Module.End R P) :
    charpoly R P f = 1 := by
  rw [charpoly_def, determinant_of_subsingleton]

end FiniteProjective

/-- On a finite free module, the determinant-line characteristic polynomial
agrees with Mathlib's characteristic polynomial. -/
theorem charpoly_eq_charpoly [Module.Finite R P] [Module.Free R P]
    (f : Module.End R P) : charpoly R P f = f.charpoly := by
  rw [charpoly_def, determinant_eq_det]
  have h := LinearMap.eval_charpoly (f.baseChange R[X]) (Polynomial.X : R[X])
  rw [LinearMap.charpoly_baseChange, Polynomial.eval_map_algebraMap,
    Polynomial.aeval_X_left_apply] at h
  simpa only [Algebra.algebraMap_eq_smul_one, Module.End.one_eq_id] using h.symm

end Module
