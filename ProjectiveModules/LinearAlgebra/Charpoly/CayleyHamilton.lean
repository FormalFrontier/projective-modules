/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.LocalRing.Module

/-!
# Cayley–Hamilton for finite projective modules

An endomorphism of a finite projective module annihilates its characteristic
polynomial. The proof checks the resulting endomorphism elementwise in the full
localizations at maximal ideals. The scalar-extended module is finite free there,
so the characteristic-polynomial base-change formula reduces the assertion to
Mathlib's finite-free Cayley–Hamilton theorem.

## References

* Mathlib's `LinearMap.aeval_self_charpoly` for the finite-free Cayley–Hamilton theorem.
* The Stacks Project, Tag 00NZ: finite flat modules over local rings are free.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

open Polynomial

private theorem aeval_baseChange
    {R : Type u} [CommSemiring R]
    {P : Type v} [AddCommMonoid P] [Module R P]
    (S : Type w) [CommSemiring S] [Algebra R S]
    (f : Module.End R P) (p : R[X]) :
    (Polynomial.aeval f p).baseChange S =
      Polynomial.aeval (f.baseChange S) (p.map (algebraMap R S)) := by
  exact Polynomial.map_aeval_eq_aeval_map
    (φ := algebraMap R S)
    (ψ := (Module.End.baseChangeHom R S P).toRingHom)
    (by
      ext1 r
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply R S (Module.End S (S ⊗[R] P))]
      exact ((Module.End.baseChangeHom R S P).commutes r).symm)
    p f

namespace Module

/-- The Cayley–Hamilton theorem for endomorphisms of finite projective modules.
This follows from Mathlib's finite-free `LinearMap.aeval_self_charpoly` by checking
the equality elementwise in the full localizations at maximal ideals. -/
theorem aeval_self_charpoly
    (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P) :
    Polynomial.aeval f (Module.charpoly R P f) = (0 : Module.End R P) := by
  classical
  ext x
  apply Module.eq_zero_of_localization_maximal
    (fun (m : Ideal R) (_ : m.IsMaximal) => Localization.AtPrime m ⊗[R] P)
    (fun m _ => TensorProduct.mk R (Localization.AtPrime m) P 1)
  intro m hm
  let S := Localization.AtPrime m
  let : Module.Free S (S ⊗[R] P) := Module.free_of_flat_of_isLocalRing
  have hzero : (Polynomial.aeval f (charpoly R P f)).baseChange S = 0 := by
    rw [aeval_baseChange, ← charpoly_baseChange, charpoly_eq_charpoly]
    exact LinearMap.aeval_self_charpoly (f.baseChange S)
  simpa only [LinearMap.baseChange_tmul, LinearMap.zero_apply, TensorProduct.tmul_zero,
    TensorProduct.mk_apply] using
    congrArg (fun g : Module.End S (S ⊗[R] P) => g (1 ⊗ₜ[R] x)) hzero

end Module
