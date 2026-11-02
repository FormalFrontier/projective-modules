/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine.Endomorphism.Basic
import ProjectiveModules.ExteriorPower.BaseChange
import ProjectiveModules.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.RingTheory.LocalRing.Module

/-!
# Scalar determinants, stabilization, and scalar extension

The determinant of an endomorphism of a finite projective module agrees with
its ordinary determinant after extending it by the identity along any split
finite-free presentation. The module may have varying stalk rank, and the
section need not be a coordinate inclusion. Canonical scalar determinants also
commute with arbitrary scalar extension, without a flatness hypothesis: a split
finite-free presentation remains split after tensoring.

The proof compares the top exterior action on each rank fiber after localization
at maximal ideals. These full localizations retain nilpotents. The rectangular
determinant identity then compares the localized map with its stabilization.

## References

The scalar determinant and its rank-fiber action use the canonical determinant-line
interfaces in `ProjectiveModules.ExteriorPower.DeterminantLine.Endomorphism.Basic`.
For background on determinants and finite projective modules, see C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*.
The finite-free comparison reuses `LinearMap.det_stabilization_eq_of_retractions`
in `ProjectiveModules.LinearAlgebra.Determinant`, based on Mathlib's
Weinstein–Aronszajn identity. Scalar extension reuses Mathlib's
`Module.Finite.exists_comp_eq_id_of_projective` and `LinearMap.det_baseChange`.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w x y

namespace Module

-- Normalize the identity presentation before specializing the coefficient ring.
private theorem det_eq_det_stabilization_of_free
    {R : Type u} [CommRing R]
    {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Free R P] [Module.Finite R P]
    {M : Type w} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (f : Module.End R P) (p : M →ₗ[R] P) (j : P →ₗ[R] M)
    (hpj : p.comp j = LinearMap.id) :
    LinearMap.det f =
      LinearMap.det (j.comp (f.comp p) + (LinearMap.id - j.comp p)) := by
  simpa only [LinearMap.id_comp, LinearMap.comp_id, sub_self, add_zero] using
    (LinearMap.det_stabilization_eq_of_retractions
      (R := R) (M := P) (N := M) (P := P) f
      LinearMap.id LinearMap.id (by simp only [LinearMap.id_comp]) p j hpj)

-- Transport the whole determinant identity over abstract coefficient rings.
private theorem det_baseChange_stabilization
    {R : Type u} [CommRing R]
    {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (T : Type*) [CommRing T] [Algebra R T]
    (f : Module.End R P) (p : M →ₗ[R] P) (j : P →ₗ[R] M) :
    LinearMap.det
        ((j.baseChange T).comp ((f.baseChange T).comp (p.baseChange T)) +
          (LinearMap.id - (j.baseChange T).comp (p.baseChange T))) =
      algebraMap R T
        (LinearMap.det (j.comp (f.comp p) + (LinearMap.id - j.comp p))) := by
  calc
    _ = LinearMap.det
        ((j.comp (f.comp p) + (LinearMap.id - j.comp p)).baseChange T) := by
      congr 1
      simp only [LinearMap.baseChange_add, LinearMap.baseChange_sub,
        LinearMap.baseChange_comp, LinearMap.baseChange_id]
    _ = _ := LinearMap.det_baseChange (R := R) (M := M) (A := T) _

-- Perform both base changes before specializing to rank fibers and localizations.
private theorem det_baseChange_baseChange_stabilization
    {R : Type u} [CommRing R]
    {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (A : Type x) [CommRing A] [Algebra R A]
    (S : Type y) [CommRing S] [Algebra A S]
    [Module.Free S (S ⊗[A] (A ⊗[R] P))]
    [Module.Finite S (S ⊗[A] (A ⊗[R] P))]
    (f : Module.End R P) (p : M →ₗ[R] P) (j : P →ₗ[R] M)
    (hpj : p.comp j = LinearMap.id) :
    LinearMap.det ((f.baseChange A).baseChange S) =
      algebraMap A S (algebraMap R A
        (LinearMap.det (j.comp (f.comp p) + (LinearMap.id - j.comp p)))) := by
  have hA := congrArg (fun e : Module.End R P ↦ e.baseChange A) hpj
  have hS := congrArg
    (fun e : Module.End A (A ⊗[R] P) ↦ e.baseChange S) hA
  have hps : ((p.baseChange A).baseChange S).comp ((j.baseChange A).baseChange S) =
      (LinearMap.id : Module.End S (S ⊗[A] (A ⊗[R] P))) := by
    simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_id] using hS
  exact (det_eq_det_stabilization_of_free
    (R := S) (P := S ⊗[A] (A ⊗[R] P)) (M := S ⊗[A] (A ⊗[R] M))
    ((f.baseChange A).baseChange S) ((p.baseChange A).baseChange S)
    ((j.baseChange A).baseChange S) hps).trans
      ((det_baseChange_stabilization (R := A) (P := A ⊗[R] P) (M := A ⊗[R] M)
        S (f.baseChange A) (p.baseChange A) (j.baseChange A)).trans
          (congrArg (algebraMap A S)
            (det_baseChange_stabilization (R := R) (P := P) (M := M) A f p j)))

variable (R : Type u) [CommRing R]
variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
variable (M : Type w) [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

/-- The scalar determinant of a finite projective endomorphism is the ordinary
determinant of its extension by the identity along any split finite-free
presentation. The retract need not be free, and its stalk rank need not be constant. -/
theorem determinant_eq_det_stabilization
    (f : Module.End R P) (p : M →ₗ[R] P) (j : P →ₗ[R] M)
    (hpj : p.comp j = LinearMap.id) :
    Module.determinant R P f =
      LinearMap.det (j.comp (f.comp p) + (LinearMap.id - j.comp p)) := by
  apply (rankFiberRingEquiv R P).injective
  ext i
  let A := rankFiberRing R P i
  let Q := rankFiberModule R P i
  let d := rankFiberRank R P i
  have hscalar (r : R) : rankFiberRingEquiv R P r i = algebraMap R A r := by
    simpa only [Algebra.algebraMap_self_apply, Pi.algebraMap_apply] using
      congrFun ((rankFiberRingEquiv R P).commutes r) i
  rw [hscalar, hscalar]
  apply Module.eq_of_localization_maximal
    (fun (m : Ideal A) [m.IsMaximal] ↦ Localization.AtPrime m)
    (fun (m : Ideal A) [m.IsMaximal] ↦ Algebra.linearMap A (Localization.AtPrime m))
  intro m hm
  let S := Localization.AtPrime m
  let QS := S ⊗[A] Q
  let fs : Module.End S QS := (f.baseChange A).baseChange S
  let : Module.Free S QS := Module.free_of_flat_of_isLocalRing (R := S) (P := QS)
  have hRank : rankAtStalk (R := S) QS = fun _ ↦ d := by
    funext q
    rw [rankAtStalk_baseChange]
    exact rankAtStalk_rankFiberModule R P i _
  let := exteriorPower.invertible_of_rankAtStalk_eq d hRank
  have hdet : LinearMap.det (A := S) (M := QS) fs =
      algebraMap A S (algebraMap R A (determinant R P f)) := by
    rw [← determinant_eq_det S QS,
      determinant_eq_exteriorPower_determinant S QS d hRank]
    apply (exteriorPower.determinant_eq_iff_map_eq_smul S QS d fs _).2
    exact exteriorPower.map_baseChange_eq_smul (R := A) (S := S) (M := Q)
      d (f.baseChange A) _ (DeterminantLine.rankFiber_map_eq_smul_determinant R P f i)
  simp only [Algebra.linearMap_apply]
  exact hdet.symm.trans
    (det_baseChange_baseChange_stabilization (R := R) (P := P) (M := M) A S f p j hpj)

/-- Canonical scalar determinants commute with arbitrary scalar extension.
No flatness hypothesis is needed, since tensoring preserves a split retraction. -/
theorem determinant_baseChange
    (S : Type w) [CommRing S] [Algebra R S] (f : Module.End R P) :
    determinant S (S ⊗[R] P) (f.baseChange S) =
      algebraMap R S (determinant R P f) := by
  obtain ⟨n, p, j, _, _, hpj⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R P
  have hpjS : (p.baseChange S).comp (j.baseChange S) =
      (LinearMap.id : Module.End S (S ⊗[R] P)) := by
    simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_id] using
      congrArg (fun g : Module.End R P ↦ g.baseChange S) hpj
  rw [determinant_eq_det_stabilization S (S ⊗[R] P) (S ⊗[R] (Fin n → R))
      (f.baseChange S) (p.baseChange S) (j.baseChange S) hpjS,
    determinant_eq_det_stabilization R P (Fin n → R) f p j hpj]
  exact det_baseChange_stabilization (R := R) (P := P) (M := Fin n → R) S f p j

end Module
