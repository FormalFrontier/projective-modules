/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine.Endomorphism
import ProjectiveModules.ExteriorPower.Map

/-!
# Scalar powers for finite projective modules

`Module.rankPower R P` raises a scalar to the stalk rank on each rank fiber of a
finite projective module `P`. It is multiplicative, but need not preserve zero or
addition. The rank-fiber characteristic and its uniqueness criterion describe it
without unfolding the construction. For constant stalk rank `n`, it is the usual
`n`th power map; for a subsingleton module it is constantly one.

The scalar-multiplication formula for `Module.determinant` uses this rank-dependent
power instead of choosing a global rank. These powers commute with arbitrary
scalar extension, are invariant under linear equivalence, and multiply under
binary module products. All statements include the zero ring.

## Implementation notes

The construction reuses this library's `Module.rankFiberRingEquiv` and Mathlib's
`powMonoidHom` and `MonoidHom.pi`. No additional rank decomposition is used.
The compatibility laws follow from the scalar-identity characteristic and the
canonical determinant's scalar-extension, intertwining, and product laws.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w x

namespace Module

variable (R : Type u) [CommRing R]

section FiniteProjective

variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

/-- The multiplicative scalar power whose exponent on each rank fiber is the
stalk rank of the finite projective module. -/
def rankPower : R →* R :=
  ((rankFiberRingEquiv R P).symm.toAlgHom.toRingHom.toMonoidHom).comp
    (MonoidHom.pi fun i : rankFiberIndex R P ↦
      (powMonoidHom (rankFiberRank R P i)).comp
        (algebraMap R (rankFiberRing R P i)).toMonoidHom)

/-- On a rank fiber, the rank-dependent power is the ordinary power with exponent
the rank of that fiber. -/
theorem algebraMap_rankPower (r : R) (i : rankFiberIndex R P) :
    algebraMap R (rankFiberRing R P i) (rankPower R P r) =
      (algebraMap R (rankFiberRing R P i) r) ^ rankFiberRank R P i := by
  rw [← rankFiberRingEquiv_apply R P (rankPower R P r) i]
  change (rankFiberRingEquiv R P)
      ((rankFiberRingEquiv R P).symm
        (fun j : rankFiberIndex R P ↦
          (algebraMap R (rankFiberRing R P j) r) ^ rankFiberRank R P j)) i = _
  exact congrFun ((rankFiberRingEquiv R P).apply_symm_apply _) i

/-- A scalar is the rank-dependent power exactly when it has the specified value
on every rank fiber. -/
theorem eq_rankPower_iff (a r : R) :
    a = rankPower R P r ↔
      ∀ i : rankFiberIndex R P,
        algebraMap R (rankFiberRing R P i) a =
          (algebraMap R (rankFiberRing R P i) r) ^ rankFiberRank R P i := by
  constructor
  · rintro rfl
    exact algebraMap_rankPower R P r
  · intro h
    apply (rankFiberRingEquiv R P).injective
    funext i
    simpa only [rankFiberRingEquiv_apply, algebraMap_rankPower] using h i

/-- Constant stalk rank recovers the usual natural-number power. -/
theorem rankPower_eq_pow (n : ℕ)
    (h : rankAtStalk (R := R) P = fun _ ↦ n) (r : R) :
    rankPower R P r = r ^ n := by
  symm
  apply (eq_rankPower_iff R P (r ^ n) r).2
  intro i
  rw [map_pow, rankFiberRank_eq_of_rankAtStalk_eq R P i (fun p ↦ congrFun h p)]

/-- The rank-dependent power for a subsingleton module is one for every scalar,
including zero. -/
@[simp] theorem rankPower_of_subsingleton [Subsingleton P] (r : R) :
    rankPower R P r = 1 := by
  simpa only [pow_zero] using
    rankPower_eq_pow R P 0
      (rankAtStalk_eq_zero_of_subsingleton (R := R) (M := P)) r

/-- The canonical determinant of a scalar multiple of the identity is the
rank-dependent scalar power. -/
theorem determinant_smul_id (r : R) :
    determinant R P (r • (LinearMap.id : Module.End R P)) = rankPower R P r := by
  apply (eq_rankPower_iff R P _ r).2
  intro i
  let A := rankFiberRing R P i
  let M := rankFiberModule R P i
  let n := rankFiberRank R P i
  let : Module.Invertible A (⋀[A]^n M) :=
    exteriorPower.invertible_of_rankAtStalk_eq n
      (funext (rankAtStalk_rankFiberModule R P i))
  have hbase :
      (r • (LinearMap.id : Module.End R P)).baseChange A =
        algebraMap R A r • (LinearMap.id : Module.End A M) := by
    apply LinearMap.ext
    intro x
    simpa only [LinearMap.baseChange_smul, LinearMap.baseChange_id,
      LinearMap.smul_apply, LinearMap.id_apply] using
      (IsScalarTower.algebraMap_smul A r x).symm
  apply eq_of_smul_eq_smul (α := ⋀[A]^n M)
  intro y
  calc
    algebraMap R A
        (determinant R P (r • (LinearMap.id : Module.End R P))) • y =
        exteriorPower.map n
          ((r • (LinearMap.id : Module.End R P)).baseChange A) y :=
      (DeterminantLine.rankFiber_map_eq_smul_determinant R P _ i y).symm
    _ = (algebraMap R A r) ^ n • y := by
      simp only [hbase, exteriorPower.map_smul, exteriorPower.map_id,
        LinearMap.smul_apply, LinearMap.id_apply]

/-- Scaling any endomorphism of a finite projective module multiplies its
canonical determinant by the rank-dependent scalar power. -/
theorem determinant_smul (r : R) (f : Module.End R P) :
    determinant R P (r • f) = rankPower R P r * determinant R P f := by
  have hs : r • f = (r • (LinearMap.id : Module.End R P)) * f := by
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_eq_comp, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
  rw [hs, (determinant R P).map_mul, determinant_smul_id R P r]

/-- Rank-dependent powers commute with arbitrary scalar extension. -/
theorem rankPower_baseChange
    (S : Type w) [CommRing S] [Algebra R S] (r : R) :
    rankPower S (S ⊗[R] P) (algebraMap R S r) =
      algebraMap R S (rankPower R P r) := by
  have hbase :
      (r • (LinearMap.id : Module.End R P)).baseChange S =
        algebraMap R S r • (LinearMap.id : Module.End S (S ⊗[R] P)) := by
    apply LinearMap.ext
    intro x
    simpa only [LinearMap.baseChange_smul, LinearMap.baseChange_id,
      LinearMap.smul_apply, LinearMap.id_apply] using
      (IsScalarTower.algebraMap_smul S r x).symm
  rw [← determinant_smul_id S (S ⊗[R] P), ← hbase,
    determinant_baseChange R P S, determinant_smul_id R P]

/-- A linear equivalence preserves the rank-dependent power homomorphism. -/
theorem rankPower_congr
    (Q : Type x) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q] (e : P ≃ₗ[R] Q) :
    rankPower R P = rankPower R Q := by
  apply MonoidHom.ext
  intro r
  rw [← determinant_smul_id R P, ← determinant_smul_id R Q]
  apply determinant_eq_of_intertwining R P Q e
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    map_smul]

/-- Binary module products multiply the rank-dependent power homomorphisms
pointwise, including when the factors have varying stalk ranks. -/
theorem rankPower_prod
    (Q : Type x) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q] :
    rankPower R (P × Q) = rankPower R P * rankPower R Q := by
  apply MonoidHom.ext
  intro r
  rw [MonoidHom.mul_apply, ← determinant_smul_id R (P × Q),
    ← determinant_smul_id R P, ← determinant_smul_id R Q]
  have hprod :
      r • (LinearMap.id : Module.End R (P × Q)) =
        (r • (LinearMap.id : Module.End R P)).prodMap
          (r • (LinearMap.id : Module.End R Q)) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;> rfl
  rw [hprod, determinant_prodMap R P Q]

end FiniteProjective

/-- On a finite free module, the rank-dependent power is the ordinary power with
exponent the module's finrank. -/
theorem rankPower_eq_pow_finrank (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Free R P] (r : R) :
    rankPower R P r = r ^ Module.finrank R P := by
  exact rankPower_eq_pow R P (Module.finrank R P) rankAtStalk_eq_finrank_of_free r

end Module
