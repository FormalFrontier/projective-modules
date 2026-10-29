/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective

/-!
# Finite-family finite free factorization

Each finite family in a projective semimodule is fixed simultaneously by a
composite of global linear maps through a finite free semimodule with
coordinates indexed by `Fin n`. The finite free semimodule and both maps may
depend on the family.
-/

@[expose] public section

universe uR uP uι

open scoped BigOperators

namespace Module.Projective

variable {R : Type uR} [Semiring R]
variable {P : Type uP} [AddCommMonoid P] [Module R P] [Module.Projective R P]

/-- Every finite family in a projective semimodule is fixed simultaneously by a
composite of global linear maps through a finite free semimodule, without a
finite generation assumption on the projective semimodule. The equality is
asserted only on the family, not globally. Empty families are allowed. -/
theorem exists_finite_free_factorization_on {ι : Type uι} [Finite ι] (x : ι → P) :
    ∃ (n : ℕ) (A : (Fin n → R) →ₗ[R] P) (B : P →ₗ[R] (Fin n → R)),
      ∀ i, A (B (x i)) = x i := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let q : (P →₀ R) →ₗ[R] P :=
    Finsupp.linearCombination R (fun p : P => p)
  have hq : Function.Surjective q := by
    intro y
    exact ⟨Finsupp.single y 1, by simp [q]⟩
  obtain ⟨s, hs⟩ :=
    Module.projective_lifting_property q (LinearMap.id : P →ₗ[R] P) hq
  let t : Finset P := Finset.univ.biUnion fun i => (s (x i)).support
  let I := {p : P // p ∈ t}
  let n : ℕ := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let A : (Fin n → R) →ₗ[R] P :=
    { toFun := fun a => ∑ i : I, a (e i) • i.1
      map_add' := by
        intro a b
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum] }
  let B : P →ₗ[R] (Fin n → R) :=
    { toFun := fun y j => (s y) (e.symm j).1
      map_add' := by
        intro y z
        funext j
        exact congrArg (fun f : P →₀ R => f (e.symm j).1) (s.map_add y z)
      map_smul' := by
        intro r y
        funext j
        exact congrArg (fun f : P →₀ R => f (e.symm j).1) (s.map_smul r y) }
  refine ⟨n, A, B, ?_⟩
  intro j
  change (∑ i : I, (s (x j)) (e.symm (e i)).1 • i.1) = x j
  simp only [Equiv.symm_apply_apply]
  calc
    (∑ i : I, (s (x j)) i.1 • i.1) = ∑ p ∈ t, (s (x j)) p • p := by
      refine Finset.sum_bij (fun i _ => i.1) (fun i _ => i.2) ?_ ?_
        (fun _ _ => rfl)
      · intro i _ k _ hik
        exact Subtype.ext hik
      · intro p hp
        exact ⟨⟨p, hp⟩, Finset.mem_univ _, rfl⟩
    _ = ∑ p ∈ (s (x j)).support, (s (x j)) p • p := by
      symm
      apply Finset.sum_subset
      · intro p hp
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hp⟩
      · intro p _ hp
        have hz : (s (x j)) p = 0 := by
          simpa only [Finsupp.mem_support_iff, not_not] using hp
        simp only [hz, zero_smul]
    _ = q (s (x j)) := by
      simp only [q, Finsupp.linearCombination_apply, Finsupp.sum]
    _ = x j := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        (LinearMap.congr_fun hs (x j))

/-- Every point of a projective semimodule is fixed by a composite of global
linear maps through a finite free semimodule, without a finite generation
assumption on the projective semimodule. The equality is asserted only at the
chosen point, not simultaneously at all points. -/
theorem exists_finite_free_factorization_at (x : P) :
    ∃ (n : ℕ) (A : (Fin n → R) →ₗ[R] P) (B : P →ₗ[R] (Fin n → R)),
      A (B x) = x := by
  obtain ⟨n, A, B, h⟩ :=
    exists_finite_free_factorization_on (R := R) (P := P) (fun _ : PUnit.{1} => x)
  exact ⟨n, A, B, h PUnit.unit⟩

end Module.Projective
