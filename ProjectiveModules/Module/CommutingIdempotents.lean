/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Projection
public import ProjectiveModules.Module.CommutingProjections
import Mathlib.Data.Fintype.BigOperators
import StableRange.Module.SplitSurjective

/-!
# Commuting idempotent endomorphisms

The simultaneous range-kernel decomposition for two commuting idempotents has
four coordinates, ordered as range-range, range-kernel, kernel-range and
kernel-kernel. The forward map applies the endomorphisms `p * q`, `p * (1 - q)`,
`(1 - p) * q` and `(1 - p) * (1 - q)` in that order. The inverse adds the four
underlying module elements, grouping the first two and the last two together.

The scalars form a semiring and the ambient module is an additive commutative
group. Subtraction takes place in its endomorphism ring; the intersection
submodules and their products need only their additive commutative monoid
structures. Commutation ensures that the two range-kernel decompositions are
compatible. This equivalence specializes the finite-family decomposition and
reindexes its Boolean choices into the four displayed coordinates.

## References

* Mathlib, `Mathlib.LinearAlgebra.Projection` and
  `Mathlib.Algebra.Module.LinearMap.End` (idempotent range-kernel identities and
  endomorphism ring operations).
* Formal Frontier Agents,
  `ProjectiveModules.Module.CommutingProjections` (finite simultaneous
  decomposition), `StableRange.Module.SplitSurjective`,
  `ProjectiveModules.Module.ProjectiveKernel` and
  `ProjectiveModules.Module.ProjectiveComplement` (split-kernel and
  module-product formalization ideas).
-/

@[expose] public section

universe uR uM

namespace LinearMap

private theorem jointBlock_pair
    {R : Type uR} [Semiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    (p q : Module.End R M) (ε : Fin 2 → Bool) :
    jointBlock ![p, q] ε =
      (if ε 0 then p.range else p.ker) ⊓
        (if ε 1 then q.range else q.ker) := by
  ext x
  simp only [jointBlock, Submodule.mem_iInf, Fin.forall_fin_two,
    Submodule.mem_inf, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem pair_idempotent
    {R : Type uR} [Semiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    (p q : Module.End R M)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    ∀ i : Fin 2, IsIdempotentElem (![p, q] i) :=
  Fin.forall_fin_two.mpr ⟨hp, hq⟩

private theorem pair_commute
    {R : Type uR} [Semiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    (p q : Module.End R M) (hpq : Commute p q) :
    Pairwise (fun i j : Fin 2 ↦ Commute (![p, q] i) (![p, q] j)) := by
  change ∀ i j : Fin 2, i ≠ j → Commute (![p, q] i) (![p, q] j)
  simp only [Fin.forall_fin_two]
  exact ⟨⟨fun h ↦ (h rfl).elim, fun _ ↦ hpq⟩,
    ⟨fun _ ↦ hpq.symm, fun h ↦ (h rfl).elim⟩⟩

private theorem jointProjector_pair
    {R : Type uR} [Semiring R]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (p q : Module.End R M) (hpq : Commute p q) (ε : Fin 2 → Bool) :
    jointProjector ![p, q] (pair_commute p q hpq) ε =
      (if ε 0 then p else 1 - p) * (if ε 1 then q else 1 - q) := by
  classical
  let g : Fin 2 → Module.End R M := fun i ↦
    if ε i then ![p, q] i else 1 - ![p, q] i
  have hε : (↑(Finset.univ : Finset (Fin 2)) : Set (Fin 2)).Pairwise
      (fun i j ↦ Commute (g i) (g j)) := by
    intro i hi j hj hij
    have h := pair_commute p q hpq hij
    dsimp only [g]
    cases ε i <;> cases ε j <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact (Commute.one_right _).sub_right ((Commute.one_left _).sub_left h)
    · exact (Commute.one_left _).sub_left h
    · exact (Commute.one_right _).sub_right h
    · exact h
  have he := (jointProjector_eq_noncommProd ![p, q] (pair_commute p q hpq) ε hε).trans
    (Finset.noncommProd_congr (f := g) (g := g)
      Finset.univ_fin2 (fun _ _ ↦ rfl) hε)
  simpa [g] using he

/-- The simultaneous range-kernel equivalence for two commuting idempotents.
The four coordinates are the range-range, range-kernel, kernel-range and
kernel-kernel components, and the inverse is the sum of their inclusions. -/
noncomputable def commutingIdempotentsEquiv
    {R : Type uR} [Semiring R]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (p q : Module.End R M)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : Commute p q) :
    M ≃ₗ[R] ((↥(p.range ⊓ q.range) × ↥(p.range ⊓ q.ker)) ×
      (↥(p.ker ⊓ q.range) × ↥(p.ker ⊓ q.ker))) := by
  refine (commutingIdempotentsPiEquiv ![p, q]
    (by exact pair_idempotent p q hp hq) (by exact pair_commute p q hpq)).trans
    (show ((ε : Fin 2 → Bool) → jointBlock ![p, q] ε) ≃ₗ[R]
      ((↥(p.range ⊓ q.range) × ↥(p.range ⊓ q.ker)) ×
        (↥(p.ker ⊓ q.range) × ↥(p.ker ⊓ q.ker))) from ?_)
  -- Only coordinate rearrangement and equality transport remain after the
  -- finite decomposition. No group structure on the block fibers is used.
  exact
    { toFun := fun b ↦
        (((LinearEquiv.ofEq _ _ (by exact jointBlock_pair p q ![true, true]))
            (b ![true, true]),
          (LinearEquiv.ofEq _ _ (by exact jointBlock_pair p q ![true, false]))
            (b ![true, false])),
          ((LinearEquiv.ofEq _ _ (by exact jointBlock_pair p q ![false, true]))
            (b ![false, true]),
          (LinearEquiv.ofEq _ _ (by exact jointBlock_pair p q ![false, false]))
            (b ![false, false])))
      invFun := fun z ε ↦
        ⟨if ε 0 then (if ε 1 then (z.1.1 : M) else (z.1.2 : M))
          else (if ε 1 then (z.2.1 : M) else (z.2.2 : M)), by
          rw [jointBlock_pair]
          cases h₀ : ε 0 <;> cases h₁ : ε 1
          · simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte] using z.2.2.property
          · simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte] using z.2.1.property
          · simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte] using z.1.2.property
          · simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte] using z.1.1.property⟩
      left_inv := by
        intro b
        funext ε
        apply Subtype.ext
        cases h₀ : ε 0 <;> cases h₁ : ε 1
        · have hε : ε = ![false, false] :=
            funext (Fin.forall_fin_two.mpr ⟨h₀, h₁⟩)
          simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte,
            LinearEquiv.coe_ofEq_apply] using
            congrArg (fun η : Fin 2 → Bool ↦ (b η : M)) hε.symm
        · have hε : ε = ![false, true] :=
            funext (Fin.forall_fin_two.mpr ⟨h₀, h₁⟩)
          simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte,
            LinearEquiv.coe_ofEq_apply] using
            congrArg (fun η : Fin 2 → Bool ↦ (b η : M)) hε.symm
        · have hε : ε = ![true, false] :=
            funext (Fin.forall_fin_two.mpr ⟨h₀, h₁⟩)
          simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte,
            LinearEquiv.coe_ofEq_apply] using
            congrArg (fun η : Fin 2 → Bool ↦ (b η : M)) hε.symm
        · have hε : ε = ![true, true] :=
            funext (Fin.forall_fin_two.mpr ⟨h₀, h₁⟩)
          simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte,
            LinearEquiv.coe_ofEq_apply] using
            congrArg (fun η : Fin 2 → Bool ↦ (b η : M)) hε.symm
      right_inv := by
        intro z
        apply Prod.ext <;> apply Prod.ext <;> apply Subtype.ext <;> rfl
      map_add' := by
        intro b c
        apply Prod.ext <;> apply Prod.ext <;> apply Subtype.ext <;> rfl
      map_smul' := by
        intro r b
        apply Prod.ext <;> apply Prod.ext <;> apply Subtype.ext <;> rfl }

/-- The range-range coordinate has underlying value `(p * q) x`. -/
@[simp] theorem commutingIdempotentsEquiv_apply_fst_fst
    {R : Type uR} [Semiring R]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (p q : Module.End R M)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : Commute p q) (x : M) :
    ((commutingIdempotentsEquiv p q hp hq hpq x).1.1 : M) = (p * q) x := by
  simp only [commutingIdempotentsEquiv, LinearEquiv.trans_apply]
  simpa using congrArg (fun e : Module.End R M ↦ e x)
    (jointProjector_pair p q hpq ![true, true])

/-- The range-kernel coordinate has underlying value `(p * (1 - q)) x`. -/
@[simp] theorem commutingIdempotentsEquiv_apply_fst_snd
    {R : Type uR} [Semiring R]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (p q : Module.End R M)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : Commute p q) (x : M) :
    ((commutingIdempotentsEquiv p q hp hq hpq x).1.2 : M) = (p * (1 - q)) x := by
  simp only [commutingIdempotentsEquiv, LinearEquiv.trans_apply]
  simpa using congrArg (fun e : Module.End R M ↦ e x)
    (jointProjector_pair p q hpq ![true, false])

/-- The kernel-range coordinate has underlying value `((1 - p) * q) x`. -/
@[simp] theorem commutingIdempotentsEquiv_apply_snd_fst
    {R : Type uR} [Semiring R]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (p q : Module.End R M)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : Commute p q) (x : M) :
    ((commutingIdempotentsEquiv p q hp hq hpq x).2.1 : M) = ((1 - p) * q) x := by
  simp only [commutingIdempotentsEquiv, LinearEquiv.trans_apply]
  simpa using congrArg (fun e : Module.End R M ↦ e x)
    (jointProjector_pair p q hpq ![false, true])

/-- The kernel-kernel coordinate has underlying value `((1 - p) * (1 - q)) x`. -/
@[simp] theorem commutingIdempotentsEquiv_apply_snd_snd
    {R : Type uR} [Semiring R]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (p q : Module.End R M)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : Commute p q) (x : M) :
    ((commutingIdempotentsEquiv p q hp hq hpq x).2.2 : M) =
      ((1 - p) * (1 - q)) x := by
  simp only [commutingIdempotentsEquiv, LinearEquiv.trans_apply]
  simpa using congrArg (fun e : Module.End R M ↦ e x)
    (jointProjector_pair p q hpq ![false, false])

/-- The inverse equivalence adds the four components in their coordinate order. -/
@[simp] theorem commutingIdempotentsEquiv_symm_apply
    {R : Type uR} [Semiring R]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (p q : Module.End R M)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : Commute p q)
    (z : (↥(p.range ⊓ q.range) × ↥(p.range ⊓ q.ker)) ×
      (↥(p.ker ⊓ q.range) × ↥(p.ker ⊓ q.ker))) :
    (commutingIdempotentsEquiv p q hp hq hpq).symm z =
      ((z.1.1 : M) + (z.1.2 : M)) + ((z.2.1 : M) + (z.2.2 : M)) := by
  classical
  let b : (ε : Fin 2 → Bool) → jointBlock ![p, q] ε := fun ε ↦
    ⟨if ε 0 then (if ε 1 then (z.1.1 : M) else (z.1.2 : M))
      else (if ε 1 then (z.2.1 : M) else (z.2.2 : M)), by
      rw [jointBlock_pair]
      cases h₀ : ε 0 <;> cases h₁ : ε 1
      · simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte] using z.2.2.property
      · simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte] using z.2.1.property
      · simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte] using z.1.2.property
      · simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte] using z.1.1.property⟩
  calc
    (commutingIdempotentsEquiv p q hp hq hpq).symm z =
        (commutingIdempotentsPiEquiv ![p, q] (pair_idempotent p q hp hq)
          (pair_commute p q hpq)).symm b := by
      unfold commutingIdempotentsEquiv
      exact LinearEquiv.symm_trans_apply z
    _ = ((z.1.1 : M) + (z.1.2 : M)) + ((z.2.1 : M) + (z.2.2 : M)) := by
      rw [commutingIdempotentsPiEquiv_symm_apply, finsum_eq_sum_of_fintype]
      rw [← (piFinTwoEquiv (fun _ : Fin 2 ↦ Bool)).symm.sum_comp (fun ε ↦ (b ε : M))]
      change (∑ z : Bool × Bool, (b ![z.1, z.2] : M)) = _
      rw [Fintype.sum_prod_type]
      simp [b]

end LinearMap
