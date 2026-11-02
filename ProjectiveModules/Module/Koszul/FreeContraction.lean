/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Koszul.FreeDifferential

/-!
# Positive-degree contraction on finite free modules

For the coordinate module `Fin m → S`, exterior and symmetric bases give a
tensor basis indexed by an exterior subset and a natural exponent function.
The pivot is the least element of the union of their supports. A basis vector
maps to zero when the pivot is already exterior; otherwise one pivot occurrence
moves from its symmetric exponent to its exterior subset, with the
insertion-position sign.

## Boundary conventions

The operator has positive symmetric source degree. The positive-total-degree
identities, including both boundary degrees, are in
`ProjectiveModules.Module.Koszul.FreeHomotopy`.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct
universe u

namespace Module.Koszul.CanonicalFreeContraction

/-- The union of the exterior subset and the exponent support. -/
def totalSupport {m i d : ℕ} (x : Label.{u} m i d) : Finset (Fin m) :=
  Finset.univ.filter (fun q => q ∈ (x.1 : Finset (Fin m)) ∨ x.2.val q ≠ 0)

/-- The natural-number values of the total support. -/
def supportedValue {m i d : ℕ} (x : Label.{u} m i d) (n : ℕ) : Prop :=
  ∃ q : Fin m, q.val = n ∧ q ∈ totalSupport x

/-- At positive symmetric degree the total support is nonempty. -/
theorem positiveSupport_exists {m i d : ℕ} (x : Label.{u} m i (d + 1)) :
    ∃ n : ℕ, supportedValue x n := by
  classical
  by_contra hn
  have hz : x.2.val = 0 := by
    apply Finsupp.ext
    intro q
    change x.2.val q = 0
    by_contra hq
    apply hn
    refine ⟨q.val, q, rfl, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, Or.inr hq⟩
  have hm : x.2.val.sum (fun _ k => k) = d + 1 := by
    simpa only [SymmetricIndex, Nat.card_ulift, Nat.card_fin] using x.2.property
  rw [hz] at hm
  change 0 = d + 1 at hm
  cases hm

/-- The least natural-number value in total support. -/
def pivotValue {m i d : ℕ} (x : Label.{u} m i (d + 1)) : ℕ := by
  classical
  exact Nat.find (positiveSupport_exists x)

/-- The selected value is bounded because it is the value of a `Fin m`. -/
theorem pivotValue_lt {m i d : ℕ} (x : Label.{u} m i (d + 1)) :
    pivotValue x < m := by
  classical
  obtain ⟨q, hq, _⟩ := Nat.find_spec (positiveSupport_exists x)
  change Nat.find (positiveSupport_exists x) < m
  rw [← hq]
  exact q.isLt

/-- The least element of total support. -/
def pivot {m i d : ℕ} (x : Label.{u} m i (d + 1)) : Fin m :=
  ⟨pivotValue x, pivotValue_lt x⟩

/-- Adjoining a missing pivot increases the exterior cardinality by one. -/
theorem inserted_card {m i d : ℕ} (x : Label.{u} m i (d + 1))
    (hp : pivot x ∉ (x.1 : Finset (Fin m))) :
    (Finset.cons (pivot x) (x.1 : Finset (Fin m)) hp).card = i + 1 := by
  rw [Finset.card_cons, Set.powersetCard.card_eq]

/-- Deleting one pivot occurrence leaves symmetric degree `d`. -/
theorem decremented_mass {m i d : ℕ} (x : Label.{u} m i (d + 1))
    (hp : pivot x ∉ (x.1 : Finset (Fin m))) :
    (x.2.val - Finsupp.single (pivot x) 1).sum (fun _ k => k) =
      Nat.card (SymmetricIndex.{u} d) := by
  classical
  have hs : pivot x ∈ totalSupport x := by
    obtain ⟨⟨n, hn⟩, hnval, hs⟩ := Nat.find_spec (positiveSupport_exists x)
    change n = pivotValue x at hnval
    subst n
    exact hs
  have hne : x.2.val (pivot x) ≠ 0 :=
    ((Finset.mem_filter.mp hs).2).resolve_left hp
  have hm :
      (x.2.val - Finsupp.single (pivot x) 1).sum (fun _ k => k) + 1 = d + 1 := by
    calc
      _ = ((x.2.val - Finsupp.single (pivot x) 1) +
          Finsupp.single (pivot x) 1).sum (fun _ k => k) := by
        have hadd :
            ((x.2.val - Finsupp.single (pivot x) 1) +
              Finsupp.single (pivot x) 1).sum (fun _ k => k) =
              (x.2.val - Finsupp.single (pivot x) 1).sum (fun _ k => k) +
                (Finsupp.single (pivot x) 1).sum (fun _ k => k) :=
          Finsupp.sum_hom_add_index
            (f := x.2.val - Finsupp.single (pivot x) 1)
            (g := Finsupp.single (pivot x) 1)
            (fun _ => AddMonoidHom.id ℕ)
        have hsingle :
            (Finsupp.single (pivot x) 1).sum (fun _ k => k) = (1 : ℕ) := by
          simp
        rw [hsingle] at hadd
        exact hadd.symm
      _ = x.2.val.sum (fun _ k => k) :=
        congrArg (fun a : Fin m →₀ ℕ => a.sum (fun _ k => k))
          (Finsupp.sub_add_single_one_cancel hne)
      _ = d + 1 := by simpa using x.2.property
  have hd : (x.2.val - Finsupp.single (pivot x) 1).sum (fun _ k => k) = d := by
    omega
  simpa using hd

/-- The label obtained by moving one pivot occurrence to the exterior subset. -/
def contractedLabel {m i d : ℕ} (x : Label.{u} m i (d + 1))
    (hp : pivot x ∉ (x.1 : Finset (Fin m))) : Label.{u} m (i + 1) d :=
  (Set.powersetCard.ofCard (inserted_card x hp),
    ⟨x.2.val - Finsupp.single (pivot x) 1, decremented_mass x hp⟩)

/-- A contracted exterior label inserts the pivot coordinate. -/
theorem contractedLabel_exterior {m i d : ℕ} (x : Label.{u} m i (d + 1))
    (hp : pivot x ∉ (x.1 : Finset (Fin m))) :
    ((contractedLabel x hp).1 : Finset (Fin m)) =
      _root_.Insert.insert (pivot x) (x.1 : Finset (Fin m)) := by
  classical
  ext q
  change q ∈ Finset.cons (pivot x) (x.1 : Finset (Fin m)) hp ↔
    q ∈ _root_.Insert.insert (pivot x) (x.1 : Finset (Fin m))
  simp only [Finset.mem_cons, Finset.mem_insert]

/-- A contracted symmetric label removes one occurrence of the pivot. -/
theorem contractedLabel_exponent {m i d : ℕ} (x : Label.{u} m i (d + 1))
    (hp : pivot x ∉ (x.1 : Finset (Fin m))) :
    (contractedLabel x hp).2.val = x.2.val - Finsupp.single (pivot x) 1 := rfl

/-- The insertion-position exponent of the integral sign. -/
def lowerCount {m i d : ℕ} (x : Label.{u} m i (d + 1)) : ℕ :=
  ((x.1 : Finset (Fin m)).filter (fun q => q < pivot x)).card

variable (S : Type u) [CommRing S]

/-- The signed pivot-insertion image of an exterior-symmetric basis vector. -/
def basisImage (m i d : ℕ) (x : Label.{u} m i (d + 1)) :
    Term S (Carrier S m) (i + 1) d :=
  if hp : pivot x ∈ (x.1 : Finset (Fin m)) then
    0
  else
    (-1 : S) ^ lowerCount x •
      termBasis S m (i + 1) d (contractedLabel x hp)

/-- The linear extension of signed pivot insertion at positive symmetric degree. -/
def kappa (m i d : ℕ) :
    Term S (Carrier S m) i (d + 1) →ₗ[S] Term S (Carrier S m) (i + 1) d :=
  (termBasis S m i (d + 1)).constr S (basisImage S m i d)

/-- The value of `kappa` on the exterior-symmetric tensor basis. -/
theorem kappa_basis (m i d : ℕ) (x : Label.{u} m i (d + 1)) :
    kappa S m i d (termBasis S m i (d + 1) x) =
      if hp : pivot x ∈ (x.1 : Finset (Fin m)) then
        0
      else
        (-1 : S) ^ lowerCount x •
          termBasis S m (i + 1) d (contractedLabel x hp) := by
  classical
  exact (termBasis S m i (d + 1)).constr_basis S (basisImage S m i d) x

/-- The mass of a degree-`d` symmetric basis label is `d`. -/
theorem symmetric_mass {m d : ℕ} (a : SymmetricLabel.{u} m d) :
    a.val.sum (fun _ k => k) = d := by
  simpa using a.property

/-- The pivot lies in total support and is its least element. -/
theorem pivot_spec {m i d : ℕ} (x : Label.{u} m i (d + 1)) :
    pivot x ∈ totalSupport x ∧
      ∀ q ∈ totalSupport x, pivot x ≤ q := by
  classical
  constructor
  · obtain ⟨⟨n, hn⟩, hnval, hs⟩ := Nat.find_spec (positiveSupport_exists x)
    change n = pivotValue x at hnval
    subst n
    exact hs
  · intro q hq
    change Nat.find (positiveSupport_exists x) ≤ q.val
    exact Nat.find_min' (positiveSupport_exists x) ⟨q, rfl, hq⟩

/-- Outside the exterior subset the pivot has positive symmetric exponent. -/
theorem pivot_exponent_pos {m i d : ℕ} (x : Label.{u} m i (d + 1))
    (hp : pivot x ∉ (x.1 : Finset (Fin m))) : 0 < x.2.val (pivot x) := by
  classical
  have hne : x.2.val (pivot x) ≠ 0 :=
    ((Finset.mem_filter.mp (pivot_spec x).1).2).resolve_left hp
  omega

/-- Over `ℤ`, the degree-one rank-one image is a nonzero basis vector with coefficient one. -/
theorem rankOne_nonzero :
    ∃ x : Label.{0} 1 0 1, ∃ y : Label.{0} 1 1 0,
      (x.1 : Finset (Fin 1)) = ∅ ∧
      x.2.val = Finsupp.single (0 : Fin 1) 1 ∧
      (y.1 : Finset (Fin 1)) = {(0 : Fin 1)} ∧
      y.2.val = 0 ∧
      kappa ℤ 1 0 0 (termBasis ℤ 1 0 1 x) =
        termBasis ℤ 1 1 0 y ∧
      termBasis ℤ 1 1 0 y ≠ 0 := by
  classical
  let x : Label.{0} 1 0 1 :=
    (Set.powersetCard.ofCard
      (by simp : (∅ : Finset (Fin 1)).card = 0),
      ⟨Finsupp.single (0 : Fin 1) 1, by simp⟩)
  have hp : pivot x ∉ (x.1 : Finset (Fin 1)) := by
    change pivot x ∉ (∅ : Finset (Fin 1))
    simp
  have hp0 : pivot x = (0 : Fin 1) := Subsingleton.elim _ _
  let y : Label.{0} 1 1 0 := contractedLabel x hp
  refine ⟨x, y, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · dsimp only [y]
    rw [contractedLabel_exterior]
    change _root_.Insert.insert (pivot x) (∅ : Finset (Fin 1)) = {(0 : Fin 1)}
    simp only [hp0, Finset.insert_empty]
  · dsimp only [y]
    rw [contractedLabel_exponent]
    change Finsupp.single (0 : Fin 1) 1 -
        Finsupp.single (pivot x) 1 = 0
    simp only [hp0, tsub_self]
  · rw [kappa_basis, dite_eq_right hp]
    change (-1 : ℤ) ^ 0 • termBasis ℤ 1 1 0 y =
      termBasis ℤ 1 1 0 y
    simp only [pow_zero, one_smul]
  · exact (termBasis ℤ 1 1 0).ne_zero y

end Module.Koszul.CanonicalFreeContraction
