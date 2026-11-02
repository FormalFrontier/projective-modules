/-
SPDX-License-Identifier: Apache-2.0
-/
module

public import ProjectiveModules.Module.Koszul.FreeBasis
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Differential labels for finite free Koszul terms

Deleting an exterior coordinate and increasing its symmetric exponent gives
labels for the Koszul differential. The basis formula records its signs.

## References

- C. Weibel, *The K-book: An Introduction to Algebraic K-theory* (2013),
  for the Koszul construction.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct
universe u

namespace Module.Koszul.CanonicalFreeContraction

/-- Removing a member of an exterior label decreases its cardinality by one. -/
theorem differentialLabel_card {m i d : ℕ} (x : Label.{u} m (i + 1) d)
    (p : Fin m) (hp : p ∈ (x.1 : Finset (Fin m))) :
    ((x.1 : Finset (Fin m)).erase p).card = i := by
  rw [Finset.card_erase_of_mem hp, Set.powersetCard.card_eq]
  omega

/-- Adding one coordinate occurrence increases the symmetric degree by one. -/
theorem differentialLabel_mass {m i d : ℕ} (x : Label.{u} m (i + 1) d)
    (p : Fin m) :
    (x.2.val + Finsupp.single p 1).sum (fun _ k => k) =
      Nat.card (SymmetricIndex.{u} (d + 1)) := by
  calc
    (x.2.val + Finsupp.single p 1).sum (fun _ k => k) =
        x.2.val.sum (fun _ k => k) +
          (Finsupp.single p 1).sum (fun _ k => k) :=
      Finsupp.sum_hom_add_index
        (f := x.2.val) (g := Finsupp.single p 1)
        (fun _ => AddMonoidHom.id ℕ)
    _ = Nat.card (SymmetricIndex.{u} d) + 1 := by
      rw [x.2.property]
      simp
    _ = Nat.card (SymmetricIndex.{u} (d + 1)) := by
      simp only [Nat.card_ulift, Nat.card_fin]

/-- The label obtained by moving an exterior coordinate into the symmetric factor. -/
def differentialLabel {m i d : ℕ} (x : Label.{u} m (i + 1) d)
    (p : Fin m) (hp : p ∈ (x.1 : Finset (Fin m))) : Label.{u} m i (d + 1) :=
  (Set.powersetCard.ofCard (differentialLabel_card x p hp),
    ⟨x.2.val + Finsupp.single p 1, differentialLabel_mass x p⟩)

/-- The exterior subset of a differential label is obtained by erasing the coordinate. -/
theorem differentialLabel_exterior {m i d : ℕ} (x : Label.{u} m (i + 1) d)
    (p : Fin m) (hp : p ∈ (x.1 : Finset (Fin m))) :
    ((differentialLabel x p hp).1 : Finset (Fin m)) =
      (x.1 : Finset (Fin m)).erase p := rfl

/-- The exponent function of a differential label gains one coordinate occurrence. -/
theorem differentialLabel_exponent {m i d : ℕ} (x : Label.{u} m (i + 1) d)
    (p : Fin m) (hp : p ∈ (x.1 : Finset (Fin m))) :
    (differentialLabel x p hp).2.val = x.2.val + Finsupp.single p 1 := rfl

variable (S : Type u) [CommRing S]

/-- The exterior family is the exterior product in increasing index order. -/
private theorem exteriorFamily_eq_orderedProduct {M I : Type*}
    [AddCommGroup M] [Module S M] [LinearOrder I] (i : ℕ)
    (v : I → M) (s : Set.powersetCard I i) :
    exteriorPower.ιMulti_family S i v s =
      exteriorPower.ιMulti S i
        (fun j => v ((s : Finset I).orderEmbOfFin (Set.powersetCard.card_eq s) j)) := by
  rfl

/-- Tensor-basis vectors at a represented symmetric label are exterior-family
vectors tensored with symmetric products of coordinate vectors. -/
theorem termBasis_apply_multidegree (m i d : ℕ) (s : ExteriorLabel m i)
    (a : SymmetricIndex.{u} d → Fin m) :
    termBasis S m i d (s, SymmetricPower.multidegree a) =
      exteriorPower.ιMulti_family S i (Pi.basisFun S (Fin m)) s ⊗ₜ[S]
        SymmetricPower.tprod S (fun j => Pi.basisFun S (Fin m) (a j)) := by
  rw [termBasis, Module.Basis.tensorProduct_apply, exteriorPower.basis_apply,
    Module.Basis.symmetricPower_apply_multidegree]

/-- The tensor basis at a represented symmetric label uses the increasing
exterior-coordinate enumeration. -/
theorem termBasis_apply_ordered_multidegree (m i d : ℕ) (s : ExteriorLabel m i)
    (a : SymmetricIndex.{u} d → Fin m) :
    termBasis S m i d (s, SymmetricPower.multidegree a) =
      exteriorPower.ιMulti S i
          (fun j => Pi.basisFun S (Fin m)
            ((s : Finset (Fin m)).orderEmbOfFin (Set.powersetCard.card_eq s) j)) ⊗ₜ[S]
        SymmetricPower.tprod S (fun j => Pi.basisFun S (Fin m) (a j)) := by
  rw [termBasis_apply_multidegree, exteriorFamily_eq_orderedProduct]

/-- Inserting a coordinate into a symmetric basis vector prepends one occurrence
of that coordinate, with coefficient one. -/
theorem insert_symmetricBasis_multidegree (m d : ℕ) (p : Fin m)
    (a : SymmetricIndex.{u} d → Fin m) :
    Module.Koszul.insert S (Carrier S m) d
        (Pi.basisFun S (Fin m) p ⊗ₜ[S]
          (Pi.basisFun S (Fin m)).symmetricPower (SymmetricPower.multidegree a)) =
      (Pi.basisFun S (Fin m)).symmetricPower
        (SymmetricPower.multidegree
          (fun k : SymmetricIndex.{u} (d + 1) =>
            Fin.cases p (fun j : Fin d => a ⟨j⟩) k.down)) := by
  simp only [Module.Basis.symmetricPower_apply_multidegree, Module.Koszul.insert_tprod]
  congr 1
  funext k
  exact Fin.cases rfl (fun _ => rfl) k.down

/-- The differential of a coordinate exterior product and a symmetric basis
vector is the signed deletion sum with coefficient-one symmetric insertions. -/
theorem delta_coordinate_multidegree (m i d : ℕ)
    (v : Fin (i + 1) → Fin m) (a : SymmetricIndex.{u} d → Fin m) :
    Module.Koszul.delta S (Carrier S m) i d
        (exteriorPower.ιMulti S (i + 1) (fun j => Pi.basisFun S (Fin m) (v j)) ⊗ₜ[S]
          (Pi.basisFun S (Fin m)).symmetricPower (SymmetricPower.multidegree a)) =
      ∑ p : Fin (i + 1), (-1 : S) ^ (p : ℕ) •
        (exteriorPower.ιMulti S i
            (fun j => Pi.basisFun S (Fin m) (v (Fin.succAbove p j))) ⊗ₜ[S]
          (Pi.basisFun S (Fin m)).symmetricPower
            (SymmetricPower.multidegree
              (fun k : SymmetricIndex.{u} (d + 1) =>
                Fin.cases (v p) (fun j : Fin d => a ⟨j⟩) k.down))) := by
  rw [Module.Koszul.delta_ιMulti_tmul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [insert_symmetricBasis_multidegree]

/-- The position in the increasing enumeration counts strictly smaller members. -/
private theorem orderEmb_lower_card {α : Type*} [LinearOrder α] (n : ℕ)
    (s : Set.powersetCard α n) (a : Fin n) :
    ((s : Finset α).filter (fun q =>
      q < (s : Finset α).orderEmbOfFin (Set.powersetCard.card_eq s) a)).card = (a : ℕ) := by
  classical
  let e : Fin n ↪o α := (s : Finset α).orderEmbOfFin (Set.powersetCard.card_eq s)
  change ((s : Finset α).filter (fun q => q < e a)).card = (a : ℕ)
  have himage : Finset.univ.image e = (s : Finset α) :=
    Finset.image_orderEmbOfFin_univ _ _
  have hmem (b : Fin n) : e b ∈ (s : Finset α) :=
    Finset.orderEmbOfFin_mem _ _ b
  have hfilter : (s : Finset α).filter (fun q => q < e a) = (Finset.Iio a).image e := by
    ext q
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hq, hqa⟩
      have hqi : q ∈ Finset.univ.image e := by rwa [himage]
      rcases Finset.mem_image.mp hqi with ⟨b, _, rfl⟩
      exact ⟨b, Finset.mem_Iio.mpr (e.lt_iff_lt.mp hqa), rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨hmem b, e.lt_iff_lt.mpr (Finset.mem_Iio.mp hb)⟩
  rw [hfilter, Finset.card_image_of_injective _ e.injective, Fin.card_Iio]

/-- Removing a position from the increasing enumeration has the erased range. -/
private theorem range_orderEmbOfFin_succAbove {α : Type*} [LinearOrder α] (n : ℕ)
    (s : Set.powersetCard α (n + 1)) (a : Fin (n + 1)) :
    let e := (s : Finset α).orderEmbOfFin (Set.powersetCard.card_eq s)
    Set.range (RelEmbedding.trans (Fin.succAboveOrderEmb a) e) =
      ((s : Finset α).erase (e a) : Set α) := by
  classical
  let e : Fin (n + 1) ↪o α :=
    (s : Finset α).orderEmbOfFin (Set.powersetCard.card_eq s)
  change Set.range (RelEmbedding.trans (Fin.succAboveOrderEmb a) e) =
    ((s : Finset α).erase (e a) : Set α)
  have hrange : Set.range e = (s : Finset α) :=
    Finset.range_orderEmbOfFin _ _
  ext z
  change (∃ b, e (Fin.succAbove a b) = z) ↔ z ∈ (s : Finset α).erase (e a)
  constructor
  · rintro ⟨b, rfl⟩
    refine Finset.mem_erase.mpr ⟨?_, Finset.orderEmbOfFin_mem _ _ _⟩
    exact fun h => Fin.succAbove_ne a b (e.injective h)
  · intro hz
    rcases Finset.mem_erase.mp hz with ⟨hz_ne, hz_mem⟩
    have hz_range : z ∈ Set.range e := by rwa [hrange]
    rcases hz_range with ⟨b, rfl⟩
    have hba : b ≠ a := fun h => hz_ne (congrArg e h)
    obtain ⟨c, hc⟩ := Fin.exists_succAbove_eq hba
    exact ⟨c, congrArg e hc⟩

/-- The exterior enumeration of a differential label deletes its selected position. -/
theorem differentialLabel_orderEmb {m i d : ℕ} (x : Label.{u} m (i + 1) d)
    (a : Fin (i + 1)) :
    let e := (x.1 : Finset (Fin m)).orderEmbOfFin (Set.powersetCard.card_eq x.1)
    let y := differentialLabel x (e a) (Finset.orderEmbOfFin_mem _ _ a)
    (y.1 : Finset (Fin m)).orderEmbOfFin (Set.powersetCard.card_eq y.1) =
      RelEmbedding.trans (Fin.succAboveOrderEmb a) e := by
  dsimp only
  apply OrderEmbedding.eq_of_range_eq
  rw [Finset.range_orderEmbOfFin, range_orderEmbOfFin_succAbove,
    differentialLabel_exterior]

/-- Sums over increasing positions reindex as sums over attached members. -/
private theorem sum_orderEmbOfFin {α β : Type*} [LinearOrder α] [AddCommMonoid β]
    (n : ℕ) (s : Set.powersetCard α n)
    (f : {p : α // p ∈ (s : Finset α)} → β) :
    (∑ a : Fin n, f ⟨(s : Finset α).orderEmbOfFin (Set.powersetCard.card_eq s) a,
      Finset.orderEmbOfFin_mem _ _ a⟩) = (s : Finset α).attach.sum f := by
  classical
  let e : Fin n ↪o α := (s : Finset α).orderEmbOfFin (Set.powersetCard.card_eq s)
  have himage : Finset.univ.image e = (s : Finset α) :=
    Finset.image_orderEmbOfFin_univ _ _
  refine Finset.sum_bij
    (fun a _ => (⟨e a, Finset.orderEmbOfFin_mem _ _ a⟩ : {p : α // p ∈ (s : Finset α)}))
    ?_ ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_attach _ _
  · intro a ha b hb hab
    exact e.injective (congrArg Subtype.val hab)
  · intro p hp
    have hpi : p.val ∈ Finset.univ.image e := by rw [himage]; exact p.property
    rcases Finset.mem_image.mp hpi with ⟨a, ha, hap⟩
    exact ⟨a, ha, Subtype.ext hap⟩
  · intro a ha
    rfl

/-- At a represented symmetric label, the differential has the attached-member
formula with the prepended representative as its symmetric label. -/
theorem delta_termBasis_multidegree_attached (m i d : ℕ)
    (s : ExteriorLabel m (i + 1)) (a : SymmetricIndex.{u} d → Fin m) :
    let x : Label.{u} m (i + 1) d := (s, SymmetricPower.multidegree a)
    Module.Koszul.delta S (Carrier S m) i d (termBasis S m (i + 1) d x) =
      (s : Finset (Fin m)).attach.sum (fun p =>
        (-1 : S) ^ ((s : Finset (Fin m)).filter (fun q => q < p.val)).card •
          termBasis S m i (d + 1)
            ((differentialLabel x p.val p.property).1,
              SymmetricPower.multidegree
                (fun k : SymmetricIndex.{u} (d + 1) =>
                  Fin.cases p.val (fun j : Fin d => a ⟨j⟩) k.down))) := by
  dsimp only
  let x : Label.{u} m (i + 1) d := (s, SymmetricPower.multidegree a)
  let e : Fin (i + 1) ↪o Fin m :=
    (s : Finset (Fin m)).orderEmbOfFin (Set.powersetCard.card_eq s)
  let f : {p : Fin m // p ∈ (s : Finset (Fin m))} →
      Term S (Carrier S m) i (d + 1) := fun p =>
    (-1 : S) ^ ((s : Finset (Fin m)).filter (fun q => q < p.val)).card •
      termBasis S m i (d + 1)
        ((differentialLabel x p.val p.property).1,
          SymmetricPower.multidegree
            (fun k : SymmetricIndex.{u} (d + 1) =>
              Fin.cases p.val (fun j : Fin d => a ⟨j⟩) k.down))
  change Module.Koszul.delta S (Carrier S m) i d (termBasis S m (i + 1) d x) =
    (s : Finset (Fin m)).attach.sum f
  have hx : termBasis S m (i + 1) d x =
      exteriorPower.ιMulti S (i + 1) (fun j => Pi.basisFun S (Fin m) (e j)) ⊗ₜ[S]
        (Pi.basisFun S (Fin m)).symmetricPower (SymmetricPower.multidegree a) := by
    dsimp only [x]
    rw [termBasis, Module.Basis.tensorProduct_apply, exteriorPower.basis_apply,
      exteriorFamily_eq_orderedProduct]
  rw [hx, delta_coordinate_multidegree]
  calc
    _ = ∑ b : Fin (i + 1), f ⟨e b, Finset.orderEmbOfFin_mem _ _ b⟩ := by
      apply Finset.sum_congr rfl
      intro b hb
      dsimp only [f]
      rw [termBasis, Module.Basis.tensorProduct_apply, exteriorPower.basis_apply,
        exteriorFamily_eq_orderedProduct, differentialLabel_orderEmb,
        orderEmb_lower_card]
      rfl
    _ = _ := sum_orderEmbOfFin (i + 1) s f

/-- A multidegree counts its finite family by adding one singleton per slot. -/
private theorem multidegree_val_eq_sum_single {ι J : Type*} [Fintype ι] (a : ι → J) :
    (SymmetricPower.multidegree a).val = ∑ t : ι, Finsupp.single (a t) 1 := by
  classical
  rw [SymmetricPower.coe_multidegree]
  have h : (∑ t : ι, Finsupp.single (a t) 1).toMultiset =
      (Finset.univ : Finset ι).val.map a := by
    calc
      _ = ((∑ t : ι, Finsupp.single t 1).mapDomain a).toMultiset := by
        simp only [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
      _ = (∑ t : ι, Finsupp.single t 1).toMultiset.map a :=
        (Finsupp.toMultiset_map _ a).symm
      _ = _ := by
        simp only [Finsupp.toMultiset_sum_single, one_nsmul]
  simpa only [Finsupp.toMultiset_toFinsupp] using
    (congrArg Multiset.toFinsupp h).symm

/-- Prepending one coordinate adds one occurrence to its multidegree. -/
private theorem multidegree_prepend_val {J : Type*} {d : ℕ} (p : J)
    (a : SymmetricIndex.{u} d → J) :
    (SymmetricPower.multidegree
      (fun k : SymmetricIndex.{u} (d + 1) =>
        Fin.cases p (fun j : Fin d => a ⟨j⟩) k.down)).val =
      (SymmetricPower.multidegree a).val + Finsupp.single p 1 := by
  classical
  rw [multidegree_val_eq_sum_single, multidegree_val_eq_sum_single]
  calc
    _ = ∑ k : Fin (d + 1),
        (Finsupp.single (Fin.cases p (fun j : Fin d => a ⟨j⟩) k) 1 : J →₀ ℕ) := by
      exact Equiv.sum_comp
        (Equiv.ulift : SymmetricIndex.{u} (d + 1) ≃ Fin (d + 1))
        (fun k : Fin (d + 1) =>
          (Finsupp.single (Fin.cases p (fun j : Fin d => a ⟨j⟩) k) 1 : J →₀ ℕ))
    _ = Finsupp.single p 1 + ∑ j : Fin d, Finsupp.single (a ⟨j⟩) 1 := by
      rw [Fin.sum_univ_succ]
      rfl
    _ = Finsupp.single p 1 + ∑ k : SymmetricIndex.{u} d, Finsupp.single (a k) 1 := by
      congr 1
      exact (Equiv.sum_comp (Equiv.ulift : SymmetricIndex.{u} d ≃ Fin d)
        (fun j : Fin d => (Finsupp.single (a ⟨j⟩) 1 : J →₀ ℕ))).symm
    _ = _ := add_comm _ _

/-- The prepended-representative label is the differential label. -/
theorem differentialLabel_multidegree {m i d : ℕ} (s : ExteriorLabel m (i + 1))
    (a : SymmetricIndex.{u} d → Fin m) (p : Fin m)
    (hp : p ∈ (s : Finset (Fin m))) :
    let x : Label.{u} m (i + 1) d := (s, SymmetricPower.multidegree a)
    ((differentialLabel x p hp).1,
      SymmetricPower.multidegree
        (fun k : SymmetricIndex.{u} (d + 1) =>
          Fin.cases p (fun j : Fin d => a ⟨j⟩) k.down)) =
        differentialLabel x p hp := by
  dsimp only
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    rw [differentialLabel_exponent]
    exact multidegree_prepend_val p a

/-- The Koszul differential deletes each exterior coordinate with its position sign.
For the Koszul construction, see Weibel, *The K-book* (2013). -/
theorem delta_termBasis (m i d : ℕ) (x : Label.{u} m (i + 1) d) :
    Module.Koszul.delta S (Carrier S m) i d
        (termBasis S m (i + 1) d x) =
      (x.1 : Finset (Fin m)).attach.sum (fun p =>
        (-1 : S) ^ ((x.1 : Finset (Fin m)).filter (fun q => q < p.val)).card •
          termBasis S m i (d + 1) (differentialLabel x p.val p.property)) := by
  rcases x with ⟨s, t⟩
  obtain ⟨a, rfl⟩ :=
    (SymmetricPower.multidegree_surjective
      (ι := SymmetricIndex.{u} d) (J := Fin m)) t
  simpa only [differentialLabel_multidegree] using
    delta_termBasis_multidegree_attached S m i d s a

end Module.Koszul.CanonicalFreeContraction
