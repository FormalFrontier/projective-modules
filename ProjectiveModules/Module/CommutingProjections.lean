/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Projection
public import ProjectiveModules.Module.ComponentwiseFree

/-!
# Finite commuting projections

For a family `p : I → Module.End R M`, `LinearMap.jointBlock p ε` is the
intersection of the original ranges at the true bits of `ε : I → Bool` and
the original kernels at its false bits. For a finite commuting idempotent
family, the commuting product of the corresponding `p i` and `1 - p i`
projects onto this block. All bit choices are retained, including zero blocks.

`LinearMap.commutingIdempotentsPiEquiv` decomposes the original module into
the product of these blocks. Its components are the product projectors and
its inverse sums the block inclusions. The supplied maps act on each
component by the corresponding Boolean bit.

The intermediate `CompleteOrthogonalIdempotents.piRangeEquiv` packages a
complete orthogonal family of endomorphisms using the canonical internal
direct sum and its finite-product equivalence.

## Implementation notes

Scalars need only form a semiring. Subtraction takes place in the endomorphism
ring of the additive-group ambient module. The block subtypes use only their
additive commutative monoid and module structures, not group instances for
arbitrary semiring submodules. The block definition itself needs neither
finiteness nor idempotence nor commutation. Finite public constructions choose
enumerations internally; sum formulas use `finsum` when no enumeration is an
input. For an empty constraint index there is one bit choice, with block `⊤`
and projector `1`.

## References

The projection and fixed-point API follows Yury Kudryashov's formalization in
`Mathlib.LinearAlgebra.Projection`. Internal direct-sum packaging uses the
formalization by Eric Wieser and Jujian Zhang in
`Mathlib.Algebra.DirectSum.Decomposition`, and the finite-product conversion
in `Mathlib.Algebra.DirectSum.Module`. Commuting products use Yakov Pechersky's
`Mathlib.Data.Finset.NoncommProd`.

The finite orthogonal partition refines complementary idempotent pairs using
`CompleteOrthogonalIdempotents.prod_mul` from
`ProjectiveModules.Module.ComponentwiseFree`. The complementary pairs use
Andrew Yang's `Mathlib.RingTheory.Idempotents`.
-/

@[expose] public section

universe uR uM uI

namespace LinearMap

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {I : Type uI}

/-- The joint block selected by `ε`: true chooses the original range and false
chooses the original kernel at each index. -/
def jointBlock (p : I → Module.End R M) (ε : I → Bool) : Submodule R M :=
  ⨅ i, if ε i then (p i).range else (p i).ker

/-- For idempotents, membership in a joint block is the prescribed fixed-point
or zero equation for each member of the supplied family. -/
theorem mem_jointBlock_iff (p : I → Module.End R M)
    (hp : ∀ i, IsIdempotentElem (p i)) (ε : I → Bool) (x : M) :
    x ∈ jointBlock p ε ↔ ∀ i, p i x = if ε i then x else 0 := by
  simp only [jointBlock, Submodule.mem_iInf]
  refine forall_congr' fun i ↦ ?_
  cases ε i <;> simp [LinearMap.IsIdempotentElem.mem_range_iff (hp i)]

/-- With no constraints the joint block is the whole module. -/
@[simp]
theorem jointBlock_of_isEmpty [IsEmpty I] (p : I → Module.End R M) (ε : I → Bool) :
    jointBlock p ε = ⊤ := by
  simp [jointBlock]

end LinearMap

namespace CompleteOrthogonalIdempotents

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {I : Type uI} [Fintype I]
variable {e : I → Module.End R M}

open scoped Classical in
private theorem apply_coeLinearMap_ranges (he : CompleteOrthogonalIdempotents e)
    (b : DirectSum I (fun j ↦ (e j).range)) (i : I) :
    e i (DirectSum.coeLinearMap (fun j ↦ (e j).range) b) = (b i : M) := by
  classical
  induction b using DirectSum.induction_on with
  | zero => simp
  | of j b =>
    rw [DirectSum.coeLinearMap_of]
    by_cases hij : i = j
    · subst j
      rw [DirectSum.of_eq_same]
      exact (LinearMap.IsIdempotentElem.mem_range_iff (he.idem i)).mp b.property
    · rw [DirectSum.of_eq_of_ne _ _ _ hij]
      change e i (b : M) = 0
      obtain ⟨x, hx⟩ := b.property
      rw [← hx, ← Module.End.mul_apply, he.ortho hij, LinearMap.zero_apply]
  | add b c hb hc =>
    simpa only [map_add, DirectSum.add_apply, Submodule.coe_add] using
      congrArg₂ (· + ·) hb hc

open scoped Classical in
/-- The ranges of a complete orthogonal family of endomorphisms form an
internal direct sum, over a semiring and an additive commutative monoid. -/
theorem isInternal_ranges (he : CompleteOrthogonalIdempotents e) :
    DirectSum.IsInternal (fun i ↦ (e i).range) := by
  classical
  change Function.Bijective (DirectSum.coeLinearMap (fun i ↦ (e i).range))
  constructor
  · intro b c h
    apply DirectSum.ext
    intro i
    apply Subtype.ext
    calc
      (b i : M) = e i (DirectSum.coeLinearMap (fun j ↦ (e j).range) b) :=
        (apply_coeLinearMap_ranges he b i).symm
      _ = e i (DirectSum.coeLinearMap (fun j ↦ (e j).range) c) := congrArg (e i) h
      _ = (c i : M) := apply_coeLinearMap_ranges he c i
  · intro x
    refine ⟨∑ i, DirectSum.lof R I (fun j ↦ (e j).range) i
      ⟨e i x, LinearMap.mem_range_self (e i) x⟩, ?_⟩
    simp only [map_sum, DirectSum.coeLinearMap_lof]
    simpa only [LinearMap.sum_apply, Module.End.one_apply] using
      LinearMap.congr_fun he.complete x

/-- The decomposition into ranges of a finite complete orthogonal family,
obtained from the canonical internal direct sum and its finite-product map. -/
noncomputable def piRangeEquiv (he : CompleteOrthogonalIdempotents e) :
    M ≃ₗ[R] ((i : I) → (e i).range) := by
  classical
  letI : DirectSum.Decomposition (fun i ↦ (e i).range) :=
    he.isInternal_ranges.chooseDecomposition
  exact (DirectSum.decomposeLinearEquiv (fun i ↦ (e i).range)).trans
    (DirectSum.linearEquivFunOnFintype R I (fun i ↦ (e i).range))

/-- Each coordinate of the range decomposition has underlying value `e i x`. -/
@[simp]
theorem coe_piRangeEquiv_apply (he : CompleteOrthogonalIdempotents e) (x : M) (i : I) :
    (he.piRangeEquiv x i : M) = e i x := by
  classical
  let : DirectSum.Decomposition (fun i ↦ (e i).range) :=
    he.isInternal_ranges.chooseDecomposition
  change (DirectSum.decomposeLinearEquiv (fun j ↦ (e j).range) x i : M) = e i x
  have hrec : DirectSum.coeLinearMap (fun j ↦ (e j).range)
      (DirectSum.decomposeLinearEquiv (fun j ↦ (e j).range) x) = x :=
    (DirectSum.decomposeLinearEquiv (fun j ↦ (e j).range)).symm_apply_apply x
  calc
    (DirectSum.decomposeLinearEquiv (fun j ↦ (e j).range) x i : M) =
        e i (DirectSum.coeLinearMap (fun j ↦ (e j).range)
          (DirectSum.decomposeLinearEquiv (fun j ↦ (e j).range) x)) :=
      (apply_coeLinearMap_ranges he _ i).symm
    _ = e i x := congrArg (e i) hrec

/-- The inverse range decomposition is the sum of the range inclusions. -/
theorem piRangeEquiv_symm_apply (he : CompleteOrthogonalIdempotents e)
    (b : (i : I) → (e i).range) :
    he.piRangeEquiv.symm b = ∑ i, (b i : M) := by
  classical
  let : DirectSum.Decomposition (fun i ↦ (e i).range) :=
    he.isInternal_ranges.chooseDecomposition
  let b' : DirectSum I (fun i ↦ (e i).range) :=
    (DirectSum.linearEquivFunOnFintype R I (fun i ↦ (e i).range)).symm b
  change (DirectSum.decomposeLinearEquiv (fun i ↦ (e i).range)).symm b' =
    ∑ i, (b i : M)
  have hsum : (∑ i, DirectSum.lof R I (fun j ↦ (e j).range) i (b' i)) = b' :=
    DirectSum.sum_univ_of b'
  rw [← hsum, map_sum]
  simp only [DirectSum.decomposeLinearEquiv_symm_lof]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun c : (e i).range ↦ (c : M))
    (congrFun ((DirectSum.linearEquivFunOnFintype R I
      (fun j ↦ (e j).range)).apply_symm_apply b) i)

end CompleteOrthogonalIdempotents

namespace LinearMap

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {I : Type uI}

private theorem jointFactors_pairwise (p : I → Module.End R M)
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j))) (ε : I → Bool) :
    Pairwise (fun i j ↦
      Commute (if ε i then p i else 1 - p i) (if ε j then p j else 1 - p j)) := by
  intro i j hij
  have h := hcomm hij
  cases ε i <;> cases ε j <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact (Commute.one_right _).sub_right ((Commute.one_left _).sub_left h)
  · exact (Commute.one_left _).sub_left h
  · exact (Commute.one_right _).sub_right h
  · exact h

/-- The joint projector is the commuting product of the supplied maps at true
bits and their endomorphism-ring complements at false bits. -/
noncomputable def jointProjector [Finite I] (p : I → Module.End R M)
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j))) (ε : I → Bool) :
    Module.End R M := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  exact Finset.univ.noncommProd (fun i ↦ if ε i then p i else 1 - p i) (by
    intro i hi j hj hij
    exact jointFactors_pairwise p hcomm ε hij)

/-- The joint projector agrees with the commuting product for any finite
enumeration and any proof that its selected factors commute. -/
theorem jointProjector_eq_noncommProd [Fintype I] (p : I → Module.End R M)
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j))) (ε : I → Bool)
    (hε : (↑(Finset.univ : Finset I) : Set I).Pairwise (fun i j ↦
      Commute (if ε i then p i else 1 - p i) (if ε j then p j else 1 - p j))) :
    jointProjector p hcomm ε =
      Finset.univ.noncommProd (fun i ↦ if ε i then p i else 1 - p i) hε := by
  classical
  unfold jointProjector
  exact Finset.noncommProd_congr
    (Finset.ext fun i ↦ by simp only [Finset.mem_univ])
    (fun _ _ ↦ rfl)
    (fun _ _ _ _ hij ↦ jointFactors_pairwise p hcomm ε hij)

/-- An empty commuting product is the identity endomorphism. -/
@[simp]
theorem jointProjector_of_isEmpty [IsEmpty I] (p : I → Module.End R M)
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j))) (ε : I → Bool) :
    jointProjector p hcomm ε = 1 := by
  classical
  simp only [jointProjector, Finset.univ_eq_empty]
  exact @Finset.noncommProd_empty I (Module.End R M) _
    (fun i ↦ if ε i then p i else 1 - p i)
    (fun _ _ _ _ hij ↦ jointFactors_pairwise p hcomm ε hij)

variable [Finite I]

private theorem jointFactor_absorbs_jointProjector (p : I → Module.End R M)
    (hp : ∀ i, IsIdempotentElem (p i))
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j))) (ε : I → Bool) (i : I) :
    (if ε i then p i else 1 - p i) * jointProjector p hcomm ε =
        jointProjector p hcomm ε ∧
      jointProjector p hcomm ε * (if ε i then p i else 1 - p i) =
        jointProjector p hcomm ε := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let f : I → Module.End R M := fun j ↦ if ε j then p j else 1 - p j
  have hf : (↑(Finset.univ : Finset I) : Set I).Pairwise
      (fun j k ↦ Commute (f j) (f k)) := by
    intro j hj k hk hjk
    exact jointFactors_pairwise p hcomm ε hjk
  have hfi : f i * f i = f i := by
    change IsIdempotentElem (if ε i then p i else 1 - p i)
    split
    · exact hp i
    · exact (hp i).one_sub
  let t := (Finset.univ.erase i).noncommProd f
    (hf.mono fun _ hj ↦ Finset.mem_of_mem_erase hj)
  have hleft : f i * t = Finset.univ.noncommProd f hf :=
    Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i) f hf
  have hright : t * f i = Finset.univ.noncommProd f hf :=
    Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ i) f hf
  rw [jointProjector_eq_noncommProd p hcomm ε hf]
  constructor
  · calc
      f i * Finset.univ.noncommProd f hf = f i * (f i * t) :=
        congrArg (fun q ↦ f i * q) hleft.symm
      _ = (f i * f i) * t := (mul_assoc _ _ _).symm
      _ = f i * t := congrArg (fun q ↦ q * t) hfi
      _ = Finset.univ.noncommProd f hf := hleft
  · calc
      Finset.univ.noncommProd f hf * f i = (t * f i) * f i :=
        congrArg (fun q ↦ q * f i) hright.symm
      _ = t * (f i * f i) := mul_assoc _ _ _
      _ = t * f i := congrArg (fun q ↦ t * q) hfi
      _ = Finset.univ.noncommProd f hf := hright

private theorem jointProjector_apply_of_mem_jointBlock (p : I → Module.End R M)
    (hp : ∀ i, IsIdempotentElem (p i))
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j))) (ε : I → Bool)
    {x : M} (hx : x ∈ jointBlock p ε) : jointProjector p hcomm ε x = x := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hx' := (mem_jointBlock_iff p hp ε x).mp hx
  have hf : (↑(Finset.univ : Finset I) : Set I).Pairwise (fun i j ↦
      Commute (if ε i then p i else 1 - p i) (if ε j then p j else 1 - p j)) := by
    intro i hi j hj hij
    exact jointFactors_pairwise p hcomm ε hij
  rw [jointProjector_eq_noncommProd p hcomm ε hf]
  refine Finset.noncommProd_induction _ _ _
    (fun q : Module.End R M ↦ q x = x) ?_ ?_ ?_
  · intro a b ha hb
    change a (b x) = x
    rw [hb, ha]
  · rfl
  · intro i hi
    cases hε : ε i
    · have hzero : p i x = 0 := by simpa [hε] using hx' i
      simp [sub_apply, hzero]
    · simpa [hε] using hx' i

/-- The range of a joint projector is the intersection of the original ranges
and kernels selected by its bits. -/
theorem range_jointProjector (p : I → Module.End R M)
    (hp : ∀ i, IsIdempotentElem (p i))
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j))) (ε : I → Bool) :
    (jointProjector p hcomm ε).range = jointBlock p ε := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply (mem_jointBlock_iff p hp ε _).mpr
    intro i
    have hfix := congrArg (fun q : Module.End R M ↦ q y)
      (jointFactor_absorbs_jointProjector p hp hcomm ε i).1
    cases hε : ε i
    · have hs : jointProjector p hcomm ε y - p i (jointProjector p hcomm ε y) =
          jointProjector p hcomm ε y := by
        simpa [hε, Module.End.mul_apply, sub_apply] using hfix
      simpa [hε] using sub_eq_self.mp hs
    · simpa [hε, Module.End.mul_apply] using hfix
  · intro hx
    exact ⟨x, jointProjector_apply_of_mem_jointBlock p hp hcomm ε hx⟩

-- Reindexing the factors changes neither their multiset nor their product.
-- The stock product API supplies congruence but not this embedding form.
private theorem noncommProd_map_embedding {J K A : Type*} [Monoid A]
    (s : Finset J) (e : J ↪ K) (f : K → A)
    (h : (↑(s.map e) : Set K).Pairwise (fun i j ↦ Commute (f i) (f j)))
    (h' : (↑s : Set J).Pairwise (fun i j ↦ Commute (f (e i)) (f (e j)))) :
    (s.map e).noncommProd f h = s.noncommProd (fun i ↦ f (e i)) h' := by
  simp only [Finset.noncommProd, Finset.map_val, Multiset.map_map, Function.comp_def]

/-- The projectors for all Boolean choices form a complete orthogonal family.
The enumeration in this statement is the canonical one chosen from finiteness. -/
theorem jointProjectors_completeOrthogonalIdempotents (p : I → Module.End R M)
    (hp : ∀ i, IsIdempotentElem (p i))
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j))) :
    @CompleteOrthogonalIdempotents (Module.End R M) _ (I → Bool)
      (Fintype.ofFinite (I → Bool)) (jointProjector p hcomm) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  refine Fintype.induction_empty_option
    (P := fun J _ ↦ ∀ (q : J → Module.End R M)
      (_hq : ∀ j, IsIdempotentElem (q j))
      (hc : Pairwise (fun i j ↦ Commute (q i) (q j))),
      @CompleteOrthogonalIdempotents (Module.End R M) _ (J → Bool)
        (Fintype.ofFinite (J → Bool)) (jointProjector q hc))
    ?_ ?_ ?_ I p hp hcomm
  · intro J K _ e ih q hq hc
    let : Fintype J := Fintype.ofEquiv K e.symm
    let : Fintype (J → Bool) := Fintype.ofFinite (J → Bool)
    let : Fintype (K → Bool) := Fintype.ofFinite (K → Bool)
    let hc' : Pairwise (fun i j : J ↦ Commute (q (e i)) (q (e j))) :=
      fun _ _ hij ↦ hc (e.injective.ne hij)
    apply (CompleteOrthogonalIdempotents.equiv
      (Equiv.arrowCongr e (Equiv.refl Bool))).1
    have hproj : (jointProjector q hc) ∘ (Equiv.arrowCongr e (Equiv.refl Bool)) =
        jointProjector (fun j ↦ q (e j)) hc' := by
      funext ε
      change jointProjector q hc (fun k ↦ ε (e.symm k)) =
        jointProjector (fun j ↦ q (e j)) hc' ε
      rw [jointProjector_eq_noncommProd q hc _
          (fun _ _ _ _ hij ↦ jointFactors_pairwise q hc _ hij),
        jointProjector_eq_noncommProd (fun j ↦ q (e j)) hc' ε
          (fun _ _ _ _ hij ↦ jointFactors_pairwise _ hc' ε hij)]
      simpa only [Finset.map_univ_equiv, Equiv.coe_toEmbedding,
        Equiv.symm_apply_apply] using
        (noncommProd_map_embedding (Finset.univ : Finset J) e.toEmbedding
          (fun k ↦ if ε (e.symm k) then q k else 1 - q k)
          (fun _ _ _ _ hij ↦
            jointFactors_pairwise q hc (fun k ↦ ε (e.symm k)) hij)
          (fun _ _ _ _ hij ↦
            jointFactors_pairwise q hc (fun k ↦ ε (e.symm k)) (e.injective.ne hij)))
    rw [hproj]
    exact ih (fun j ↦ q (e j)) (fun j ↦ hq (e j)) hc'
  · intro q hq hc
    -- There is exactly one empty Boolean choice, and its projector is 1.
    have hempty : CompleteOrthogonalIdempotents (jointProjector q hc) :=
      CompleteOrthogonalIdempotents.unique_iff.mpr
        (jointProjector_of_isEmpty q hc _)
    -- Transport the proposition from the stock Pi enumeration to the
    -- canonical enumeration required by the induction predicate.
    exact (congrArg
      (fun t : Fintype (PEmpty.{uI + 1} → Bool) ↦
        @CompleteOrthogonalIdempotents (Module.End R M) _ (PEmpty.{uI + 1} → Bool)
          t (jointProjector q hc))
      (Subsingleton.elim (inferInstance : Fintype (PEmpty.{uI + 1} → Bool))
        (Fintype.ofFinite (PEmpty.{uI + 1} → Bool)))).mp hempty
  · intro J _ ih q hq hc
    let : Fintype (J → Bool) := Fintype.ofFinite (J → Bool)
    let : Fintype (Option J → Bool) := Fintype.ofFinite (Option J → Bool)
    let hc' : Pairwise (fun i j : J ↦ Commute (q (some i)) (q (some j))) :=
      fun _ _ hij ↦ hc ((Option.some_injective J).ne hij)
    have htail := ih (fun j ↦ q (some j)) (fun j ↦ hq (some j)) hc'
    have hpair : CompleteOrthogonalIdempotents
        (fun b : Bool ↦ if b then q none else 1 - q none) := by
      apply (CompleteOrthogonalIdempotents.equiv finTwoEquiv).1
      have heq : (fun b : Bool ↦ if b then q none else 1 - q none) ∘ finTwoEquiv =
          ![1 - q none, 1 - (1 - q none)] := by
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp [finTwoEquiv]
        · have hj : j = 0 := Subsingleton.elim _ _
          subst j
          simp [finTwoEquiv]
      rw [heq]
      exact CompleteOrthogonalIdempotents.of_isIdempotentElem (hq none).one_sub
    have hcross : ∀ (b : Bool) (ε : J → Bool),
        Commute (if b then q none else 1 - q none)
          (jointProjector (fun j ↦ q (some j)) hc' ε) := by
      intro b ε
      rw [jointProjector_eq_noncommProd _ hc' ε
        (fun _ _ _ _ hij ↦ jointFactors_pairwise _ hc' ε hij)]
      apply Finset.noncommProd_commute
      intro j _
      have hne : (none : Option J) ≠ some j := by simp
      exact jointFactors_pairwise q hc (fun o ↦ o.elim b ε) hne
    -- This is the Cartesian refinement step; all pairs, including zero
    -- products, survive the equivalence with Boolean functions on Option J.
    have hrefine := (CompleteOrthogonalIdempotents.equiv
      (Equiv.piOptionEquivProd : (Option J → Bool) ≃ Bool × (J → Bool))).2
      (hpair.prod_mul htail hcross)
    have hproj : jointProjector q hc =
        (fun bε : Bool × (J → Bool) ↦
          (if bε.1 then q none else 1 - q none) *
            jointProjector (fun j ↦ q (some j)) hc' bε.2) ∘
          Equiv.piOptionEquivProd := by
      funext ε
      change jointProjector q hc ε = (if ε none then q none else 1 - q none) *
        jointProjector (fun j ↦ q (some j)) hc' (fun j ↦ ε (some j))
      rw [jointProjector_eq_noncommProd q hc ε
          (fun _ _ _ _ hij ↦ jointFactors_pairwise q hc ε hij),
        jointProjector_eq_noncommProd _ hc' (fun j ↦ ε (some j))
          (fun _ _ _ _ hij ↦ jointFactors_pairwise _ hc' (fun j ↦ ε (some j)) hij)]
      simp only [univ_option, Finset.insertNone, OrderEmbedding.coe_ofMapLEIff]
      refine (@Finset.noncommProd_cons (Option J) (Module.End R M) _
        ((Finset.univ : Finset J).map Function.Embedding.some) none
        (fun i ↦ if ε i then q i else 1 - q i) (by simp)
        (fun _ _ _ _ hij ↦ jointFactors_pairwise q hc ε hij)).trans ?_
      congr 1
      apply noncommProd_map_embedding
    rw [hproj]
    exact hrefine

open scoped Classical in
/-- A joint projector fixes its own block and kills every differently indexed
joint block. -/
theorem jointProjector_apply_jointBlock (p : I → Module.End R M)
    (hp : ∀ i, IsIdempotentElem (p i))
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j)))
    (ε η : I → Bool) (b : jointBlock p η) :
    jointProjector p hcomm ε (b : M) = if ε = η then (b : M) else 0 := by
  by_cases h : ε = η
  · subst η
    simpa using jointProjector_apply_of_mem_jointBlock p hp hcomm ε b.property
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    have hbi := (mem_jointBlock_iff p hp η (b : M)).mp b.property i
    have hkill : (if ε i then p i else 1 - p i) (b : M) = 0 := by
      cases hε : ε i <;> cases hη : η i <;> simp_all [sub_apply]
    calc
      jointProjector p hcomm ε (b : M) =
          (jointProjector p hcomm ε * (if ε i then p i else 1 - p i)) (b : M) :=
        congrArg (fun q : Module.End R M ↦ q (b : M))
          (jointFactor_absorbs_jointProjector p hp hcomm ε i).2.symm
      _ = 0 := by rw [Module.End.mul_apply, hkill, map_zero]

/-- The component map to a joint block, corestricting its product projector. -/
noncomputable def jointComponent (p : I → Module.End R M)
    (hp : ∀ i, IsIdempotentElem (p i))
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j))) (ε : I → Bool) :
    M →ₗ[R] jointBlock p ε :=
  (jointProjector p hcomm ε).codRestrict (jointBlock p ε) fun x ↦ by
    rw [← range_jointProjector p hp hcomm ε]
    exact mem_range_self (jointProjector p hcomm ε) x

/-- The underlying value of a component is the joint product projector. -/
@[simp]
theorem jointComponent_apply (p : I → Module.End R M)
    (hp : ∀ i, IsIdempotentElem (p i))
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j))) (ε : I → Bool) (x : M) :
    (jointComponent p hp hcomm ε x : M) = jointProjector p hcomm ε x := rfl

/-- Simultaneous decomposition of the original module by a finite commuting
idempotent family into its range/kernel intersection blocks. The construction
uses the complete orthogonal range decomposition and transports each range
along `range_jointProjector`. No zero block is discarded. -/
noncomputable def commutingIdempotentsPiEquiv (p : I → Module.End R M)
    (hp : ∀ i, IsIdempotentElem (p i))
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j))) :
    M ≃ₗ[R] ((ε : I → Bool) → jointBlock p ε) := by
  classical
  letI : Fintype (I → Bool) := Fintype.ofFinite (I → Bool)
  exact ((jointProjectors_completeOrthogonalIdempotents p hp hcomm).piRangeEquiv).trans
    (LinearEquiv.piCongrRight fun ε ↦
      LinearEquiv.ofEq (jointProjector p hcomm ε).range (jointBlock p ε)
        (range_jointProjector p hp hcomm ε))

/-- The coordinates of simultaneous decomposition are the corestricted joint
product projectors. -/
@[simp]
theorem commutingIdempotentsPiEquiv_apply (p : I → Module.End R M)
    (hp : ∀ i, IsIdempotentElem (p i))
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j))) (x : M) (ε : I → Bool) :
    commutingIdempotentsPiEquiv p hp hcomm x ε = jointComponent p hp hcomm ε x := by
  classical
  let : Fintype (I → Bool) := Fintype.ofFinite (I → Bool)
  apply Subtype.ext
  simp only [commutingIdempotentsPiEquiv, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply, LinearEquiv.coe_ofEq_apply,
    CompleteOrthogonalIdempotents.coe_piRangeEquiv_apply, jointComponent_apply]

/-- The inverse simultaneous decomposition sums the original block inclusions.
The sum is finite because `I → Bool` is finite, including when `I` is empty. -/
theorem commutingIdempotentsPiEquiv_symm_apply (p : I → Module.End R M)
    (hp : ∀ i, IsIdempotentElem (p i))
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j)))
    (b : (ε : I → Bool) → jointBlock p ε) :
    (commutingIdempotentsPiEquiv p hp hcomm).symm b = ∑ᶠ ε, (b ε : M) := by
  classical
  let : Fintype (I → Bool) := Fintype.ofFinite (I → Bool)
  simp only [commutingIdempotentsPiEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.piCongrRight_symm, LinearEquiv.piCongrRight_apply,
    LinearEquiv.ofEq_symm, CompleteOrthogonalIdempotents.piRangeEquiv_symm_apply,
    LinearEquiv.coe_ofEq_apply, finsum_eq_sum_of_fintype]

/-- Each supplied idempotent acts on a joint component by its selected bit. -/
theorem commutingIdempotentsPiEquiv_apply_projection (p : I → Module.End R M)
    (hp : ∀ i, IsIdempotentElem (p i))
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j)))
    (i : I) (x : M) (ε : I → Bool) :
    commutingIdempotentsPiEquiv p hp hcomm (p i x) ε =
      if ε i then commutingIdempotentsPiEquiv p hp hcomm x ε else 0 := by
  classical
  simp only [commutingIdempotentsPiEquiv_apply]
  have habs := (jointFactor_absorbs_jointProjector p hp hcomm ε i).2
  cases hε : ε i
  · have hsub : jointProjector p hcomm ε - jointProjector p hcomm ε * p i =
        jointProjector p hcomm ε := by
      simpa [hε, mul_sub] using habs
    have hzero : jointProjector p hcomm ε * p i = 0 := sub_eq_self.mp hsub
    apply Subtype.ext
    simpa [hε, jointComponent_apply] using
      congrArg (fun q : Module.End R M ↦ q x) hzero
  · have hmul : jointProjector p hcomm ε * p i = jointProjector p hcomm ε := by
      simpa [hε] using habs
    apply Subtype.ext
    simpa [hε, jointComponent_apply] using
      congrArg (fun q : Module.End R M ↦ q x) hmul

end LinearMap
