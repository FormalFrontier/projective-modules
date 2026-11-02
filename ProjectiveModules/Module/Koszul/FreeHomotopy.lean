/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Koszul.FreeContraction

/-!
# Contraction identities for finite free Koszul terms

For the coordinate module `Fin m → S`, the contraction moves one occurrence
of the least total-support coordinate from the symmetric factor to the exterior
factor, with its insertion sign, and is zero when that coordinate is already
exterior. The identities below cover precisely the positive total degrees.
Degree `(0, 0)` is excluded.

## References

- C. Weibel, *The K-book: An Introduction to Algebraic K-theory* (2013),
  for the Koszul construction.
-/

public section

universe u

namespace Module.Koszul.CanonicalFreeContraction

variable (S : Type u) [CommRing S]

private theorem exterior_sign_exponent_zero {m i d : ℕ}
    (x : Label.{u} m i d) (p : Fin m)
    (hmin : ∀ q ∈ totalSupport x, p ≤ q) :
    ((x.1 : Finset (Fin m)).filter (fun q => q < p)).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨hqI, hqp⟩ := Finset.mem_filter.mp hq
  have hqs : q ∈ totalSupport x :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ q, Or.inl hqI⟩
  exact (not_lt_of_ge (hmin q hqs)) hqp

private theorem lowerCount_eq_zero {m i d : ℕ}
    (x : Label.{u} m i (d + 1)) : lowerCount x = 0 := by
  exact exterior_sign_exponent_zero x (pivot x) (pivot_spec x).2

private theorem totalSupport_differentialLabel {m i d : ℕ}
    (x : Label.{u} m (i + 1) d) (p : Fin m)
    (hp : p ∈ (x.1 : Finset (Fin m))) :
    totalSupport (differentialLabel x p hp) = totalSupport x := by
  classical
  ext q
  simp only [totalSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    differentialLabel_exterior, differentialLabel_exponent]
  by_cases hq : q = p
  · subst q
    simp [hp]
  · simp [hq, Ne.symm hq, Finsupp.single_apply]

private theorem totalSupport_contractedLabel {m i d : ℕ}
    (x : Label.{u} m i (d + 1))
    (hp : pivot x ∉ (x.1 : Finset (Fin m))) :
    totalSupport (contractedLabel x hp) = totalSupport x := by
  classical
  ext q
  simp only [totalSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [contractedLabel_exterior, contractedLabel_exponent]
  by_cases hq : q = pivot x
  · subst q
    have hs : pivot x ∈ (x.1 : Finset (Fin m)) ∨
        x.2.val (pivot x) ≠ 0 :=
      (Finset.mem_filter.mp (pivot_spec x).1).2
    simp [hs]
  · simp [hq]

private theorem pivot_differentialLabel_of_min {m i d : ℕ}
    (x : Label.{u} m (i + 1) d) (p : Fin m)
    (hp : p ∈ (x.1 : Finset (Fin m)))
    (hmin : ∀ q ∈ totalSupport x, p ≤ q)
    (q : Fin m) (hq : q ∈ (x.1 : Finset (Fin m))) :
    pivot (differentialLabel x q hq) = p := by
  apply le_antisymm
  · apply (pivot_spec (differentialLabel x q hq)).2 p
    rw [totalSupport_differentialLabel]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, Or.inl hp⟩
  · apply hmin
    rw [← totalSupport_differentialLabel x q hq]
    exact (pivot_spec (differentialLabel x q hq)).1

private theorem contracted_differentialLabel {m i d : ℕ}
    (x : Label.{u} m (i + 1) d) (p : Fin m)
    (hp : p ∈ (x.1 : Finset (Fin m)))
    (hpi : pivot (differentialLabel x p hp) = p)
    (hn : pivot (differentialLabel x p hp) ∉
      ((differentialLabel x p hp).1 : Finset (Fin m))) :
    contractedLabel (differentialLabel x p hp) hn = x := by
  classical
  apply Prod.ext
  · apply Subtype.ext
    rw [contractedLabel_exterior, differentialLabel_exterior, hpi]
    simp [hp]
  · apply Subtype.ext
    rw [contractedLabel_exponent, differentialLabel_exponent, hpi]
    simp

private theorem differential_contractedLabel_pivot {m i d : ℕ}
    (x : Label.{u} m i (d + 1))
    (hp : pivot x ∉ (x.1 : Finset (Fin m)))
    (hmem : pivot x ∈ ((contractedLabel x hp).1 : Finset (Fin m))) :
    differentialLabel (contractedLabel x hp) (pivot x) hmem = x := by
  classical
  apply Prod.ext
  · apply Subtype.ext
    rw [differentialLabel_exterior, contractedLabel_exterior]
    simp [hp]
  · apply Subtype.ext
    rw [differentialLabel_exponent, contractedLabel_exponent]
    exact Finsupp.sub_add_single_one_cancel
      (Nat.ne_of_gt (pivot_exponent_pos x hp))

private theorem kappa_delta_basis_of_min (m i d : ℕ)
    (x : Label.{u} m (i + 1) d) (p : Fin m)
    (hp : p ∈ (x.1 : Finset (Fin m)))
    (hmin : ∀ q ∈ totalSupport x, p ≤ q) :
    kappa S m i d
      (Module.Koszul.delta S (Carrier S m) i d
        (termBasis S m (i + 1) d x)) = termBasis S m (i + 1) d x := by
  classical
  have hpi := pivot_differentialLabel_of_min x p hp hmin
  rw [delta_termBasis]
  simp only [map_sum, map_smul]
  rw [Finset.sum_eq_single ⟨p, hp⟩]
  · have hn : pivot (differentialLabel x p hp) ∉
        ((differentialLabel x p hp).1 : Finset (Fin m)) := by
      rw [hpi p hp, differentialLabel_exterior]
      simp
    rw [kappa_basis, dite_eq_right hn, lowerCount_eq_zero,
      exterior_sign_exponent_zero x p hmin]
    simp only [pow_zero, one_smul]
    rw [contracted_differentialLabel x p hp (hpi p hp) hn]
  · intro q hq hne
    have hqp : q.val ≠ p := by
      intro he
      exact hne (Subtype.ext he)
    have hmem : pivot (differentialLabel x q.val q.property) ∈
        ((differentialLabel x q.val q.property).1 : Finset (Fin m)) := by
      rw [hpi q.val q.property, differentialLabel_exterior]
      simp [Ne.symm hqp, hp]
    rw [kappa_basis, dite_eq_left hmem, smul_zero]
  · intro hnot
    exfalso
    exact hnot (by simp)

private theorem mixed_basis_pivot_missing (m i d : ℕ)
    (x : Label.{u} m (i + 1) (d + 1))
    (hp : pivot x ∉ (x.1 : Finset (Fin m))) :
    Module.Koszul.delta S (Carrier S m) (i + 1) d
        (kappa S m (i + 1) d (termBasis S m (i + 1) (d + 1) x)) +
      kappa S m i (d + 1)
        (Module.Koszul.delta S (Carrier S m) i (d + 1)
          (termBasis S m (i + 1) (d + 1) x)) =
      termBasis S m (i + 1) (d + 1) x := by
  classical
  let y : Label.{u} m (i + 2) d := contractedLabel x hp
  have hpy : pivot x ∈ (y.1 : Finset (Fin m)) := by
    dsimp only [y]
    rw [contractedLabel_exterior]
    simp
  have hminy : ∀ q ∈ totalSupport y, pivot x ≤ q := by
    intro q hq
    apply (pivot_spec x).2 q
    change q ∈ totalSupport (contractedLabel x hp) at hq
    rw [totalSupport_contractedLabel] at hq
    exact hq
  let a : {q // q ∈ (y.1 : Finset (Fin m))} := ⟨pivot x, hpy⟩
  let R : Term S (Carrier S m) (i + 1) (d + 1) :=
    ((y.1 : Finset (Fin m)).attach.erase a).sum (fun q =>
      (-1 : S) ^ ((y.1 : Finset (Fin m)).filter (fun r => r < q.val)).card •
        termBasis S m (i + 1) (d + 1)
          (differentialLabel y q.val q.property))
  have hterm :
      (-1 : S) ^ ((y.1 : Finset (Fin m)).filter (fun r => r < a.val)).card •
        termBasis S m (i + 1) (d + 1)
          (differentialLabel y a.val a.property) =
      termBasis S m (i + 1) (d + 1) x := by
    change (-1 : S) ^ ((y.1 : Finset (Fin m)).filter
      (fun r => r < pivot x)).card •
      termBasis S m (i + 1) (d + 1) (differentialLabel y (pivot x) hpy) = _
    rw [exterior_sign_exponent_zero y (pivot x) hminy, pow_zero, one_smul,
      differential_contractedLabel_pivot x hp hpy]
  have hsplit :
      Module.Koszul.delta S (Carrier S m) (i + 1) d
          (termBasis S m (i + 2) d y) =
        R + termBasis S m (i + 1) (d + 1) x := by
    have hs : R +
        (-1 : S) ^ ((y.1 : Finset (Fin m)).filter (fun r => r < a.val)).card •
          termBasis S m (i + 1) (d + 1)
            (differentialLabel y a.val a.property) =
        Module.Koszul.delta S (Carrier S m) (i + 1) d
          (termBasis S m (i + 2) d y) := by
      rw [delta_termBasis]
      exact Finset.sum_erase_add _ _ (by simp : a ∈ (y.1 : Finset (Fin m)).attach)
    simpa only [hterm] using hs.symm
  have hR :
      kappa S m i (d + 1)
        (Module.Koszul.delta S (Carrier S m) i (d + 1) R) = R := by
    dsimp only [R]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro q hq
    have hqp : q.val ≠ pivot x := by
      intro he
      have heq : q = a := Subtype.ext he
      subst q
      simp at hq
    have hmem : pivot x ∈
        ((differentialLabel y q.val q.property).1 : Finset (Fin m)) := by
      rw [differentialLabel_exterior]
      simp [Ne.symm hqp, hpy]
    have hmin : ∀ r ∈ totalSupport (differentialLabel y q.val q.property),
        pivot x ≤ r := by
      intro r hr
      apply hminy r
      rw [totalSupport_differentialLabel] at hr
      exact hr
    rw [kappa_delta_basis_of_min S m i (d + 1)
      (differentialLabel y q.val q.property) (pivot x) hmem hmin]
  have hdd := congrArg
    (fun f : Term S (Carrier S m) (i + 2) d →ₗ[S]
        Term S (Carrier S m) i (d + 2) => f (termBasis S m (i + 2) d y))
    (Module.Koszul.delta_comp_delta S (Carrier S m) i d)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hdd
  have hzero : R +
      kappa S m i (d + 1)
        (Module.Koszul.delta S (Carrier S m) i (d + 1)
          (termBasis S m (i + 1) (d + 1) x)) = 0 := by
    have h := congrArg (kappa S m i (d + 1)) hdd
    rw [hsplit] at h
    simpa only [map_add, map_zero, hR] using h
  rw [kappa_basis, dite_eq_right hp, lowerCount_eq_zero, pow_zero, one_smul]
  change (Module.Koszul.delta S (Carrier S m) (i + 1) d
    (termBasis S m (i + 2) d y)) + _ = _
  rw [hsplit]
  calc
    (R + termBasis S m (i + 1) (d + 1) x) + _ =
        termBasis S m (i + 1) (d + 1) x +
          (R + kappa S m i (d + 1)
            (Module.Koszul.delta S (Carrier S m) i (d + 1)
              (termBasis S m (i + 1) (d + 1) x))) := by ac_rfl
    _ = _ := by rw [hzero, add_zero]

/-- The two differential-contraction composites sum to the identity when
both exterior and symmetric degrees are positive.
For the Koszul construction, see Weibel, *The K-book* (2013). -/
theorem delta_comp_kappa_add_kappa_comp_delta (m i d : ℕ) :
    (Module.Koszul.delta S (Carrier S m) (i + 1) d).comp
        (kappa S m (i + 1) d) +
      (kappa S m i (d + 1)).comp
        (Module.Koszul.delta S (Carrier S m) i (d + 1)) =
      (LinearMap.id :
        Term S (Carrier S m) (i + 1) (d + 1) →ₗ[S]
          Term S (Carrier S m) (i + 1) (d + 1)) := by
  classical
  apply (termBasis S m (i + 1) (d + 1)).ext
  intro x
  change Module.Koszul.delta S (Carrier S m) (i + 1) d
      (kappa S m (i + 1) d (termBasis S m (i + 1) (d + 1) x)) +
    kappa S m i (d + 1)
      (Module.Koszul.delta S (Carrier S m) i (d + 1)
        (termBasis S m (i + 1) (d + 1) x)) =
    termBasis S m (i + 1) (d + 1) x
  by_cases hp : pivot x ∈ (x.1 : Finset (Fin m))
  · rw [kappa_basis, dite_eq_left hp, map_zero, zero_add]
    exact kappa_delta_basis_of_min S m i (d + 1) x (pivot x) hp (pivot_spec x).2
  · exact mixed_basis_pivot_missing S m i d x hp

/-- In exterior degree zero and positive symmetric degree, differential after
contraction is the identity.
For the Koszul construction, see Weibel, *The K-book* (2013). -/
theorem delta_comp_kappa_exterior_zero (m d : ℕ) :
    (Module.Koszul.delta S (Carrier S m) 0 d).comp
        (kappa S m 0 d) =
      (LinearMap.id :
        Term S (Carrier S m) 0 (d + 1) →ₗ[S]
          Term S (Carrier S m) 0 (d + 1)) := by
  classical
  apply (termBasis S m 0 (d + 1)).ext
  intro x
  change Module.Koszul.delta S (Carrier S m) 0 d
    (kappa S m 0 d (termBasis S m 0 (d + 1) x)) =
      termBasis S m 0 (d + 1) x
  have hI : (x.1 : Finset (Fin m)) = ∅ := by
    apply Finset.card_eq_zero.mp
    exact Set.powersetCard.card_eq x.1
  have hp : pivot x ∉ (x.1 : Finset (Fin m)) := by simp [hI]
  let y : Label.{u} m 1 d := contractedLabel x hp
  have hy : (y.1 : Finset (Fin m)) = {pivot x} := by
    dsimp only [y]
    rw [contractedLabel_exterior, hI]
    simp
  have hpy : pivot x ∈ (y.1 : Finset (Fin m)) := by simp [hy]
  have hdelta : Module.Koszul.delta S (Carrier S m) 0 d
      (termBasis S m 1 d y) = termBasis S m 0 (d + 1) x := by
    rw [delta_termBasis]
    rw [Finset.sum_eq_single ⟨pivot x, hpy⟩]
    · have hc : ((y.1 : Finset (Fin m)).filter
          (fun q => q < pivot x)).card = 0 := by simp [hy]
      rw [hc, pow_zero, one_smul, differential_contractedLabel_pivot x hp hpy]
    · intro q hq hne
      have he : q.val = pivot x := by
        have hmem := q.property
        simpa only [hy, Finset.mem_singleton] using hmem
      exact (hne (Subtype.ext he)).elim
    · intro hnot
      exfalso
      exact hnot (by simp)
  rw [kappa_basis, dite_eq_right hp, lowerCount_eq_zero, pow_zero, one_smul]
  exact hdelta

/-- In symmetric degree zero and positive exterior degree, contraction after
differential is the identity.
For the Koszul construction, see Weibel, *The K-book* (2013). -/
theorem kappa_comp_delta_symmetric_zero (m i : ℕ) :
    (kappa S m i 0).comp (Module.Koszul.delta S (Carrier S m) i 0) =
      (LinearMap.id :
        Term S (Carrier S m) (i + 1) 0 →ₗ[S]
          Term S (Carrier S m) (i + 1) 0) := by
  classical
  apply (termBasis S m (i + 1) 0).ext
  intro x
  change kappa S m i 0
    (Module.Koszul.delta S (Carrier S m) i 0
      (termBasis S m (i + 1) 0 x)) = termBasis S m (i + 1) 0 x
  have ha : x.2.val = 0 := by
    apply Finsupp.ext
    intro r
    change x.2.val r = 0
    by_cases hr : r ∈ x.2.val.support
    · have hle : x.2.val r ≤ x.2.val.sum (fun _ n => n) :=
        Finset.single_le_sum (fun q _ => Nat.zero_le (x.2.val q)) hr
      rw [symmetric_mass x.2] at hle
      exact Nat.eq_zero_of_le_zero hle
    · by_contra hne
      exact hr (Finsupp.mem_support_iff.mpr hne)
  have hI : (x.1 : Finset (Fin m)).Nonempty := by
    apply Finset.card_pos.mp
    rw [Set.powersetCard.card_eq]
    exact Nat.succ_pos i
  obtain ⟨q, hq⟩ := hI
  let p := pivot (differentialLabel x q hq)
  have hp : p ∈ (x.1 : Finset (Fin m)) := by
    have hs : p ∈ totalSupport x := by
      rw [← totalSupport_differentialLabel x q hq]
      exact (pivot_spec (differentialLabel x q hq)).1
    simpa [totalSupport, ha] using hs
  have hmin : ∀ r ∈ totalSupport x, p ≤ r := by
    intro r hr
    apply (pivot_spec (differentialLabel x q hq)).2 r
    rw [totalSupport_differentialLabel]
    exact hr
  exact kappa_delta_basis_of_min S m i 0 x p hp hmin

end Module.Koszul.CanonicalFreeContraction
