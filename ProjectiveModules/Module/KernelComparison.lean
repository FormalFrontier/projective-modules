/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Tactic.Abel

public import Mathlib.LinearAlgebra.Prod

/-!
# Comparing kernels using prescribed lifts

Given linear maps `p : P →ₗ[R] M` and `q : Q →ₗ[R] M` and lifts
`s : Q →ₗ[R] P` and `t : P →ₗ[R] Q` satisfying `p.comp s = q` and
`q.comp t = p`, `LinearMap.kerProdEquivOfLifts` identifies `p.ker × Q`
with `q.ker × P`. Both the equivalence and its inverse retain the supplied lifts.

Only `P` and `Q` need additive inverses; the common target `M` may be an additive
commutative monoid. No surjectivity or projectivity is needed for this comparison.
Subtraction is performed in the ambient modules, not in the kernel submodules.

## References

This is the explicit two-lift kernel comparison underlying Schanuel's lemma;
see Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory* (2013).
The construction uses Mathlib's generic linear-map products and restrictions.
-/

@[expose] public section

universe uR uP uQ uM

namespace LinearMap

variable {R : Type uR} [Semiring R]
variable {P : Type uP} [AddCommGroup P] [Module R P]
variable {Q : Type uQ} [AddCommGroup Q] [Module R Q]
variable {M : Type uM} [AddCommMonoid M] [Module R M]

-- The target need not admit subtraction or cancellation.
private theorem map_sub_eq_zero_of_eq {G : Type*} [AddGroup G]
    (f : G →+ M) {x y : G} (hxy : f x = f y) : f (x - y) = 0 := by
  calc
    f (x - y) = f x + f (-y) := by rw [sub_eq_add_neg, map_add]
    _ = f y + f (-y) := by rw [hxy]
    _ = f (y + -y) := (map_add f y (-y)).symm
    _ = 0 := by rw [add_neg_cancel, map_zero]

/-- The kernel-product comparison for two prescribed lifts, as used in
Schanuel's lemma (Weibel, *The K-book*, 2013). It sends `(k, y)` to
`(y - t (k + s y), k + s y)` and has inverse
`(l, x) ↦ (x - s (l + t x), l + t x)`, with kernel coordinates viewed in
the ambient modules. -/
def kerProdEquivOfLifts
    (p : P →ₗ[R] M) (q : Q →ₗ[R] M)
    (s : Q →ₗ[R] P) (t : P →ₗ[R] Q)
    (hps : p.comp s = q) (hqt : q.comp t = p) :
    (p.ker × Q) ≃ₗ[R] (q.ker × P) where
  toLinearMap :=
    let a : p.ker × Q →ₗ[R] P :=
      p.ker.subtype.comp (fst R p.ker Q) + s.comp (snd R p.ker Q)
    let b : p.ker × Q →ₗ[R] Q := snd R p.ker Q - t.comp a
    (codRestrict q.ker b fun z ↦ by
      apply mem_ker.mpr
      change q (z.2 - t ((z.1 : P) + s z.2)) = 0
      apply map_sub_eq_zero_of_eq q.toAddMonoidHom
      calc
        q z.2 = p (s z.2) := (LinearMap.congr_fun hps z.2).symm
        _ = p ((z.1 : P) + s z.2) := by
          rw [map_add, mem_ker.mp z.1.property, zero_add]
        _ = q (t ((z.1 : P) + s z.2)) :=
          (LinearMap.congr_fun hqt _).symm).prod a
  invFun :=
    let a : q.ker × P →ₗ[R] Q :=
      q.ker.subtype.comp (fst R q.ker P) + t.comp (snd R q.ker P)
    let b : q.ker × P →ₗ[R] P := snd R q.ker P - s.comp a
    (codRestrict p.ker b fun z ↦ by
      apply mem_ker.mpr
      change p (z.2 - s ((z.1 : Q) + t z.2)) = 0
      apply map_sub_eq_zero_of_eq p.toAddMonoidHom
      calc
        p z.2 = q (t z.2) := (LinearMap.congr_fun hqt z.2).symm
        _ = q ((z.1 : Q) + t z.2) := by
          rw [map_add, mem_ker.mp z.1.property, zero_add]
        _ = p (s ((z.1 : Q) + t z.2)) :=
          (LinearMap.congr_fun hps _).symm).prod a
  left_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      change ((z.1 : P) + s z.2) -
        s ((z.2 - t ((z.1 : P) + s z.2)) + t ((z.1 : P) + s z.2)) = (z.1 : P)
      simp only [sub_add_cancel, add_sub_cancel_right]
    · change (z.2 - t ((z.1 : P) + s z.2)) + t ((z.1 : P) + s z.2) = z.2
      exact sub_add_cancel _ _
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      change ((z.1 : Q) + t z.2) -
        t ((z.2 - s ((z.1 : Q) + t z.2)) + s ((z.1 : Q) + t z.2)) = (z.1 : Q)
      simp only [sub_add_cancel, add_sub_cancel_right]
    · change (z.2 - s ((z.1 : Q) + t z.2)) + s ((z.1 : Q) + t z.2) = z.2
      exact sub_add_cancel _ _

/-- The kernel coordinate of the comparison, viewed in `Q`. -/
@[simp] theorem kerProdEquivOfLifts_apply_fst
    (p : P →ₗ[R] M) (q : Q →ₗ[R] M)
    (s : Q →ₗ[R] P) (t : P →ₗ[R] Q)
    (hps : p.comp s = q) (hqt : q.comp t = p) (z : p.ker × Q) :
    ((kerProdEquivOfLifts p q s t hps hqt z).1 : Q) =
      z.2 - t ((z.1 : P) + s z.2) := rfl

/-- The ambient coordinate of the comparison. -/
@[simp] theorem kerProdEquivOfLifts_apply_snd
    (p : P →ₗ[R] M) (q : Q →ₗ[R] M)
    (s : Q →ₗ[R] P) (t : P →ₗ[R] Q)
    (hps : p.comp s = q) (hqt : q.comp t = p) (z : p.ker × Q) :
    (kerProdEquivOfLifts p q s t hps hqt z).2 = (z.1 : P) + s z.2 := rfl

/-- The kernel coordinate of the inverse comparison, viewed in `P`. -/
@[simp] theorem kerProdEquivOfLifts_symm_apply_fst
    (p : P →ₗ[R] M) (q : Q →ₗ[R] M)
    (s : Q →ₗ[R] P) (t : P →ₗ[R] Q)
    (hps : p.comp s = q) (hqt : q.comp t = p) (z : q.ker × P) :
    (((kerProdEquivOfLifts p q s t hps hqt).symm z).1 : P) =
      z.2 - s ((z.1 : Q) + t z.2) := rfl

/-- The ambient coordinate of the inverse comparison. -/
@[simp] theorem kerProdEquivOfLifts_symm_apply_snd
    (p : P →ₗ[R] M) (q : Q →ₗ[R] M)
    (s : Q →ₗ[R] P) (t : P →ₗ[R] Q)
    (hps : p.comp s = q) (hqt : q.comp t = p) (z : q.ker × P) :
    ((kerProdEquivOfLifts p q s t hps hqt).symm z).2 = (z.1 : Q) + t z.2 := rfl

end LinearMap

end

@[expose] public section

universe uK uH uA

private theorem commonSectionResidual
    {K : Type uK} {H : Type uH} {A : Type uA}
    [Semiring K] [AddCommMonoid H] [Module K H]
    [AddCommGroup A] [Module K A]
    (Γ : H →ₗ[K] A) (u v : A →ₗ[K] H)
    (hu : ∀ h : H, u (Γ h) = h) (a : A) :
    ((a - Γ (v a)) - Γ (u (a - Γ (v a)))) = a - Γ (u a) := by
  let P : A →ₗ[K] A := Γ.comp u
  have hP : P (a - Γ (v a)) = Γ (u a) - Γ (v a) := by
    rw [map_sub]
    change Γ (u a) - Γ (u (Γ (v a))) = Γ (u a) - Γ (v a)
    rw [hu]
  change (a - Γ (v a)) - P (a - Γ (v a)) = a - Γ (u a)
  rw [hP]
  abel

private theorem commonSectionResidual_mem
    {K : Type uK} {H : Type uH} {A : Type uA}
    [Semiring K] [AddCommMonoid H] [Module K H]
    [AddCommGroup A] [Module K A]
    (Γ : H →ₗ[K] A) (u : A →ₗ[K] H)
    (hu : ∀ h : H, u (Γ h) = h) (a : A) :
    u (a - Γ (u a)) = 0 := by
  -- Reflect zero through the split injection, keeping subtraction in the ambient group.
  have hΓ : Function.Injective Γ := by
    intro x y h
    simpa only [hu] using congrArg u h
  apply hΓ
  change (Γ.comp u) (a - Γ (u a)) = Γ 0
  rw [map_sub]
  change Γ (u a) - Γ (u (Γ (u a))) = Γ 0
  rw [hu, sub_self, map_zero]

namespace LinearMap

/-- The linear equivalence between the kernels of two split linear retractions
with a common section. Its ambient formula is `a ↦ a - Γ (q a)`, with inverse
`b ↦ b - Γ (r b)`. Only the ambient module needs an additive group structure. -/
def kerEquivOfCommonRightInverse
    {K : Type uK} {H : Type uH} {A : Type uA}
    [Semiring K] [AddCommMonoid H] [Module K H]
    [AddCommGroup A] [Module K A]
    (Γ : H →ₗ[K] A) (r q : A →ₗ[K] H)
    (hr : ∀ h : H, r (Γ h) = h) (hq : ∀ h : H, q (Γ h) = h) :
    LinearMap.ker r ≃ₗ[K] LinearMap.ker q where
  toFun a := ⟨(a : A) - Γ (q (a : A)), by
    exact commonSectionResidual_mem Γ q hq a⟩
  invFun b := ⟨(b : A) - Γ (r (b : A)), by
    exact commonSectionResidual_mem Γ r hr b⟩
  left_inv a := by
    apply Subtype.ext
    have ha : r (a : A) = 0 := a.property
    simpa only [ha, map_zero, sub_zero] using commonSectionResidual Γ r q hr (a : A)
  right_inv b := by
    apply Subtype.ext
    have hb : q (b : A) = 0 := b.property
    simpa only [hb, map_zero, sub_zero] using commonSectionResidual Γ q r hq (b : A)
  map_add' a b := by
    apply Subtype.ext
    change (a : A) + (b : A) - Γ (q ((a : A) + (b : A))) =
      ((a : A) - Γ (q (a : A))) + ((b : A) - Γ (q (b : A)))
    rw [map_add, map_add]
    abel
  map_smul' c a := by
    apply Subtype.ext
    change c • (a : A) - Γ (q (c • (a : A))) = c • ((a : A) - Γ (q (a : A)))
    rw [map_smul, map_smul, smul_sub]

variable {K : Type uK} [Semiring K]
variable {H : Type uH} [AddCommMonoid H] [Module K H]
variable {A : Type uA} [AddCommGroup A] [Module K A]

/-- The ambient value of the common-section kernel comparison. -/
@[simp]
theorem coe_kerEquivOfCommonRightInverse_apply (Γ : H →ₗ[K] A) (r q : A →ₗ[K] H)
    (hr : ∀ h : H, r (Γ h) = h) (hq : ∀ h : H, q (Γ h) = h)
    (a : LinearMap.ker r) :
    (kerEquivOfCommonRightInverse Γ r q hr hq a : A) = (a : A) - Γ (q (a : A)) :=
  rfl

/-- The ambient value of the inverse common-section kernel comparison. -/
theorem coe_kerEquivOfCommonRightInverse_symm_apply (Γ : H →ₗ[K] A)
    (r q : A →ₗ[K] H) (hr : ∀ h : H, r (Γ h) = h) (hq : ∀ h : H, q (Γ h) = h)
    (b : LinearMap.ker q) :
    ((kerEquivOfCommonRightInverse Γ r q hr hq).symm b : A) =
      (b : A) - Γ (r (b : A)) :=
  rfl

/-- Comparing a kernel with itself gives the identity linear equivalence. -/
@[simp]
theorem kerEquivOfCommonRightInverse_refl (Γ : H →ₗ[K] A) (r : A →ₗ[K] H)
    (hr : ∀ h : H, r (Γ h) = h) :
    kerEquivOfCommonRightInverse Γ r r hr hr = LinearEquiv.refl K (LinearMap.ker r) := by
  ext a : 1
  apply Subtype.ext
  change (a : A) - Γ (r (a : A)) = (a : A)
  have ha : r (a : A) = 0 := a.property
  rw [ha, map_zero, sub_zero]

/-- Reversing the two retractions gives the inverse linear equivalence. -/
@[simp]
theorem kerEquivOfCommonRightInverse_symm (Γ : H →ₗ[K] A) (r q : A →ₗ[K] H)
    (hr : ∀ h : H, r (Γ h) = h) (hq : ∀ h : H, q (Γ h) = h) :
    (kerEquivOfCommonRightInverse Γ r q hr hq).symm =
      kerEquivOfCommonRightInverse Γ q r hq hr := by
  ext b : 1
  rfl

/-- Kernel comparisons with a fixed common section compose in order. -/
@[simp]
theorem kerEquivOfCommonRightInverse_trans (Γ : H →ₗ[K] A) (r q s : A →ₗ[K] H)
    (hr : ∀ h : H, r (Γ h) = h) (hq : ∀ h : H, q (Γ h) = h)
    (hs : ∀ h : H, s (Γ h) = h) :
    (kerEquivOfCommonRightInverse Γ r q hr hq).trans
        (kerEquivOfCommonRightInverse Γ q s hq hs) =
      kerEquivOfCommonRightInverse Γ r s hr hs := by
  ext a : 1
  apply Subtype.ext
  exact commonSectionResidual Γ s q hs (a : A)

end LinearMap
