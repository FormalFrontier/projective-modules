/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

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
