/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine.Endomorphism.Product
public import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Projective

/-!
# Scalar determinants in short exact sequences

An endomorphism of a short exact sequence of finite projective modules has scalar
determinant equal to the product of the determinants on the two endpoints. In
particular, an invariant finite projective submodule with finite projective quotient
gives a restriction/quotient formula.

## Implementation notes

Projectivity of the quotient supplies an ordinary linear section. Mathlib's
`Function.Exact.splitSurjectiveEquiv` identifies the middle module with the product
of the endpoints. The transported endomorphism is upper triangular, with arbitrary
off-diagonal block, so the product formula applies without an equivariant section.
Neither constant rank nor invertibility of any endomorphism is required.
-/

@[expose] public section

noncomputable section

universe uR uP uM uQ

namespace Module

variable (R : Type uR) [CommRing R]
variable (P : Type uP) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
variable (M : Type uM) [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]
variable (Q : Type uQ) [AddCommGroup Q] [Module R Q]
  [Module.Finite R Q] [Module.Projective R Q]

/-- An endomorphism of a short exact sequence of finite projective modules has
scalar determinant equal to the product of the endpoint determinants. The sequence
need not admit a section commuting with the endomorphisms. -/
theorem determinant_eq_mul_of_exact
    (i : P →ₗ[R] M) (q : M →ₗ[R] Q)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hex : Function.Exact i q)
    (fp : Module.End R P) (fm : Module.End R M) (fq : Module.End R Q)
    (hp : fm.comp i = i.comp fp) (hfq : q.comp fm = fq.comp q) :
    determinant R M fm = determinant R P fp * determinant R Q fq := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q (LinearMap.id : Module.End R Q) hq
  obtain ⟨e, he_i, he_q⟩ := hex.splitSurjectiveEquiv hi ⟨s, hs⟩
  let T : Module.End R (P × Q) := e.conj fm
  let b : Q →ₗ[R] P :=
    (LinearMap.fst R P Q).comp (T.comp (LinearMap.inr R P Q))
  have he_inl (p : P) : e.symm (p, 0) = i p :=
    (DFunLike.congr_fun he_i p).symm
  have he_snd (x : M) : q x = (e x).2 := DFunLike.congr_fun he_q x
  have hfp (p : P) : fm (i p) = i (fp p) := DFunLike.congr_fun hp p
  have hfq' (x : M) : q (fm x) = fq (q x) := DFunLike.congr_fun hfq x
  have hT_inl (p : P) : T (p, 0) = (fp p, 0) := by
    change e (fm (e.symm (p, 0))) = (fp p, 0)
    rw [he_inl, hfp, ← he_inl, e.apply_symm_apply]
  have hT_snd (x : P × Q) : (T x).2 = fq x.2 := by
    change (e (fm (e.symm x))).2 = fq x.2
    rw [← he_snd, hfq', he_snd, e.apply_symm_apply]
  have hT : T = (LinearMap.coprod fp b).prod
      (LinearMap.coprod (0 : P →ₗ[R] Q) fq) := by
    apply LinearMap.ext
    rintro ⟨p, t⟩
    have hsplit : T (p, t) = T (p, 0) + T (0, t) := by
      rw [← map_add]
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    apply Prod.ext
    · change (T (p, t)).1 = fp p + b t
      rw [hsplit, hT_inl]
      rfl
    · change (T (p, t)).2 = 0 + fq t
      rw [zero_add]
      exact hT_snd (p, t)
  calc
    determinant R M fm = determinant R (P × Q) T :=
      (determinant_conj R M (P × Q) e fm).symm
    _ = determinant R P fp * determinant R Q fq := by
      rw [hT]
      exact determinant_prod_coprod_zero₂₁ R P Q fp b fq

/-- The scalar determinant factors through an invariant finite projective submodule
and its finite projective quotient. This uses the same invariance condition as
`LinearMap.det_eq_det_mul_det`, but the modules need not be free. -/
theorem determinant_eq_restrict_mul_quotient
    (W : Submodule R M) [Module.Finite R W] [Module.Projective R W]
    [Module.Finite R (M ⧸ W)] [Module.Projective R (M ⧸ W)]
    (f : Module.End R M) (hW : W ≤ W.comap f) :
    determinant R M f =
      determinant R W (f.restrict hW) * determinant R (M ⧸ W) (W.mapQ W f hW) := by
  apply determinant_eq_mul_of_exact R W M (M ⧸ W) W.subtype W.mkQ
    (fun _ _ h ↦ Subtype.ext h) W.mkQ_surjective (LinearMap.exact_subtype_mkQ W)
    (f.restrict hW) f (W.mapQ W f hW)
  · apply LinearMap.ext
    intro x
    rfl
  · exact (Submodule.mapQ_mkQ W W f).symm

end Module
