/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Module.NatInt
public import ProjectiveModules.ExteriorPower.DirectSum
public import ProjectiveModules.ExteriorPower.Quadratic

/-!
# Homogeneous exterior coproducts

The homogeneous coproduct is the exterior power of the linear diagonal, followed by
projection through the canonical binary direct-sum decomposition. The construction
uses Mathlib's exterior powers and the product decomposition in
`ProjectiveModules.ExteriorPower.DirectSum`.

Write `E n = ⋀[R]^n M`, and let `C h : E a →ₗ[R] E b` be the canonical indexed
linear cast associated to `h : a = b`. The characteristic identities are naturality
under arbitrary module maps, the tensor unit laws in degree zero, graded symmetry
with sign `(-1)^(p*q)`, and coassociativity with the tensor associator and the cast
`C (Nat.add_assoc p q r)`.

On a generating wedge the characteristic expression is Mathlib's existing
`AlternatingMap.domCoprod` of the two universal alternating maps, with the input
reindexed along `finSumFinEquiv`. Thus each shuffle occurs once, without dividing by
factorials. In bidegree `(1, 1)`, the canonical degree-one identifications give
`x ⊗ y - y ⊗ x`, including in characteristic two.
-/

@[expose] public section

open scoped DirectSum TensorProduct

universe u v

namespace exteriorPower

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The bidegree `(p, q)` component of the exterior power of the linear diagonal.
The selected summand has right degree `(p + q) - p`; the canonical indexed linear
cast identifies this degree with `q`. -/
noncomputable def comul (p q : ℕ) :
    (⋀[R]^(p + q) M) →ₗ[R] (⋀[R]^p M) ⊗[R] (⋀[R]^q M) :=
  (LinearEquiv.cast (R := R)
      (M := fun d : ℕ ↦ (⋀[R]^p M) ⊗[R] (⋀[R]^d M))
      (Nat.add_sub_cancel_left p q)).toLinearMap ∘ₗ
    DirectSum.component R (Fin (p + q + 1))
      (fun i ↦ (⋀[R]^i.1 M) ⊗[R] (⋀[R]^(p + q - i.1) M))
      ⟨p, Nat.lt_succ_of_le (Nat.le_add_right p q)⟩ ∘ₗ
    (prodEquivDirectSum R M M (p + q)).toLinearMap ∘ₗ
    map (p + q) ((LinearMap.id (R := R) (M := M)).prod LinearMap.id)

/-- The homogeneous exterior coproduct is the Cauchy component of the exterior
power of the linear diagonal. -/
theorem comul_eq_prodComponent_comp_map (p q : ℕ) :
    comul R M p q =
      prodComponent R M M p q ∘ₗ
        map (p + q) ((LinearMap.id (R := R) (M := M)).prod LinearMap.id) := by
  rfl

universe w

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The homogeneous exterior coproduct is natural under arbitrary linear maps.
This follows from naturality of `prodEquivDirectSum` and of the linear diagonal. -/
theorem comul_naturality (p q : ℕ) (f : M →ₗ[R] N) :
    TensorProduct.map (map p f) (map q f) ∘ₗ comul R M p q =
      comul R N p q ∘ₗ map (p + q) f := by
  rw [comul_eq_prodComponent_comp_map, comul_eq_prodComponent_comp_map]
  apply LinearMap.ext
  intro x
  let δM : M →ₗ[R] M × M := (LinearMap.id (R := R) (M := M)).prod LinearMap.id
  let δN : N →ₗ[R] N × N := (LinearMap.id (R := R) (M := N)).prod LinearMap.id
  have hd : (f.prodMap f) ∘ₗ δM = δN ∘ₗ f := by
    apply LinearMap.ext
    intro m
    rfl
  change TensorProduct.map (map p f) (map q f)
      (prodComponent R M M p q (map (p + q) δM x)) =
    prodComponent R N N p q (map (p + q) δN (map (p + q) f x))
  rw [← prodComponent_map]
  apply congrArg (prodComponent R N N p q)
  change (map (p + q) (f.prodMap f) ∘ₗ map (p + q) δM) x =
    (map (p + q) δN ∘ₗ map (p + q) f) x
  rw [← map_comp, ← map_comp, hd]

/-- Applying the exterior coproduct after an induced exterior-power map amounts to
applying that map to both tensor factors of the coproduct. -/
@[simp]
theorem comul_map (p q : ℕ) (f : M →ₗ[R] N) (x : ⋀[R]^(p + q) M) :
    comul R N p q (map (p + q) f x) =
      TensorProduct.map (map p f) (map q f) (comul R M p q x) := by
  exact (LinearMap.congr_fun (comul_naturality R M p q f) x).symm

end exteriorPower

namespace exteriorPower

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

private theorem comul_one_one_ιMulti (v : Fin 2 → M) :
    comul R M 1 1 (ιMulti R 2 v) =
      ιMulti R 1 (fun _ ↦ v 0) ⊗ₜ[R] ιMulti R 1 (fun _ ↦ v 1) -
        ιMulti R 1 (fun _ ↦ v 1) ⊗ₜ[R] ιMulti R 1 (fun _ ↦ v 0) := by
  classical
  let A := fun i : Fin 3 ↦ (⋀[R]^i.1 M) ⊗[R] (⋀[R]^(2 - i.1) M)
  let e := prodEquivDirectSum R M M 2
  -- Supply inverses from the existing R-action, without replacing the additive
  -- monoids of the tensor-product summands.
  let : AddCommGroup (⨁ i : Fin 3, A i) :=
    Module.addCommMonoidToAddCommGroup R
  let δ : M →ₗ[R] M × M := (LinearMap.id (R := R) (M := M)).prod LinearMap.id
  let ε : ⋀[R]^0 M := ιMulti R 0 Fin.elim0
  let η (x : M) : ⋀[R]^1 M := ιMulti R 1 (fun _ ↦ x)
  let z : ⨁ i : Fin 3, A i :=
    DirectSum.of A 2 (ιMulti R 2 v ⊗ₜ[R] ε) +
      DirectSum.of A 1 (η (v 0) ⊗ₜ[R] η (v 1)) +
      -DirectSum.of A 1 (η (v 1) ⊗ₜ[R] η (v 0)) +
      DirectSum.of A 0 (ε ⊗ₜ[R] ιMulti R 2 v)
  have hδ (x : M) :
      ExteriorAlgebra.ι R (δ x) =
        ExteriorAlgebra.ι R (LinearMap.inl R M M x) +
          ExteriorAlgebra.ι R (LinearMap.inr R M M x) := by
    have hx : δ x = LinearMap.inl R M M x + LinearMap.inr R M M x := by
      change (x, x) = (x, 0) + (0, x)
      simp
    rw [hx, map_add]
  have hswap :
      ExteriorAlgebra.ι R (LinearMap.inr R M M (v 0)) *
          ExteriorAlgebra.ι R (LinearMap.inl R M M (v 1)) =
        -(ExteriorAlgebra.ι R (LinearMap.inl R M M (v 1)) *
          ExteriorAlgebra.ι R (LinearMap.inr R M M (v 0))) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := R)
      (LinearMap.inr R M M (v 0)) (LinearMap.inl R M M (v 1)))
  have hz : e (map 2 δ (ιMulti R 2 v)) = z := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    dsimp only [z]
    rw [map_add, map_add, map_add, map_neg, map_apply_ιMulti]
    apply Subtype.ext
    change ExteriorAlgebra.ιMulti R 2 (δ ∘ v) =
      ((e.symm (DirectSum.of A 2 (ιMulti R 2 v ⊗ₜ[R] ε))).1 +
        (e.symm (DirectSum.of A 1 (η (v 0) ⊗ₜ[R] η (v 1)))).1) +
        -(e.symm (DirectSum.of A 1 (η (v 1) ⊗ₜ[R] η (v 0)))).1 +
        (e.symm (DirectSum.of A 0 (ε ⊗ₜ[R] ιMulti R 2 v))).1
    dsimp only [e]
    rw [coe_prodEquivDirectSum_symm_of_tmul, coe_prodEquivDirectSum_symm_of_tmul,
      coe_prodEquivDirectSum_symm_of_tmul, coe_prodEquivDirectSum_symm_of_tmul]
    simp only [ε, η, ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, Function.comp_apply, Matrix.vecTail,
      mul_one, one_mul, map_mul, map_one, ExteriorAlgebra.map_apply_ι]
    rw [show (0 : Fin 1).succ = (1 : Fin 2) from Fin.ext rfl]
    rw [hδ, hδ, add_mul, mul_add, mul_add, hswap]
    simp only [add_assoc]
  -- The pure left and pure right terms have zero component in bidegree `(1, 1)`.
  change e (map 2 δ (ιMulti R 2 v)) (1 : Fin 3) =
    η (v 0) ⊗ₜ[R] η (v 1) - η (v 1) ⊗ₜ[R] η (v 0)
  rw [hz, DirectSum.apply_eq_component R]
  dsimp only [z]
  rw [map_add, map_add, map_add, map_neg]
  simp [← DirectSum.lof_eq_of R, DirectSum.component.of, sub_eq_add_neg]

/-- Under the canonical degree-one identifications, the homogeneous exterior coproduct
in bidegree `(1, 1)` is antisymmetrization into the tensor square. -/
theorem comul_one_one :
    (TensorProduct.congr (oneEquiv R M) (oneEquiv R M)).toLinearMap ∘ₗ
        comul R M 1 1 = toTensorSquare R M := by
  apply toTensorSquare_unique R M
  intro v
  change TensorProduct.congr (oneEquiv R M) (oneEquiv R M)
      (comul R M 1 1 (ιMulti R 2 v)) =
    v 0 ⊗ₜ[R] v 1 - v 1 ⊗ₜ[R] v 0
  rw [comul_one_one_ιMulti, map_sub, TensorProduct.congr_tmul,
    TensorProduct.congr_tmul]
  simp only [oneEquiv_ιMulti]

end exteriorPower

namespace exteriorPower

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

private theorem comul_coe_zeroEquiv (a : ⋀[R]^0 M) :
    a.1 = algebraMap R (ExteriorAlgebra R M) (zeroEquiv R M a) := by
  obtain ⟨r, rfl⟩ := (zeroEquiv R M).symm.surjective a
  simp [zeroEquiv_symm_apply, Algebra.smul_def]

private theorem comul_exterior_map_zero_of_pos (n : ℕ) (hn : 0 < n)
    (a : ⋀[R]^n M) :
    ExteriorAlgebra.map (0 : M →ₗ[R] M) a.1 = 0 := by
  have h : (ExteriorAlgebra.map (0 : M →ₗ[R] M)).toLinearMap ∘ₗ
      (⋀[R]^n M).subtype = 0 := by
    apply linearMap_ext
    apply AlternatingMap.ext
    intro m
    cases n with
    | zero => omega
    | succ n => simp [ExteriorAlgebra.ιMulti_succ_apply]
  exact LinearMap.congr_fun h a

/-- Projection to the summand with left degree zero recovers the exterior power of
the second projection after applying the left tensor unitor. -/
private theorem comul_prodEquivDirectSum_lid (n : ℕ) :
    (TensorProduct.lid R (⋀[R]^n M)).toLinearMap ∘ₗ
        TensorProduct.map (zeroEquiv R M).toLinearMap LinearMap.id ∘ₗ
        DirectSum.component R (Fin (n + 1))
          (fun i ↦ (⋀[R]^i.1 M) ⊗[R] (⋀[R]^(n - i.1) M))
          ⟨0, Nat.zero_lt_succ n⟩ ∘ₗ
        (prodEquivDirectSum R M M n).toLinearMap =
      map n (LinearMap.snd R M M) := by
  apply prodEquivDirectSum_ext R M M n
  intro i a b
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_map, coe_prodEquivDirectSum_symm_of_tmul, map_mul]
  simp only [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  rw [show (LinearMap.snd R M M).comp (LinearMap.inl R M M) = 0 from rfl,
    show (LinearMap.snd R M M).comp (LinearMap.inr R M M) =
      LinearMap.id from rfl, ExteriorAlgebra.map_id]
  change _ = ExteriorAlgebra.map (0 : M →ₗ[R] M) a.1 * b.1
  rcases i with ⟨i, hi⟩
  by_cases h : i = 0
  · subst i
    rw [← DirectSum.lof_eq_of R, DirectSum.component.lof_self,
      TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul]
    change (zeroEquiv R M a) • b.1 =
      ExteriorAlgebra.map (0 : M →ₗ[R] M) a.1 * b.1
    simpa only [comul_coe_zeroEquiv R M a, AlgHom.commutes] using
      (Algebra.smul_def (zeroEquiv R M a) b.1)
  · have hi0 : (⟨i, hi⟩ : Fin (n + 1)) ≠ ⟨0, Nat.zero_lt_succ n⟩ := by
      intro he
      exact h (congrArg Fin.val he)
    have ha := comul_exterior_map_zero_of_pos R M i (Nat.pos_of_ne_zero h) a
    rw [← DirectSum.lof_eq_of R, DirectSum.component.of, dite_eq_right hi0]
    simp [ha]

/-- Projection to the summand with right degree zero recovers the exterior power of
the first projection after applying the right tensor unitor. -/
private theorem comul_prodEquivDirectSum_rid (n : ℕ) :
    (TensorProduct.rid R (⋀[R]^n M)).toLinearMap ∘ₗ
        TensorProduct.map LinearMap.id (zeroEquiv R M).toLinearMap ∘ₗ
        (LinearEquiv.cast (R := R)
          (M := fun d : ℕ ↦ (⋀[R]^n M) ⊗[R] (⋀[R]^d M))
          (Nat.sub_self n)).toLinearMap ∘ₗ
        DirectSum.component R (Fin (n + 1))
          (fun i ↦ (⋀[R]^i.1 M) ⊗[R] (⋀[R]^(n - i.1) M))
          ⟨n, Nat.lt_succ_self n⟩ ∘ₗ
        (prodEquivDirectSum R M M n).toLinearMap =
      map n (LinearMap.fst R M M) := by
  apply prodEquivDirectSum_ext R M M n
  intro i a b
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_map, coe_prodEquivDirectSum_symm_of_tmul, map_mul]
  simp only [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  rw [show (LinearMap.fst R M M).comp (LinearMap.inl R M M) =
      LinearMap.id from rfl,
    show (LinearMap.fst R M M).comp (LinearMap.inr R M M) = 0 from rfl,
    ExteriorAlgebra.map_id]
  change _ = a.1 * ExteriorAlgebra.map (0 : M →ₗ[R] M) b.1
  rcases i with ⟨i, hi⟩
  by_cases h : i = n
  · subst i
    let r : R := zeroEquiv R M
      (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d M)
        (Nat.sub_self n) b)
    have hb : b.1 = algebraMap R (ExteriorAlgebra R M) r := by
      rw [← coe_cast R M (Nat.sub_self n) b]
      exact comul_coe_zeroEquiv R M _
    rw [← DirectSum.lof_eq_of R, DirectSum.component.lof_self,
      tensor_cast_tmul, TensorProduct.map_tmul,
      LinearMap.id_apply, TensorProduct.rid_tmul]
    change r • a.1 = a.1 * ExteriorAlgebra.map (0 : M →ₗ[R] M) b.1
    calc
      r • a.1 = algebraMap R (ExteriorAlgebra R M) r * a.1 :=
        Algebra.smul_def _ _
      _ = a.1 * algebraMap R (ExteriorAlgebra R M) r := Algebra.commutes _ _
      _ = a.1 * ExteriorAlgebra.map (0 : M →ₗ[R] M) b.1 := by
        rw [hb, AlgHom.commutes]
  · have hin : (⟨i, hi⟩ : Fin (n + 1)) ≠ ⟨n, Nat.lt_succ_self n⟩ := by
      intro he
      exact h (congrArg Fin.val he)
    have hpos : 0 < n - i := by omega
    have hb := comul_exterior_map_zero_of_pos R M (n - i) hpos b
    rw [← DirectSum.lof_eq_of R, DirectSum.component.of, dite_eq_right hin]
    rw [map_zero, map_zero, map_zero, Submodule.coe_zero, hb, mul_zero]

private theorem comul_lid_cast {a b : ℕ} (h : a = b)
    (z : (⋀[R]^0 M) ⊗[R] (⋀[R]^a M)) :
    TensorProduct.lid R (⋀[R]^b M)
        (TensorProduct.map (zeroEquiv R M).toLinearMap LinearMap.id
          (LinearEquiv.cast (R := R)
            (M := fun d : ℕ ↦ (⋀[R]^0 M) ⊗[R] (⋀[R]^d M)) h z)) =
      LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d M) h
        (TensorProduct.lid R (⋀[R]^a M)
          (TensorProduct.map (zeroEquiv R M).toLinearMap LinearMap.id z)) := by
  cases h
  rfl

/-- The degree-zero left factor of the exterior coproduct is the tensor unit.
The indexed cast identifies exterior degrees `0 + n` and `n`. -/
theorem comul_left_unit (n : ℕ) :
    (TensorProduct.lid R (⋀[R]^n M)).toLinearMap ∘ₗ
        TensorProduct.map (zeroEquiv R M).toLinearMap LinearMap.id ∘ₗ
        comul R M 0 n =
      (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d M)
        (Nat.zero_add n)).toLinearMap := by
  apply LinearMap.ext
  intro x
  let δ : M →ₗ[R] M × M := (LinearMap.id (R := R) (M := M)).prod LinearMap.id
  let y := prodEquivDirectSum R M M (0 + n) (map (0 + n) δ x)
  change TensorProduct.lid R (⋀[R]^n M)
      (TensorProduct.map (zeroEquiv R M).toLinearMap LinearMap.id
        (LinearEquiv.cast (R := R)
          (M := fun d : ℕ ↦ (⋀[R]^0 M) ⊗[R] (⋀[R]^d M))
          (Nat.add_sub_cancel_left 0 n) (y ⟨0, Nat.zero_lt_succ (0 + n)⟩))) =
    LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d M) (Nat.zero_add n) x
  rw [comul_lid_cast]
  apply congrArg (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d M)
    (Nat.zero_add n))
  have h := LinearMap.congr_fun (comul_prodEquivDirectSum_lid R M (0 + n))
    (map (0 + n) δ x)
  change TensorProduct.lid R (⋀[R]^(0 + n) M)
      (TensorProduct.map (zeroEquiv R M).toLinearMap LinearMap.id
        (y ⟨0, Nat.zero_lt_succ (0 + n)⟩)) =
    map (0 + n) (LinearMap.snd R M M) (map (0 + n) δ x) at h
  refine h.trans ?_
  rw [← LinearMap.comp_apply, ← map_comp]
  change map (0 + n) (LinearMap.id (R := R) (M := M)) x = x
  rw [map_id, LinearMap.id_apply]

/-- The degree-zero right factor of the exterior coproduct is the tensor unit.
The indexed cast identifies exterior degrees `n + 0` and `n`. -/
theorem comul_right_unit (n : ℕ) :
    (TensorProduct.rid R (⋀[R]^n M)).toLinearMap ∘ₗ
        TensorProduct.map LinearMap.id (zeroEquiv R M).toLinearMap ∘ₗ
        comul R M n 0 =
      (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d M)
        (Nat.add_zero n)).toLinearMap := by
  apply LinearMap.ext
  intro x
  let δ : M →ₗ[R] M × M := (LinearMap.id (R := R) (M := M)).prod LinearMap.id
  have h := LinearMap.congr_fun (comul_prodEquivDirectSum_rid R M n) (map n δ x)
  change TensorProduct.rid R (⋀[R]^n M)
      (TensorProduct.map LinearMap.id (zeroEquiv R M).toLinearMap
        (LinearEquiv.cast (R := R)
          (M := fun d : ℕ ↦ (⋀[R]^n M) ⊗[R] (⋀[R]^d M)) (Nat.sub_self n)
          (prodEquivDirectSum R M M n (map n δ x) ⟨n, Nat.lt_succ_self n⟩))) =
    map n (LinearMap.fst R M M) (map n δ x) at h
  change TensorProduct.rid R (⋀[R]^n M)
      (TensorProduct.map LinearMap.id (zeroEquiv R M).toLinearMap
        (LinearEquiv.cast (R := R)
          (M := fun d : ℕ ↦ (⋀[R]^n M) ⊗[R] (⋀[R]^d M)) (Nat.sub_self n)
          (prodEquivDirectSum R M M n (map n δ x) ⟨n, Nat.lt_succ_self n⟩))) = x
  refine h.trans ?_
  rw [← LinearMap.comp_apply, ← map_comp]
  change map n (LinearMap.id (R := R) (M := M)) x = x
  rw [map_id, LinearMap.id_apply]

/-- In bidegree `(0, 0)`, a scalar `r` has coproduct `r ⊗ 1`, equivalently `1 ⊗ r`.
In particular, the empty wedge has coproduct `1 ⊗ 1`; the scalar is not duplicated. -/
@[simp]
theorem comul_zero_zero (r : R) :
    TensorProduct.map (zeroEquiv R M).toLinearMap (zeroEquiv R M).toLinearMap
        (comul R M 0 0 ((zeroEquiv R M).symm r)) =
      r ⊗ₜ[R] (1 : R) := by
  have h : TensorProduct.map LinearMap.id (zeroEquiv R M).toLinearMap
      (comul R M 0 0 ((zeroEquiv R M).symm r)) =
      (zeroEquiv R M).symm r ⊗ₜ[R] (1 : R) := by
    apply (TensorProduct.rid R (⋀[R]^0 M)).injective
    simpa using LinearMap.congr_fun (comul_right_unit R M 0) ((zeroEquiv R M).symm r)
  have h' := congrArg
    (TensorProduct.map (zeroEquiv R M).toLinearMap (LinearMap.id (R := R) (M := R))) h
  simpa only [TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp,
    TensorProduct.map_tmul, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearMap.id_apply] using h'

/-- The homogeneous exterior coproduct is graded cocommutative. The degree cast
is on the source, before the coproduct with its two degrees exchanged. -/
theorem comul_comm (p q : ℕ) :
    (TensorProduct.comm R (⋀[R]^p M) (⋀[R]^q M)).toLinearMap ∘ₗ comul R M p q =
      ((-1 : R) ^ (p * q)) •
        (comul R M q p ∘ₗ
          (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d M)
            (Nat.add_comm p q)).toLinearMap) := by
  rw [comul_eq_prodComponent_comp_map, comul_eq_prodComponent_comp_map]
  apply LinearMap.ext
  intro x
  let δ : M →ₗ[R] M × M := (LinearMap.id (R := R) (M := M)).prod LinearMap.id
  let σ := (LinearEquiv.prodComm R M M).toLinearMap
  have hd : σ.comp δ = δ := by
    apply LinearMap.ext
    intro m
    rfl
  have hswap : map (q + p) σ
      (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d (M × M))
        (Nat.add_comm p q) (map (p + q) δ x)) =
      map (q + p) δ
        (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d M)
          (Nat.add_comm p q) x) := by
    apply Subtype.ext
    simp only [coe_map, coe_cast]
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hd]
  have h := LinearMap.congr_fun (prodComponent_comm R M M p q) (map (p + q) δ x)
  change TensorProduct.comm R (⋀[R]^p M) (⋀[R]^q M)
      (prodComponent R M M p q (map (p + q) δ x)) =
    ((-1 : R) ^ (p * q)) • prodComponent R M M q p
      (map (q + p) σ
        (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d (M × M))
          (Nat.add_comm p q) (map (p + q) δ x))) at h
  rw [hswap] at h
  exact h

/-- The homogeneous exterior coproduct is coassociative, with the canonical
tensor associator and the source degree cast. There is no permutation of blocks
and hence no graded sign. -/
theorem comul_assoc (p q r : ℕ) :
    (TensorProduct.assoc R (⋀[R]^p M) (⋀[R]^q M) (⋀[R]^r M)).toLinearMap ∘ₗ
        TensorProduct.map (comul R M p q) LinearMap.id ∘ₗ
        comul R M (p + q) r =
      TensorProduct.map LinearMap.id (comul R M q r) ∘ₗ
        comul R M p (q + r) ∘ₗ
        (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d M)
          (Nat.add_assoc p q r)).toLinearMap := by
  apply LinearMap.ext
  intro x
  let δ : M →ₗ[R] M × M := (LinearMap.id (R := R) (M := M)).prod LinearMap.id
  let δL : M →ₗ[R] (M × M) × M := (δ.prodMap LinearMap.id).comp δ
  let δR : M →ₗ[R] M × (M × M) := (LinearMap.id.prodMap δ).comp δ
  let α := (LinearEquiv.prodAssoc R M M M).toLinearMap
  have hd : α.comp δL = δR := by
    apply LinearMap.ext
    intro m
    rfl
  have hleft : TensorProduct.map (comul R M p q) LinearMap.id
      (comul R M (p + q) r x) =
      TensorProduct.map (prodComponent R M M p q) LinearMap.id
        (prodComponent R (M × M) M (p + q) r (map ((p + q) + r) δL x)) := by
    rw [comul_eq_prodComponent_comp_map, comul_eq_prodComponent_comp_map]
    change TensorProduct.map (prodComponent R M M p q ∘ₗ map (p + q) δ) LinearMap.id
        (prodComponent R M M (p + q) r (map ((p + q) + r) δ x)) =
      TensorProduct.map (prodComponent R M M p q) LinearMap.id
        (prodComponent R (M × M) M (p + q) r
          (map ((p + q) + r) ((δ.prodMap LinearMap.id).comp δ) x))
    rw [map_comp, LinearMap.comp_apply, prodComponent_map]
    simp only [map_id, TensorProduct.map_map, LinearMap.comp_id]
  have hright (z : ⋀[R]^(p + (q + r)) M) :
      TensorProduct.map LinearMap.id (prodComponent R M M q r)
          (prodComponent R M (M × M) p (q + r) (map (p + (q + r)) δR z)) =
        TensorProduct.map LinearMap.id (comul R M q r)
          (comul R M p (q + r) z) := by
    rw [comul_eq_prodComponent_comp_map, comul_eq_prodComponent_comp_map]
    change TensorProduct.map LinearMap.id (prodComponent R M M q r)
        (prodComponent R M (M × M) p (q + r)
          (map (p + (q + r)) ((LinearMap.id.prodMap δ).comp δ) z)) =
      TensorProduct.map LinearMap.id (prodComponent R M M q r ∘ₗ map (q + r) δ)
        (prodComponent R M M p (q + r) (map (p + (q + r)) δ z))
    rw [map_comp, LinearMap.comp_apply, prodComponent_map]
    simp only [map_id, TensorProduct.map_map, LinearMap.comp_id]
  have hdiag : map (p + (q + r)) α
      (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d ((M × M) × M))
        (Nat.add_assoc p q r) (map ((p + q) + r) δL x)) =
      map (p + (q + r)) δR
        (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d M)
          (Nat.add_assoc p q r) x) := by
    apply Subtype.ext
    simp only [coe_map, coe_cast]
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hd]
  have h := LinearMap.congr_fun (prodComponent_assoc R M M M p q r)
    (map ((p + q) + r) δL x)
  change TensorProduct.assoc R (⋀[R]^p M) (⋀[R]^q M) (⋀[R]^r M)
      (TensorProduct.map (prodComponent R M M p q) LinearMap.id
        (prodComponent R (M × M) M (p + q) r (map ((p + q) + r) δL x))) =
    TensorProduct.map LinearMap.id (prodComponent R M M q r)
      (prodComponent R M (M × M) p (q + r)
        (map (p + (q + r)) α
          (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d ((M × M) × M))
            (Nat.add_assoc p q r) (map ((p + q) + r) δL x)))) at h
  rw [hdiag, hright] at h
  change TensorProduct.assoc R (⋀[R]^p M) (⋀[R]^q M) (⋀[R]^r M)
      (TensorProduct.map (comul R M p q) LinearMap.id (comul R M (p + q) r x)) =
    TensorProduct.map LinearMap.id (comul R M q r)
      (comul R M p (q + r)
        (LinearEquiv.cast (R := R) (M := fun d : ℕ ↦ ⋀[R]^d M)
          (Nat.add_assoc p q r) x))
  rw [hleft]
  exact h

/-- On a generating wedge, the homogeneous exterior coproduct is the exterior product of the
universal alternating maps. Each signed coshuffle occurs once, without factorial coefficients. -/
@[simp]
theorem comul_ιMulti (p q : ℕ) (v : Fin (p + q) → M) :
    comul R M p q (ιMulti R (p + q) v) =
      ((ιMulti R p).domCoprod (ιMulti R q)) (v ∘ finSumFinEquiv) := by
  classical
  rw [comul_eq_prodComponent_comp_map]
  simp only [LinearMap.comp_apply, map_apply_ιMulti, prodComponent_ιMulti]
  simp only [AlternatingMap.domCoprod_apply, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  refine Quotient.inductionOn' s (fun σ ↦ ?_)
  simp only [AlternatingMap.domCoprod.summand_mk'', _root_.smul_apply,
    MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    AlternatingMap.coe_multilinearMap, AlternatingMap.compLinearMap_apply,
    Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    LinearMap.prod_apply]
  rfl

end exteriorPower
