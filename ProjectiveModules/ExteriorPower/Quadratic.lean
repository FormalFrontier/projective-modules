/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.LinearAlgebra.TensorPower.Basic

public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Logic.Equiv.Defs
public import ProjectiveModules.Module.SymmetricPower.Basis

/-!
# The quadratic exterior–tensor–symmetric sequence

The canonical antisymmetrization from the exterior square to the tensor square and the
canonical quotient from the tensor square to the symmetric square are natural linear maps.
The quotient is surjective and its kernel is the image of antisymmetrization. For a
projective module, the quotient admits a linear section.

The symmetric square uses the scalar-universe-aligned index `ULift (Fin 2)` and the
existing symmetric-power quotient and scalar action. A section is asserted to exist for
projective modules, without asserting a canonical or natural choice of section.

The ring-level quadratic Koszul comparison is described in Weibel's *The K-book*.
The quotient-only construction and its projective-section API are stated over
commutative semirings here, generalizing that ring-level setting.

The indexed antisymmetrization is Mathlib's `exteriorPower.toTensorPower`, and the
symmetric quotient uses `SymmetricPower.mk`. The private binary identifications compose
Mathlib's reindexing, tensor-decomposition, and singleton linear equivalences.

## References

* Charles A. Weibel, *The K-book: An introduction to Algebraic K-theory* (2013).
* The Mathlib contributors, *Mathlib*: exterior powers, symmetric powers, and tensor
  products.
-/

@[expose] public section

open scoped TensorProduct

universe uR uM uN

section CommSemiring

variable (R : Type uR) [CommSemiring R]
variable (M : Type uM) [AddCommMonoid M] [Module R M]

/-- The fixed ordered identification of the two indices with a sum of singleton indices. -/
private def finTwoEquivSumUnit : Fin 2 ≃ Unit ⊕ Unit where
  toFun i := if i = 0 then Sum.inl () else Sum.inr ()
  invFun := Sum.elim (fun _ => 0) (fun _ => 1)
  left_inv := by decide
  right_inv := by decide

/-- The canonical ordered identification of the degree-two tensor power with a binary tensor. -/
private noncomputable def tensorPowerTwoEquivTensorSquare :
    TensorPower R 2 M ≃ₗ[R] TensorProduct R M M :=
  (PiTensorProduct.reindex R (fun _ : Fin 2 => M) finTwoEquivSumUnit).trans
    ((PiTensorProduct.tmulEquiv (ι := Unit) (ι₂ := Unit) R M).symm.trans
      (TensorProduct.congr
        (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Unit => M) ())
        (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Unit => M) ())))

/-- The identification evaluates every indexed pure tensor in the order `0`, then `1`. -/
private theorem tensorPowerTwoEquivTensorSquare_tprod (v : Fin 2 → M) :
    tensorPowerTwoEquivTensorSquare R M (PiTensorProduct.tprod R v) =
      TensorProduct.tmul R (v 0) (v 1) := by
  change
    TensorProduct.congr
      (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Unit => M) ())
      (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Unit => M) ())
      ((PiTensorProduct.tmulEquiv (ι := Unit) (ι₂ := Unit) R M).symm
        (PiTensorProduct.reindex R (fun _ : Fin 2 => M) finTwoEquivSumUnit
          (PiTensorProduct.tprod R v))) =
      TensorProduct.tmul R (v 0) (v 1)
  rw [PiTensorProduct.reindex_tprod, PiTensorProduct.tmulEquiv_symm_apply,
    TensorProduct.congr_tmul, PiTensorProduct.subsingletonEquiv_apply_tprod,
    PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

/-- The inverse sends a binary pure tensor to the indexed tensor with its two ordered entries. -/
private theorem tensorPowerTwoEquivTensorSquare_symm_tmul (x y : M) :
    (tensorPowerTwoEquivTensorSquare R M).symm (TensorProduct.tmul R x y) =
      PiTensorProduct.tprod R (fun i : Fin 2 => if i = 0 then x else y) := by
  have h :
      tensorPowerTwoEquivTensorSquare R M
          (PiTensorProduct.tprod R (fun i : Fin 2 => if i = 0 then x else y)) =
        TensorProduct.tmul R x y := by
    rw [tensorPowerTwoEquivTensorSquare_tprod]
    rfl
  calc
    (tensorPowerTwoEquivTensorSquare R M).symm (TensorProduct.tmul R x y) =
        (tensorPowerTwoEquivTensorSquare R M).symm
          (tensorPowerTwoEquivTensorSquare R M
            (PiTensorProduct.tprod R (fun i : Fin 2 => if i = 0 then x else y))) :=
      congrArg (tensorPowerTwoEquivTensorSquare R M).symm h.symm
    _ = PiTensorProduct.tprod R (fun i : Fin 2 => if i = 0 then x else y) :=
      (tensorPowerTwoEquivTensorSquare R M).symm_apply_apply _

private noncomputable def tensorSquareEquivLiftedPiTensorTwo :
    TensorProduct R M M ≃ₗ[R]
      PiTensorProduct R (fun _ : ULift.{uR} (Fin 2) => M) :=
  (tensorPowerTwoEquivTensorSquare R M).symm.trans
    (PiTensorProduct.reindex R (fun _ : Fin 2 => M)
      (Equiv.ulift : ULift.{uR} (Fin 2) ≃ Fin 2).symm)

private theorem tensorSquareEquivLiftedPiTensorTwo_tmul (v : Fin 2 → M) :
    tensorSquareEquivLiftedPiTensorTwo R M (v 0 ⊗ₜ[R] v 1) =
      PiTensorProduct.tprod R (fun i : ULift.{uR} (Fin 2) => v i.down) := by
  have h :
      (tensorPowerTwoEquivTensorSquare R M).symm (v 0 ⊗ₜ[R] v 1) =
        PiTensorProduct.tprod R v := by
    calc
      _ = (tensorPowerTwoEquivTensorSquare R M).symm
          (tensorPowerTwoEquivTensorSquare R M (PiTensorProduct.tprod R v)) :=
        congrArg (tensorPowerTwoEquivTensorSquare R M).symm
          (tensorPowerTwoEquivTensorSquare_tprod R M v).symm
      _ = _ := (tensorPowerTwoEquivTensorSquare R M).symm_apply_apply _
  change PiTensorProduct.reindex R (fun _ : Fin 2 => M)
      (Equiv.ulift : ULift.{uR} (Fin 2) ≃ Fin 2).symm
      ((tensorPowerTwoEquivTensorSquare R M).symm (v 0 ⊗ₜ[R] v 1)) = _
  calc
    _ = PiTensorProduct.reindex R (fun _ : Fin 2 => M)
        (Equiv.ulift : ULift.{uR} (Fin 2) ≃ Fin 2).symm
        (PiTensorProduct.tprod R v) :=
      congrArg (PiTensorProduct.reindex R (fun _ : Fin 2 => M)
        (Equiv.ulift : ULift.{uR} (Fin 2) ≃ Fin 2).symm) h
    _ = _ := PiTensorProduct.reindex_tprod
      (Equiv.ulift : ULift.{uR} (Fin 2) ≃ Fin 2).symm v

namespace SymmetricPower

/-- The canonical quotient from the tensor square to the symmetric square. -/
@[no_expose] noncomputable def tensorSquareQuotient :
    TensorProduct R M M →ₗ[R] SymmetricPower R (ULift.{uR} (Fin 2)) M :=
  (SymmetricPower.mk R (ULift.{uR} (Fin 2)) M).comp
    (tensorSquareEquivLiftedPiTensorTwo R M).toLinearMap

/-- The tensor-square quotient sends an ordered pure tensor to its symmetric product. -/
@[simp] theorem tensorSquareQuotient_tmul (x y : M) :
    tensorSquareQuotient R M (x ⊗ₜ[R] y) =
      SymmetricPower.tprod R
        (fun i : ULift.{uR} (Fin 2) => if i.down = 0 then x else y) := by
  have h :
      tensorSquareEquivLiftedPiTensorTwo R M (x ⊗ₜ[R] y) =
        PiTensorProduct.tprod R
          (fun i : ULift.{uR} (Fin 2) => if i.down = 0 then x else y) :=
    tensorSquareEquivLiftedPiTensorTwo_tmul R M
      (fun i : Fin 2 => if i = 0 then x else y)
  change SymmetricPower.mk R (ULift.{uR} (Fin 2)) M
      (tensorSquareEquivLiftedPiTensorTwo R M (x ⊗ₜ[R] y)) = _
  exact (congrArg (SymmetricPower.mk R (ULift.{uR} (Fin 2)) M) h).trans
    (SymmetricPower.mk_tprod _)

/-- The pure-tensor formula uniquely determines the tensor-square quotient. -/
theorem tensorSquareQuotient_unique
    (f : TensorProduct R M M →ₗ[R] SymmetricPower R (ULift.{uR} (Fin 2)) M)
    (hf : ∀ x y : M, f (x ⊗ₜ[R] y) =
      SymmetricPower.tprod R
        (fun i : ULift.{uR} (Fin 2) => if i.down = 0 then x else y)) :
    f = tensorSquareQuotient R M := by
  apply TensorProduct.ext'
  intro x y
  exact (hf x y).trans (tensorSquareQuotient_tmul R M x y).symm

/-- The tensor-square quotient is natural in the module. -/
theorem tensorSquareQuotient_natural
    {N : Type uN} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    (SymmetricPower.map (ι := ULift.{uR} (Fin 2)) f).comp
        (tensorSquareQuotient R M) =
      (tensorSquareQuotient R N).comp (TensorProduct.map f f) := by
  apply TensorProduct.ext'
  intro x y
  change SymmetricPower.map (ι := ULift.{uR} (Fin 2)) f
      (tensorSquareQuotient R M (x ⊗ₜ[R] y)) =
    tensorSquareQuotient R N (TensorProduct.map f f (x ⊗ₜ[R] y))
  rw [tensorSquareQuotient_tmul, TensorProduct.map_tmul,
    tensorSquareQuotient_tmul, SymmetricPower.map_tprod]
  congr 1
  funext i
  by_cases hi : i.down = 0 <;> simp [hi]

/-- Every symmetric square element has a preimage in the tensor square. -/
theorem tensorSquareQuotient_surjective :
    Function.Surjective (tensorSquareQuotient R M) := by
  intro z
  obtain ⟨t, ht⟩ := SymmetricPower.mk_surjective
    (R := R) (ι := ULift.{uR} (Fin 2)) (M := M) z
  refine ⟨(tensorSquareEquivLiftedPiTensorTwo R M).symm t, ?_⟩
  change SymmetricPower.mk R (ULift.{uR} (Fin 2)) M
      (tensorSquareEquivLiftedPiTensorTwo R M
        ((tensorSquareEquivLiftedPiTensorTwo R M).symm t)) = z
  calc
    _ = SymmetricPower.mk R (ULift.{uR} (Fin 2)) M t :=
      congrArg (SymmetricPower.mk R (ULift.{uR} (Fin 2)) M)
        ((tensorSquareEquivLiftedPiTensorTwo R M).symm.symm_apply_apply t)
    _ = z := ht

/-- For a projective module, the tensor-square quotient has a linear section.

This semiring formulation generalizes the ring-level projective splitting associated
with the quadratic Koszul comparison; see the module references. -/
theorem exists_tensorSquareQuotient_section [Module.Projective R M] :
    ∃ s : SymmetricPower R (ULift.{uR} (Fin 2)) M →ₗ[R] TensorProduct R M M,
      (tensorSquareQuotient R M).comp s = LinearMap.id := by
  exact Module.projective_lifting_property
    (tensorSquareQuotient R M) LinearMap.id
    (tensorSquareQuotient_surjective R M)

end SymmetricPower

end CommSemiring

section CommRing

variable (R : Type uR) [CommRing R]
variable (M : Type uM) [AddCommGroup M] [Module R M]

namespace exteriorPower

/-- Antisymmetrization from the exterior square to the binary tensor square. -/
@[no_expose] noncomputable def toTensorSquare :
    ExteriorAlgebra.exteriorPower R 2 M →ₗ[R] TensorProduct R M M :=
  (tensorPowerTwoEquivTensorSquare R M).toLinearMap.comp
    (exteriorPower.toTensorPower R M 2)

/-- Antisymmetrization sends a wedge to the difference of the ordered pure tensors. -/
@[simp] theorem toTensorSquare_ιMulti (v : Fin 2 → M) :
    toTensorSquare R M (exteriorPower.ιMulti R 2 v) =
      v 0 ⊗ₜ[R] v 1 - v 1 ⊗ₜ[R] v 0 := by
  classical
  have hperms : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by decide
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  change tensorPowerTwoEquivTensorSquare R M
    (exteriorPower.toTensorPower R M 2 (exteriorPower.ιMulti R 2 v)) = _
  rw [exteriorPower.toTensorPower_apply_ιMulti, hperms]
  simp [hne, tensorPowerTwoEquivTensorSquare_tprod, sub_eq_add_neg]

/-- The wedge-generator formula uniquely determines binary antisymmetrization. -/
theorem toTensorSquare_unique
    (f : ExteriorAlgebra.exteriorPower R 2 M →ₗ[R] TensorProduct R M M)
    (hf : ∀ v : Fin 2 → M, f (exteriorPower.ιMulti R 2 v) =
      v 0 ⊗ₜ[R] v 1 - v 1 ⊗ₜ[R] v 0) :
    f = toTensorSquare R M := by
  apply exteriorPower.linearMap_ext
  apply DFunLike.ext
  intro v
  exact (hf v).trans (toTensorSquare_ιMulti R M v).symm

/-- Binary antisymmetrization is natural in the module. -/
theorem toTensorSquare_natural
    {N : Type uN} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (TensorProduct.map f f).comp (toTensorSquare R M) =
      (toTensorSquare R N).comp (exteriorPower.map 2 f) := by
  apply exteriorPower.linearMap_ext
  apply DFunLike.ext
  intro v
  change TensorProduct.map f f
      (toTensorSquare R M (exteriorPower.ιMulti R 2 v)) =
    toTensorSquare R N (exteriorPower.map 2 f (exteriorPower.ιMulti R 2 v))
  rw [toTensorSquare_ιMulti, map_sub, TensorProduct.map_tmul,
    TensorProduct.map_tmul, exteriorPower.map_apply_ιMulti, toTensorSquare_ιMulti]
  rfl

/-- The symmetric quotient kills antisymmetrization. -/
@[simp] theorem tensorSquareQuotient_comp_toTensorSquare :
    (SymmetricPower.tensorSquareQuotient R M).comp (toTensorSquare R M) = 0 := by
  apply exteriorPower.linearMap_ext
  apply DFunLike.ext
  intro v
  change SymmetricPower.tensorSquareQuotient R M
    (toTensorSquare R M (exteriorPower.ιMulti R 2 v)) = 0
  rw [toTensorSquare_ιMulti, map_sub,
    SymmetricPower.tensorSquareQuotient_tmul,
    SymmetricPower.tensorSquareQuotient_tmul, sub_eq_zero]
  let e : Equiv.Perm (ULift.{uR} (Fin 2)) :=
    (Equiv.ulift : ULift.{uR} (Fin 2) ≃ Fin 2).trans
      ((Equiv.swap (0 : Fin 2) 1).trans
        (Equiv.ulift : ULift.{uR} (Fin 2) ≃ Fin 2).symm)
  have hswap :
      (fun i : ULift.{uR} (Fin 2) => if (e i).down = 0 then v 0 else v 1) =
        (fun i : ULift.{uR} (Fin 2) => if i.down = 0 then v 1 else v 0) := by
    funext i
    have hi : i.down = 0 ∨ i.down = 1 :=
      (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1) i.down
    rcases hi with hi | hi
    · simp [e, hi]
    · simp [e, hi]
  have hs := SymmetricPower.tprod_equiv (R := R) e
    (fun i : ULift.{uR} (Fin 2) => if i.down = 0 then v 0 else v 1)
  change SymmetricPower.tprod R
      (fun i : ULift.{uR} (Fin 2) => if (e i).down = 0 then v 0 else v 1) =
    SymmetricPower.tprod R
      (fun i : ULift.{uR} (Fin 2) => if i.down = 0 then v 0 else v 1) at hs
  rw [hswap] at hs
  exact hs.symm

/-- The quadratic exterior–tensor–symmetric sequence is exact at the tensor square.

See the module references for the mathematical source of the quadratic comparison. -/
theorem ker_tensorSquareQuotient :
    LinearMap.ker (SymmetricPower.tensorSquareQuotient R M) =
      LinearMap.range (toTensorSquare R M) := by
  classical
  let K : Submodule R (TensorProduct R M M) := LinearMap.range (toTensorSquare R M)
  let π : TensorProduct R M M →ₗ[R] (TensorProduct R M M) ⧸ K := K.mkQ
  have hswap (x y : M) : π (x ⊗ₜ[R] y) = π (y ⊗ₜ[R] x) := by
    apply (Submodule.Quotient.eq K).2
    refine ⟨exteriorPower.ιMulti R 2 (fun i : Fin 2 => if i = 0 then x else y), ?_⟩
    rw [toTensorSquare_ιMulti]
    rfl
  let f : MultilinearMap R (fun _ : ULift.{uR} (Fin 2) => M)
      ((TensorProduct R M M) ⧸ K) :=
    (π.comp (tensorSquareEquivLiftedPiTensorTwo R M).symm.toLinearMap).compMultilinearMap
      (PiTensorProduct.tprod R)
  have hf (v : ULift.{uR} (Fin 2) → M) :
      f v = π (v ⟨0⟩ ⊗ₜ[R] v ⟨1⟩) := by
    change π ((tensorSquareEquivLiftedPiTensorTwo R M).symm
      (PiTensorProduct.tprod R v)) = π (v ⟨0⟩ ⊗ₜ[R] v ⟨1⟩)
    apply congrArg π
    have h := congrArg (tensorSquareEquivLiftedPiTensorTwo R M).symm
      (tensorSquareEquivLiftedPiTensorTwo_tmul R M (fun i : Fin 2 => v ⟨i⟩))
    rw [(tensorSquareEquivLiftedPiTensorTwo R M).symm_apply_apply] at h
    exact h.symm
  have htwo (i : ULift.{uR} (Fin 2)) : i = ⟨0⟩ ∨ i = ⟨1⟩ := by
    rcases i with ⟨i⟩
    have h : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    rcases h i with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hsymm (e : Equiv.Perm (ULift.{uR} (Fin 2)))
      (v : ULift.{uR} (Fin 2) → M) : f (fun i => v (e i)) = f v := by
    rw [hf, hf]
    have hne : e ⟨0⟩ ≠ e ⟨1⟩ := by
      intro h
      exact (by decide : (⟨0⟩ : ULift.{uR} (Fin 2)) ≠ ⟨1⟩) (e.injective h)
    rcases htwo (e ⟨0⟩) with h0 | h0
    · rcases htwo (e ⟨1⟩) with h1 | h1
      · exact (hne (h0.trans h1.symm)).elim
      · rw [h0, h1]
    · rcases htwo (e ⟨1⟩) with h1 | h1
      · rw [h0, h1]
        exact hswap _ _
      · exact (hne (h0.trans h1.symm)).elim
  let P : SymmetricPower R (ULift.{uR} (Fin 2)) M →ₗ[R]
      (TensorProduct R M M) ⧸ K := SymmetricPower.lift f hsymm
  have hP : P.comp (SymmetricPower.tensorSquareQuotient R M) = π := by
    apply TensorProduct.ext'
    intro x y
    change SymmetricPower.lift f hsymm
      (SymmetricPower.tensorSquareQuotient R M (x ⊗ₜ[R] y)) = π (x ⊗ₜ[R] y)
    rw [SymmetricPower.tensorSquareQuotient_tmul, SymmetricPower.lift_tprod, hf]
    rfl
  apply le_antisymm
  · intro t ht
    change SymmetricPower.tensorSquareQuotient R M t = 0 at ht
    have hπ : π t = 0 := by
      have h := congrArg
        (fun g : TensorProduct R M M →ₗ[R] (TensorProduct R M M) ⧸ K => g t) hP
      change P (SymmetricPower.tensorSquareQuotient R M t) = π t at h
      rw [ht, LinearMap.map_zero] at h
      exact h.symm
    have hkt : t ∈ LinearMap.ker K.mkQ := hπ
    rw [Submodule.ker_mkQ] at hkt
    exact hkt
  · rintro t ⟨w, rfl⟩
    change SymmetricPower.tensorSquareQuotient R M (toTensorSquare R M w) = 0
    have h := congrArg
      (fun g : ExteriorAlgebra.exteriorPower R 2 M →ₗ[R]
        SymmetricPower R (ULift.{uR} (Fin 2)) M => g w)
      (tensorSquareQuotient_comp_toTensorSquare R M)
    exact h

end exteriorPower

end CommRing
