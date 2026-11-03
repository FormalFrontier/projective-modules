/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.Quadratic
public import ProjectiveModules.TensorPower.Quadratic
import ProjectiveModules.ExteriorPower.Antisymmetrization
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.FinCases

/-!
# The tensor square of a projective module

Antisymmetrization identifies the second exterior power of a projective module with the
kernel of its symmetric quotient. Consequently its tensor square is isomorphic to the
product of its second exterior and symmetric powers. The isomorphism depends on a choice
of section of the symmetric quotient; no natural choice of section is asserted.

There is no finite-generation or characteristic restriction on the module or base ring.
Finite tensor indices are lifted to the universe of the base ring in the symmetric-power
construction.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe uR uM

namespace exteriorPower

variable (R : Type uR) [CommRing R]
variable (M : Type uM) [AddCommGroup M] [Module R M]

private theorem toTensorPower_ιMulti_two (v : Fin 2 → M) :
    toTensorPower R M 2 ((ιMulti (R := R) (n := 2) (M := M)) v) =
      PiTensorProduct.tprod R v -
        PiTensorProduct.tprod R (v ∘ Equiv.swap (0 : Fin 2) 1) := by
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap (0 : Fin 2) 1} := by decide
  have hswap : (Equiv.swap (0 : Fin 2) 1 : Equiv.Perm (Fin 2)) ≠ 1 := by
    decide
  classical
  rw [exteriorPower.toTensorPower_apply_ιMulti]
  simp [hperm, Ne.symm hswap, sub_eq_add_neg]
  congr 1

/-- Binary and indexed antisymmetrization agree under the tensor-square comparison. -/
theorem tensorSquareEquiv_comp_toTensorSquare :
    (TensorPower.tensorSquareEquiv R M).toLinearMap.comp (toTensorSquare R M) =
      toTensorPower R M 2 := by
  ext v
  change TensorPower.tensorSquareEquiv R M
      (toTensorSquare R M ((ιMulti (R := R) (n := 2) (M := M)) v)) =
    toTensorPower R M 2 ((ιMulti (R := R) (n := 2) (M := M)) v)
  have hv : ![v 0, v 1] = v := by
    funext i
    fin_cases i <;> rfl
  have hrev : ![v 1, v 0] = v ∘ Equiv.swap (0 : Fin 2) 1 := by
    funext i
    fin_cases i <;> simp
  rw [toTensorSquare_ιMulti, map_sub,
    TensorPower.tensorSquareEquiv_tmul R M (v 0) (v 1),
    TensorPower.tensorSquareEquiv_tmul R M (v 1) (v 0),
    hv, hrev, toTensorPower_ιMulti_two R M v]

/-- Antisymmetrization into the tensor square is injective for a projective module.
See Weibel, *The K-book: An Introduction to Algebraic K-theory*. -/
theorem toTensorSquare_injective [Module.Projective R M] :
    Function.Injective (toTensorSquare R M) := by
  intro x y h
  have hx :
      TensorPower.tensorSquareEquiv R M (toTensorSquare R M x) =
        toTensorPower R M 2 x :=
    LinearMap.congr_fun (tensorSquareEquiv_comp_toTensorSquare R M) x
  have hy :
      TensorPower.tensorSquareEquiv R M (toTensorSquare R M y) =
        toTensorPower R M 2 y :=
    LinearMap.congr_fun (tensorSquareEquiv_comp_toTensorSquare R M) y
  apply exteriorPower.toTensorPower_injective (R := R) (M := M) (n := 2)
  exact hx.symm.trans ((congrArg (TensorPower.tensorSquareEquiv R M) h).trans hy)

/-- The tensor square of a projective module decomposes as its alternating and symmetric
quadratic powers, with antisymmetrization as the first inclusion and the symmetric
quotient as the second projection. The decomposition need not be chosen naturally.
See Weibel, *The K-book: An Introduction to Algebraic K-theory*. -/
theorem exists_tensorSquareEquiv [Module.Projective R M] :
    ∃ e : (M ⊗[R] M) ≃ₗ[R]
        ((⋀[R]^2 M) × SymmetricPower R (ULift.{uR} (Fin 2)) M),
      (∀ z, e (toTensorSquare R M z) = (z, 0)) ∧
        ∀ t, (e t).2 = SymmetricPower.tensorSquareQuotient R M t := by
  let E := ⋀[R]^2 M
  let T := M ⊗[R] M
  let S := SymmetricPower R (ULift.{uR} (Fin 2)) M
  let a : E →ₗ[R] T := toTensorSquare R M
  let q : T →ₗ[R] S := SymmetricPower.tensorSquareQuotient R M
  have ha : Function.Injective a := toTensorSquare_injective R M
  have hq : Function.Surjective q :=
    SymmetricPower.tensorSquareQuotient_surjective R M
  have hker : LinearMap.ker q = LinearMap.range a :=
    ker_tensorSquareQuotient R M
  obtain ⟨s, hs⟩ : ∃ s : S →ₗ[R] T, q.comp s = LinearMap.id := by
    exact SymmetricPower.exists_tensorSquareQuotient_section R M
  have hs_apply (y : S) : q (s y) = y :=
    congrArg (fun v : S →ₗ[R] S => v y) hs
  have hqa (z : E) : q (a z) = 0 := by
    have hz : a z ∈ LinearMap.ker q := by
      rw [hker]
      exact ⟨z, rfl⟩
    exact hz
  -- Identify the first factor with the kernel, using exactness and injectivity.
  let aK : E →ₗ[R] LinearMap.ker q :=
    a.codRestrict (LinearMap.ker q) (fun z => by
      rw [hker]
      exact ⟨z, rfl⟩)
  have haK : Function.Bijective aK := by
    constructor
    · intro z w h
      apply ha
      exact congrArg (fun v : LinearMap.ker q => (v : T)) h
    · intro t
      have ht : (t : T) ∈ LinearMap.range a := by
        rw [← hker]
        exact t.property
      obtain ⟨z, hz⟩ := ht
      refine ⟨z, ?_⟩
      apply Subtype.ext
      exact hz
  let aE : E ≃ₗ[R] LinearMap.ker q := LinearEquiv.ofBijective aK haK
  -- The section produces the projection to the kernel, hence a retraction of a.
  let p : T →ₗ[R] LinearMap.ker q :=
    (LinearMap.id - s.comp q).codRestrict (LinearMap.ker q) (fun t => by
      change q (t - s (q t)) = 0
      rw [map_sub, hs_apply, sub_self])
  let f : T →ₗ[R] E := aE.symm.toLinearMap.comp p
  have hfa (z : E) : f (a z) = z := by
    change aE.symm (p (a z)) = z
    apply aE.injective
    rw [aE.apply_symm_apply]
    apply Subtype.ext
    change a z - s (q (a z)) = a z
    rw [hqa, map_zero, sub_zero]
  have hfs (y : S) : f (s y) = 0 := by
    have hps : p (s y) = 0 := by
      apply Subtype.ext
      change s y - s (q (s y)) = 0
      rw [hs_apply, sub_self]
    change aE.symm (p (s y)) = 0
    rw [hps, map_zero]
  have hdecomp (t : T) : a (f t) + s (q t) = t := by
    have h := congrArg (fun v : LinearMap.ker q => (v : T))
      (aE.apply_symm_apply (p t))
    change a (f t) = t - s (q t) at h
    rw [h, sub_add_cancel]
  have hf : Function.Surjective f := by
    intro z
    exact ⟨a z, hfa z⟩
  have hcompl : IsCompl (LinearMap.ker f) (LinearMap.ker q) := by
    constructor
    · apply disjoint_iff_inf_le.mpr
      intro t ht
      change t = 0
      have hqt : t ∈ LinearMap.range a := by
        rw [← hker]
        exact ht.2
      obtain ⟨z, rfl⟩ := hqt
      have hz : z = 0 := (hfa z).symm.trans ht.1
      rw [hz, map_zero]
    · apply codisjoint_iff_le_sup.mpr
      intro t _
      apply Submodule.mem_sup.mpr
      refine ⟨s (q t), ?_, a (f t), ?_, ?_⟩
      · exact hfs (q t)
      · exact hqa (f t)
      · exact (add_comm _ _).trans (hdecomp t)
  -- The complementary kernels give the product decomposition.
  have hfr : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hf
  have hqr : LinearMap.range q = ⊤ := LinearMap.range_eq_top.mpr hq
  let e : T ≃ₗ[R] E × S :=
    LinearMap.equivProdOfSurjectiveOfIsCompl f q hfr hqr hcompl
  have he (t : T) : e t = (f t, q t) := by
    exact LinearMap.equivProdOfSurjectiveOfIsCompl_apply (f := f) (g := q) hfr hqr hcompl t
  refine ⟨e, ?_, ?_⟩
  · intro z
    change e (a z) = (z, 0)
    rw [he, hfa, hqa]
  · intro t
    change (e t).2 = q t
    rw [he]

end exteriorPower
