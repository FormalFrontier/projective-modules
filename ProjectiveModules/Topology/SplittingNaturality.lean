/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Instances.Int
public import ProjectiveModules.Topology.ContinuousLinearMap.Prod
public import ProjectiveModules.Topology.Splitting

/-!
# Semilinear maps in splitting coordinates

A continuous linear section identifies a module with the product of the base and
its kernel. A semilinear map over a commuting square is triangular in these
coordinates. Its off-diagonal entry measures the failure to preserve the chosen
sections; it vanishes when the sections are compatible.

The section deviation is defined using only the target splitting, so its source
may be an additive commutative monoid. Its composition law likewise requires no
source splitting or maps on the bases, only preservation of the middle kernel.
All kernel maps below are restrictions to the given submodules.

## References

* `ContinuousLinearMap.equivProdKerOfRightInverse` in
  `ProjectiveModules.Topology.Splitting` supplies the splitting and its coordinate laws.
* Mathlib's `ContinuousLinearMap.restrict` supplies the maps between kernels;
  `ContinuousLinearEquiv.skewProd` supplies the shear illustrating the off-diagonal term.
* `ContinuousLinearMap.prodSemilinear` supplies semilinear pairing without continuity
  assumptions on addition in the base modules.
-/

@[expose] public section

universe uR uS uA uE₁ uF₁ uE₂ uF₂ uE₃ uF₃

namespace ContinuousLinearMap

/-- A semilinear map over a commuting square sends the first kernel into the second. -/
theorem map_mem_ker_of_comp_eq
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    {E₁ : Type uE₁} {F₁ : Type uF₁} {E₂ : Type uE₂} {F₂ : Type uF₂}
    [AddCommMonoid E₁] [Module R E₁] [TopologicalSpace E₁]
    [AddCommMonoid F₁] [Module R F₁] [TopologicalSpace F₁]
    [AddCommMonoid E₂] [Module S E₂] [TopologicalSpace E₂]
    [AddCommMonoid F₂] [Module S F₂] [TopologicalSpace F₂]
    {σ : R →+* S} (f₁ : E₁ →L[R] F₁) (f₂ : E₂ →L[S] F₂)
    (u : E₁ →SL[σ] E₂) (v : F₁ →SL[σ] F₂)
    (hsq : f₂.comp u = v.comp f₁) : ∀ x ∈ f₁.ker, u x ∈ f₂.ker := by
  intro x hx
  have h : f₁ x = 0 := hx
  have heq : f₂ (u x) = v (f₁ x) := DFunLike.congr_fun hsq x
  change f₂ (u x) = 0
  rw [heq, h, map_zero]

section Deviation

variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
  {E₁ : Type uE₁} {F₁ : Type uF₁} {E₂ : Type uE₂} {F₂ : Type uF₂}
  [AddCommMonoid E₁] [Module R E₁] [TopologicalSpace E₁]
  [AddCommMonoid F₁] [Module R F₁] [TopologicalSpace F₁]
  [AddCommGroup E₂] [Module S E₂] [TopologicalSpace E₂] [IsTopologicalAddGroup E₂]
  [AddCommMonoid F₂] [Module S F₂] [TopologicalSpace F₂]
  {σ : R →+* S}

/-- The kernel coordinate of the image of a chosen source section under a semilinear map.
Only the target section is required to be a right inverse. -/
def splittingDeviation (f₂ : E₂ →L[S] F₂) (s₂ : F₂ →L[S] E₂)
    (hs₂ : Function.RightInverse s₂ f₂) (u : E₁ →SL[σ] E₂) (s₁ : F₁ →L[R] E₁) :
    F₁ →SL[σ] f₂.ker :=
  (ContinuousLinearMap.snd S F₂ f₂.ker).comp
    ((f₂.equivProdKerOfRightInverse s₂ hs₂).toContinuousLinearMap.comp (u.comp s₁))

/-- Applying the deviation gives the second splitting coordinate of the image section. -/
theorem splittingDeviation_apply (f₂ : E₂ →L[S] F₂) (s₂ : F₂ →L[S] E₂)
    (hs₂ : Function.RightInverse s₂ f₂) (u : E₁ →SL[σ] E₂) (s₁ : F₁ →L[R] E₁)
    (y : F₁) :
    splittingDeviation f₂ s₂ hs₂ u s₁ y =
      (f₂.equivProdKerOfRightInverse s₂ hs₂ (u (s₁ y))).2 := rfl

/-- In the ambient target, the deviation is the residual after subtracting the target section. -/
@[simp]
theorem coe_splittingDeviation_apply (f₂ : E₂ →L[S] F₂) (s₂ : F₂ →L[S] E₂)
    (hs₂ : Function.RightInverse s₂ f₂) (u : E₁ →SL[σ] E₂) (s₁ : F₁ →L[R] E₁)
    (y : F₁) :
    (splittingDeviation f₂ s₂ hs₂ u s₁ y : E₂) =
      u (s₁ y) - s₂ (f₂ (u (s₁ y))) := by
  rw [splittingDeviation_apply, coe_snd_equivProdKerOfRightInverse]

/-- A commuting square identifies the base term in the ambient deviation formula. -/
theorem coe_splittingDeviation_apply_of_commute
    (f₁ : E₁ →L[R] F₁) (s₁ : F₁ →L[R] E₁) (hs₁ : Function.RightInverse s₁ f₁)
    (f₂ : E₂ →L[S] F₂) (s₂ : F₂ →L[S] E₂) (hs₂ : Function.RightInverse s₂ f₂)
    (u : E₁ →SL[σ] E₂) (v : F₁ →SL[σ] F₂)
    (hsq : f₂.comp u = v.comp f₁) (y : F₁) :
    (splittingDeviation f₂ s₂ hs₂ u s₁ y : E₂) = u (s₁ y) - s₂ (v y) := by
  have heq : f₂ (u (s₁ y)) = v (f₁ (s₁ y)) := DFunLike.congr_fun hsq (s₁ y)
  rw [coe_splittingDeviation_apply, heq, hs₁ y]

/-- The identity has zero deviation when the same section is used on both sides. -/
@[simp]
theorem splittingDeviation_id (f : E₂ →L[S] F₂) (s : F₂ →L[S] E₂)
    (hs : Function.RightInverse s f) :
    splittingDeviation f s hs (ContinuousLinearMap.id S E₂) s = 0 := by
  apply DFunLike.ext
  intro y
  apply Subtype.ext
  simp only [coe_splittingDeviation_apply, id_apply, hs y, sub_self, zero_apply,
    Submodule.coe_zero]

/-- A map preserving the chosen sections has zero deviation. -/
theorem splittingDeviation_eq_zero_of_commute
    (f₂ : E₂ →L[S] F₂) (s₂ : F₂ →L[S] E₂) (hs₂ : Function.RightInverse s₂ f₂)
    (u : E₁ →SL[σ] E₂) (s₁ : F₁ →L[R] E₁) (v : F₁ →SL[σ] F₂)
    (hsec : u.comp s₁ = s₂.comp v) :
    splittingDeviation f₂ s₂ hs₂ u s₁ = 0 := by
  apply DFunLike.ext
  intro y
  apply Subtype.ext
  have heq : u (s₁ y) = s₂ (v y) := DFunLike.congr_fun hsec y
  simp only [coe_splittingDeviation_apply, heq, hs₂ (v y), sub_self,
    zero_apply, Submodule.coe_zero]

end Deviation

section Composition

variable {R : Type uR} {S : Type uS} {A : Type uA}
  [Semiring R] [Semiring S] [Semiring A]
  {E₁ : Type uE₁} {F₁ : Type uF₁} {E₂ : Type uE₂} {F₂ : Type uF₂}
  {E₃ : Type uE₃} {F₃ : Type uF₃}
  [AddCommMonoid E₁] [Module R E₁] [TopologicalSpace E₁]
  [AddCommMonoid F₁] [Module R F₁] [TopologicalSpace F₁]
  [AddCommGroup E₂] [Module S E₂] [TopologicalSpace E₂] [IsTopologicalAddGroup E₂]
  [AddCommMonoid F₂] [Module S F₂] [TopologicalSpace F₂]
  [AddCommGroup E₃] [Module A E₃] [TopologicalSpace E₃] [IsTopologicalAddGroup E₃]
  [AddCommMonoid F₃] [Module A F₃] [TopologicalSpace F₃]
  {σ₁₂ : R →+* S} {σ₂₃ : S →+* A} {σ₁₃ : R →+* A}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- Deviations compose by the triangular cocycle law. The source section is arbitrary;
only the middle and target sections split, and the second map need only preserve the
middle kernel. No maps on the bases or compatibility of sections are required. -/
theorem splittingDeviation_comp
    (f₂ : E₂ →L[S] F₂) (s₂ : F₂ →L[S] E₂) (hs₂ : Function.RightInverse s₂ f₂)
    (f₃ : E₃ →L[A] F₃) (s₃ : F₃ →L[A] E₃) (hs₃ : Function.RightInverse s₃ f₃)
    (s₁ : F₁ →L[R] E₁) (u₁₂ : E₁ →SL[σ₁₂] E₂) (u₂₃ : E₂ →SL[σ₂₃] E₃)
    (hk₂₃ : ∀ x ∈ f₂.ker, u₂₃ x ∈ f₃.ker) :
    splittingDeviation f₃ s₃ hs₃ (u₂₃.comp u₁₂) s₁ =
      (splittingDeviation f₃ s₃ hs₃ u₂₃ s₂).comp (f₂.comp (u₁₂.comp s₁)) +
        (u₂₃.restrict hk₂₃).comp (splittingDeviation f₂ s₂ hs₂ u₁₂ s₁) := by
  apply DFunLike.ext
  intro y
  apply Subtype.ext
  let w := u₁₂ (s₁ y)
  let b := f₂ w
  let d : f₂.ker := splittingDeviation f₂ s₂ hs₂ u₁₂ s₁ y
  have hdecomp : w = s₂ b + (d : E₂) := by
    dsimp only [w, b, d]
    rw [coe_splittingDeviation_apply, add_comm, sub_add_cancel]
  have hzero : f₃ (u₂₃ (d : E₂)) = 0 := hk₂₃ d d.property
  have hres : u₂₃ w - s₃ (f₃ (u₂₃ w)) =
      (u₂₃ (s₂ b) - s₃ (f₃ (u₂₃ (s₂ b)))) + u₂₃ (d : E₂) := by
    calc
      _ = (u₂₃ (s₂ b) + u₂₃ (d : E₂)) - s₃ (f₃ (u₂₃ (s₂ b))) := by
        conv_lhs => rw [hdecomp]
        rw [map_add, map_add, hzero, add_zero]
      _ = _ := add_sub_right_comm _ _ _
  simpa only [comp_apply, add_apply, Submodule.coe_add, coe_splittingDeviation_apply,
    coe_restrict_apply, w, b, d] using hres

end Composition

section Naturality

variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
  {E₁ : Type uE₁} {F₁ : Type uF₁} {E₂ : Type uE₂} {F₂ : Type uF₂}
  [AddCommGroup E₁] [Module R E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁]
  [AddCommMonoid F₁] [Module R F₁] [TopologicalSpace F₁]
  [AddCommGroup E₂] [Module S E₂] [TopologicalSpace E₂] [IsTopologicalAddGroup E₂]
  [AddCommMonoid F₂] [Module S F₂] [TopologicalSpace F₂]
  {σ : R →+* S}

/-- A semilinear map over a commuting square has triangular splitting coordinates:
the off-diagonal entry is its section deviation, and the kernel entry is its restriction. -/
theorem equivProdKerOfRightInverse_map_apply
    (f₁ : E₁ →L[R] F₁) (s₁ : F₁ →L[R] E₁) (hs₁ : Function.RightInverse s₁ f₁)
    (f₂ : E₂ →L[S] F₂) (s₂ : F₂ →L[S] E₂) (hs₂ : Function.RightInverse s₂ f₂)
    (u : E₁ →SL[σ] E₂) (v : F₁ →SL[σ] F₂)
    (hsq : f₂.comp u = v.comp f₁) (y : F₁) (k : f₁.ker) :
    (f₂.equivProdKerOfRightInverse s₂ hs₂).toContinuousLinearMap.comp
        (u.comp (f₁.equivProdKerOfRightInverse s₁ hs₁).symm.toContinuousLinearMap) (y, k) =
      (v y, splittingDeviation f₂ s₂ hs₂ u s₁ y +
        u.restrict (map_mem_ker_of_comp_eq f₁ f₂ u v hsq) k) := by
  simp only [comp_apply, ContinuousLinearEquiv.coe_coe]
  apply Prod.ext
  · have hk : f₁ (k : E₁) = 0 := k.property
    rw [fst_equivProdKerOfRightInverse, ← comp_apply, hsq, comp_apply,
      equivProdKerOfRightInverse_symm_apply, map_add, hk, hs₁ y, zero_add]
  · apply Subtype.ext
    have hzero : f₂ (u (k : E₁)) = 0 :=
      map_mem_ker_of_comp_eq f₁ f₂ u v hsq k k.property
    rw [coe_snd_equivProdKerOfRightInverse, equivProdKerOfRightInverse_symm_apply,
      Submodule.coe_add, coe_splittingDeviation_apply, coe_restrict_apply,
      map_add, map_add, hzero, zero_add, add_comm (u (k : E₁)), add_sub_right_comm]

/-- The triangular coordinate formula as an equality of whole continuous semilinear maps.
There is no requirement that the two chosen sections be compatible. -/
theorem equivProdKerOfRightInverse_map
    (f₁ : E₁ →L[R] F₁) (s₁ : F₁ →L[R] E₁) (hs₁ : Function.RightInverse s₁ f₁)
    (f₂ : E₂ →L[S] F₂) (s₂ : F₂ →L[S] E₂) (hs₂ : Function.RightInverse s₂ f₂)
    (u : E₁ →SL[σ] E₂) (v : F₁ →SL[σ] F₂)
    (hsq : f₂.comp u = v.comp f₁) :
    (f₂.equivProdKerOfRightInverse s₂ hs₂).toContinuousLinearMap.comp
        (u.comp (f₁.equivProdKerOfRightInverse s₁ hs₁).symm.toContinuousLinearMap) =
      prodSemilinear (v.comp (ContinuousLinearMap.fst R F₁ f₁.ker))
        ((splittingDeviation f₂ s₂ hs₂ u s₁).comp (ContinuousLinearMap.fst R F₁ f₁.ker) +
          (u.restrict (map_mem_ker_of_comp_eq f₁ f₂ u v hsq)).comp
            (ContinuousLinearMap.snd R F₁ f₁.ker)) := by
  apply DFunLike.ext
  rintro ⟨y, k⟩
  simpa only [prodSemilinear_apply, comp_apply, add_apply, coe_fst', coe_snd'] using
    equivProdKerOfRightInverse_map_apply f₁ s₁ hs₁ f₂ s₂ hs₂ u v hsq y k

/-- Preservation of the chosen sections makes the whole coordinate map diagonal. -/
theorem equivProdKerOfRightInverse_map_of_commute
    (f₁ : E₁ →L[R] F₁) (s₁ : F₁ →L[R] E₁) (hs₁ : Function.RightInverse s₁ f₁)
    (f₂ : E₂ →L[S] F₂) (s₂ : F₂ →L[S] E₂) (hs₂ : Function.RightInverse s₂ f₂)
    (u : E₁ →SL[σ] E₂) (v : F₁ →SL[σ] F₂)
    (hsq : f₂.comp u = v.comp f₁) (hsec : u.comp s₁ = s₂.comp v) :
    (f₂.equivProdKerOfRightInverse s₂ hs₂).toContinuousLinearMap.comp
        (u.comp (f₁.equivProdKerOfRightInverse s₁ hs₁).symm.toContinuousLinearMap) =
      prodSemilinear (v.comp (ContinuousLinearMap.fst R F₁ f₁.ker))
        ((u.restrict (map_mem_ker_of_comp_eq f₁ f₂ u v hsq)).comp
          (ContinuousLinearMap.snd R F₁ f₁.ker)) := by
  rw [equivProdKerOfRightInverse_map f₁ s₁ hs₁ f₂ s₂ hs₂ u v hsq,
    splittingDeviation_eq_zero_of_commute f₂ s₂ hs₂ u s₁ v hsec,
    zero_comp, zero_add]

end Naturality

/-- The integral shear over the semiring of natural numbers has a genuinely nonzero
section deviation in the kernel of the first projection. Its coordinate map is given
by the triangular theorem, while the ambient deviation at `y` is `(0, y)`. -/
theorem equivProdKerOfRightInverse_skewProd :
    let f := ContinuousLinearMap.fst ℕ ℤ ℤ
    let s := ContinuousLinearMap.inl ℕ ℤ ℤ
    let hs : Function.RightInverse s f := fun _ => rfl
    let u := (ContinuousLinearEquiv.skewProd (ContinuousLinearEquiv.refl ℕ ℤ)
      (ContinuousLinearEquiv.refl ℕ ℤ) (ContinuousLinearMap.id ℕ ℤ)).toContinuousLinearMap
    let v := ContinuousLinearMap.id ℕ ℤ
    let hsq : f.comp u = v.comp f := by
      apply DFunLike.ext
      intro x
      simp [f, u, v, ContinuousLinearEquiv.skewProd_apply]
    let K := u.restrict (map_mem_ker_of_comp_eq f f u v hsq)
    let D := splittingDeviation f s hs u s
    let χ := f.equivProdKerOfRightInverse s hs
    (χ.toContinuousLinearMap.comp (u.comp χ.symm.toContinuousLinearMap) =
      prodSemilinear (v.comp (ContinuousLinearMap.fst ℕ ℤ f.ker))
        (D.comp (ContinuousLinearMap.fst ℕ ℤ f.ker) +
          K.comp (ContinuousLinearMap.snd ℕ ℤ f.ker))) ∧
      (∀ y : ℤ, (D y : ℤ × ℤ) = (0, y)) ∧ D 1 ≠ 0 := by
  dsimp only
  let f := ContinuousLinearMap.fst ℕ ℤ ℤ
  let s := ContinuousLinearMap.inl ℕ ℤ ℤ
  let hs : Function.RightInverse s f := fun _ => rfl
  let u := (ContinuousLinearEquiv.skewProd (ContinuousLinearEquiv.refl ℕ ℤ)
    (ContinuousLinearEquiv.refl ℕ ℤ) (ContinuousLinearMap.id ℕ ℤ)).toContinuousLinearMap
  let v := ContinuousLinearMap.id ℕ ℤ
  have hsq : f.comp u = v.comp f := by
    apply DFunLike.ext
    intro x
    simp [f, u, v, ContinuousLinearEquiv.skewProd_apply]
  have hamb (y : ℤ) : (splittingDeviation f s hs u s y : ℤ × ℤ) = (0, y) := by
    rw [coe_splittingDeviation_apply_of_commute f s hs f s hs u v hsq]
    simp [s, u, v, ContinuousLinearEquiv.skewProd_apply]
  refine ⟨equivProdKerOfRightInverse_map f s hs f s hs u v hsq, hamb, ?_⟩
  intro h
  have hcoe := congrArg (fun k : f.ker => (k : ℤ × ℤ)) h
  have hone : (1 : ℤ) = 0 := congrArg Prod.snd ((hamb 1).symm.trans hcoe)
  exact one_ne_zero hone

end ContinuousLinearMap
