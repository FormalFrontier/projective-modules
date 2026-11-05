/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import ProjectiveModules.Topology.ContinuousLinearMap.Prod

/-!
# Semilinear maps between pullbacks

Two commuting squares induce a continuous semilinear map between the equalizer
submodules defining two pullbacks. The map is the restriction of the ambient
coordinatewise map. All six modules may be additive commutative monoids with
arbitrary given topologies; no continuity of their operations is needed.

The restricted projections characterize this map uniquely. Identity and composition
of diagrams agree with identity and composition of the induced maps.

## References

* Mathlib's `LinearMap.eqLocus` and `ContinuousLinearMap.restrict` supply the
  equalizer submodules and restrictions with their induced topologies.
* `ProjectiveModules.Topology.ContinuousLinearMap.Prod` supplies the continuous
  semilinear pairing used for the ambient map.
-/

@[expose] public section

universe uR uS uE₁ uF₁ uG₁ uE₂ uF₂ uG₂

namespace ContinuousLinearMap

section Map

variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S] {σ : R →+* S}
  {E₁ : Type uE₁} {F₁ : Type uF₁} {G₁ : Type uG₁}
  {E₂ : Type uE₂} {F₂ : Type uF₂} {G₂ : Type uG₂}
  [AddCommMonoid E₁] [Module R E₁] [TopologicalSpace E₁]
  [AddCommMonoid F₁] [Module R F₁] [TopologicalSpace F₁]
  [AddCommMonoid G₁] [Module R G₁] [TopologicalSpace G₁]
  [AddCommMonoid E₂] [Module S E₂] [TopologicalSpace E₂]
  [AddCommMonoid F₂] [Module S F₂] [TopologicalSpace F₂]
  [AddCommMonoid G₂] [Module S G₂] [TopologicalSpace G₂]
  (f₁ : E₁ →L[R] F₁) (h₁ : G₁ →L[R] F₁)
  (f₂ : E₂ →L[S] F₂) (h₂ : G₂ →L[S] F₂)
  (u : E₁ →SL[σ] E₂) (v : F₁ →SL[σ] F₂) (w : G₁ →SL[σ] G₂)
  (hf : f₂.comp u = v.comp f₁) (hh : h₂.comp w = v.comp h₁)

local notation "P₁" => LinearMap.eqLocus
  (f₁.toLinearMap.comp (LinearMap.fst R E₁ G₁))
  (h₁.toLinearMap.comp (LinearMap.snd R E₁ G₁))

local notation "P₂" => LinearMap.eqLocus
  (f₂.toLinearMap.comp (LinearMap.fst S E₂ G₂))
  (h₂.toLinearMap.comp (LinearMap.snd S E₂ G₂))

/-- The continuous semilinear map between pullbacks induced by two commuting squares. -/
def pullbackMap : P₁ →SL[σ] P₂ :=
  (prodSemilinear (u.comp (fst R E₁ G₁)) (w.comp (snd R E₁ G₁))).restrict (by
    intro p hp
    apply LinearMap.mem_eqLocus.mpr
    have hp' : f₁ p.1 = h₁ p.2 := hp
    have hfp : f₂ (u p.1) = v (f₁ p.1) := DFunLike.congr_fun hf p.1
    have hhp : h₂ (w p.2) = v (h₁ p.2) := DFunLike.congr_fun hh p.2
    exact hfp.trans ((congrArg v hp').trans hhp.symm))

/-- The induced map applies the two ambient coordinate maps. -/
@[simp]
theorem pullbackMap_apply (p : P₁) :
    (pullbackMap f₁ h₁ f₂ h₂ u v w hf hh p : E₂ × G₂) =
      (u p.val.1, w p.val.2) := rfl

/-- The ambient-source projection commutes with the induced pullback map. -/
@[simp]
theorem fst_comp_pullbackMap :
    ((fst S E₂ G₂).domRestrict P₂).comp (pullbackMap f₁ h₁ f₂ h₂ u v w hf hh) =
      u.comp ((fst R E₁ G₁).domRestrict P₁) := by
  apply DFunLike.ext
  intro p
  exact congrArg Prod.fst (pullbackMap_apply f₁ h₁ f₂ h₂ u v w hf hh p)

/-- The base projection commutes with the induced pullback map. -/
@[simp]
theorem snd_comp_pullbackMap :
    ((snd S E₂ G₂).domRestrict P₂).comp (pullbackMap f₁ h₁ f₂ h₂ u v w hf hh) =
      w.comp ((snd R E₁ G₁).domRestrict P₁) := by
  apply DFunLike.ext
  intro p
  exact congrArg Prod.snd (pullbackMap_apply f₁ h₁ f₂ h₂ u v w hf hh p)

/-- A map between the pullbacks with the prescribed two projections is the induced map. -/
theorem pullbackMap_unique (q : P₁ →SL[σ] P₂)
    (hE : ((fst S E₂ G₂).domRestrict P₂).comp q =
      u.comp ((fst R E₁ G₁).domRestrict P₁))
    (hG : ((snd S E₂ G₂).domRestrict P₂).comp q =
      w.comp ((snd R E₁ G₁).domRestrict P₁)) :
    q = pullbackMap f₁ h₁ f₂ h₂ u v w hf hh := by
  apply DFunLike.ext
  intro p
  apply Subtype.ext
  apply Prod.ext
  · exact (DFunLike.congr_fun hE p).trans
      (congrArg Prod.fst (pullbackMap_apply f₁ h₁ f₂ h₂ u v w hf hh p)).symm
  · exact (DFunLike.congr_fun hG p).trans
      (congrArg Prod.snd (pullbackMap_apply f₁ h₁ f₂ h₂ u v w hf hh p)).symm

/-- The identity morphism of a diagram induces the identity of its pullback. -/
@[simp]
theorem pullbackMap_id :
    pullbackMap f₁ h₁ f₁ h₁ (ContinuousLinearMap.id R E₁) (ContinuousLinearMap.id R F₁)
      (ContinuousLinearMap.id R G₁)
      (by simp only [comp_id, id_comp]) (by simp only [comp_id, id_comp]) =
        ContinuousLinearMap.id R P₁ := by
  apply DFunLike.ext
  intro p
  apply Subtype.ext
  simpa only [id_apply] using
    pullbackMap_apply f₁ h₁ f₁ h₁ (ContinuousLinearMap.id R E₁) (ContinuousLinearMap.id R F₁)
      (ContinuousLinearMap.id R G₁)
      (by simp only [comp_id, id_comp]) (by simp only [comp_id, id_comp]) p

end Map

section Composition

universe uT uE₃ uF₃ uG₃

variable {R : Type uR} {S : Type uS} {T : Type uT}
  [Semiring R] [Semiring S] [Semiring T]
  {σ₁₂ : R →+* S} {σ₂₃ : S →+* T} {σ₁₃ : R →+* T}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  {E₁ : Type uE₁} {F₁ : Type uF₁} {G₁ : Type uG₁}
  {E₂ : Type uE₂} {F₂ : Type uF₂} {G₂ : Type uG₂}
  {E₃ : Type uE₃} {F₃ : Type uF₃} {G₃ : Type uG₃}
  [AddCommMonoid E₁] [Module R E₁] [TopologicalSpace E₁]
  [AddCommMonoid F₁] [Module R F₁] [TopologicalSpace F₁]
  [AddCommMonoid G₁] [Module R G₁] [TopologicalSpace G₁]
  [AddCommMonoid E₂] [Module S E₂] [TopologicalSpace E₂]
  [AddCommMonoid F₂] [Module S F₂] [TopologicalSpace F₂]
  [AddCommMonoid G₂] [Module S G₂] [TopologicalSpace G₂]
  [AddCommMonoid E₃] [Module T E₃] [TopologicalSpace E₃]
  [AddCommMonoid F₃] [Module T F₃] [TopologicalSpace F₃]
  [AddCommMonoid G₃] [Module T G₃] [TopologicalSpace G₃]

/-- Composition of diagram morphisms agrees with composition of the induced pullback maps.
The commuting squares of the composite are consequences of the original squares. -/
@[simp]
theorem pullbackMap_comp
    (f₁ : E₁ →L[R] F₁) (h₁ : G₁ →L[R] F₁)
    (f₂ : E₂ →L[S] F₂) (h₂ : G₂ →L[S] F₂)
    (f₃ : E₃ →L[T] F₃) (h₃ : G₃ →L[T] F₃)
    (u₁₂ : E₁ →SL[σ₁₂] E₂) (v₁₂ : F₁ →SL[σ₁₂] F₂) (w₁₂ : G₁ →SL[σ₁₂] G₂)
    (hf₁₂ : f₂.comp u₁₂ = v₁₂.comp f₁) (hh₁₂ : h₂.comp w₁₂ = v₁₂.comp h₁)
    (u₂₃ : E₂ →SL[σ₂₃] E₃) (v₂₃ : F₂ →SL[σ₂₃] F₃) (w₂₃ : G₂ →SL[σ₂₃] G₃)
    (hf₂₃ : f₃.comp u₂₃ = v₂₃.comp f₂) (hh₂₃ : h₃.comp w₂₃ = v₂₃.comp h₂) :
    (pullbackMap f₂ h₂ f₃ h₃ u₂₃ v₂₃ w₂₃ hf₂₃ hh₂₃).comp (σ₁₃ := σ₁₃)
        (pullbackMap f₁ h₁ f₂ h₂ u₁₂ v₁₂ w₁₂ hf₁₂ hh₁₂) =
      pullbackMap f₁ h₁ f₃ h₃ (u₂₃.comp u₁₂) (v₂₃.comp v₁₂) (w₂₃.comp w₁₂)
        (by
          apply DFunLike.ext
          intro x
          exact (DFunLike.congr_fun hf₂₃ (u₁₂ x)).trans
            (congrArg v₂₃ (DFunLike.congr_fun hf₁₂ x)))
        (by
          apply DFunLike.ext
          intro x
          exact (DFunLike.congr_fun hh₂₃ (w₁₂ x)).trans
            (congrArg v₂₃ (DFunLike.congr_fun hh₁₂ x))) := by
  apply DFunLike.ext
  intro p
  apply Subtype.ext
  simp only [comp_apply, pullbackMap_apply]

end Composition

end ContinuousLinearMap
