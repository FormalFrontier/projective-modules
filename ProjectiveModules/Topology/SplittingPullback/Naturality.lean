/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Topology.Pullback.Map
public import ProjectiveModules.Topology.SplittingNaturality
public import ProjectiveModules.Topology.SplittingPullback

/-!
# Semilinear naturality of split pullbacks

A morphism of pullback diagrams is triangular in the canonical splitting coordinates.
Its base component is the given base map. Its kernel component is the sum of the
section deviation evaluated at the image of the source base point and the
restriction of the ambient semilinear map to the original kernel.

No compatibility of the chosen sections is required. Only the two ambient source
modules are topological additive groups; the bases and pullback modules remain
additive commutative monoids with their given module structures and topologies.
Addition in the triangular map takes place only in the target kernel, whose addition
is continuous by `Submodule.continuousAdd`.

## References

* `ProjectiveModules.Topology.SplittingNaturality` supplies the section deviation,
  kernel restriction and whole triangular law for the ambient canonical splittings.
* `ProjectiveModules.Topology.SplittingPullback` supplies the pullback splittings
  and their coordinate laws, using the same canonical splittings and whole inverses.
* `ProjectiveModules.Topology.Pullback.Map` supplies the induced map of equalizers.
-/

@[expose] public section

universe uR uS uE₁ uF₁ uG₁ uE₂ uF₂ uG₂

namespace ContinuousLinearMap

variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S] {σ : R →+* S}
  {E₁ : Type uE₁} {F₁ : Type uF₁} {G₁ : Type uG₁}
  {E₂ : Type uE₂} {F₂ : Type uF₂} {G₂ : Type uG₂}
  [AddCommGroup E₁] [Module R E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁]
  [AddCommMonoid F₁] [Module R F₁] [TopologicalSpace F₁]
  [AddCommMonoid G₁] [Module R G₁] [TopologicalSpace G₁]
  [AddCommGroup E₂] [Module S E₂] [TopologicalSpace E₂] [IsTopologicalAddGroup E₂]
  [AddCommMonoid F₂] [Module S F₂] [TopologicalSpace F₂]
  [AddCommMonoid G₂] [Module S G₂] [TopologicalSpace G₂]

variable (f₁ : E₁ →L[R] F₁) (h₁ : G₁ →L[R] F₁)
  (s₁ : F₁ →L[R] E₁) (hs₁ : Function.RightInverse s₁ f₁)
  (f₂ : E₂ →L[S] F₂) (h₂ : G₂ →L[S] F₂)
  (s₂ : F₂ →L[S] E₂) (hs₂ : Function.RightInverse s₂ f₂)
  (u : E₁ →SL[σ] E₂) (v : F₁ →SL[σ] F₂) (w : G₁ →SL[σ] G₂)
  (hf : f₂.comp u = v.comp f₁) (hh : h₂.comp w = v.comp h₁)

/-- The induced pullback map is triangular in the canonical splitting coordinates,
as an equality of whole continuous semilinear maps. The triangular map is constructed
from the base map, section deviation and kernel restriction, independently of the
pullback splittings. -/
theorem pullbackEquivProdKerOfRightInverse_map :
    let D := splittingDeviation f₂ s₂ hs₂ u s₁
    let K := u.restrict (map_mem_ker_of_comp_eq f₁ f₂ u v hf)
    let T : G₁ × f₁.ker →SL[σ] (G₂ × f₂.ker) :=
      prodSemilinear (w.comp (fst R G₁ f₁.ker))
        (D.comp (h₁.comp (fst R G₁ f₁.ker)) + K.comp (snd R G₁ f₁.ker))
    (f₂.pullbackEquivProdKerOfRightInverse s₂ hs₂ h₂).toContinuousLinearMap.comp
        (pullbackMap f₁ h₁ f₂ h₂ u v w hf hh) =
      T.comp (f₁.pullbackEquivProdKerOfRightInverse s₁ hs₁ h₁).toContinuousLinearMap := by
  dsimp only
  apply DFunLike.ext
  intro p
  have hC := DFunLike.congr_fun
    (equivProdKerOfRightInverse_map f₁ s₁ hs₁ f₂ s₂ hs₂ u v hf)
    (f₁.equivProdKerOfRightInverse s₁ hs₁ p.val.1)
  have hk :
      (f₂.equivProdKerOfRightInverse s₂ hs₂ (u p.val.1)).2 =
        splittingDeviation f₂ s₂ hs₂ u s₁ (h₁ p.val.2) +
          u.restrict (map_mem_ker_of_comp_eq f₁ f₂ u v hf)
            (f₁.equivProdKerOfRightInverse s₁ hs₁ p.val.1).2 := by
    have hp : f₁ p.val.1 = h₁ p.val.2 := p.property
    simpa only [comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, prodSemilinear_apply, coe_fst', coe_snd',
      add_apply, fst_equivProdKerOfRightInverse, hp] using congrArg Prod.snd hC
  simpa only [comp_apply, ContinuousLinearEquiv.coe_coe,
    pullbackEquivProdKerOfRightInverse_apply, pullbackMap_apply,
    prodSemilinear_apply, add_apply, coe_fst', coe_snd'] using
      (Prod.ext (rfl : w p.val.2 = w p.val.2) hk)

/-- In splitting coordinates, the induced map sends `(g, k)` to
`(w g, D (h₁ g) + K k)`, where `D` is the section deviation and `K` is the
restriction to the original kernel. -/
theorem pullbackEquivProdKerOfRightInverse_map_apply (g : G₁) (k : f₁.ker) :
    f₂.pullbackEquivProdKerOfRightInverse s₂ hs₂ h₂
        (pullbackMap f₁ h₁ f₂ h₂ u v w hf hh
          ((f₁.pullbackEquivProdKerOfRightInverse s₁ hs₁ h₁).symm (g, k))) =
      (w g, splittingDeviation f₂ s₂ hs₂ u s₁ (h₁ g) +
        u.restrict (map_mem_ker_of_comp_eq f₁ f₂ u v hf) k) := by
  have h := DFunLike.congr_fun
    (pullbackEquivProdKerOfRightInverse_map f₁ h₁ s₁ hs₁ f₂ h₂ s₂ hs₂ u v w hf hh)
    ((f₁.pullbackEquivProdKerOfRightInverse s₁ hs₁ h₁).symm (g, k))
  simpa only [comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, prodSemilinear_apply, coe_fst', coe_snd',
    add_apply] using h

end ContinuousLinearMap
