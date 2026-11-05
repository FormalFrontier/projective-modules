/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Topology.Pullback.Assoc
public import ProjectiveModules.Topology.Pullback.Prod

/-!
# Iterated continuous linear pullbacks

The canonical associator of equalizer submodules compares two successive
pullbacks with pullback along the composite. Product coordinates given by a
continuous linear equivalence commute with this comparison. The intermediate
and iterated pullbacks need only be additive monoids, and all their module and
topological structures are inherited from the displayed stock submodules.

## References

* `ProjectiveModules.Topology.Pullback.Assoc`: the canonical associator and its
  coordinate laws.
* `ProjectiveModules.Topology.Pullback.Prod`: base change of product coordinates
  using a continuous linear equivalence and its inverse.
-/

@[expose] public section

universe uR uE uF uG uH uK

namespace ContinuousLinearMap

variable {R : Type uR} {E : Type uE} {F : Type uF} {G : Type uG}
  {H : Type uH} {K : Type uK}
  [Semiring R]
  [AddCommMonoid E] [Module R E] [TopologicalSpace E]
  [AddCommMonoid F] [Module R F] [TopologicalSpace F]
  [AddCommMonoid G] [Module R G] [TopologicalSpace G]
  [AddCommMonoid H] [Module R H] [TopologicalSpace H]
  [AddCommMonoid K] [Module R K] [TopologicalSpace K]

variable (f : E →L[R] F) (C : E ≃L[R] (F × K))
  (hC : (fst R F K).comp C.toContinuousLinearMap = f)
  (h : G →L[R] F) (k : H →L[R] G)

/-- Successive base changes of product coordinates agree with base change along
composition after the canonical pullback associator. The left equivalence uses
the first base-change equivalence and its inverse as its coordinate data; no
group structure on either pullback is required. -/
theorem pullbackEquivProdOfEquiv_comp :
    let P := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))
    let p : P →L[R] G := (snd R E G).domRestrict P
    let B_h := f.pullbackEquivProdOfEquiv C hC h
    p.pullbackEquivProdOfEquiv B_h
        (fst_comp_pullbackEquivProdOfEquiv f C hC h) k =
      (f.pullbackAssoc h k).trans
        (f.pullbackEquivProdOfEquiv C hC (h.comp k)) := by
  dsimp only
  apply ContinuousLinearEquiv.ext
  funext q
  simpa only [ContinuousLinearEquiv.trans_apply, pullbackEquivProdOfEquiv_apply] using
    (congrArg (fun ez : E × H ↦ (ez.2, (C ez.1).2))
      (coe_pullbackAssoc_apply f h k q)).symm

end ContinuousLinearMap
