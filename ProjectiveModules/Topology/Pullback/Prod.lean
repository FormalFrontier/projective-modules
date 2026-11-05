/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Base change of continuous linear product coordinates

A continuous linear equivalence `C : E ≃L[R] (F × K)` whose first projection is
`f : E →L[R] F` gives product coordinates on the pullback of `f` along any
`h : G →L[R] F`. The pullback is the equalizer submodule of the original `E × G`,
with its induced topology. Its coordinates are the base point in `G` and the
second coordinate supplied by `C`.

All four carriers need only be additive commutative monoids with their given
module structures and topologies over a semiring. Neither continuous addition
nor continuous scalar multiplication is required. The inverse uses the whole
inverse of `C`, without a section or subtraction.

## References

* Mathlib's `LinearMap.eqLocus`, continuous linear products and restrictions,
  and `ContinuousLinearEquiv.equivOfInverse`.
* `ProjectiveModules.Topology.SplittingPullback`: the section-based
  specialization using the canonical product coordinates.
-/

@[expose] public section

universe uR uE uF uG uK

namespace ContinuousLinearMap

variable {R : Type uR} {E : Type uE} {F : Type uF} {G : Type uG} {K : Type uK}
  [Semiring R]
  [AddCommMonoid E] [Module R E] [TopologicalSpace E]
  [AddCommMonoid F] [Module R F] [TopologicalSpace F]
  [AddCommMonoid G] [Module R G] [TopologicalSpace G]
  [AddCommMonoid K] [Module R K] [TopologicalSpace K]

variable (f : E →L[R] F) (C : E ≃L[R] (F × K))
  (hC : (fst R F K).comp C.toContinuousLinearMap = f) (h : G →L[R] F)

/-- Base change of given continuous linear product coordinates. The source is
the equalizer submodule of `E × G` defined by `f e = h g`; the inverse is induced
by `(g, c) ↦ (C.symm (h g, c), g)` in the original ambient product. -/
def pullbackEquivProdOfEquiv :
    LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G)) ≃L[R] (G × K) := by
  let P := LinearMap.eqLocus
    (f.toLinearMap.comp (LinearMap.fst R E G))
    (h.toLinearMap.comp (LinearMap.snd R E G))
  let πE := (fst R E G).domRestrict P
  let πG := (snd R E G).domRestrict P
  let a : P →L[R] (G × K) :=
    πG.prod ((snd R F K).comp (C.toContinuousLinearMap.comp πE))
  let b₀ : G × K →L[R] E × G :=
    (C.symm.toContinuousLinearMap.comp
      ((h.comp (fst R G K)).prod (snd R G K))).prod (fst R G K)
  have hfst (x : E) : (C x).1 = f x := DFunLike.congr_fun hC x
  have hb (z : G × K) : b₀ z ∈ P := by
    change f (C.symm (h z.1, z.2)) = h z.1
    calc
      f (C.symm (h z.1, z.2)) = (C (C.symm (h z.1, z.2))).1 :=
        (hfst _).symm
      _ = h z.1 := congrArg Prod.fst (C.apply_symm_apply (h z.1, z.2))
  let b : G × K →L[R] P := b₀.codRestrict P hb
  refine ContinuousLinearEquiv.equivOfInverse a b ?_ ?_
  · intro p
    have hp : f p.val.1 = h p.val.2 := p.property
    have hpair : (h p.val.2, (C p.val.1).2) = C p.val.1 := by
      apply Prod.ext
      · exact hp.symm.trans (hfst p.val.1).symm
      · rfl
    apply Subtype.ext
    apply Prod.ext
    · change C.symm (h p.val.2, (C p.val.1).2) = p.val.1
      rw [hpair]
      exact C.symm_apply_apply p.val.1
    · rfl
  · intro z
    apply Prod.ext
    · rfl
    · change (C (C.symm (h z.1, z.2))).2 = z.2
      exact congrArg Prod.snd (C.apply_symm_apply (h z.1, z.2))

/-- The product coordinates retain the base point and the second coordinate
of the given ambient equivalence. -/
theorem pullbackEquivProdOfEquiv_apply
    (p : LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))) :
    f.pullbackEquivProdOfEquiv C hC h p = (p.val.2, (C p.val.1).2) := rfl

/-- The first coordinate is the original base point. -/
@[simp]
theorem fst_pullbackEquivProdOfEquiv
    (p : LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))) :
    (f.pullbackEquivProdOfEquiv C hC h p).1 = p.val.2 := rfl

/-- The second coordinate is supplied by the given ambient equivalence. -/
theorem snd_pullbackEquivProdOfEquiv
    (p : LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))) :
    (f.pullbackEquivProdOfEquiv C hC h p).2 = (C p.val.1).2 := rfl

/-- In the ambient product, the inverse uses the whole inverse of the given
product-coordinate equivalence and retains the base point. -/
@[simp]
theorem coe_pullbackEquivProdOfEquiv_symm_apply (z : G × K) :
    ((f.pullbackEquivProdOfEquiv C hC h).symm z : E × G) =
      (C.symm (h z.1, z.2), z.1) := rfl

/-- The first projection of the product coordinates is the restriction of the
original base projection, as an equality of whole continuous linear maps. -/
@[simp]
theorem fst_comp_pullbackEquivProdOfEquiv :
    (fst R G K).comp (f.pullbackEquivProdOfEquiv C hC h).toContinuousLinearMap =
      (snd R E G).domRestrict
        (LinearMap.eqLocus
          (f.toLinearMap.comp (LinearMap.fst R E G))
          (h.toLinearMap.comp (LinearMap.snd R E G))) := by
  apply ContinuousLinearMap.ext
  intro p
  exact fst_pullbackEquivProdOfEquiv f C hC h p

/-- The second projection is the ambient second coordinate restricted to the
pullback, as an equality of whole continuous linear maps. -/
theorem snd_comp_pullbackEquivProdOfEquiv :
    (snd R G K).comp (f.pullbackEquivProdOfEquiv C hC h).toContinuousLinearMap =
      (snd R F K).comp (C.toContinuousLinearMap.comp
        ((fst R E G).domRestrict
          (LinearMap.eqLocus
            (f.toLinearMap.comp (LinearMap.fst R E G))
            (h.toLinearMap.comp (LinearMap.snd R E G))))) := by
  apply ContinuousLinearMap.ext
  intro p
  exact snd_pullbackEquivProdOfEquiv f C hC h p

/-- After the inverse, the original base projection is the first projection
on `G × K`, as an equality of whole continuous linear maps. -/
@[simp]
theorem snd_comp_pullbackEquivProdOfEquiv_symm :
    ((snd R E G).domRestrict
      (LinearMap.eqLocus
        (f.toLinearMap.comp (LinearMap.fst R E G))
        (h.toLinearMap.comp (LinearMap.snd R E G)))).comp
        (f.pullbackEquivProdOfEquiv C hC h).symm.toContinuousLinearMap =
      fst R G K := by
  apply ContinuousLinearMap.ext
  intro z
  exact congrArg Prod.snd (coe_pullbackEquivProdOfEquiv_symm_apply f C hC h z)

/-- The ambient-source projection of the inverse is the whole inverse of `C`
composed with the pairing `(g, c) ↦ (h g, c)`. -/
theorem fst_comp_pullbackEquivProdOfEquiv_symm :
    ((fst R E G).domRestrict
      (LinearMap.eqLocus
        (f.toLinearMap.comp (LinearMap.fst R E G))
        (h.toLinearMap.comp (LinearMap.snd R E G)))).comp
        (f.pullbackEquivProdOfEquiv C hC h).symm.toContinuousLinearMap =
      C.symm.toContinuousLinearMap.comp
        ((h.comp (fst R G K)).prod (snd R G K)) := by
  apply ContinuousLinearMap.ext
  intro z
  exact congrArg Prod.fst (coe_pullbackEquivProdOfEquiv_symm_apply f C hC h z)

/-- Pulling back along the identity and composing with the graph map
`e ↦ (e, f e)` recovers the whole given product-coordinate map. The graph map is
corestricted to the equalizer submodule of the original `E × F`. -/
theorem pullbackEquivProdOfEquiv_comp_graph :
    (f.pullbackEquivProdOfEquiv C hC (ContinuousLinearMap.id R F)).toContinuousLinearMap.comp
        (((ContinuousLinearMap.id R E).prod f).codRestrict
          (LinearMap.eqLocus
            (f.toLinearMap.comp (LinearMap.fst R E F))
            ((ContinuousLinearMap.id R F).toLinearMap.comp (LinearMap.snd R E F)))
          (fun _ ↦ LinearMap.mem_eqLocus.mpr (by
            simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
              prod_apply, id_apply, LinearMap.fst_apply, LinearMap.snd_apply]))) =
      C.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [comp_apply, ContinuousLinearEquiv.coe_coe,
    pullbackEquivProdOfEquiv_apply, coe_codRestrict_apply, prod_apply, id_apply]
  apply Prod.ext
  · simpa only [comp_apply, coe_fst', ContinuousLinearEquiv.coe_coe] using
      (DFunLike.congr_fun hC x).symm
  · rfl

end ContinuousLinearMap
