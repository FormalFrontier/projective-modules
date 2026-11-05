/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Topology.Pullback
public import ProjectiveModules.Topology.Splitting

/-!
# Pullbacks of continuous split linear maps

A continuous linear section of `f : E →L[R] F` identifies the submodule of pairs
`(e, g)` satisfying `f e = h g` with `G × f.ker`. The construction uses the
canonical splitting of `f` and its inverse, with the original submodule and
subtype topology on the pullback. Neither `F`, `G`, nor the pullback needs to be
an additive group, and continuity of their additive operations is not required.

The coordinate laws characterize both directions. Pullback along the identity
recovers the whole canonical splitting after the graph map `e ↦ (e, f e)`.

## References

* `ProjectiveModules.Topology.Splitting`: the canonical continuous splitting
  `ContinuousLinearMap.equivProdKerOfRightInverse` and its coordinate laws.
* Mathlib's `LinearMap.eqLocus`, continuous linear restrictions and products, and
  `ContinuousLinearEquiv.equivOfInverse`.
-/

@[expose] public section

universe uR uE uF uG uH

namespace ContinuousLinearMap

variable {R : Type uR} {E : Type uE} {F : Type uF} {G : Type uG}
  [Semiring R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [AddCommMonoid F] [Module R F] [TopologicalSpace F]
  [AddCommMonoid G] [Module R G] [TopologicalSpace G]

variable (f : E →L[R] F) (s : F →L[R] E) (hs : Function.RightInverse s f)
  (h : G →L[R] F)

/-- Pulling back a continuous split linear map along `h` preserves its product
splitting. The source is the equalizer submodule of the original `E × G`, with
its induced topology, and the second factor is the original kernel of `f`.
The construction specializes `pullbackEquivProdOfEquiv` using
`equivProdKerOfRightInverse` and its whole inverse. -/
def pullbackEquivProdKerOfRightInverse :
    LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G)) ≃L[R] (G × f.ker) :=
  f.pullbackEquivProdOfEquiv (f.equivProdKerOfRightInverse s hs)
    (by
      apply ContinuousLinearMap.ext
      intro x
      exact fst_equivProdKerOfRightInverse f s hs x) h

/-- Base change of the canonical product coordinates is the section-based
pullback splitting, for any proof of the whole first-projection compatibility. -/
theorem pullbackEquivProdOfEquiv_equivProdKerOfRightInverse
    (hC : (fst R F f.ker).comp
      (f.equivProdKerOfRightInverse s hs).toContinuousLinearMap = f) :
    f.pullbackEquivProdOfEquiv (f.equivProdKerOfRightInverse s hs) hC h =
      f.pullbackEquivProdKerOfRightInverse s hs h := rfl

/-- The pullback splitting retains the base coordinate and the canonical kernel
coordinate of the ambient source point. -/
theorem pullbackEquivProdKerOfRightInverse_apply
    (p : LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))) :
    f.pullbackEquivProdKerOfRightInverse s hs h p =
      (p.val.2, (f.equivProdKerOfRightInverse s hs p.val.1).2) := rfl

/-- The first coordinate of the pullback splitting is the given base point. -/
@[simp]
theorem fst_pullbackEquivProdKerOfRightInverse
    (p : LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))) :
    (f.pullbackEquivProdKerOfRightInverse s hs h p).1 = p.val.2 := rfl

/-- The second coordinate is the coordinate in the original kernel supplied by
`equivProdKerOfRightInverse`. -/
theorem snd_pullbackEquivProdKerOfRightInverse
    (p : LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))) :
    (f.pullbackEquivProdKerOfRightInverse s hs h p).2 =
      (f.equivProdKerOfRightInverse s hs p.val.1).2 := rfl

/-- In the original source group, the kernel coordinate is the difference from
the section evaluated at the image of the base point. -/
@[simp]
theorem coe_snd_pullbackEquivProdKerOfRightInverse
    (p : LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))) :
    ((f.pullbackEquivProdKerOfRightInverse s hs h p).2 : E) =
      p.val.1 - s (h p.val.2) := by
  rw [snd_pullbackEquivProdKerOfRightInverse, coe_snd_equivProdKerOfRightInverse]
  exact congrArg (fun y : F ↦ p.val.1 - s y) p.property

/-- The inverse uses the whole inverse canonical splitting at `(h g, k)` and
retains `g` as its base coordinate. -/
@[simp]
theorem coe_pullbackEquivProdKerOfRightInverse_symm_apply (z : G × f.ker) :
    ((f.pullbackEquivProdKerOfRightInverse s hs h).symm z : E × G) =
      ((f.equivProdKerOfRightInverse s hs).symm (h z.1, z.2), z.1) := rfl

/-- The inverse has ambient coordinates `(s (h g) + k, g)`, by the inverse law
of the canonical splitting. Addition takes place only in the original `E`. -/
theorem coe_pullbackEquivProdKerOfRightInverse_symm_apply_eq_add (z : G × f.ker) :
    ((f.pullbackEquivProdKerOfRightInverse s hs h).symm z : E × G) =
      (s (h z.1) + (z.2 : E), z.1) := by
  rw [coe_pullbackEquivProdKerOfRightInverse_symm_apply,
    equivProdKerOfRightInverse_symm_apply]
  exact congrArg (fun e : E ↦ (e, z.1)) (add_comm _ _)

/-- As a whole continuous linear map, the first projection of the splitting is
the restriction of the original base projection. -/
@[simp]
theorem fst_comp_pullbackEquivProdKerOfRightInverse :
    (fst R G f.ker).comp
        (f.pullbackEquivProdKerOfRightInverse s hs h).toContinuousLinearMap =
      (snd R E G).domRestrict
        (LinearMap.eqLocus
          (f.toLinearMap.comp (LinearMap.fst R E G))
          (h.toLinearMap.comp (LinearMap.snd R E G))) := by
  apply ContinuousLinearMap.ext
  intro p
  exact fst_pullbackEquivProdKerOfRightInverse f s hs h p

/-- The base projection after the inverse is the first projection on
`G × f.ker`, as an equality of whole continuous linear maps. -/
@[simp]
theorem snd_comp_pullbackEquivProdKerOfRightInverse_symm :
    ((snd R E G).domRestrict
      (LinearMap.eqLocus
        (f.toLinearMap.comp (LinearMap.fst R E G))
        (h.toLinearMap.comp (LinearMap.snd R E G)))).comp
        (f.pullbackEquivProdKerOfRightInverse s hs h).symm.toContinuousLinearMap =
      fst R G f.ker := by
  apply ContinuousLinearMap.ext
  intro z
  exact congrArg Prod.snd
    (coe_pullbackEquivProdKerOfRightInverse_symm_apply f s hs h z)

/-- The ambient-source projection of the inverse is the whole inverse
canonical splitting composed with the pairing `(g, k) ↦ (h g, k)`. -/
theorem fst_comp_pullbackEquivProdKerOfRightInverse_symm :
    ((fst R E G).domRestrict
      (LinearMap.eqLocus
        (f.toLinearMap.comp (LinearMap.fst R E G))
        (h.toLinearMap.comp (LinearMap.snd R E G)))).comp
        (f.pullbackEquivProdKerOfRightInverse s hs h).symm.toContinuousLinearMap =
      (f.equivProdKerOfRightInverse s hs).symm.toContinuousLinearMap.comp
        ((h.comp (fst R G f.ker)).prod (snd R G f.ker)) := by
  apply ContinuousLinearMap.ext
  intro z
  exact congrArg Prod.fst
    (coe_pullbackEquivProdKerOfRightInverse_symm_apply f s hs h z)

/-- Pulling back along the identity and composing with the graph map
`e ↦ (e, f e)` recovers the whole canonical continuous linear splitting of `f`.
The graph map is the corestriction of `(ContinuousLinearMap.id R E).prod f` to the equalizer. -/
theorem pullbackEquivProdKerOfRightInverse_comp_graph :
    (f.pullbackEquivProdKerOfRightInverse s hs
      (ContinuousLinearMap.id R F)).toContinuousLinearMap.comp
        (((ContinuousLinearMap.id R E).prod f).codRestrict
          (LinearMap.eqLocus
            (f.toLinearMap.comp (LinearMap.fst R E F))
            ((ContinuousLinearMap.id R F).toLinearMap.comp (LinearMap.snd R E F)))
          (fun _ ↦ LinearMap.mem_eqLocus.mpr (by
            simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
              prod_apply, id_apply, LinearMap.fst_apply, LinearMap.snd_apply]))) =
      (f.equivProdKerOfRightInverse s hs).toContinuousLinearMap := by
  have hC : (fst R F f.ker).comp
      (f.equivProdKerOfRightInverse s hs).toContinuousLinearMap = f := by
    apply ContinuousLinearMap.ext
    intro x
    simpa only [comp_apply, coe_fst', ContinuousLinearEquiv.coe_coe] using
      (fst_equivProdKerOfRightInverse f s hs x)
  rw [← pullbackEquivProdOfEquiv_equivProdKerOfRightInverse f s hs
    (ContinuousLinearMap.id R F) hC]
  exact pullbackEquivProdOfEquiv_comp_graph f (f.equivProdKerOfRightInverse s hs) hC

variable {H : Type uH} [AddCommMonoid H] [Module R H] [TopologicalSpace H]

/-- Successive base changes of a split map preserve its original kernel
coordinates through the canonical pullback associator. The second base change
uses the first whole equivalence and its inverse, so the intermediate pullback
needs no additive group structure. -/
theorem pullbackEquivProdKerOfRightInverse_comp (k : H →L[R] G) :
    let P := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))
    let p : P →L[R] G := (snd R E G).domRestrict P
    let B_h := f.pullbackEquivProdKerOfRightInverse s hs h
    p.pullbackEquivProdOfEquiv B_h
        (fst_comp_pullbackEquivProdKerOfRightInverse f s hs h) k =
      (f.pullbackAssoc h k).trans
        (f.pullbackEquivProdKerOfRightInverse s hs (h.comp k)) := by
  have hC : (fst R F f.ker).comp
      (f.equivProdKerOfRightInverse s hs).toContinuousLinearMap = f := by
    apply ContinuousLinearMap.ext
    intro x
    exact fst_equivProdKerOfRightInverse f s hs x
  simpa only [pullbackEquivProdOfEquiv_equivProdKerOfRightInverse] using
    (pullbackEquivProdOfEquiv_comp f (f.equivProdKerOfRightInverse s hs) hC h k)

end ContinuousLinearMap
