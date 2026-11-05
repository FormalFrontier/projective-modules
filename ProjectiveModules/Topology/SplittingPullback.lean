/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.EqLocus
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

universe uR uE uF uG

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
The construction reuses `equivProdKerOfRightInverse` and its whole inverse. -/
def pullbackEquivProdKerOfRightInverse :
    LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G)) ≃L[R] (G × f.ker) := by
  let P := LinearMap.eqLocus
    (f.toLinearMap.comp (LinearMap.fst R E G))
    (h.toLinearMap.comp (LinearMap.snd R E G))
  let C := f.equivProdKerOfRightInverse s hs
  let πE := (fst R E G).domRestrict P
  let πG := (snd R E G).domRestrict P
  let a : P →L[R] (G × f.ker) :=
    πG.prod ((snd R F f.ker).comp (C.toContinuousLinearMap.comp πE))
  let b₀ : G × f.ker →L[R] E × G :=
    (C.symm.toContinuousLinearMap.comp
      ((h.comp (fst R G f.ker)).prod (snd R G f.ker))).prod (fst R G f.ker)
  have hb (z : G × f.ker) : b₀ z ∈ P := by
    change f (C.symm (h z.1, z.2)) = h z.1
    calc
      f (C.symm (h z.1, z.2)) = (C (C.symm (h z.1, z.2))).1 :=
        (fst_equivProdKerOfRightInverse f s hs _).symm
      _ = h z.1 := congrArg Prod.fst (C.apply_symm_apply (h z.1, z.2))
  let b : G × f.ker →L[R] P := b₀.codRestrict P hb
  refine ContinuousLinearEquiv.equivOfInverse a b ?_ ?_
  · intro p
    have hp : f p.val.1 = h p.val.2 := p.property
    have hpair : (h p.val.2, (C p.val.1).2) = C p.val.1 := by
      apply Prod.ext
      · exact hp.symm.trans (fst_equivProdKerOfRightInverse f s hs p.val.1).symm
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
  apply ContinuousLinearMap.ext
  intro x
  simp only [comp_apply, ContinuousLinearEquiv.coe_coe,
    pullbackEquivProdKerOfRightInverse_apply, coe_codRestrict_apply, prod_apply, id_apply]
  exact Prod.ext (fst_equivProdKerOfRightInverse f s hs x).symm rfl

end ContinuousLinearMap
