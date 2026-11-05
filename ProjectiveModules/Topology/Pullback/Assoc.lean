/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Associativity of pullbacks of continuous linear maps

`ContinuousLinearMap.pullbackAssoc` identifies the iterated pullback of `f` along `h` and
then `k` with the pullback of `f` along `h.comp k`. Its forward map forgets the intermediate
coordinate, and its inverse inserts the image under `k`.

The pullbacks are submodules defined by `LinearMap.eqLocus`, with their subtype topologies.
Only additive commutative monoids and modules over a semiring are needed. The construction
uses Mathlib's continuous linear products, restrictions and inverse-equivalence constructor.

## References

* Mathlib's `LinearMap.eqLocus`, continuous linear products and restrictions, and
  `ContinuousLinearEquiv.equivOfInverse`.
-/

@[expose] public section

universe uR uE uF uG uH

namespace ContinuousLinearMap

variable {R : Type uR} [Semiring R]
  {E : Type uE} [AddCommMonoid E] [Module R E] [TopologicalSpace E]
  {F : Type uF} [AddCommMonoid F] [Module R F] [TopologicalSpace F]
  {G : Type uG} [AddCommMonoid G] [Module R G] [TopologicalSpace G]
  {H : Type uH} [AddCommMonoid H] [Module R H] [TopologicalSpace H]

variable (f : E →L[R] F) (h : G →L[R] F) (k : H →L[R] G)

/-- Associativity of pullbacks: forgetting the intermediate coordinate identifies the
pullback of the projection to `G` along `k` with the pullback of `f` along `h.comp k`.
The inverse sends `(e, z)` to `((e, k z), z)`. -/
def pullbackAssoc :
    let P := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))
    let p := (snd R E G).domRestrict P
    let Q := LinearMap.eqLocus
      (p.toLinearMap.comp (LinearMap.fst R P H))
      (k.toLinearMap.comp (LinearMap.snd R P H))
    let T := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E H))
      ((h.comp k).toLinearMap.comp (LinearMap.snd R E H))
    Q ≃L[R] T := by
  let P := LinearMap.eqLocus
    (f.toLinearMap.comp (LinearMap.fst R E G))
    (h.toLinearMap.comp (LinearMap.snd R E G))
  let p := (snd R E G).domRestrict P
  let Q := LinearMap.eqLocus
    (p.toLinearMap.comp (LinearMap.fst R P H))
    (k.toLinearMap.comp (LinearMap.snd R P H))
  let T := LinearMap.eqLocus
    (f.toLinearMap.comp (LinearMap.fst R E H))
    ((h.comp k).toLinearMap.comp (LinearMap.snd R E H))
  let forward : Q →L[R] T :=
    ((((fst R E G).domRestrict P).comp ((fst R P H).domRestrict Q)).prod
      ((snd R P H).domRestrict Q)).codRestrict T (by
        intro q
        change f q.val.1.val.1 = h (k q.val.2)
        have hP : f q.val.1.val.1 = h q.val.1.val.2 := q.val.1.property
        have hQ : q.val.1.val.2 = k q.val.2 := q.property
        exact hP.trans (congrArg h hQ))
  let insert : T →L[R] P :=
    (((fst R E H).domRestrict T).prod
      (k.comp ((snd R E H).domRestrict T))).codRestrict P (by
        intro t
        exact t.property)
  let backward : T →L[R] Q :=
    (insert.prod ((snd R E H).domRestrict T)).codRestrict Q (by
      intro t
      rfl)
  exact ContinuousLinearEquiv.equivOfInverse forward backward
    (by
      intro q
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact (show q.val.1.val.2 = k q.val.2 from q.property).symm
      · rfl)
    (by
      intro t
      apply Subtype.ext
      rfl)

/-- The ambient value of the pullback associator forgets the intermediate coordinate. -/
theorem coe_pullbackAssoc_apply :
    let P := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))
    let p := (snd R E G).domRestrict P
    let Q := LinearMap.eqLocus
      (p.toLinearMap.comp (LinearMap.fst R P H))
      (k.toLinearMap.comp (LinearMap.snd R P H))
    ∀ q : Q, (f.pullbackAssoc h k q : E × H) = (q.val.1.val.1, q.val.2) :=
  fun _ => rfl

/-- The associator preserves the `E` coordinate. -/
theorem fst_pullbackAssoc_apply :
    let P := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))
    let p := (snd R E G).domRestrict P
    let Q := LinearMap.eqLocus
      (p.toLinearMap.comp (LinearMap.fst R P H))
      (k.toLinearMap.comp (LinearMap.snd R P H))
    ∀ q : Q, (f.pullbackAssoc h k q).val.1 = q.val.1.val.1 :=
  fun q => congrArg Prod.fst (coe_pullbackAssoc_apply f h k q)

/-- The associator preserves the `H` coordinate. -/
theorem snd_pullbackAssoc_apply :
    let P := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))
    let p := (snd R E G).domRestrict P
    let Q := LinearMap.eqLocus
      (p.toLinearMap.comp (LinearMap.fst R P H))
      (k.toLinearMap.comp (LinearMap.snd R P H))
    ∀ q : Q, (f.pullbackAssoc h k q).val.2 = q.val.2 :=
  fun q => congrArg Prod.snd (coe_pullbackAssoc_apply f h k q)

/-- The inverse associator inserts `(e, k z)` in the first pullback and retains `z`. -/
theorem coe_pullbackAssoc_symm_apply :
    let P := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))
    let T := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E H))
      ((h.comp k).toLinearMap.comp (LinearMap.snd R E H))
    ∀ t : T, ((f.pullbackAssoc h k).symm t : P × H) =
      (⟨(t.val.1, k t.val.2), t.property⟩, t.val.2) :=
  fun _ => rfl

/-- The inverse associator preserves the `E` coordinate. -/
theorem fst_fst_pullbackAssoc_symm_apply :
    let T := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E H))
      ((h.comp k).toLinearMap.comp (LinearMap.snd R E H))
    ∀ t : T, ((f.pullbackAssoc h k).symm t).val.1.val.1 = t.val.1 :=
  fun t => congrArg Prod.fst
    (congrArg Subtype.val (congrArg Prod.fst (coe_pullbackAssoc_symm_apply f h k t)))

/-- The intermediate coordinate of the inverse associator is the image under `k`. -/
theorem snd_fst_pullbackAssoc_symm_apply :
    let T := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E H))
      ((h.comp k).toLinearMap.comp (LinearMap.snd R E H))
    ∀ t : T, ((f.pullbackAssoc h k).symm t).val.1.val.2 = k t.val.2 :=
  fun t => congrArg Prod.snd
    (congrArg Subtype.val (congrArg Prod.fst (coe_pullbackAssoc_symm_apply f h k t)))

/-- The inverse associator preserves the `H` coordinate. -/
theorem snd_pullbackAssoc_symm_apply :
    let T := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E H))
      ((h.comp k).toLinearMap.comp (LinearMap.snd R E H))
    ∀ t : T, ((f.pullbackAssoc h k).symm t).val.2 = t.val.2 :=
  fun t => congrArg Prod.snd (coe_pullbackAssoc_symm_apply f h k t)

/-- Composing the associator with the ambient inclusion is the product of the
`E` projection through the first pullback and the `H` projection. -/
theorem subtypeL_comp_pullbackAssoc :
    let P := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))
    let p := (snd R E G).domRestrict P
    let Q := LinearMap.eqLocus
      (p.toLinearMap.comp (LinearMap.fst R P H))
      (k.toLinearMap.comp (LinearMap.snd R P H))
    let T := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E H))
      ((h.comp k).toLinearMap.comp (LinearMap.snd R E H))
    T.subtypeL.comp (f.pullbackAssoc h k).toContinuousLinearMap =
      (((fst R E G).domRestrict P).comp ((fst R P H).domRestrict Q)).prod
        ((snd R P H).domRestrict Q) :=
  ContinuousLinearMap.ext (fun q => coe_pullbackAssoc_apply f h k q)

/-- Composing the inverse associator with the ambient inclusion is the product of
insertion into the first pullback and the `H` projection. -/
theorem subtypeL_comp_pullbackAssoc_symm :
    let P := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E G))
      (h.toLinearMap.comp (LinearMap.snd R E G))
    let p := (snd R E G).domRestrict P
    let Q := LinearMap.eqLocus
      (p.toLinearMap.comp (LinearMap.fst R P H))
      (k.toLinearMap.comp (LinearMap.snd R P H))
    let T := LinearMap.eqLocus
      (f.toLinearMap.comp (LinearMap.fst R E H))
      ((h.comp k).toLinearMap.comp (LinearMap.snd R E H))
    Q.subtypeL.comp (f.pullbackAssoc h k).symm.toContinuousLinearMap =
      ((((fst R E H).domRestrict T).prod
        (k.comp ((snd R E H).domRestrict T))).codRestrict P
          (fun t => t.property)).prod ((snd R E H).domRestrict T) :=
  ContinuousLinearMap.ext (fun t => coe_pullbackAssoc_symm_apply f h k t)

end ContinuousLinearMap
