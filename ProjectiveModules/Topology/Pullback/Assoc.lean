/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Topology.Algebra.Module.Equiv
public import ProjectiveModules.Topology.Pullback.Map

/-!
# Associativity of pullbacks of continuous linear maps

`ContinuousLinearMap.pullbackAssoc` identifies the iterated pullback of `f` along `h` and
then `k` with the pullback of `f` along `h.comp k`. Its forward map forgets the intermediate
coordinate, and its inverse inserts the image under `k`.

`ContinuousLinearMap.pullbackAssoc_naturality` states that this comparison commutes with
the maps of pullbacks induced by semilinear maps of the defining diagrams.

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

section Naturality

universe uS uE₁ uF₁ uG₁ uH₁ uE₂ uF₂ uG₂ uH₂

variable {S : Type uS} [Semiring S] {σ : R →+* S}
  {E₁ : Type uE₁} {F₁ : Type uF₁} {G₁ : Type uG₁} {H₁ : Type uH₁}
  {E₂ : Type uE₂} {F₂ : Type uF₂} {G₂ : Type uG₂} {H₂ : Type uH₂}
  [AddCommMonoid E₁] [Module R E₁] [TopologicalSpace E₁]
  [AddCommMonoid F₁] [Module R F₁] [TopologicalSpace F₁]
  [AddCommMonoid G₁] [Module R G₁] [TopologicalSpace G₁]
  [AddCommMonoid H₁] [Module R H₁] [TopologicalSpace H₁]
  [AddCommMonoid E₂] [Module S E₂] [TopologicalSpace E₂]
  [AddCommMonoid F₂] [Module S F₂] [TopologicalSpace F₂]
  [AddCommMonoid G₂] [Module S G₂] [TopologicalSpace G₂]
  [AddCommMonoid H₂] [Module S H₂] [TopologicalSpace H₂]

/-- Pullback associativity is natural under commuting semilinear maps of the defining
diagrams: forgetting the intermediate coordinate commutes with the induced pullback maps. -/
theorem pullbackAssoc_naturality
    (f₁ : E₁ →L[R] F₁) (h₁ : G₁ →L[R] F₁) (k₁ : H₁ →L[R] G₁)
    (f₂ : E₂ →L[S] F₂) (h₂ : G₂ →L[S] F₂) (k₂ : H₂ →L[S] G₂)
    (u : E₁ →SL[σ] E₂) (v : F₁ →SL[σ] F₂)
    (w : G₁ →SL[σ] G₂) (z : H₁ →SL[σ] H₂)
    (hf : f₂.comp u = v.comp f₁) (hh : h₂.comp w = v.comp h₁)
    (hk : k₂.comp z = w.comp k₁) :
    let P₁ := LinearMap.eqLocus
      (f₁.toLinearMap.comp (LinearMap.fst R E₁ G₁))
      (h₁.toLinearMap.comp (LinearMap.snd R E₁ G₁))
    let p₁ := (snd R E₁ G₁).domRestrict P₁
    let P₂ := LinearMap.eqLocus
      (f₂.toLinearMap.comp (LinearMap.fst S E₂ G₂))
      (h₂.toLinearMap.comp (LinearMap.snd S E₂ G₂))
    let p₂ := (snd S E₂ G₂).domRestrict P₂
    let Pmap := pullbackMap f₁ h₁ f₂ h₂ u v w hf hh
    let hP : p₂.comp Pmap = w.comp p₁ :=
      snd_comp_pullbackMap f₁ h₁ f₂ h₂ u v w hf hh
    let hhk : (h₂.comp k₂).comp z = v.comp (h₁.comp k₁) := by
      apply DFunLike.ext
      intro s
      exact (congrArg h₂ (DFunLike.congr_fun hk s)).trans
        (DFunLike.congr_fun hh (k₁ s))
    (pullbackAssoc f₂ h₂ k₂).toContinuousLinearMap.comp (σ₁₃ := σ)
        (pullbackMap p₁ k₁ p₂ k₂ Pmap w z hP hk) =
      (pullbackMap f₁ (h₁.comp k₁) f₂ (h₂.comp k₂) u v z hf hhk).comp (σ₁₃ := σ)
        (pullbackAssoc f₁ h₁ k₁).toContinuousLinearMap := by
  dsimp only
  apply DFunLike.ext
  intro q
  apply Subtype.ext
  simp only [comp_apply, ContinuousLinearEquiv.coe_coe, coe_pullbackAssoc_apply,
    pullbackMap_apply]

end Naturality

end ContinuousLinearMap
