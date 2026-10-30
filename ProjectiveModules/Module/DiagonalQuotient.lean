/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Prod

/-!
# Diagonal quotients of products of modules

For linear maps `f : X →ₗ[S] M` and `g : X →ₗ[S] N`, the quotient of `M × N` by
`LinearMap.range (f.prod g)` maps canonically onto the product of the two range quotients.
Its kernel is the image of `x ↦ [(f x, 0)]`, whose kernel is `ker f ⊔ ker g`.
Consequently, the quotient of `X` by this kernel sum identifies canonically with the
kernel of the projection.

## Main definitions

* `LinearMap.DiagonalQuotient.left`: the map `x ↦ [(f x, 0)]`.
* `LinearMap.DiagonalQuotient.projection`: the map to the product of range quotients.
* `LinearMap.DiagonalQuotient.map`: the map on diagonal quotients induced by commuting squares.
* `LinearMap.DiagonalQuotient.cokernelProdMap`: the corresponding map on product cokernels.
* `LinearMap.DiagonalQuotient.congr`: transport by coordinate equivalences carrying the
  relation range exactly onto the target relation range.
* `LinearMap.DiagonalQuotient.quotientKerEquiv`: the canonical identification of
  `X ⧸ (ker f ⊔ ker g)` with the kernel of the projection.
* `LinearMap.DiagonalQuotient.quotientKerMap`: the induced map on the source kernel-sum quotients.
* `LinearMap.DiagonalQuotient.kerMap`: the induced map on the projection kernels.

For the pair of identity maps on any module, the left map is bijective, and the class
of `(x, y)` is the image of `x - y`. The ring need not be commutative or nontrivial,
and the scalar ring and all modules have independent universes. Commuting squares induce
maps on diagonal quotients and product cokernels. These respect the left maps and the
projections, and satisfy the identity and composition laws. Surjective coordinate maps
make both induced maps surjective. If the common-source map is surjective,
injective or bijective coordinate maps induce injective or bijective quotient maps,
respectively.
Coordinate equivalences transporting the relation range give a presentation equivalence,
with componentwise forward and inverse representative formulas. For commuting squares its
underlying linear map is the induced quotient map; surjectivity of the common-source map
is sufficient to establish the required relation-range equality.

For arbitrary commuting squares, `quotientKerMap_mk` and `kerMap_coe` describe the
source-quotient and projection-kernel maps on representatives and ambient values.
The determining properties `quotientKerMap_unique` and `kerMap_unique` characterize
these maps by composition with the source quotient map and the target kernel inclusion,
respectively. With `θ = quotientKerEquiv f g`, `θ' = quotientKerEquiv f' g'`,
`h̄ = quotientKerMap f g f' g' h u v hf hg` and `κ = kerMap f g f' g' h u v hf hg`,
`kerMap_comp_quotientKerEquiv` states the equality of linear maps
`κ.comp θ.toLinearMap = θ'.toLinearMap.comp h̄`. This naturality uses the characteristic
API without unfolding either induced map, and requires no injectivity or surjectivity.

## Implementation notes

The canonical maps use the stock submodule quotient maps and quotient descent. The
kernel equivalence uses the stock first isomorphism theorem and transport along equal
submodules.

## References

* Mathlib's product, submodule-quotient and first-isomorphism APIs in
  `Mathlib.LinearAlgebra.Prod`, `Mathlib.LinearAlgebra.Quotient.Basic`, and
  `Mathlib.LinearAlgebra.Isomorphisms`.
* Mathlib's kernel, restriction and extensionality APIs in
  `Mathlib.Algebra.Module.Submodule.Ker`, `Mathlib.Algebra.Module.Submodule.LinearMap`,
  and `Mathlib.Algebra.Module.LinearMap.Defs`, and its linear-equivalence coercion API
  in `Mathlib.Algebra.Module.Equiv.Defs`.
-/

@[expose] public section

universe uS uX uM uN

namespace LinearMap.DiagonalQuotient

variable {S : Type uS} [Ring S]
variable {X : Type uX} {M : Type uM} {N : Type uN}
variable [AddCommGroup X] [AddCommGroup M] [AddCommGroup N]
variable [Module S X] [Module S M] [Module S N]
variable (f : X →ₗ[S] M) (g : X →ₗ[S] N)

/-- The class of the first coordinate of the common-source diagonal map. -/
def left : X →ₗ[S] (M × N) ⧸ LinearMap.range (f.prod g) :=
  (LinearMap.range (f.prod g)).mkQ.comp (f.prod (0 : X →ₗ[S] N))

/-- The canonical projection from a diagonal range quotient to the two range quotients. -/
def projection :
    ((M × N) ⧸ LinearMap.range (f.prod g)) →ₗ[S]
      (M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g) :=
  (LinearMap.range (f.prod g)).liftQ
    ((LinearMap.range f).mkQ.prodMap (LinearMap.range g).mkQ) (by
      rintro _ ⟨x, rfl⟩
      change ((LinearMap.range f).mkQ (f x), (LinearMap.range g).mkQ (g x)) = (0, 0)
      apply Prod.ext
      · exact congrArg (fun h : X →ₗ[S] M ⧸ LinearMap.range f => h x)
          (LinearMap.range_mkQ_comp f)
      · exact congrArg (fun h : X →ₗ[S] N ⧸ LinearMap.range g => h x)
          (LinearMap.range_mkQ_comp g))

/-- The defining representative formula for the left map. -/
@[simp] theorem left_apply (x : X) :
    left f g x = Submodule.Quotient.mk (f x, (0 : N)) := by
  rfl

/-- The defining representative formula for the projection. -/
@[simp] theorem projection_mk (m : M) (n : N) :
    projection f g (Submodule.Quotient.mk (m, n)) =
      (Submodule.Quotient.mk m, Submodule.Quotient.mk n) := by
  simp only [projection, Submodule.liftQ_apply, LinearMap.prodMap_apply, Submodule.mkQ_apply]

/-- The projection descends the product of the two quotient maps. -/
theorem projection_comp_mkQ :
    (projection f g).comp (LinearMap.range (f.prod g)).mkQ =
      (LinearMap.range f).mkQ.prodMap (LinearMap.range g).mkQ := by
  exact Submodule.liftQ_mkQ _ _ _

/-- The projection kills the image of the left map. -/
@[simp] theorem projection_comp_left : (projection f g).comp (left f g) = 0 := by
  ext1 x
  change projection f g (left f g x) = 0
  rw [left_apply, projection_mk]
  apply Prod.ext
  · exact congrArg (fun h : X →ₗ[S] M ⧸ LinearMap.range f => h x)
      (LinearMap.range_mkQ_comp f)
  · exact map_zero (LinearMap.range g).mkQ

/-- Every pair of range-quotient classes has a representative in the diagonal quotient. -/
theorem projection_surjective : Function.Surjective (projection f g) := by
  rintro ⟨a, b⟩
  obtain ⟨m, rfl⟩ := (LinearMap.range f).mkQ_surjective a
  obtain ⟨n, rfl⟩ := (LinearMap.range g).mkQ_surjective b
  refine ⟨Submodule.Quotient.mk (m, n), ?_⟩
  simpa only [Submodule.mkQ_apply] using projection_mk f g m n

/-- Exactness at the quotient of the product by the common-source diagonal range. -/
theorem range_left : LinearMap.range (left f g) = LinearMap.ker (projection f g) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change projection f g (left f g x) = 0
    exact congrArg
      (fun h : X →ₗ[S] (M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g) => h x)
      (projection_comp_left f g)
  · intro z hz
    change projection f g z = 0 at hz
    obtain ⟨⟨m, n⟩, rfl⟩ := (LinearMap.range (f.prod g)).mkQ_surjective z
    change projection f g (Submodule.Quotient.mk (m, n)) = 0 at hz
    rw [projection_mk] at hz
    have hm : (Submodule.Quotient.mk m : M ⧸ LinearMap.range f) = 0 :=
      congrArg Prod.fst hz
    have hn : (Submodule.Quotient.mk n : N ⧸ LinearMap.range g) = 0 :=
      congrArg Prod.snd hz
    rcases (Submodule.Quotient.mk_eq_zero (p := LinearMap.range f)).mp hm with ⟨x, hx⟩
    rcases (Submodule.Quotient.mk_eq_zero (p := LinearMap.range g)).mp hn with ⟨y, hy⟩
    refine ⟨x - y, ?_⟩
    change left f g (x - y) = Submodule.Quotient.mk (m, n)
    symm
    rw [left_apply, Submodule.Quotient.eq]
    refine ⟨y, ?_⟩
    apply Prod.ext
    · change f y = m - f (x - y)
      rw [map_sub, hx]
      simp only [sub_sub_cancel]
    · change g y = n - 0
      rw [hy, sub_zero]

/-- The kernel of the left map is the sum, not the intersection, of the two kernels. -/
theorem ker_left : LinearMap.ker (left f g) = LinearMap.ker f ⊔ LinearMap.ker g := by
  apply le_antisymm
  · intro x hx
    change left f g x = 0 at hx
    rw [left_apply, Submodule.Quotient.mk_eq_zero] at hx
    rcases hx with ⟨y, hy⟩
    have hfy : f y = f x := congrArg Prod.fst hy
    have hgy : g y = 0 := congrArg Prod.snd hy
    have hxmy : x - y ∈ LinearMap.ker f := by
      change f (x - y) = 0
      rw [map_sub, hfy, sub_self]
    have hyker : y ∈ LinearMap.ker g := hgy
    have hsum : x - y + y ∈ LinearMap.ker f ⊔ LinearMap.ker g :=
      (LinearMap.ker f ⊔ LinearMap.ker g).add_mem
        ((le_sup_left : LinearMap.ker f ≤ LinearMap.ker f ⊔ LinearMap.ker g) hxmy)
        ((le_sup_right : LinearMap.ker g ≤ LinearMap.ker f ⊔ LinearMap.ker g) hyker)
    simpa only [sub_add_cancel] using hsum
  · refine sup_le ?_ ?_
    · intro x hx
      change f x = 0 at hx
      change left f g x = 0
      calc
        left f g x = left f g 0 := by rw [left_apply, left_apply, hx, map_zero]
        _ = 0 := (left f g).map_zero
    · intro x hx
      change g x = 0 at hx
      change left f g x = 0
      rw [left_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨x, Prod.ext rfl hx⟩

/-- A class from the left map vanishes precisely on the sum of the two kernels. -/
theorem left_eq_zero_iff (x : X) :
    left f g x = 0 ↔ x ∈ LinearMap.ker f ⊔ LinearMap.ker g := by
  change x ∈ LinearMap.ker (left f g) ↔ x ∈ LinearMap.ker f ⊔ LinearMap.ker g
  rw [ker_left]

/-- The zero fiber of the projection consists of the classes from the left map. -/
theorem projection_eq_zero_iff (z : (M × N) ⧸ LinearMap.range (f.prod g)) :
    projection f g z = 0 ↔ ∃ x : X, left f g x = z := by
  change z ∈ LinearMap.ker (projection f g) ↔ ∃ x : X, left f g x = z
  rw [← range_left]
  rfl

/-- The first isomorphism theorem identifies the kernel of the projection canonically. -/
noncomputable def quotientKerEquiv :
    (X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g)) ≃ₗ[S] LinearMap.ker (projection f g) :=
  (Submodule.quotEquivOfEq _ _ (ker_left f g).symm).trans
    ((left f g).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (range_left f g)))

/-- The kernel equivalence sends a source class to its class in the product quotient. -/
theorem quotientKerEquiv_mk (x : X) :
    (quotientKerEquiv f g (Submodule.Quotient.mk x) :
      (M × N) ⧸ LinearMap.range (f.prod g)) = left f g x := by
  simp only [quotientKerEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearEquiv.coe_ofEq_apply, LinearMap.quotKerEquivRange_apply_mk]

end LinearMap.DiagonalQuotient

namespace LinearMap.DiagonalQuotient

variable {S : Type uS} [Ring S]
variable {X : Type uX} [AddCommGroup X] [Module S X]

/-- In the quotient by the identity diagonal, `(x, y)` is represented by `(x - y, 0)`. -/
theorem left_id_sub (x y : X) :
    left (LinearMap.id : X →ₗ[S] X) (LinearMap.id : X →ₗ[S] X) (x - y) =
      Submodule.Quotient.mk (x, y) := by
  symm
  rw [left_apply, Submodule.Quotient.eq]
  refine ⟨y, ?_⟩
  apply Prod.ext
  · change y = x - (x - y)
    simp only [sub_sub_cancel]
  · change y = y - 0
    exact (sub_zero y).symm

/-- With both inputs the identity, the left map identifies the diagonal quotient with
its original module. -/
theorem left_id_bijective :
    Function.Bijective
      (left (LinearMap.id : X →ₗ[S] X) (LinearMap.id : X →ₗ[S] X)) := by
  constructor
  · intro x y h
    simp only [left_apply, Submodule.Quotient.eq] at h
    rcases h with ⟨z, hz⟩
    have hxy : z = x - y := congrArg Prod.fst hz
    have hz0 : z = 0 := by
      have hz2 := congrArg Prod.snd hz
      change z = (0 : X) - 0 at hz2
      simpa only [sub_self] using hz2
    exact sub_eq_zero.mp (hxy.symm.trans hz0)
  · intro z
    obtain ⟨⟨x, y⟩, rfl⟩ :=
      (LinearMap.range
        ((LinearMap.id : X →ₗ[S] X).prod (LinearMap.id : X →ₗ[S] X))).mkQ_surjective z
    exact ⟨x - y, left_id_sub (S := S) x y⟩

end LinearMap.DiagonalQuotient

namespace LinearMap.DiagonalQuotient

universe uX' uM' uN' uX'' uM'' uN''

variable {S : Type uS} [Ring S]
variable {X : Type uX} {M : Type uM} {N : Type uN}
variable {X' : Type uX'} {M' : Type uM'} {N' : Type uN'}
variable [AddCommGroup X] [AddCommGroup M] [AddCommGroup N]
variable [AddCommGroup X'] [AddCommGroup M'] [AddCommGroup N']
variable [Module S X] [Module S M] [Module S N]
variable [Module S X'] [Module S M'] [Module S N']
variable (f : X →ₗ[S] M) (g : X →ₗ[S] N)
variable (f' : X' →ₗ[S] M') (g' : X' →ₗ[S] N')
variable (h : X →ₗ[S] X') (u : M →ₗ[S] M') (v : N →ₗ[S] N')
variable (hf : u.comp f = f'.comp h) (hg : v.comp g = g'.comp h)

/-- A pair of commuting squares induces a linear map on the diagonal range quotients. -/
def map :
    ((M × N) ⧸ LinearMap.range (f.prod g)) →ₗ[S]
      (M' × N') ⧸ LinearMap.range (f'.prod g') :=
  (LinearMap.range (f.prod g)).liftQ
    ((LinearMap.range (f'.prod g')).mkQ.comp (u.prodMap v)) (by
      rintro _ ⟨x, rfl⟩
      change (LinearMap.range (f'.prod g')).mkQ (u (f x), v (g x)) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨h x, ?_⟩
      apply Prod.ext
      · exact (congrArg (fun k : X →ₗ[S] M' => k x) hf).symm
      · exact (congrArg (fun k : X →ₗ[S] N' => k x) hg).symm)

/-- A pair of commuting squares induces the product map on the two range quotients. -/
def cokernelProdMap :
    (M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g) →ₗ[S]
      (M' ⧸ LinearMap.range f') × (N' ⧸ LinearMap.range g') :=
  ((LinearMap.range f).liftQ ((LinearMap.range f').mkQ.comp u) (by
    rintro _ ⟨x, rfl⟩
    change (LinearMap.range f').mkQ (u (f x)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨h x, (congrArg (fun k : X →ₗ[S] M' => k x) hf).symm⟩)).prodMap
      ((LinearMap.range g).liftQ ((LinearMap.range g').mkQ.comp v) (by
        rintro _ ⟨x, rfl⟩
        change (LinearMap.range g').mkQ (v (g x)) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨h x, (congrArg (fun k : X →ₗ[S] N' => k x) hg).symm⟩))

/-- The induced diagonal-quotient map applies the two maps to a representative. -/
@[simp] theorem map_mk (m : M) (n : N) :
    map f g f' g' h u v hf hg (Submodule.Quotient.mk (m, n)) =
      Submodule.Quotient.mk (u m, v n) := by
  simp only [map, Submodule.liftQ_apply]
  change (LinearMap.range (f'.prod g')).mkQ ((u.prodMap v) (m, n)) = _
  simp only [LinearMap.prodMap_apply, Submodule.mkQ_apply]

/-- The induced product-cokernel map applies each map to its representative. -/
@[simp] theorem cokernelProdMap_mk (m : M) (n : N) :
    cokernelProdMap f g f' g' h u v hf hg
        (Submodule.Quotient.mk m, Submodule.Quotient.mk n) =
      (Submodule.Quotient.mk (u m), Submodule.Quotient.mk (v n)) := by
  simp only [cokernelProdMap, LinearMap.prodMap_apply, Submodule.liftQ_apply]
  change ((LinearMap.range f').mkQ (u m), (LinearMap.range g').mkQ (v n)) = _
  simp only [Submodule.mkQ_apply]

/-- The diagonal-quotient map descends the product map followed by the quotient map. -/
theorem map_comp_mkQ :
    (map f g f' g' h u v hf hg).comp (LinearMap.range (f.prod g)).mkQ =
      (LinearMap.range (f'.prod g')).mkQ.comp (u.prodMap v) := by
  exact Submodule.liftQ_mkQ _ _ _

/-- The product-cokernel map descends the coordinate maps to the two quotient factors. -/
theorem cokernelProdMap_comp_mkQ :
    (cokernelProdMap f g f' g' h u v hf hg).comp
        ((LinearMap.range f).mkQ.prodMap (LinearMap.range g).mkQ) =
      ((LinearMap.range f').mkQ.comp u).prodMap ((LinearMap.range g').mkQ.comp v) := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨m, n⟩
  exact cokernelProdMap_mk f g f' g' h u v hf hg m n

/-- The representative formula uniquely determines the diagonal-quotient map. -/
theorem map_unique
    (a : ((M × N) ⧸ LinearMap.range (f.prod g)) →ₗ[S]
      (M' × N') ⧸ LinearMap.range (f'.prod g'))
    (ha : a.comp (LinearMap.range (f.prod g)).mkQ =
      (LinearMap.range (f'.prod g')).mkQ.comp (u.prodMap v)) :
    a = map f g f' g' h u v hf hg := by
  apply LinearMap.ext
  intro z
  obtain ⟨p, rfl⟩ := (LinearMap.range (f.prod g)).mkQ_surjective z
  exact congrArg
    (fun k : (M × N) →ₗ[S] (M' × N') ⧸ LinearMap.range (f'.prod g') => k p)
    (ha.trans (map_comp_mkQ f g f' g' h u v hf hg).symm)

/-- The representative formula uniquely determines the product-cokernel map. -/
theorem cokernelProdMap_unique
    (a : (M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g) →ₗ[S]
      (M' ⧸ LinearMap.range f') × (N' ⧸ LinearMap.range g'))
    (ha : a.comp ((LinearMap.range f).mkQ.prodMap (LinearMap.range g).mkQ) =
      ((LinearMap.range f').mkQ.comp u).prodMap ((LinearMap.range g').mkQ.comp v)) :
    a = cokernelProdMap f g f' g' h u v hf hg := by
  apply LinearMap.ext
  intro z
  rcases z with ⟨qm, qn⟩
  obtain ⟨m, rfl⟩ := (LinearMap.range f).mkQ_surjective qm
  obtain ⟨n, rfl⟩ := (LinearMap.range g).mkQ_surjective qn
  exact congrArg
    (fun k : (M × N) →ₗ[S]
      (M' ⧸ LinearMap.range f') × (N' ⧸ LinearMap.range g') => k (m, n))
    (ha.trans (cokernelProdMap_comp_mkQ f g f' g' h u v hf hg).symm)

/-- Surjective coordinate maps induce a surjective map on diagonal quotients. -/
theorem map_surjective
    (f : X →ₗ[S] M) (g : X →ₗ[S] N)
    (f' : X' →ₗ[S] M') (g' : X' →ₗ[S] N')
    (h : X →ₗ[S] X') (u : M →ₗ[S] M') (v : N →ₗ[S] N')
    (hf : u.comp f = f'.comp h) (hg : v.comp g = g'.comp h)
    (hu : Function.Surjective u) (hv : Function.Surjective v) :
    Function.Surjective (LinearMap.DiagonalQuotient.map f g f' g' h u v hf hg) := by
  intro z
  obtain ⟨⟨m', n'⟩, rfl⟩ := (LinearMap.range (f'.prod g')).mkQ_surjective z
  obtain ⟨m, rfl⟩ := hu m'
  obtain ⟨n, rfl⟩ := hv n'
  refine ⟨Submodule.Quotient.mk (m, n), ?_⟩
  simpa only [Submodule.mkQ_apply] using map_mk f g f' g' h u v hf hg m n

/-- Surjective coordinate maps induce a surjective map on the product of cokernels. -/
theorem cokernelProdMap_surjective
    (f : X →ₗ[S] M) (g : X →ₗ[S] N)
    (f' : X' →ₗ[S] M') (g' : X' →ₗ[S] N')
    (h : X →ₗ[S] X') (u : M →ₗ[S] M') (v : N →ₗ[S] N')
    (hf : u.comp f = f'.comp h) (hg : v.comp g = g'.comp h)
    (hu : Function.Surjective u) (hv : Function.Surjective v) :
    Function.Surjective
      (LinearMap.DiagonalQuotient.cokernelProdMap f g f' g' h u v hf hg) := by
  rintro ⟨qm', qn'⟩
  obtain ⟨m', rfl⟩ := (LinearMap.range f').mkQ_surjective qm'
  obtain ⟨n', rfl⟩ := (LinearMap.range g').mkQ_surjective qn'
  obtain ⟨m, rfl⟩ := hu m'
  obtain ⟨n, rfl⟩ := hv n'
  refine ⟨(Submodule.Quotient.mk m, Submodule.Quotient.mk n), ?_⟩
  simpa only [Submodule.mkQ_apply] using cokernelProdMap_mk f g f' g' h u v hf hg m n

/-- The left maps commute with a pair of commuting squares. -/
theorem map_comp_left :
    (map f g f' g' h u v hf hg).comp (left f g) = (left f' g').comp h := by
  ext1 x
  change map f g f' g' h u v hf hg (left f g x) = left f' g' (h x)
  have hfx : u (f x) = f' (h x) :=
    congrArg (fun k : X →ₗ[S] M' => k x) hf
  rw [left_apply, map_mk, left_apply, map_zero, hfx]

/-- The projections commute with the induced diagonal-quotient and product-cokernel maps. -/
theorem projection_comp_map :
    (projection f' g').comp (map f g f' g' h u v hf hg) =
      (cokernelProdMap f g f' g' h u v hf hg).comp (projection f g) := by
  apply LinearMap.ext
  intro z
  obtain ⟨⟨m, n⟩, rfl⟩ := (LinearMap.range (f.prod g)).mkQ_surjective z
  change projection f' g' (map f g f' g' h u v hf hg (Submodule.Quotient.mk (m, n))) =
    cokernelProdMap f g f' g' h u v hf hg (projection f g (Submodule.Quotient.mk (m, n)))
  rw [map_mk, projection_mk, projection_mk, cokernelProdMap_mk]

/-- Identity commuting squares induce the identity on the diagonal quotient. -/
@[simp] theorem map_id :
    map f g f g (LinearMap.id : X →ₗ[S] X)
        (LinearMap.id : M →ₗ[S] M) (LinearMap.id : N →ₗ[S] N) rfl rfl =
      (LinearMap.id : ((M × N) ⧸ LinearMap.range (f.prod g)) →ₗ[S]
        (M × N) ⧸ LinearMap.range (f.prod g)) := by
  apply LinearMap.ext
  intro z
  obtain ⟨⟨m, n⟩, rfl⟩ := (LinearMap.range (f.prod g)).mkQ_surjective z
  change map f g f g (LinearMap.id : X →ₗ[S] X)
    (LinearMap.id : M →ₗ[S] M) (LinearMap.id : N →ₗ[S] N) rfl rfl
    (Submodule.Quotient.mk (m, n)) = Submodule.Quotient.mk (m, n)
  exact map_mk f g f g (LinearMap.id : X →ₗ[S] X)
    (LinearMap.id : M →ₗ[S] M) (LinearMap.id : N →ₗ[S] N) rfl rfl m n

/-- Identity commuting squares induce the identity on the product of the two cokernels. -/
@[simp] theorem cokernelProdMap_id :
    cokernelProdMap f g f g (LinearMap.id : X →ₗ[S] X)
        (LinearMap.id : M →ₗ[S] M) (LinearMap.id : N →ₗ[S] N) rfl rfl =
      (LinearMap.id : (M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g) →ₗ[S]
        (M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g)) := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨a, b⟩
  obtain ⟨m, rfl⟩ := (LinearMap.range f).mkQ_surjective a
  obtain ⟨n, rfl⟩ := (LinearMap.range g).mkQ_surjective b
  change cokernelProdMap f g f g (LinearMap.id : X →ₗ[S] X)
    (LinearMap.id : M →ₗ[S] M) (LinearMap.id : N →ₗ[S] N) rfl rfl
    (Submodule.Quotient.mk m, Submodule.Quotient.mk n) =
      (Submodule.Quotient.mk m, Submodule.Quotient.mk n)
  exact cokernelProdMap_mk f g f g (LinearMap.id : X →ₗ[S] X)
    (LinearMap.id : M →ₗ[S] M) (LinearMap.id : N →ₗ[S] N) rfl rfl m n

/-- Injective coordinate maps and a surjective common-source map induce an injective map
on diagonal quotients. -/
theorem map_injective
    (f : X →ₗ[S] M) (g : X →ₗ[S] N)
    (f' : X' →ₗ[S] M') (g' : X' →ₗ[S] N')
    (h : X →ₗ[S] X') (u : M →ₗ[S] M') (v : N →ₗ[S] N')
    (hf : u.comp f = f'.comp h) (hg : v.comp g = g'.comp h)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hh : Function.Surjective h) :
    Function.Injective (LinearMap.DiagonalQuotient.map f g f' g' h u v hf hg) := by
  intro a b hab
  obtain ⟨⟨m₁, n₁⟩, rfl⟩ := (LinearMap.range (f.prod g)).mkQ_surjective a
  obtain ⟨⟨m₂, n₂⟩, rfl⟩ := (LinearMap.range (f.prod g)).mkQ_surjective b
  simp only [Submodule.mkQ_apply, map_mk, Submodule.Quotient.eq] at hab
  rcases hab with ⟨x', hx'⟩
  obtain ⟨x, rfl⟩ := hh x'
  change (Submodule.Quotient.mk (m₁, n₁) :
    (M × N) ⧸ LinearMap.range (f.prod g)) = Submodule.Quotient.mk (m₂, n₂)
  rw [Submodule.Quotient.eq]
  refine ⟨x, ?_⟩
  apply Prod.ext
  · change f x = m₁ - m₂
    apply hu
    rw [map_sub]
    exact (congrArg (fun k : X →ₗ[S] M' => k x) hf).trans
      (congrArg Prod.fst hx')
  · change g x = n₁ - n₂
    apply hv
    rw [map_sub]
    exact (congrArg (fun k : X →ₗ[S] N' => k x) hg).trans
      (congrArg Prod.snd hx')

/-- Injective coordinate maps and a surjective common-source map induce an injective map
on the product of cokernels. -/
theorem cokernelProdMap_injective
    (f : X →ₗ[S] M) (g : X →ₗ[S] N)
    (f' : X' →ₗ[S] M') (g' : X' →ₗ[S] N')
    (h : X →ₗ[S] X') (u : M →ₗ[S] M') (v : N →ₗ[S] N')
    (hf : u.comp f = f'.comp h) (hg : v.comp g = g'.comp h)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hh : Function.Surjective h) :
    Function.Injective
      (LinearMap.DiagonalQuotient.cokernelProdMap f g f' g' h u v hf hg) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hab
  obtain ⟨m₁, rfl⟩ := (LinearMap.range f).mkQ_surjective a₁
  obtain ⟨n₁, rfl⟩ := (LinearMap.range g).mkQ_surjective b₁
  obtain ⟨m₂, rfl⟩ := (LinearMap.range f).mkQ_surjective a₂
  obtain ⟨n₂, rfl⟩ := (LinearMap.range g).mkQ_surjective b₂
  simp only [Submodule.mkQ_apply, cokernelProdMap_mk] at hab
  have hm : (Submodule.Quotient.mk (u m₁) : M' ⧸ LinearMap.range f') =
      Submodule.Quotient.mk (u m₂) := congrArg Prod.fst hab
  have hn : (Submodule.Quotient.mk (v n₁) : N' ⧸ LinearMap.range g') =
      Submodule.Quotient.mk (v n₂) := congrArg Prod.snd hab
  rw [Submodule.Quotient.eq] at hm hn
  rcases hm with ⟨x', hx'⟩
  rcases hn with ⟨y', hy'⟩
  obtain ⟨x, rfl⟩ := hh x'
  obtain ⟨y, rfl⟩ := hh y'
  apply Prod.ext
  · change (Submodule.Quotient.mk m₁ : M ⧸ LinearMap.range f) = Submodule.Quotient.mk m₂
    rw [Submodule.Quotient.eq]
    refine ⟨x, ?_⟩
    apply hu
    rw [map_sub]
    exact (congrArg (fun k : X →ₗ[S] M' => k x) hf).trans hx'
  · change (Submodule.Quotient.mk n₁ : N ⧸ LinearMap.range g) = Submodule.Quotient.mk n₂
    rw [Submodule.Quotient.eq]
    refine ⟨y, ?_⟩
    apply hv
    rw [map_sub]
    exact (congrArg (fun k : X →ₗ[S] N' => k y) hg).trans hy'

/-- Bijective coordinate maps and a surjective common-source map induce a bijection
on diagonal quotients. -/
theorem map_bijective
    (f : X →ₗ[S] M) (g : X →ₗ[S] N)
    (f' : X' →ₗ[S] M') (g' : X' →ₗ[S] N')
    (h : X →ₗ[S] X') (u : M →ₗ[S] M') (v : N →ₗ[S] N')
    (hf : u.comp f = f'.comp h) (hg : v.comp g = g'.comp h)
    (hu : Function.Bijective u) (hv : Function.Bijective v)
    (hh : Function.Surjective h) :
    Function.Bijective (LinearMap.DiagonalQuotient.map f g f' g' h u v hf hg) := by
  exact ⟨map_injective f g f' g' h u v hf hg hu.1 hv.1 hh,
    map_surjective f g f' g' h u v hf hg hu.2 hv.2⟩

/-- Bijective coordinate maps and a surjective common-source map induce a bijection
on the product of cokernels. -/
theorem cokernelProdMap_bijective
    (f : X →ₗ[S] M) (g : X →ₗ[S] N)
    (f' : X' →ₗ[S] M') (g' : X' →ₗ[S] N')
    (h : X →ₗ[S] X') (u : M →ₗ[S] M') (v : N →ₗ[S] N')
    (hf : u.comp f = f'.comp h) (hg : v.comp g = g'.comp h)
    (hu : Function.Bijective u) (hv : Function.Bijective v)
    (hh : Function.Surjective h) :
    Function.Bijective
      (LinearMap.DiagonalQuotient.cokernelProdMap f g f' g' h u v hf hg) := by
  exact ⟨cokernelProdMap_injective f g f' g' h u v hf hg hu.1 hv.1 hh,
    cokernelProdMap_surjective f g f' g' h u v hf hg hu.2 hv.2⟩

variable {X'' : Type uX''} {M'' : Type uM''} {N'' : Type uN''}
variable [AddCommGroup X''] [AddCommGroup M''] [AddCommGroup N'']
variable [Module S X''] [Module S M''] [Module S N'']
variable (f'' : X'' →ₗ[S] M'') (g'' : X'' →ₗ[S] N'')
variable (h' : X' →ₗ[S] X'') (u' : M' →ₗ[S] M'') (v' : N' →ₗ[S] N'')
variable (hf' : u'.comp f' = f''.comp h') (hg' : v'.comp g' = g''.comp h')

/-- Composing commuting squares composes their induced diagonal-quotient maps. -/
theorem map_comp :
    (map f' g' f'' g'' h' u' v' hf' hg').comp (map f g f' g' h u v hf hg) =
      map f g f'' g'' (h'.comp h) (u'.comp u) (v'.comp v)
        (by
          ext x
          exact (congrArg u' (congrArg (fun k : X →ₗ[S] M' => k x) hf)).trans
            (congrArg (fun k : X' →ₗ[S] M'' => k (h x)) hf'))
        (by
          ext x
          exact (congrArg v' (congrArg (fun k : X →ₗ[S] N' => k x) hg)).trans
            (congrArg (fun k : X' →ₗ[S] N'' => k (h x)) hg')) := by
  apply LinearMap.ext
  intro z
  obtain ⟨⟨m, n⟩, rfl⟩ := (LinearMap.range (f.prod g)).mkQ_surjective z
  change map f' g' f'' g'' h' u' v' hf' hg'
    (map f g f' g' h u v hf hg (Submodule.Quotient.mk (m, n))) = _
  simp only [Submodule.mkQ_apply, map_mk]
  rfl

/-- Composing commuting squares composes their induced product-cokernel maps. -/
theorem cokernelProdMap_comp :
    (cokernelProdMap f' g' f'' g'' h' u' v' hf' hg').comp
        (cokernelProdMap f g f' g' h u v hf hg) =
      cokernelProdMap f g f'' g'' (h'.comp h) (u'.comp u) (v'.comp v)
        (by
          ext x
          exact (congrArg u' (congrArg (fun k : X →ₗ[S] M' => k x) hf)).trans
            (congrArg (fun k : X' →ₗ[S] M'' => k (h x)) hf'))
        (by
          ext x
          exact (congrArg v' (congrArg (fun k : X →ₗ[S] N' => k x) hg)).trans
            (congrArg (fun k : X' →ₗ[S] N'' => k (h x)) hg')) := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨a, b⟩
  obtain ⟨m, rfl⟩ := (LinearMap.range f).mkQ_surjective a
  obtain ⟨n, rfl⟩ := (LinearMap.range g).mkQ_surjective b
  change cokernelProdMap f' g' f'' g'' h' u' v' hf' hg'
    (cokernelProdMap f g f' g' h u v hf hg
      (Submodule.Quotient.mk m, Submodule.Quotient.mk n)) = _
  simp only [Submodule.mkQ_apply, cokernelProdMap_mk]
  rfl

end LinearMap.DiagonalQuotient

namespace LinearMap.DiagonalQuotient

universe uX' uM' uN'

variable {S : Type uS} [Ring S]
variable {X : Type uX} {M : Type uM} {N : Type uN}
variable {X' : Type uX'} {M' : Type uM'} {N' : Type uN'}
variable [AddCommGroup X] [AddCommGroup M] [AddCommGroup N]
variable [AddCommGroup X'] [AddCommGroup M'] [AddCommGroup N']
variable [Module S X] [Module S M] [Module S N]
variable [Module S X'] [Module S M'] [Module S N']
variable (f : X →ₗ[S] M) (g : X →ₗ[S] N)
variable (f' : X' →ₗ[S] M') (g' : X' →ₗ[S] N')
/-- Commuting squares with a surjective common-source map transport the diagonal relation
range onto the target diagonal relation range under the product of the coordinate maps. -/
theorem map_range_prod (h : X →ₗ[S] X') (u0 : M →ₗ[S] M') (v0 : N →ₗ[S] N')
    (hf : u0.comp f = f'.comp h) (hg : v0.comp g = g'.comp h)
    (hh : Function.Surjective h) :
    (LinearMap.range (f.prod g)).map (u0.prodMap v0) =
      LinearMap.range (f'.prod g') := by
  apply le_antisymm
  · intro z hz
    rcases Submodule.mem_map.mp hz with ⟨p, hp, rfl⟩
    rcases hp with ⟨x, rfl⟩
    refine ⟨h x, ?_⟩
    rw [LinearMap.prodMap_apply]
    apply Prod.ext
    · exact (congrArg (fun k : X →ₗ[S] M' => k x) hf).symm
    · exact (congrArg (fun k : X →ₗ[S] N' => k x) hg).symm
  · rintro _ ⟨x', rfl⟩
    obtain ⟨x, rfl⟩ := hh x'
    apply Submodule.mem_map.mpr
    refine ⟨(f.prod g) x, ⟨x, rfl⟩, ?_⟩
    rw [LinearMap.prodMap_apply]
    apply Prod.ext
    · exact congrArg (fun k : X →ₗ[S] M' => k x) hf
    · exact congrArg (fun k : X →ₗ[S] N' => k x) hg

variable (u : M ≃ₗ[S] M') (v : N ≃ₗ[S] N')
variable (he : (LinearMap.range (f.prod g)).map
    (u.prodCongr v : (M × N) →ₗ[S] (M' × N')) = LinearMap.range (f'.prod g'))

/-- Transport of the diagonal quotient by a product equivalence preserving its relation range. -/
def congr :
    ((M × N) ⧸ LinearMap.range (f.prod g)) ≃ₗ[S]
      (M' × N') ⧸ LinearMap.range (f'.prod g') :=
  Submodule.Quotient.equiv (LinearMap.range (f.prod g)) (LinearMap.range (f'.prod g'))
    (u.prodCongr v) he

/-- The presentation equivalence applies the coordinate equivalences to a representative. -/
@[simp] theorem congr_mk (m : M) (n : N) :
    congr f g f' g' u v he (Submodule.Quotient.mk (m, n)) =
      Submodule.Quotient.mk (u m, v n) := by
  simp only [congr, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    LinearEquiv.coe_prodCongr, LinearMap.prodMap_apply, LinearEquiv.coe_coe]

/-- The inverse presentation equivalence applies the inverse coordinate equivalences. -/
@[simp] theorem congr_symm_mk (m' : M') (n' : N') :
    (congr f g f' g' u v he).symm (Submodule.Quotient.mk (m', n')) =
      Submodule.Quotient.mk (u.symm m', v.symm n') := by
  simp only [congr, Submodule.Quotient.equiv_symm, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply, LinearEquiv.prodCongr_symm, LinearEquiv.coe_prodCongr,
    LinearMap.prodMap_apply, LinearEquiv.coe_coe]

/-- For commuting squares, the presentation equivalence has the induced quotient map
as its underlying linear map. -/
theorem congr_toLinearMap (h : X →ₗ[S] X')
    (hf : u.toLinearMap.comp f = f'.comp h)
    (hg : v.toLinearMap.comp g = g'.comp h) :
    (congr f g f' g' u v he).toLinearMap =
      map f g f' g' h u.toLinearMap v.toLinearMap hf hg := by
  apply map_unique f g f' g' h u.toLinearMap v.toLinearMap hf hg
  apply LinearMap.ext
  rintro ⟨m, n⟩
  change congr f g f' g' u v he ((LinearMap.range (f.prod g)).mkQ (m, n)) =
    (LinearMap.range (f'.prod g')).mkQ (u.toLinearMap.prodMap v.toLinearMap (m, n))
  simpa only [Submodule.mkQ_apply, LinearMap.prodMap_apply, LinearEquiv.coe_toLinearMap] using
    congr_mk f g f' g' u v he m n

end LinearMap.DiagonalQuotient

namespace LinearMap.DiagonalQuotient

universe uX' uM' uN'

variable {S : Type uS} [Ring S]
variable {X : Type uX} {M : Type uM} {N : Type uN}
variable {X' : Type uX'} {M' : Type uM'} {N' : Type uN'}
variable [AddCommGroup X] [AddCommGroup M] [AddCommGroup N]
variable [AddCommGroup X'] [AddCommGroup M'] [AddCommGroup N']
variable [Module S X] [Module S M] [Module S N]
variable [Module S X'] [Module S M'] [Module S N']
variable (f : X →ₗ[S] M) (g : X →ₗ[S] N)
variable (f' : X' →ₗ[S] M') (g' : X' →ₗ[S] N')
variable (h : X →ₗ[S] X') (u : M →ₗ[S] M') (v : N →ₗ[S] N')
variable (hf : u.comp f = f'.comp h) (hg : v.comp g = g'.comp h)

/-- The source map descends to the quotients by the sums of the two kernels. -/
def quotientKerMap :
    (X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g)) →ₗ[S]
      X' ⧸ (LinearMap.ker f' ⊔ LinearMap.ker g') :=
  (LinearMap.ker f ⊔ LinearMap.ker g).mapQ
    (LinearMap.ker f' ⊔ LinearMap.ker g') h (by
      refine sup_le ?_ ?_
      · intro x hx
        apply Submodule.mem_comap.mpr
        apply (le_sup_left : LinearMap.ker f' ≤ LinearMap.ker f' ⊔ LinearMap.ker g')
        apply LinearMap.mem_ker.mpr
        have hx0 : f x = 0 := LinearMap.mem_ker.mp hx
        have hfx : u (f x) = f' (h x) :=
          congrArg (fun k : X →ₗ[S] M' => k x) hf
        rw [← hfx, hx0, map_zero]
      · intro x hx
        apply Submodule.mem_comap.mpr
        apply (le_sup_right : LinearMap.ker g' ≤ LinearMap.ker f' ⊔ LinearMap.ker g')
        apply LinearMap.mem_ker.mpr
        have hx0 : g x = 0 := LinearMap.mem_ker.mp hx
        have hgx : v (g x) = g' (h x) :=
          congrArg (fun k : X →ₗ[S] N' => k x) hg
        rw [← hgx, hx0, map_zero])

/-- The induced diagonal-quotient map restricts to the kernels of the projections. -/
def kerMap :
    LinearMap.ker (projection f g) →ₗ[S] LinearMap.ker (projection f' g') :=
  (LinearMap.DiagonalQuotient.map f g f' g' h u v hf hg).restrict (by
    intro z hz
    apply LinearMap.mem_ker.mpr
    have hz0 : projection f g z = 0 := LinearMap.mem_ker.mp hz
    have hcomm :
        projection f' g' (LinearMap.DiagonalQuotient.map f g f' g' h u v hf hg z) =
          cokernelProdMap f g f' g' h u v hf hg (projection f g z) :=
      congrArg
        (fun k : ((M × N) ⧸ LinearMap.range (f.prod g)) →ₗ[S]
          (M' ⧸ LinearMap.range f') × (N' ⧸ LinearMap.range g') => k z)
        (projection_comp_map f g f' g' h u v hf hg)
    rw [hcomm, hz0, map_zero])

/-- The induced source quotient map sends the class of `x` to the class of `h x`. -/
@[simp] theorem quotientKerMap_mk (x : X) :
    quotientKerMap f g f' g' h u v hf hg (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (h x) := by
  unfold quotientKerMap
  exact Submodule.mapQ_apply _ _ _ _

/-- A linear map of the source quotients agreeing with `h` after the quotient maps
is the induced source quotient map. -/
theorem quotientKerMap_unique
    (l : (X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g)) →ₗ[S]
      X' ⧸ (LinearMap.ker f' ⊔ LinearMap.ker g'))
    (H : l.comp (LinearMap.ker f ⊔ LinearMap.ker g).mkQ =
      (LinearMap.ker f' ⊔ LinearMap.ker g').mkQ.comp h) :
    l = quotientKerMap f g f' g' h u v hf hg := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (LinearMap.ker f ⊔ LinearMap.ker g).mkQ_surjective q
  have hx :
      l ((LinearMap.ker f ⊔ LinearMap.ker g).mkQ x) =
        (LinearMap.ker f' ⊔ LinearMap.ker g').mkQ (h x) :=
    congrArg
      (fun k : X →ₗ[S] X' ⧸ (LinearMap.ker f' ⊔ LinearMap.ker g') => k x) H
  simpa only [Submodule.mkQ_apply, quotientKerMap_mk] using hx

/-- The induced map on projection kernels has the prescribed ambient value. -/
@[simp] theorem kerMap_coe (z : LinearMap.ker (projection f g)) :
    (kerMap f g f' g' h u v hf hg z :
      (M' × N') ⧸ LinearMap.range (f'.prod g')) =
    map f g f' g' h u v hf hg
      (z : (M × N) ⧸ LinearMap.range (f.prod g)) := by
  unfold kerMap
  exact LinearMap.coe_restrict_apply _ z

/-- Ambient composition with the kernel inclusion determines the induced kernel map. -/
theorem kerMap_unique
    (k : LinearMap.ker (projection f g) →ₗ[S] LinearMap.ker (projection f' g'))
    (H : (LinearMap.ker (projection f' g')).subtype.comp k =
      (map f g f' g' h u v hf hg).domRestrict (LinearMap.ker (projection f g))) :
    k = kerMap f g f' g' h u v hf hg := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  calc
    (k z : (M' × N') ⧸ LinearMap.range (f'.prod g')) =
        (map f g f' g' h u v hf hg).domRestrict
          (LinearMap.ker (projection f g)) z :=
      congrArg
        (fun l : LinearMap.ker (projection f g) →ₗ[S]
          (M' × N') ⧸ LinearMap.range (f'.prod g') => l z) H
    _ = map f g f' g' h u v hf hg
        (z : (M × N) ⧸ LinearMap.range (f.prod g)) :=
      LinearMap.domRestrict_apply _ _ z
    _ = (kerMap f g f' g' h u v hf hg z :
        (M' × N') ⧸ LinearMap.range (f'.prod g')) :=
      (kerMap_coe f g f' g' h u v hf hg z).symm

/-- The canonical equivalence from the source kernel-sum quotient to the projection
kernel is natural for arbitrary commuting maps. -/
theorem kerMap_comp_quotientKerEquiv :
    (kerMap f g f' g' h u v hf hg).comp (quotientKerEquiv f g).toLinearMap =
      (quotientKerEquiv f' g').toLinearMap.comp
        (quotientKerMap f g f' g' h u v hf hg) := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (LinearMap.ker f ⊔ LinearMap.ker g).mkQ_surjective q
  apply Subtype.ext
  change (kerMap f g f' g' h u v hf hg
      ((quotientKerEquiv f g).toLinearMap
        ((LinearMap.ker f ⊔ LinearMap.ker g).mkQ x)) :
      (M' × N') ⧸ LinearMap.range (f'.prod g')) =
    ((quotientKerEquiv f' g').toLinearMap
      (quotientKerMap f g f' g' h u v hf hg
        ((LinearMap.ker f ⊔ LinearMap.ker g).mkQ x)) :
      (M' × N') ⧸ LinearMap.range (f'.prod g'))
  rw [kerMap_coe]
  simp only [LinearEquiv.coe_toLinearMap, Submodule.mkQ_apply,
    quotientKerEquiv_mk, quotientKerMap_mk]
  exact congrArg
    (fun l : X →ₗ[S] (M' × N') ⧸ LinearMap.range (f'.prod g') => l x)
    (map_comp_left f g f' g' h u v hf hg)

end LinearMap.DiagonalQuotient
