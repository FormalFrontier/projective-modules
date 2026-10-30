/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective

/-!
# Kernel row of a lifted coproduct

For maps `i : M' →ₗ[S] M`, `j : M →ₗ[S] M''`, covers `p'`, `p''`, and a
supplied lift `ell` with `j.comp ell = p''`, put `q = (i.comp p').coprod ell`.
The canonical maps `kerCoprodInl` and `kerCoprodSnd` form the row
`p'.ker → q.ker → p''.ker`. The first map is always injective, and the row is
exact if `i` is injective. These facts require only additive commutative monoids.
If `P'` has additive inverses, bottom exactness and surjectivity of `p'` make the
last projection surjective.

When `i` is injective, a supplied section of this projection gives
`kerCoprodEquivOfSection`, whose forward map is the coproduct of the canonical
inclusion and the section. It requires neither bottom exactness nor surjectivity
of either cover. Projectivity of the last kernel is a separate sufficient condition
for obtaining a section.
The construction agrees with the inverse of Mathlib's splitting equivalence
over rings. Separate surjectivity results for `q` require additive inverses in
`M` or in `P''`; surjectivity of `q` is not a conclusion of the kernel-row results.

## Implementation notes

Subtraction in the kernel-product construction takes place only in ambient `P'`.
Neither its kernels nor `P''` are assumed to be additive groups over a semiring.
The row depends on the supplied lift, and its splitting also depends on the
supplied section. All scalar and carrier universes are independent.

## References

* Mathlib, `Mathlib.Algebra.Exact.Basic` (exact pairs and splitting equivalences).
* Mathlib, `Mathlib.LinearAlgebra.Prod` (products and coproducts of linear maps).
* Mathlib, `Mathlib.Algebra.Module.Submodule.Equiv` (bijective linear maps).
* Mathlib, `Mathlib.Algebra.Module.Projective` (the projective lifting property).
-/

@[expose] public section

universe uS uP1 uP2 uM1 uM uM2

namespace LinearMap

section Inclusion

variable {S : Type uS} [Semiring S]
variable {P' : Type uP1} [AddCommMonoid P'] [Module S P']
variable {P'' : Type uP2} [AddCommMonoid P''] [Module S P'']
variable {M' : Type uM1} [AddCommMonoid M'] [Module S M']
variable {M : Type uM} [AddCommMonoid M] [Module S M]

/-- The inclusion of the left kernel into the kernel of a lifted coproduct,
sending `a` to `(a, 0)`. No compatibility or injectivity is required. -/
def kerCoprodInl
    (i : M' →ₗ[S] M) (p' : P' →ₗ[S] M') (ell : P'' →ₗ[S] M) :
    p'.ker →ₗ[S] ((i.comp p').coprod ell).ker :=
  codRestrict _ ((inl S P' P'').comp p'.ker.subtype) fun a ↦ by
    apply mem_ker.mpr
    simp only [comp_apply, Submodule.subtype_apply, inl_apply, coprod_apply,
      mem_ker.mp a.property, map_zero, add_zero]

/-- The ambient coordinates of the kernel inclusion. -/
@[simp] theorem kerCoprodInl_apply
    (i : M' →ₗ[S] M) (p' : P' →ₗ[S] M') (ell : P'' →ₗ[S] M)
    (a : p'.ker) :
    (kerCoprodInl i p' ell a : P' × P'') = ((a : P'), 0) := rfl

/-- The kernel inclusion followed by ambient inclusion is the usual left inclusion. -/
@[simp] theorem subtype_comp_kerCoprodInl
    (i : M' →ₗ[S] M) (p' : P' →ₗ[S] M') (ell : P'' →ₗ[S] M) :
    ((i.comp p').coprod ell).ker.subtype.comp (kerCoprodInl i p' ell) =
      (inl S P' P'').comp p'.ker.subtype := rfl

/-- The first map of the kernel row is injective without assumptions on `i`. -/
theorem kerCoprodInl_injective
    (i : M' →ₗ[S] M) (p' : P' →ₗ[S] M') (ell : P'' →ₗ[S] M) :
    Function.Injective (kerCoprodInl i p' ell) := by
  intro a b hab
  apply Subtype.ext
  simpa only [kerCoprodInl_apply] using
    congrArg (fun z : ((i.comp p').coprod ell).ker ↦ (z : P' × P'').1) hab

end Inclusion

section Row

variable {S : Type uS} [Semiring S]
variable {P' : Type uP1} [AddCommMonoid P'] [Module S P']
variable {P'' : Type uP2} [AddCommMonoid P''] [Module S P'']
variable {M' : Type uM1} [AddCommMonoid M'] [Module S M']
variable {M : Type uM} [AddCommMonoid M] [Module S M]
variable {M'' : Type uM2} [AddCommMonoid M''] [Module S M'']

/-- The second-coordinate projection on the kernel of a lifted coproduct.
The two compatibility identities suffice to put its values in the right kernel. -/
def kerCoprodSnd
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') :
    ((i.comp p').coprod ell).ker →ₗ[S] p''.ker :=
  codRestrict _ ((snd S P' P'').comp ((i.comp p').coprod ell).ker.subtype) fun b ↦ by
    apply mem_ker.mpr
    have hb := congrArg j (mem_ker.mp b.property)
    have hji' : j (i (p' (b : P' × P'').1)) = 0 :=
      LinearMap.congr_fun hji (p' (b : P' × P'').1)
    have hℓ' : j (ell (b : P' × P'').2) = p'' (b : P' × P'').2 :=
      LinearMap.congr_fun hℓ (b : P' × P'').2
    simpa only [comp_apply, snd_apply, Submodule.subtype_apply, coprod_apply,
      map_add, hji', hℓ', map_zero, zero_add] using hb

/-- The ambient coordinate of the kernel projection. -/
@[simp] theorem kerCoprodSnd_apply
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'')
    (b : ((i.comp p').coprod ell).ker) :
    (kerCoprodSnd i j p' p'' ell hji hℓ b : P'') = (b : P' × P'').2 := rfl

/-- The kernel projection followed by ambient inclusion is the usual second projection. -/
@[simp] theorem subtype_comp_kerCoprodSnd
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') :
    p''.ker.subtype.comp (kerCoprodSnd i j p' p'' ell hji hℓ) =
      (snd S P' P'').comp ((i.comp p').coprod ell).ker.subtype := rfl

/-- Consecutive maps in the kernel row compose to zero. -/
@[simp] theorem kerCoprodSnd_comp_kerCoprodInl
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') :
    (kerCoprodSnd i j p' p'' ell hji hℓ).comp (kerCoprodInl i p' ell) = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  rfl

/-- Injectivity of `i` makes the kernel row exact at its middle term.
Bottom exactness, cover surjectivity and additive inverses are not needed. -/
theorem exact_kerCoprodInl_kerCoprodSnd
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'')
    (hi : Function.Injective i) :
    Function.Exact (kerCoprodInl i p' ell) (kerCoprodSnd i j p' p'' ell hji hℓ) := by
  intro b
  constructor
  · intro hb
    have hb2 : (b : P' × P'').2 = 0 := by
      simpa only [kerCoprodSnd_apply, Submodule.coe_zero] using
        congrArg (fun c : p''.ker ↦ (c : P'')) hb
    have hb1 : i (p' (b : P' × P'').1) = 0 := by
      simpa only [coprod_apply, comp_apply, hb2, map_zero, add_zero] using
        (mem_ker.mp b.property)
    have hx : p' (b : P' × P'').1 = 0 := by
      apply hi
      simpa only [map_zero] using hb1
    refine ⟨⟨(b : P' × P'').1, hx⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl hb2.symm
  · rintro ⟨a, rfl⟩
    exact LinearMap.congr_fun (kerCoprodSnd_comp_kerCoprodInl i j p' p'' ell hji hℓ) a

end Row

section LeftGroup

variable {S : Type uS} [Semiring S]
variable {P' : Type uP1} [AddCommGroup P'] [Module S P']
variable {P'' : Type uP2} [AddCommMonoid P''] [Module S P'']
variable {M' : Type uM1} [AddCommMonoid M'] [Module S M']
variable {M : Type uM} [AddCommMonoid M] [Module S M]
variable {M'' : Type uM2} [AddCommMonoid M''] [Module S M'']

/-- Bottom exactness and a surjective left cover make the kernel projection onto.
Only the left source needs additive inverses; injectivity of `i` is not required. -/
theorem kerCoprodSnd_surjective
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hij : Function.Exact i j)
    (hℓ : j.comp ell = p'') (hp' : Function.Surjective p') :
    Function.Surjective
      (kerCoprodSnd i j p' p'' ell hij.linearMap_comp_eq_zero hℓ) := by
  intro y
  have hy : j (ell (y : P'')) = 0 := by
    rw [show j (ell (y : P'')) = p'' (y : P'') from LinearMap.congr_fun hℓ y]
    exact mem_ker.mp y.property
  obtain ⟨z, hz⟩ := (hij (ell (y : P''))).mp hy
  obtain ⟨a, ha⟩ := hp' z
  have hla : i (p' a) = ell (y : P'') := by rw [ha, hz]
  have hmem : ((i.comp p').coprod ell) (-a, (y : P'')) = 0 := by
    calc
      ((i.comp p').coprod ell) (-a, (y : P'')) =
          i (p' (-a)) + i (p' a) := by rw [coprod_apply, comp_apply, hla]
      _ = i (p' (-a + a)) := by rw [map_add, map_add]
      _ = 0 := by rw [neg_add_cancel, map_zero, map_zero]
  refine ⟨⟨(-a, (y : P'')), hmem⟩, ?_⟩
  apply Subtype.ext
  rfl

/-- For injective `i`, a supplied section identifies the lifted coproduct kernel
with the product of the two cover kernels. Its forward map is the coproduct of
`kerCoprodInl i p' ell` and `s`.
Only ambient `P'` is used for subtraction; the kernels need not be groups. -/
noncomputable def kerCoprodEquivOfSection
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id) :
    (p'.ker × p''.ker) ≃ₗ[S] ((i.comp p').coprod ell).ker :=
  LinearEquiv.ofBijective ((kerCoprodInl i p' ell).coprod s) <| by
    have hs_apply (c : p''.ker) : kerCoprodSnd i j p' p'' ell hji hℓ (s c) = c :=
      LinearMap.congr_fun hs c
    have hπI (a : p'.ker) : (kerCoprodSnd i j p' p'' ell hji hℓ) ((kerCoprodInl i p' ell) a) = 0 :=
      LinearMap.congr_fun (kerCoprodSnd_comp_kerCoprodInl i j p' p'' ell hji hℓ) a
    constructor
    · rintro ⟨a, c⟩ ⟨a', c'⟩ h
      have hc : c = c' := by
        have hπ := congrArg (kerCoprodSnd i j p' p'' ell hji hℓ) h
        simpa only [coprod_apply, map_add, hπI, zero_add, hs_apply] using hπ
      refine Prod.ext ?_ hc
      apply Subtype.ext
      have hfst : (a : P') + (s c : P' × P'').1 =
          (a' : P') + (s c' : P' × P'').1 := by
        simpa only [coprod_apply, Submodule.coe_add, Prod.fst_add, kerCoprodInl_apply] using
          congrArg (fun b : ((i.comp p').coprod ell).ker ↦ (b : P' × P'').1) h
      rw [hc] at hfst
      exact add_right_cancel hfst
    · intro b
      let c : p''.ker := (kerCoprodSnd i j p' p'' ell hji hℓ) b
      let x : P' := (b : P' × P'').1 - (s c : P' × P'').1
      have hsc : (s c : P' × P'').2 = (b : P' × P'').2 := by
        simpa only [c, kerCoprodSnd_apply] using
          congrArg (fun z : p''.ker ↦ (z : P'')) (hs_apply c)
      have hsum : ((x, 0) : P' × P'') + (s c : P' × P'') = (b : P' × P'') := by
        apply Prod.ext
        · exact sub_add_cancel _ _
        · exact (zero_add _).trans hsc
      let q : P' × P'' →ₗ[S] M := (i.comp p').coprod ell
      have hximage : i (p' x) = 0 := by
        calc
          i (p' x) = q (x, 0) := by simp only [q, coprod_apply, comp_apply, map_zero, add_zero]
          _ = q (x, 0) + q (s c : P' × P'') := by
            rw [mem_ker.mp (s c).property, add_zero]
          _ = q (((x, 0) : P' × P'') + (s c : P' × P'')) := (map_add q _ _).symm
          _ = q (b : P' × P'') := congrArg q hsum
          _ = 0 := mem_ker.mp b.property
      have hx : p' x = 0 := by
        apply hi
        simpa only [map_zero] using hximage
      refine ⟨(⟨x, hx⟩, c), ?_⟩
      apply Subtype.ext
      simpa only [coprod_apply, Submodule.coe_add, kerCoprodInl_apply] using hsum

/-- The prescribed forward linear map of the kernel-product equivalence. -/
@[simp] theorem kerCoprodEquivOfSection_toLinearMap
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id) :
    (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).toLinearMap =
      (kerCoprodInl i p' ell).coprod s := by
  apply LinearMap.ext
  intro z
  rfl

/-- The forward formula for the kernel-product equivalence. -/
@[simp] theorem kerCoprodEquivOfSection_apply
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id)
    (a : p'.ker) (c : p''.ker) :
    kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs (a, c) =
      kerCoprodInl i p' ell a + s c := rfl

/-- The first ambient coordinate of the kernel-product equivalence. -/
theorem kerCoprodEquivOfSection_apply_fst
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id)
    (a : p'.ker) (c : p''.ker) :
    (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs (a, c) : P' × P'').1 =
      (a : P') + (s c : P' × P'').1 := rfl

/-- The equivalence restricts to the canonical kernel inclusion on the left factor. -/
theorem kerCoprodEquivOfSection_comp_inl
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id) :
    (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).toLinearMap.comp
        (inl S p'.ker p''.ker) = kerCoprodInl i p' ell := by
  rw [kerCoprodEquivOfSection_toLinearMap, coprod_inl]

/-- The equivalence restricts to the supplied section on the right factor. -/
theorem kerCoprodEquivOfSection_comp_inr
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id) :
    (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).toLinearMap.comp
        (inr S p'.ker p''.ker) = s := by
  rw [kerCoprodEquivOfSection_toLinearMap, coprod_inr]

/-- The kernel projection is the second coordinate of the equivalence. -/
theorem kerCoprodSnd_comp_kerCoprodEquivOfSection
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id) :
    (kerCoprodSnd i j p' p'' ell hji hℓ).comp
        (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).toLinearMap =
      snd S p'.ker p''.ker := by
  rw [kerCoprodEquivOfSection_toLinearMap, comp_coprod,
    kerCoprodSnd_comp_kerCoprodInl, hs, coprod_zero_left, id_comp]

/-- The second ambient coordinate of the kernel-product equivalence. -/
theorem kerCoprodEquivOfSection_apply_snd
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id)
    (a : p'.ker) (c : p''.ker) :
    ((kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs) (a, c) : P' × P'').2 = (c : P'') :=
  congrArg (fun z : p''.ker ↦ (z : P''))
    (LinearMap.congr_fun
      (kerCoprodSnd_comp_kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs) (a, c))

/-- The inverse sends the canonical kernel inclusion to the left factor. -/
@[simp] theorem kerCoprodEquivOfSection_symm_comp_kerCoprodInl
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id) :
    (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).symm.toLinearMap.comp
        (kerCoprodInl i p' ell) = inl S p'.ker p''.ker := by
  apply LinearMap.ext
  intro a
  apply (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).injective
  simpa only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
    (LinearMap.congr_fun
      (kerCoprodEquivOfSection_comp_inl i j p' p'' ell hji hℓ hi s hs) a).symm

/-- The inverse sends the supplied section to the right factor. -/
@[simp] theorem kerCoprodEquivOfSection_symm_comp_section
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id) :
    (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).symm.toLinearMap.comp s =
      inr S p'.ker p''.ker := by
  apply LinearMap.ext
  intro c
  apply (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).injective
  simpa only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
    (LinearMap.congr_fun
      (kerCoprodEquivOfSection_comp_inr i j p' p'' ell hji hℓ hi s hs) c).symm

/-- The second coordinate of the inverse is the kernel projection. -/
@[simp] theorem snd_comp_kerCoprodEquivOfSection_symm
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id) :
    (snd S p'.ker p''.ker).comp
        (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).symm.toLinearMap =
      kerCoprodSnd i j p' p'' ell hji hℓ := by
  apply LinearMap.ext
  intro b
  simpa only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, snd_apply] using
    (LinearMap.congr_fun
      (kerCoprodSnd_comp_kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs)
      ((kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).symm b)).symm

/-- The kernel-product inverse is a left inverse to the prescribed coproduct. -/
theorem kerCoprodEquivOfSection_symm_comp_coprod
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id) :
    (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).symm.toLinearMap.comp
        ((kerCoprodInl i p' ell).coprod s) = LinearMap.id := by
  rw [← kerCoprodEquivOfSection_toLinearMap i j p' p'' ell hji hℓ hi s hs]
  exact (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).symm_comp

/-- The kernel-product inverse is a right inverse to the prescribed coproduct. -/
theorem kerCoprodEquivOfSection_coprod_comp_symm
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id) :
    ((kerCoprodInl i p' ell).coprod s).comp
        (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).symm.toLinearMap =
      LinearMap.id := by
  rw [← kerCoprodEquivOfSection_toLinearMap i j p' p'' ell hji hℓ hi s hs]
  exact (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).comp_symm

/-- The right kernel coordinate of the inverse. -/
@[simp] theorem kerCoprodEquivOfSection_symm_apply_snd
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id)
    (b : ((i.comp p').coprod ell).ker) :
    ((kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).symm b).2 =
      kerCoprodSnd i j p' p'' ell hji hℓ b :=
  LinearMap.congr_fun
    (snd_comp_kerCoprodEquivOfSection_symm i j p' p'' ell hji hℓ hi s hs) b

/-- Every element of the middle kernel reconstructs from its two kernel coordinates. -/
theorem kerCoprodEquivOfSection_reconstruct
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id)
    (b : ((i.comp p').coprod ell).ker) :
    kerCoprodInl i p' ell
          ((kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).symm b).1 +
        s (kerCoprodSnd i j p' p'' ell hji hℓ b) = b := by
  let e := kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs
  calc
    kerCoprodInl i p' ell (e.symm b).1 + s (kerCoprodSnd i j p' p'' ell hji hℓ b) =
        e ((e.symm b).1, (e.symm b).2) := by
      rw [kerCoprodEquivOfSection_apply, kerCoprodEquivOfSection_symm_apply_snd]
    _ = b := e.apply_symm_apply b

/-- The left inverse coordinate, viewed in ambient `P'`, is obtained by subtracting
the first coordinate of the supplied section. No target subtraction is used. -/
@[simp] theorem kerCoprodEquivOfSection_symm_apply_fst
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id)
    (b : ((i.comp p').coprod ell).ker) :
    (((kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).symm b).1 : P') =
      (b : P' × P'').1 - (s (kerCoprodSnd i j p' p'' ell hji hℓ b) : P' × P'').1 := by
  apply (eq_sub_iff_add_eq).mpr
  exact congrArg (fun z : ((i.comp p').coprod ell).ker ↦ (z : P' × P'').1)
    (kerCoprodEquivOfSection_reconstruct i j p' p'' ell hji hℓ hi s hs b)

/-- The inverse coordinates are uniquely characterized by reconstruction. -/
theorem kerCoprodEquivOfSection_symm_apply_eq_iff
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id)
    (b : ((i.comp p').coprod ell).ker) (a : p'.ker) (c : p''.ker) :
    (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).symm b = (a, c) ↔
      kerCoprodInl i p' ell a + s c = b := by
  constructor
  · intro h
    simpa only [LinearEquiv.apply_symm_apply, kerCoprodEquivOfSection_apply] using
      (congrArg (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs) h).symm
  · intro h
    apply (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).injective
    simpa only [LinearEquiv.apply_symm_apply, kerCoprodEquivOfSection_apply] using h.symm

/-- The prescribed restrictions to the two product factors uniquely determine the equivalence. -/
theorem kerCoprodEquivOfSection_unique
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id)
    (e : (p'.ker × p''.ker) ≃ₗ[S] ((i.comp p').coprod ell).ker)
    (heI : e.toLinearMap.comp (inl S p'.ker p''.ker) = (kerCoprodInl i p' ell))
    (hes : e.toLinearMap.comp (inr S p'.ker p''.ker) = s) :
    e = kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs := by
  have he : e.toLinearMap =
      (kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs).toLinearMap := LinearMap.prod_ext
    (heI.trans (kerCoprodEquivOfSection_comp_inl i j p' p'' ell hji hℓ hi s hs).symm)
    (hes.trans (kerCoprodEquivOfSection_comp_inr i j p' p'' ell hji hℓ hi s hs).symm)
  exact LinearEquiv.toLinearMap_injective he

end LeftGroup

section ProjectiveLastKernel

variable {S : Type uS} [Semiring S]
variable {P' : Type uP1} [AddCommGroup P'] [Module S P']
variable {P'' : Type uP2} [AddCommMonoid P''] [Module S P'']
variable {M' : Type uM1} [AddCommMonoid M'] [Module S M']
variable {M : Type uM} [AddCommMonoid M] [Module S M]
variable {M'' : Type uM2} [AddCommMonoid M''] [Module S M'']

/-- If the last kernel is projective, the short exact kernel row splits.
Only this kernel is assumed projective; neither cover source is required projective,
and the right cover need not be onto. -/
theorem nonempty_kerCoprodEquiv_of_projective
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    [Module.Projective S p''.ker] (hi : Function.Injective i)
    (hij : Function.Exact i j) (hℓ : j.comp ell = p'')
    (hp' : Function.Surjective p') :
    Nonempty ((p'.ker × p''.ker) ≃ₗ[S] ((i.comp p').coprod ell).ker) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (kerCoprodSnd i j p' p'' ell hij.linearMap_comp_eq_zero hℓ)
    (LinearMap.id : p''.ker →ₗ[S] p''.ker)
    (kerCoprodSnd_surjective i j p' p'' ell hij hℓ hp')
  exact ⟨kerCoprodEquivOfSection i j p' p'' ell hij.linearMap_comp_eq_zero hℓ hi s hs⟩

end ProjectiveLastKernel

section Ring

variable {S : Type uS} [Ring S]
variable {P' : Type uP1} [AddCommGroup P'] [Module S P']
variable {P'' : Type uP2} [AddCommGroup P''] [Module S P'']
variable {M' : Type uM1} [AddCommMonoid M'] [Module S M']
variable {M : Type uM} [AddCommMonoid M] [Module S M]
variable {M'' : Type uM2} [AddCommMonoid M''] [Module S M'']

/-- Over a ring, the supplied-section construction agrees with the inverse of
Mathlib's splitting equivalence. No target is assumed to be an additive group. -/
theorem kerCoprodEquivOfSection_eq_splitSurjectiveEquiv_symm
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hji : j.comp i = 0) (hℓ : j.comp ell = p'') (hi : Function.Injective i)
    (s : p''.ker →ₗ[S] ((i.comp p').coprod ell).ker)
    (hs : (kerCoprodSnd i j p' p'' ell hji hℓ).comp s = LinearMap.id) :
    kerCoprodEquivOfSection i j p' p'' ell hji hℓ hi s hs =
      (((exact_kerCoprodInl_kerCoprodSnd i j p' p'' ell hji hℓ hi).splitSurjectiveEquiv
        (kerCoprodInl_injective i p' ell)) ⟨s, hs⟩).1.symm := by
  apply LinearEquiv.ext
  intro z
  rfl

end Ring

section AddCommGroupMiddle

variable {S : Type uS} [Semiring S]
variable {P' : Type uP1} [AddCommMonoid P'] [Module S P']
variable {P'' : Type uP2} [AddCommMonoid P''] [Module S P'']
variable {M' : Type uM1} [AddCommMonoid M'] [Module S M']
variable {M : Type uM} [AddCommGroup M] [Module S M]
variable {M'' : Type uM2} [AddCommMonoid M''] [Module S M'']

/-- The lifted coproduct of two surjective covers of an exact pair is surjective
when the middle module has additive inverses. The other modules need only be
additive commutative monoids. -/
theorem surjective_coprod_comp_of_exact
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hij : Function.Exact i j) (hℓ : j.comp ell = p'')
    (hp' : Function.Surjective p') (hp'' : Function.Surjective p'') :
    Function.Surjective ((i.comp p').coprod ell) := by
  intro m
  obtain ⟨y, hy⟩ := hp'' (j m)
  have hly : j (ell y) = j m := (LinearMap.congr_fun hℓ y).trans hy
  have hd : j (m - ell y) = 0 := by
    calc
      j (m - ell y) = j m + j (-ell y) := by rw [sub_eq_add_neg, map_add]
      _ = j (ell y) + j (-ell y) := by rw [hly]
      _ = j (ell y + -ell y) := (map_add j _ _).symm
      _ = 0 := by rw [add_neg_cancel, map_zero]
  obtain ⟨z, hz⟩ := (hij (m - ell y)).mp hd
  obtain ⟨x, hx⟩ := hp' z
  refine ⟨(x, y), ?_⟩
  calc
    ((i.comp p').coprod ell) (x, y) = (m - ell y) + ell y := by
      simp only [coprod_apply, comp_apply, hx, hz]
    _ = m := sub_add_cancel m (ell y)

end AddCommGroupMiddle

section AddCommGroupRight

variable {S : Type uS} [Semiring S]
variable {P' : Type uP1} [AddCommMonoid P'] [Module S P']
variable {P'' : Type uP2} [AddCommGroup P''] [Module S P'']
variable {M' : Type uM1} [AddCommMonoid M'] [Module S M']
variable {M : Type uM} [AddCommMonoid M] [Module S M]
variable {M'' : Type uM2} [AddCommMonoid M''] [Module S M'']

/-- The lifted coproduct of two surjective covers of an exact pair is surjective
when the source of the right cover has additive inverses. The middle module and
all remaining modules need only be additive commutative monoids. -/
theorem surjective_coprod_comp_of_exact_of_addCommGroup_right
    (i : M' →ₗ[S] M) (j : M →ₗ[S] M'')
    (p' : P' →ₗ[S] M') (p'' : P'' →ₗ[S] M'') (ell : P'' →ₗ[S] M)
    (hij : Function.Exact i j) (hℓ : j.comp ell = p'')
    (hp' : Function.Surjective p') (hp'' : Function.Surjective p'') :
    Function.Surjective ((i.comp p').coprod ell) := by
  intro m
  obtain ⟨y, hy⟩ := hp'' (j m)
  have hlny : j (ell (-y)) = p'' (-y) := LinearMap.congr_fun hℓ (-y)
  have hd : j (m + ell (-y)) = 0 := by
    calc
      j (m + ell (-y)) = j m + j (ell (-y)) := map_add j _ _
      _ = p'' y + p'' (-y) := by rw [← hy, hlny]
      _ = p'' (y + -y) := (map_add p'' _ _).symm
      _ = 0 := by rw [add_neg_cancel, map_zero]
  obtain ⟨z, hz⟩ := (hij (m + ell (-y))).mp hd
  obtain ⟨x, hx⟩ := hp' z
  refine ⟨(x, y), ?_⟩
  calc
    ((i.comp p').coprod ell) (x, y) = (m + ell (-y)) + ell y := by
      simp only [coprod_apply, comp_apply, hx, hz]
    _ = m + (ell (-y) + ell y) := add_assoc _ _ _
    _ = m + ell (-y + y) := by rw [map_add]
    _ = m := by rw [neg_add_cancel, map_zero, add_zero]

end AddCommGroupRight

end LinearMap
