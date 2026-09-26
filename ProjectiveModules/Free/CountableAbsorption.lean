/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Complemented endomorphism ideals and countable absorption

This file relates direct-sum decompositions of a module to complementary right
ideals of its endomorphism ring. It also packages a countable Eilenberg swindle
and applies it to complemented right ideals of the endomorphism ring of
`ℕ →₀ R`. The coefficient ring may be noncommutative, and the statements
include the zero ring.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Module.Free

variable (R : Type u) [Ring R]

/-- The right ideal of endomorphisms whose ranges lie in `p`.

Right ideals of `Module.End R M` are represented as submodules over the
opposite endomorphism ring, so scalar multiplication is right multiplication.
-/
def endomorphismsInto
    (M : Type v) [AddCommGroup M] [Module R M] (p : Submodule R M) :
    Submodule (Module.End R M)ᵐᵒᵖ (Module.End R M) where
  carrier := {f | ∀ x, f x ∈ p}
  zero_mem' := fun _ ↦ p.zero_mem
  add_mem' := by
    intro f g hf hg x
    exact p.add_mem (hf x) (hg x)
  smul_mem' := by
    intro a f hf x
    exact hf (a.unop x)

theorem mem_endomorphismsInto_iff_range_le
    (M : Type v) [AddCommGroup M] [Module R M]
    (p : Submodule R M) (f : Module.End R M) :
    f ∈ endomorphismsInto R M p ↔ LinearMap.range f ≤ p := by
  constructor
  · intro hf
    rintro _ ⟨x, rfl⟩
    exact hf x
  · intro hf x
    exact hf (LinearMap.mem_range_self f x)

/-- Complementary submodules give complementary right ideals consisting of
endomorphisms with range in the respective submodule. -/
theorem isCompl_endomorphismsInto
    (M : Type v) [AddCommGroup M] [Module R M]
    {p q : Submodule R M} (h : IsCompl p q) :
    IsCompl (endomorphismsInto R M p) (endomorphismsInto R M q) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro f hfp hfq
    ext x
    have hx : f x = 0 := Submodule.disjoint_def.mp h.disjoint (f x) (hfp x) (hfq x)
    simp [hx]
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro f
    let fp : Module.End R M := p.projection q h * f
    let fq : Module.End R M := q.projection p h.symm * f
    have hfp : fp ∈ endomorphismsInto R M p := by
      intro x
      exact Submodule.projection_apply_mem h (f x)
    have hfq : fq ∈ endomorphismsInto R M q := by
      intro x
      exact Submodule.projection_apply_mem h.symm (f x)
    have hsum : fp + fq = f := by
      ext x
      exact Submodule.projection_add_projection_eq_self h (f x)
    rw [← hsum]
    exact ((endomorphismsInto R M p) ⊔ (endomorphismsInto R M q)).add_mem
      (Submodule.mem_sup_left hfp) (Submodule.mem_sup_right hfq)

/-- A finitely supported sequence of pairs is the product of two finitely
supported sequences. -/
def finsuppProdLEquiv
    (V : Type v) (W : Type w)
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] :
    (ℕ →₀ V × W) ≃ₗ[R] (ℕ →₀ V) × (ℕ →₀ W) where
  toFun f :=
    (Finsupp.mapRange.linearMap (LinearMap.fst R V W) f,
      Finsupp.mapRange.linearMap (LinearMap.snd R V W) f)
  invFun fg := Finsupp.zipWith (fun x y ↦ (x, y)) rfl fg.1 fg.2
  left_inv f := by
    ext i <;> rfl
  right_inv fg := by
    rcases fg with ⟨f, g⟩
    ext i <;> rfl
  map_add' f g := by
    ext i <;> simp
  map_smul' a f := by
    ext i <;> simp

/-- One copy of a module is absorbed by its countable direct sum. -/
def prodFinsuppNatEquiv (V : Type v) [AddCommGroup V] [Module R V] :
    (V × (ℕ →₀ V)) ≃ₗ[R] ℕ →₀ V := by
  classical
  exact (LinearEquiv.prodComm R V (ℕ →₀ V)).trans <|
    ((Finsupp.domLCongr Equiv.natSumPUnitEquivNat.{0}.symm).trans
      ((Finsupp.sumFinsuppLEquivProdFinsupp R).trans
        ((LinearEquiv.refl R (ℕ →₀ V)).prodCongr
          (Finsupp.uniqueLinearEquiv R V PUnit.unit.{1})))).symm

/-- If `M` is equivalent to a countable direct sum of itself, every chosen
direct summand of `M` is absorbed by `M`. -/
def prodEquivOfCountableSelfSum
    (M : Type v) (V : Type w) (W : Type*)
    [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    (countableSelfSum : M ≃ₗ[R] ℕ →₀ M)
    (split : M ≃ₗ[R] V × W) :
    (V × M) ≃ₗ[R] M :=
  ((LinearEquiv.refl R V).prodCongr countableSelfSum).trans <|
    ((LinearEquiv.refl R V).prodCongr
      (Finsupp.lcongr (Equiv.refl ℕ) split)).trans <|
    ((LinearEquiv.refl R V).prodCongr (finsuppProdLEquiv R V W)).trans <|
    (LinearEquiv.prodAssoc R V (ℕ →₀ V) (ℕ →₀ W)).symm.trans <|
    ((prodFinsuppNatEquiv R V).prodCongr (LinearEquiv.refl R (ℕ →₀ W))).trans <|
    (finsuppProdLEquiv R V W).symm.trans <|
    (Finsupp.lcongr (Equiv.refl ℕ) split.symm).trans countableSelfSum.symm

/-- Pairing natural coordinates identifies `ℕ →₀ R` with a countable direct
sum of copies of itself. -/
def natFinsuppCountableSelfSum :
    (ℕ →₀ R) ≃ₗ[R] ℕ →₀ (ℕ →₀ R) := by
  classical
  exact (Finsupp.domLCongr
      (((Equiv.sigmaEquivProd ℕ ℕ).trans Nat.pairEquiv).symm)).trans <|
    (sigmaFinsuppLequivDFinsupp R).trans <|
      (finsuppLequivDFinsupp R).symm

/-- Every chosen direct summand of `ℕ →₀ R` is absorbed by `ℕ →₀ R`. -/
def prodNatFinsuppEquivOfSplit
    (V : Type v) (W : Type w)
    [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    (split : (ℕ →₀ R) ≃ₗ[R] V × W) :
    (V × (ℕ →₀ R)) ≃ₗ[R] (ℕ →₀ R) :=
  prodEquivOfCountableSelfSum R (ℕ →₀ R) V W
    (natFinsuppCountableSelfSum R) split

end Module.Free

namespace LinearMap

variable (R : Type u) [Ring R]

/-- Precomposition is the natural right action of `End_R(M)` on linear maps
out of `M`. The low priority leaves the regular-module instance in control when
the codomain is definitionally `M`. -/
instance (priority := 100) instModuleMulOppositeEnd
    (M : Type v) (V : Type w)
    [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V] :
    Module (Module.End R M)ᵐᵒᵖ (M →ₗ[R] V) where
  smul a f := f.comp a.unop
  one_smul f := by ext; rfl
  mul_smul a b f := by ext; rfl
  smul_zero a := by ext; rfl
  smul_add a f g := by ext; rfl
  add_smul a b f := by
    ext x
    change f (a.unop x + b.unop x) = f (a.unop x) + f (b.unop x)
    exact f.map_add _ _
  zero_smul f := by
    ext x
    change f (0 : M) = 0
    exact f.map_zero

end LinearMap

namespace Module.Free

variable (R : Type u) [Ring R]

/-- Postcomposition with an equivalence `V × M ≃ M` identifies
`Hom_R(M,V) × End_R(M)` with `End_R(M)` as right `End_R(M)`-modules. -/
def linearMapProdEndEquiv
    (M : Type v) (V : Type w)
    [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module R V]
    (absorb : (V × M) ≃ₗ[R] M) :
    ((M →ₗ[R] V) × Module.End R M) ≃ₗ[(Module.End R M)ᵐᵒᵖ] Module.End R M where
  toFun fg := absorb.toLinearMap.comp (fg.1.prod fg.2)
  invFun f :=
    ((LinearMap.fst R V M).comp (absorb.symm.toLinearMap.comp f),
      (LinearMap.snd R V M).comp (absorb.symm.toLinearMap.comp f))
  left_inv fg := by
    rcases fg with ⟨f, g⟩
    ext x <;> simp
  right_inv f := by
    ext x
    exact absorb.apply_symm_apply (f x)
  map_add' f g := by
    ext x
    exact absorb.map_add (f.1 x, f.2 x) (g.1 x, g.2 x)
  map_smul' a f := by
    ext x
    rfl

/-- The idempotent obtained by projecting the identity onto a complemented
right ideal of an endomorphism ring. -/
def rightIdealProjection
    (M : Type v) [AddCommGroup M] [Module R M]
    {I J : Submodule (Module.End R M)ᵐᵒᵖ (Module.End R M)} (h : IsCompl I J) :
    Module.End R M :=
  I.projection J h (1 : Module.End R M)

theorem rightIdealProjection_mem
    (M : Type v) [AddCommGroup M] [Module R M]
    {I J : Submodule (Module.End R M)ᵐᵒᵖ (Module.End R M)} (h : IsCompl I J) :
    rightIdealProjection R M h ∈ I :=
  Submodule.projection_apply_mem h (1 : Module.End R M)

theorem rightIdealProjection_isIdempotent
    (M : Type v) [AddCommGroup M] [Module R M]
    {I J : Submodule (Module.End R M)ᵐᵒᵖ (Module.End R M)} (h : IsCompl I J) :
    IsIdempotentElem (rightIdealProjection R M h) := by
  let e : Module.End R M := rightIdealProjection R M h
  have heI : e ∈ I := rightIdealProjection_mem R M h
  have hfix : I.projection J h e = e := Submodule.projection_apply_of_mem_left h heI
  have hlin := (I.projection J h).map_smul (MulOpposite.op e) (1 : Module.End R M)
  change e * e = e
  calc
    e * e = I.projection J h e := by simpa [e, rightIdealProjection] using hlin.symm
    _ = e := hfix

theorem coe_eq_rightIdealProjection_mul
    (M : Type v) [AddCommGroup M] [Module R M]
    {I J : Submodule (Module.End R M)ᵐᵒᵖ (Module.End R M)} (h : IsCompl I J)
    (f : I) :
    (f : Module.End R M) = rightIdealProjection R M h * (f : Module.End R M) := by
  have hfix : I.projection J h (f : Module.End R M) = (f : Module.End R M) :=
    Submodule.projection_apply_of_mem_left h f.property
  have hlin :=
    (I.projection J h).map_smul (MulOpposite.op (f : Module.End R M))
      (1 : Module.End R M)
  calc
    (f : Module.End R M) = I.projection J h (f : Module.End R M) := hfix.symm
    _ = rightIdealProjection R M h * (f : Module.End R M) := by
      simpa [rightIdealProjection] using hlin

/-- The submodule generated by the values of all endomorphisms in a right
ideal. For a complemented right ideal, this is the range of its projection
idempotent. -/
def rightIdealAction
    (M : Type v) [AddCommGroup M] [Module R M]
    (I : Submodule (Module.End R M)ᵐᵒᵖ (Module.End R M)) : Submodule R M :=
  ⨆ f : I, LinearMap.range (f : Module.End R M)

theorem rightIdealAction_eq_range_rightIdealProjection
    (M : Type v) [AddCommGroup M] [Module R M]
    {I J : Submodule (Module.End R M)ᵐᵒᵖ (Module.End R M)} (h : IsCompl I J) :
    rightIdealAction R M I = LinearMap.range (rightIdealProjection R M h) := by
  apply le_antisymm
  · refine iSup_le fun f ↦ ?_
    rw [coe_eq_rightIdealProjection_mul R M h f, Module.End.mul_eq_comp]
    exact LinearMap.range_comp_le_range _ _
  · exact le_iSup (fun f : I ↦ LinearMap.range (f : Module.End R M))
      ⟨rightIdealProjection R M h, rightIdealProjection_mem R M h⟩

/-- A complemented right ideal of `End_R(M)` is the right module of maps from
`M` into the range of its projection idempotent. -/
def rightIdealEquivRange
    (M : Type v) [AddCommGroup M] [Module R M]
    {I J : Submodule (Module.End R M)ᵐᵒᵖ (Module.End R M)} (h : IsCompl I J) :
    I ≃ₗ[(Module.End R M)ᵐᵒᵖ]
      (M →ₗ[R] LinearMap.range (rightIdealProjection R M h)) where
  toFun f := LinearMap.codRestrict
    (LinearMap.range (rightIdealProjection R M h)) (f : Module.End R M) (by
      intro x
      refine ⟨(f : Module.End R M) x, ?_⟩
      exact (LinearMap.congr_fun (coe_eq_rightIdealProjection_mul R M h f) x).symm)
  invFun g := by
    let f : Module.End R M :=
      (LinearMap.range (rightIdealProjection R M h)).subtype.comp g
    refine ⟨f, ?_⟩
    have hidem := rightIdealProjection_isIdempotent R M h
    have hfix : rightIdealProjection R M h * f = f := by
      ext x
      rcases (g x).property with ⟨y, hy⟩
      change rightIdealProjection R M h (g x : M) = (g x : M)
      rw [← hy]
      change (rightIdealProjection R M h * rightIdealProjection R M h) y =
        rightIdealProjection R M h y
      rw [hidem]
    have heI := rightIdealProjection_mem R M h
    have hmem : rightIdealProjection R M h * f ∈ I := by
      change (MulOpposite.op f) • rightIdealProjection R M h ∈ I
      exact I.smul_mem _ heI
    rwa [hfix] at hmem
  left_inv f := by
    apply Subtype.ext
    ext x
    rfl
  right_inv g := by
    ext x
    rfl
  map_add' f g := by
    ext x
    rfl
  map_smul' a f := by
    ext x
    rfl

theorem isCompl_range_rightIdealProjection
    (M : Type v) [AddCommGroup M] [Module R M]
    {I J : Submodule (Module.End R M)ᵐᵒᵖ (Module.End R M)} (h : IsCompl I J) :
    IsCompl (LinearMap.range (rightIdealProjection R M h))
      (LinearMap.range (rightIdealProjection R M h.symm)) := by
  let e : Module.End R M := rightIdealProjection R M h
  let e' : Module.End R M := rightIdealProjection R M h.symm
  have hsum : e + e' = 1 :=
    Submodule.projection_add_projection_eq_self h (1 : Module.End R M)
  have he' : e' = 1 - e := eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hsum)
  have he : IsIdempotentElem e := rightIdealProjection_isIdempotent R M h
  have hc := LinearMap.IsIdempotentElem.isCompl he
  rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub he, ← he'] at hc
  exact hc

/-- Complementary right ideals of an endomorphism ring give complementary
submodules after evaluation on the underlying module. -/
theorem isCompl_rightIdealAction
    (M : Type v) [AddCommGroup M] [Module R M]
    {I J : Submodule (Module.End R M)ᵐᵒᵖ (Module.End R M)} (h : IsCompl I J) :
    IsCompl (rightIdealAction R M I) (rightIdealAction R M J) := by
  rw [rightIdealAction_eq_range_rightIdealProjection R M h,
    rightIdealAction_eq_range_rightIdealProjection R M h.symm]
  exact isCompl_range_rightIdealProjection R M h

/-- Every complemented right ideal of the endomorphism ring of `ℕ →₀ R` is
absorbed by that endomorphism ring. -/
def rightIdealProdEndNatFinsuppEquiv
    {I J : Submodule (Module.End R (ℕ →₀ R))ᵐᵒᵖ (Module.End R (ℕ →₀ R))}
    (h : IsCompl I J) :
    (I × Module.End R (ℕ →₀ R)) ≃ₗ[(Module.End R (ℕ →₀ R))ᵐᵒᵖ]
      Module.End R (ℕ →₀ R) :=
  ((rightIdealEquivRange R (ℕ →₀ R) h).prodCongr
      (LinearEquiv.refl (Module.End R (ℕ →₀ R))ᵐᵒᵖ
        (Module.End R (ℕ →₀ R)))).trans <|
    linearMapProdEndEquiv R (ℕ →₀ R)
      (LinearMap.range (rightIdealProjection R (ℕ →₀ R) h))
      (prodNatFinsuppEquivOfSplit R
        (LinearMap.range (rightIdealProjection R (ℕ →₀ R) h))
        (LinearMap.range (rightIdealProjection R (ℕ →₀ R) h.symm))
        (Submodule.prodEquivOfIsCompl _ _
          (isCompl_range_rightIdealProjection R (ℕ →₀ R) h)).symm)

end Module.Free
