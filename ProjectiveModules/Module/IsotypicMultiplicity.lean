/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Free.CountableAbsorption
public import Mathlib.Algebra.Field.Opposite
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.SetTheory.Cardinal.Defs

/-!
# Multiplicity of a fixed simple module

The multiplicity of a simple module `S` in a semisimple module consisting entirely of
copies of `S` is the dimension of `Hom(S, M)` over the opposite endomorphism
division ring of `S`. Precomposition uses the existing action on linear maps.
The characterization compares this cardinal with every direct-sum decomposition,
including decompositions indexed in unrelated universes.
Its proof uses Schur's lemma, finite generation of a simple module, and Mathlib's
finite-source Hom/direct-sum bijection.
For a chosen ring equivalence, semilinear equivalences of both the ambient modules
and the specified simple modules compare the same cardinal after universe lifts.

The simple-type and semisimplicity assumptions are essential. Over `k × k` for
a field `k`, the two simple modules `k × 0` and `0 × k` cannot both be counted
by one fixed type. Taking `S = 0` would give a zero Hom space even for nonzero
`M`, whereas `0` is not simple. The `ℤ`-module `ℤ/4ℤ` has a simple submodule of
type `ℤ/2ℤ` but is not a direct sum of such modules; Hom from `ℤ/2ℤ` sees
only its socle. No commutativity or finiteness assumption is made on the
coefficient ring or on the number of summands.

## References

Charles A. Weibel, *The K-book*, Example I.1.1.1, motivates the number of
copies of a simple module over a simple Artinian ring. This interface instead
fixes an arbitrary simple left module over an arbitrary ring. It does not
identify concrete right row modules or assert a rank formula for nonfree modules.
Mathlib's `LinearEquiv.arrowCongrAddEquiv`, `LinearEquiv.conjRingEquiv`, and
`lift_rank_eq_of_equiv_equiv` provide the transport primitives for a chosen
change of coefficient ring.
-/

@[expose] public section

noncomputable section

open Cardinal

universe u v w x y z

private theorem endOpp_isUnit_of_ne_zero
    {A : Type u} [Ring A] {S : Type v} [AddCommGroup S] [Module A S]
    [IsSimpleModule A S] {f : (Module.End A S)ᵐᵒᵖ} (hf : f ≠ 0) : IsUnit f := by
  have hf' : f.unop ≠ 0 := (MulOpposite.unop_ne_zero_iff f).mpr hf
  let equivalence := LinearEquiv.ofBijective f.unop (LinearMap.bijective_of_ne_zero hf')
  apply isUnit_iff_exists.mpr
  refine ⟨MulOpposite.op equivalence.symm.toLinearMap, ?_, ?_⟩
  · apply MulOpposite.unop_injective
    ext s
    exact equivalence.left_inv s
  · apply MulOpposite.unop_injective
    ext s
    exact equivalence.right_inv s

private theorem endOpp_strongRankCondition
    {A : Type u} [Ring A] {S : Type v} [AddCommGroup S] [Module A S]
    [IsSimpleModule A S] : StrongRankCondition (Module.End A S)ᵐᵒᵖ := by
  classical
  have : DivisionRing (Module.End A S) := inferInstance
  have : DivisionRing (Module.End A S)ᵐᵒᵖ := inferInstance
  have : IsSimpleModule (Module.End A S)ᵐᵒᵖ (Module.End A S)ᵐᵒᵖ :=
    isSimpleModule_self_iff_isUnit.mpr ⟨inferInstance, fun _ h ↦ endOpp_isUnit_of_ne_zero h⟩
  exact inferInstance

private noncomputable def linearMapFinsuppEquiv
    {A : Type u} [Ring A] {S : Type v} [AddCommGroup S] [Module A S]
    [IsSimpleModule A S] (ι : Type w) :
    (ι →₀ Module.End A S) ≃ₗ[(Module.End A S)ᵐᵒᵖ] (S →ₗ[A] (ι →₀ S)) := by
  classical
  haveI : Nontrivial S := IsSimpleModule.nontrivial A S
  have : Module.Finite A S := by
    obtain ⟨s, hs⟩ := exists_ne (0 : S)
    rw [Module.finite_def]
    exact ⟨{s}, by simpa using IsSimpleModule.span_singleton_eq_top A hs⟩
  letI : Module.Finite A S := this
  let equivalence := LinearEquiv.ofBijective
    (LinearMap.finsuppLinearMap ℤ :
      (ι →₀ Module.End A S) →ₗ[ℤ] (S →ₗ[A] (ι →₀ S)))
    (LinearMap.finsuppLinearMap_bijective_of_moduleFinite A S S ι ℤ)
  refine {
    toFun := equivalence
    invFun := equivalence.symm
    left_inv := equivalence.left_inv
    right_inv := equivalence.right_inv
    map_add' := equivalence.map_add
    map_smul' := ?_ }
  intro a f
  ext index s
  rfl

private noncomputable def linearMapCongrRight
    {A : Type u} [Ring A] {S : Type v} [AddCommGroup S] [Module A S]
    {M : Type w} [AddCommGroup M] [Module A M]
    {N : Type x} [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) :
    (S →ₗ[A] M) ≃ₗ[(Module.End A S)ᵐᵒᵖ] (S →ₗ[A] N) where
  toFun f := e.toLinearMap.comp f
  invFun f := e.symm.toLinearMap.comp f
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_add' f g := by ext; simp
  map_smul' a f := by ext; rfl

private theorem rank_linearMap_finsupp
    {A : Type u} [Ring A] {S : Type v} [AddCommGroup S] [Module A S]
    [IsSimpleModule A S] (ι : Type w) :
    Module.rank (Module.End A S)ᵐᵒᵖ (S →ₗ[A] (ι →₀ S)) =
      Cardinal.lift.{v} (#ι) := by
  classical
  have : StrongRankCondition (Module.End A S)ᵐᵒᵖ := endOpp_strongRankCondition
  calc
    Module.rank (Module.End A S)ᵐᵒᵖ (S →ₗ[A] (ι →₀ S)) =
        Module.rank (Module.End A S)ᵐᵒᵖ (ι →₀ Module.End A S) :=
      (linearMapFinsuppEquiv ι).symm.rank_eq
    _ = Module.rank (Module.End A S)ᵐᵒᵖ (ι →₀ (Module.End A S)ᵐᵒᵖ) :=
      (Finsupp.mapRange.linearEquiv
        (MulOpposite.opLinearEquiv (Module.End A S)ᵐᵒᵖ)).rank_eq
    _ = Cardinal.lift.{v} (#ι) := rank_finsupp_self _ ι

namespace Finsupp

variable {A : Type u} [Ring A] {S : Type v} [AddCommGroup S] [Module A S]
  [IsSimpleModule A S] {ι : Type w} {κ : Type x}

/-- Isomorphic direct sums of a fixed simple module have the same lifted index cardinal,
even when the two index types inhabit different universes. -/
theorem lift_cardinalMk_eq_of_linearEquiv
    (e : (ι →₀ S) ≃ₗ[A] (κ →₀ S)) :
    Cardinal.lift.{x} (#ι) = Cardinal.lift.{w} (#κ) := by
  classical
  have h := (linearMapCongrRight (S := S) e).lift_rank_eq
  apply (Cardinal.lift_mk_eq' (α := ι) (β := κ)).mpr
  apply (Cardinal.lift_mk_eq (α := ι) (β := κ)).mp
  simpa only [rank_linearMap_finsupp, Cardinal.lift_lift, Cardinal.lift_umax,
    Cardinal.lift_id] using h

/-- Direct sums of a fixed simple module are equivalent exactly when their
indices have the same cardinality, without a finiteness condition. -/
theorem nonempty_linearEquiv_iff_lift_cardinalMk_eq_of_isSimpleModule :
    Nonempty ((ι →₀ S) ≃ₗ[A] (κ →₀ S)) ↔
      Cardinal.lift.{x} (#ι) = Cardinal.lift.{w} (#κ) := by
  constructor
  · rintro ⟨e⟩
    exact lift_cardinalMk_eq_of_linearEquiv e
  · intro h
    obtain ⟨e⟩ := (Cardinal.lift_mk_eq' (α := ι) (β := κ)).mp h
    exact ⟨Finsupp.domLCongr (R := A) (M := S) e⟩

end Finsupp

namespace IsIsotypicOfType

variable {A : Type u} [Ring A] {M : Type v} [AddCommGroup M] [Module A M]
  {S : Type w} [AddCommGroup S] [Module A S]

/-- The number of copies of the specified simple module in an isotypic
semisimple module, measured by the rank of `Hom_A(S, M)` over `End_A(S)ᵐᵒᵖ`.
The module action is precomposition. -/
def multiplicity [IsSimpleModule A S] [IsSemisimpleModule A M]
    (_h : IsIsotypicOfType A M S) : Cardinal :=
  Module.rank (Module.End A S)ᵐᵒᵖ (S →ₗ[A] M)

/-- The multiplicity is the dimension of the Hom space over the opposite
endomorphism division ring. -/
@[simp] theorem multiplicity_eq_rank [IsSimpleModule A S] [IsSemisimpleModule A M]
    (h : IsIsotypicOfType A M S) :
    h.multiplicity = Module.rank (Module.End A S)ᵐᵒᵖ (S →ₗ[A] M) := rfl

variable [simple : IsSimpleModule A S] [semisimple : IsSemisimpleModule A M]

include simple semisimple

/-- Any decomposition of the whole module into copies of `S` has the
specified multiplicity, with cardinal lifts across the index universe. -/
theorem lift_multiplicity_eq_of_linearEquiv_finsupp
    (h : IsIsotypicOfType A M S) {ι : Type x} (e : M ≃ₗ[A] (ι →₀ S)) :
    Cardinal.lift.{x} h.multiplicity = Cardinal.lift.{max v w} (#ι) := by
  classical
  have hr := (linearMapCongrRight (S := S) e).lift_rank_eq
  apply (Cardinal.lift_inj.{_, w}).mp
  simpa only [multiplicity_eq_rank, rank_linearMap_finsupp, Cardinal.lift_lift,
    Cardinal.lift_umax, Cardinal.lift_id] using hr

/-- Mathlib's fixed-type decomposition supplies an index realizing the
cardinal multiplicity. -/
theorem exists_linearEquiv_finsupp_lift_multiplicity_eq
    (h : IsIsotypicOfType A M S) :
    ∃ ι : Type v, Nonempty (M ≃ₗ[A] (ι →₀ S)) ∧
      Cardinal.lift.{v} h.multiplicity = Cardinal.lift.{max v w} (#ι) := by
  obtain ⟨ι, ⟨e⟩⟩ := h.linearEquiv_finsupp
  exact ⟨ι, ⟨e⟩, h.lift_multiplicity_eq_of_linearEquiv_finsupp e⟩

/-- Multiplicity of the same simple type is invariant under a linear equivalence,
including when the two modules inhabit unrelated universes. -/
theorem lift_multiplicity_eq_of_linearEquiv
    {N : Type x} [AddCommGroup N] [Module A N] [IsSemisimpleModule A N]
    (hM : IsIsotypicOfType A M S) (hN : IsIsotypicOfType A N S)
    (e : M ≃ₗ[A] N) :
    Cardinal.lift.{x} hM.multiplicity = Cardinal.lift.{v} hN.multiplicity := by
  have hr := (linearMapCongrRight (S := S) e).lift_rank_eq
  apply (Cardinal.lift_inj.{_, w}).mp
  simpa only [multiplicity_eq_rank, Cardinal.lift_lift] using hr

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- Semilinear equivalences over the same chosen ring equivalence preserve the
cardinal multiplicity of corresponding simple types, across independent universes.
No finiteness or commutativity of the coefficient rings is required. -/
theorem lift_multiplicity_eq_of_semilinearEquiv
    {B : Type z} [Ring B] {N : Type x} [AddCommGroup N] [Module B N]
    [IsSemisimpleModule B N] {T : Type y} [AddCommGroup T] [Module B T]
    [IsSimpleModule B T] (hM : IsIsotypicOfType A M S)
    (hN : IsIsotypicOfType B N T) (e : A ≃+* B)
    (eM : M ≃ₛₗ[(e : A →+* B)] N) (eS : S ≃ₛₗ[(e : A →+* B)] T) :
    Cardinal.lift.{max x y} hM.multiplicity =
      Cardinal.lift.{max v w} hN.multiplicity := by
  let ringEquivalence : (Module.End A S)ᵐᵒᵖ ≃+* (Module.End B T)ᵐᵒᵖ :=
    RingEquiv.op (LinearEquiv.conjRingEquiv eS)
  let homEquivalence : (S →ₗ[A] M) ≃+ (T →ₗ[B] N) :=
    LinearEquiv.arrowCongrAddEquiv eS eM
  have compatible (a : (Module.End A S)ᵐᵒᵖ) (f : S →ₗ[A] M) :
      homEquivalence (a • f) = ringEquivalence a • homEquivalence f := by
    ext t
    change eM.toLinearMap (f (a.unop (eS.invFun t))) =
      eM.toLinearMap (f (eS.invFun (eS.toFun (a.unop (eS.invFun t)))))
    rw [eS.left_inv]
  simpa only [multiplicity_eq_rank] using
    lift_rank_eq_of_equiv_equiv ringEquivalence homEquivalence
      ringEquivalence.bijective compatible

/-- A zero module has no copies of a simple module. -/
theorem multiplicity_eq_zero_of_subsingleton [Subsingleton M]
    (h : IsIsotypicOfType A M S) : h.multiplicity = 0 := by
  classical
  have : DivisionRing (Module.End A S) := inferInstance
  have : DivisionRing (Module.End A S)ᵐᵒᵖ := inferInstance
  have : Subsingleton (S →ₗ[A] M) := inferInstance
  simpa only [multiplicity_eq_rank] using (rank_subsingleton' (Module.End A S)ᵐᵒᵖ (S →ₗ[A] M))

omit simple semisimple

/-- A simple module consists of one copy of itself. -/
theorem multiplicity_self (A : Type u) [Ring A]
    (S : Type w) [AddCommGroup S] [Module A S] [IsSimpleModule A S] :
    (IsIsotypicOfType.of_isSimpleModule A S).multiplicity = 1 := by
  classical
  have : StrongRankCondition (Module.End A S)ᵐᵒᵖ := endOpp_strongRankCondition
  simpa only [multiplicity_eq_rank] using
    (MulOpposite.opLinearEquiv (Module.End A S)ᵐᵒᵖ).rank_eq.trans (Module.rank_self _)

end IsIsotypicOfType
