/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
public import ProjectiveModules.Module.CommutingIdempotentRanges
import ProjectiveModules.KTheory.ShortExact
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Inclusion-exclusion for ranges of commuting idempotents

For two commuting idempotents on a finite projective right module, their ranges,
intersection and sum are finite projective. Their classes satisfy inclusion-exclusion
in `KTheory.K0`.
The additive groups in these class expressions are induced by the original ring
actions, preserving the additive monoids and module structures.

Commutation does not require the two ranges to be disjoint or their sum to be the
whole ambient module. The intersection and sum are taken in its submodule lattice.

## References

C. Weibel, *The K-book: An introduction to algebraic K-theory*, Chapter II, §2,
for the definition and additivity of the Grothendieck group. The formula here is a
consequence of additivity for the intersection, product and sum of two submodules.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe uR uP

namespace KTheory.K0

private theorem of_add_eq_inf_add_sup (R : Type uR) [Ring R]
    {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P]
    (U V : Submodule Rᵐᵒᵖ P)
    [Module.Finite Rᵐᵒᵖ U] [Module.Projective Rᵐᵒᵖ U]
    [Module.Finite Rᵐᵒᵖ V] [Module.Projective Rᵐᵒᵖ V]
    [Module.Finite Rᵐᵒᵖ ↥(U ⊓ V)] [Module.Projective Rᵐᵒᵖ ↥(U ⊓ V)]
    [Module.Finite Rᵐᵒᵖ ↥(U ⊔ V)] [Module.Projective Rᵐᵒᵖ ↥(U ⊔ V)] :
    of R U + of R V = of R ↥(U ⊓ V) + of R ↥(U ⊔ V) := by
  let i : ↥(U ⊓ V) →ₗ[Rᵐᵒᵖ] U × V :=
    { toFun := fun x =>
        (⟨(x : P), (Submodule.mem_inf.mp x.property).1⟩,
          ⟨-(x : P), V.neg_mem (Submodule.mem_inf.mp x.property).2⟩)
      map_add' := by
        intro x y
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          change -((x : P) + (y : P)) = -(x : P) + -(y : P)
          exact neg_add _ _
      map_smul' := by
        intro r x
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          change -(r • (x : P)) = r • -(x : P)
          exact (smul_neg r (x : P)).symm }
  let s : U × V →ₗ[Rᵐᵒᵖ] ↥(U ⊔ V) :=
    { toFun := fun x =>
        ⟨(x.1 : P) + (x.2 : P), Submodule.add_mem_sup x.1.property x.2.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change ((x.1 : P) + (y.1 : P)) + ((x.2 : P) + (y.2 : P)) =
          ((x.1 : P) + (x.2 : P)) + ((y.1 : P) + (y.2 : P))
        rw [add_assoc, ← add_assoc (y.1 : P) (x.2 : P) (y.2 : P),
          add_comm (y.1 : P) (x.2 : P), add_assoc (x.2 : P) (y.1 : P) (y.2 : P),
          ← add_assoc]
      map_smul' := by
        intro r x
        apply Subtype.ext
        change r • (x.1 : P) + r • (x.2 : P) = r • ((x.1 : P) + (x.2 : P))
        exact (smul_add r (x.1 : P) (x.2 : P)).symm }
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : U × V => (z.1 : P)) h
  have hs : Function.Surjective s := by
    intro x
    rcases Submodule.mem_sup.mp x.property with ⟨u, hu, v, hv, huv⟩
    refine ⟨(⟨u, hu⟩, ⟨v, hv⟩), ?_⟩
    apply Subtype.ext
    exact huv
  have his : LinearMap.range i = LinearMap.ker s := by
    apply le_antisymm
    · intro x hx
      rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change (y : P) + -(y : P) = 0
      exact add_neg_cancel _
    · intro x hx
      have hsum : (x.1 : P) + (x.2 : P) = 0 := by
        have hzero : s x = 0 := LinearMap.mem_ker.mp hx
        exact congrArg (fun z : ↥(U ⊔ V) => (z : P)) hzero
      have hsecond : -(x.1 : P) = (x.2 : P) := by
        calc
          -(x.1 : P) = -(x.1 : P) + ((x.1 : P) + (x.2 : P)) := by
            rw [hsum, add_zero]
          _ = (x.2 : P) := by rw [← add_assoc, neg_add_cancel, zero_add]
      have hV : (x.1 : P) ∈ V := by
        have hmem := V.neg_mem x.2.property
        rw [← hsecond, neg_neg] at hmem
        exact hmem
      refine LinearMap.mem_range.mpr
        ⟨⟨(x.1 : P), Submodule.mem_inf.mpr ⟨x.1.property, hV⟩⟩, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        exact hsecond
  calc
    of R U + of R V = of R (U × V) := (KTheory.K0.of_prod R U V).symm
    _ = of R ↥(U ⊓ V) + of R ↥(U ⊔ V) :=
      KTheory.K0.of_eq_add_of_exact R ↥(U ⊓ V) (U × V) ↥(U ⊔ V) i s hi hs his

/-- The ranges of commuting idempotents satisfy inclusion-exclusion in `K₀`.
Finite projectivity of both ranges, their intersection and their sum is derived from
the finite projective ambient module. The identity follows from additivity for the
canonical intersection-product-sum exact sequence; see Weibel, *The K-book*, II, §2. -/
theorem of_range_add_range_eq_inf_add_sup :
  ∀ (R : Type uR) [Ring R] (P : Type uP) [AddCommMonoid P]
    [_μ : Module Rᵐᵒᵖ P] [_hfinite : Module.Finite Rᵐᵒᵖ P]
    [_hprojective : Module.Projective Rᵐᵒᵖ P] (e f : Module.End Rᵐᵒᵖ P),
    IsIdempotentElem e → IsIdempotentElem f → Commute e f →
      ∃ hfiniteE : Module.Finite Rᵐᵒᵖ e.range,
        ∃ hprojectiveE : Module.Projective Rᵐᵒᵖ e.range,
          ∃ hfiniteF : Module.Finite Rᵐᵒᵖ f.range,
            ∃ hprojectiveF : Module.Projective Rᵐᵒᵖ f.range,
              ∃ hfiniteI : Module.Finite Rᵐᵒᵖ ↥(e.range ⊓ f.range),
                ∃ hprojectiveI : Module.Projective Rᵐᵒᵖ ↥(e.range ⊓ f.range),
                  ∃ hfiniteS : Module.Finite Rᵐᵒᵖ ↥(e.range ⊔ f.range),
                    ∃ hprojectiveS : Module.Projective Rᵐᵒᵖ ↥(e.range ⊔ f.range),
                      @of R _ e.range (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
                          inferInstance hfiniteE hprojectiveE +
                        @of R _ f.range (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
                          inferInstance hfiniteF hprojectiveF =
                        @of R _ ↥(e.range ⊓ f.range)
                            (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
                            inferInstance hfiniteI hprojectiveI +
                          @of R _ ↥(e.range ⊔ f.range)
                            (Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ)
                            inferInstance hfiniteS hprojectiveS := by
  intro R _ P _ _ _ _ e f he hf hef
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ
  let hfiniteE : Module.Finite Rᵐᵒᵖ e.range := Module.Finite.range e
  let hprojectiveE : Module.Projective Rᵐᵒᵖ e.range :=
    Module.Projective.range_of_isIdempotentElem e he
  let hfiniteF : Module.Finite Rᵐᵒᵖ f.range := Module.Finite.range f
  let hprojectiveF : Module.Projective Rᵐᵒᵖ f.range :=
    Module.Projective.range_of_isIdempotentElem f hf
  let hfiniteI : Module.Finite Rᵐᵒᵖ ↥(e.range ⊓ f.range) :=
    Module.Finite.inf_range_of_commute e f he hf hef
  let hprojectiveI : Module.Projective Rᵐᵒᵖ ↥(e.range ⊓ f.range) :=
    Module.Projective.inf_range_of_commute e f he hf hef
  let hfiniteS : Module.Finite Rᵐᵒᵖ ↥(e.range ⊔ f.range) := by
    rw [← LinearMap.range_add_sub_mul_of_commute e f he hf hef]
    exact Module.Finite.range (e + f - e * f)
  let hprojectiveS : Module.Projective Rᵐᵒᵖ ↥(e.range ⊔ f.range) :=
    Module.Projective.sup_range_of_commute e f he hf hef
  refine ⟨hfiniteE, hprojectiveE, hfiniteF, hprojectiveF,
    hfiniteI, hprojectiveI, hfiniteS, hprojectiveS, ?_⟩
  exact of_add_eq_inf_add_sup R e.range f.range

end KTheory.K0
