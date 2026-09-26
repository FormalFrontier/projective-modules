/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Exactness of Hom from a projective module

This file packages postcomposition on spaces of linear maps as an additive
homomorphism.  Postcomposition preserves injectivity and exactness at the
middle term, and it preserves surjectivity when the fixed domain is
projective.  Thus `Hom(P, -)` sends short exact sequences of modules to short
exact sequences of additive commutative monoids when `P` is projective.

The results hold over an arbitrary semiring and make no finiteness assumption.
-/

@[expose] public section

universe uR uP uL uM uN

namespace LinearMap

variable {R : Type uR} [Semiring R]
variable {P : Type uP} {L : Type uL} {M : Type uM} {N : Type uN}
variable [AddCommMonoid P] [AddCommMonoid L] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R P] [Module R L] [Module R M] [Module R N]

/-- Postcomposition by a linear map, as an additive homomorphism on a linear
Hom space. -/
def postcomp (f : M →ₗ[R] N) : (P →ₗ[R] M) →+ (P →ₗ[R] N) where
  toFun g := f.comp g
  map_zero' := comp_zero f
  map_add' g h := comp_add g h f

@[simp]
theorem postcomp_apply (f : M →ₗ[R] N) (g : P →ₗ[R] M) :
    postcomp f g = f.comp g :=
  rfl

/-- Postcomposition with an injective linear map is injective. -/
theorem postcomp_injective (i : L →ₗ[R] M) (hi : Function.Injective i) :
    Function.Injective (postcomp (P := P) i) :=
  hi.injective_linearMapComp_left

/-- Postcomposition preserves exactness at the middle Hom space when the
first map of the original exact pair is injective. -/
theorem exact_postcomp (i : L →ₗ[R] M) (p : M →ₗ[R] N)
    (hi : Function.Injective i) (h : Function.Exact i p) :
    Function.Exact (postcomp (P := P) i) (postcomp (P := P) p) := by
  intro g
  constructor
  · intro hg
    change p.comp g = 0 at hg
    let gRange : P →ₗ[R] range i :=
      g.codRestrict (range i) fun x ↦
        (h (g x)).mp <| by
          exact DFunLike.congr_fun hg x
    let lift : P →ₗ[R] L :=
      (LinearEquiv.ofInjective i hi).symm.toLinearMap.comp gRange
    refine ⟨lift, ?_⟩
    ext x
    simp only [postcomp_apply, comp_apply, lift, LinearEquiv.coe_coe,
      LinearEquiv.ofInjective_symm_apply]
    rfl
  · rintro ⟨g', rfl⟩
    change p.comp (i.comp g') = 0
    rw [← comp_assoc, h.linearMap_comp_eq_zero, zero_comp]

end LinearMap

namespace Module.Projective

variable {R : Type uR} [Semiring R]
variable {P : Type uP} {L : Type uL} {M : Type uM} {N : Type uN}
variable [AddCommMonoid P] [AddCommMonoid L] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R P] [Module R L] [Module R M] [Module R N]

/-- If `P` is projective, postcomposition with a surjective linear map is
surjective on linear maps out of `P`. -/
theorem postcomp_surjective [Module.Projective R P]
    (p : M →ₗ[R] N) (hp : Function.Surjective p) :
    Function.Surjective (LinearMap.postcomp (P := P) p) := by
  intro g
  exact Module.projective_lifting_property p g hp

/-- Applying `Hom(P, -)` to an injective/exact/surjective pair preserves all
three properties when `P` is projective. -/
theorem hom_short_exact [Module.Projective R P]
    (i : L →ₗ[R] M) (p : M →ₗ[R] N)
    (hi : Function.Injective i) (h : Function.Exact i p)
    (hp : Function.Surjective p) :
    Function.Injective (LinearMap.postcomp (P := P) i) ∧
      Function.Exact (LinearMap.postcomp (P := P) i)
        (LinearMap.postcomp (P := P) p) ∧
      Function.Surjective (LinearMap.postcomp (P := P) p) :=
  ⟨LinearMap.postcomp_injective i hi, LinearMap.exact_postcomp i p hi h,
    postcomp_surjective p hp⟩

end Module.Projective
