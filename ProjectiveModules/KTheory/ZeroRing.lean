/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0

/-!
# K₀ over the zero ring

If `R` is a subsingleton ring, every unital right `R`-module is a
subsingleton. Thus all finite projective right modules are linearly
equivalent, the direct-sum class monoid is a subsingleton, and its additive
Grothendieck group is a subsingleton as well.

The instances apply to the entire class monoid and K₀ group. The generator
normalization lemmas accept finite projective modules in arbitrary carrier
universes through the existing ring-universe representative API. No
commutativity, nontriviality or cancellation assumption is needed.

Module rank is not used here: Mathlib's `Module.finrank` over subsingleton
scalars is one, including on a zero module, and does not give an additive
K₀ invariant in this case.

## References and credits

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter II, the group-completion definition of K₀. Allowing the zero ring
  is a generalization of the nonzero-ring convention.
* Mathlib's `Module.subsingleton`, `LinearEquiv.ofSubsingleton`, and
  `AddSubmonoid.LocalizationMap.subsingleton_of_subsingleton`.
* The finite-projective representative and direct-sum class APIs in this
  library.
-/

@[expose] public section

universe u v

namespace KTheory

variable (R : Type u) [Ring R] [Subsingleton R]

namespace ProjectiveClass

/-- All finite projective right modules over a subsingleton ring have the
same direct-sum isomorphism class. -/
instance subsingleton_of_subsingleton : Subsingleton (ProjectiveClass R) := by
  refine ⟨fun a b ↦ ?_⟩
  refine induction_on R a (p := fun a ↦ a = b) fun P ↦ ?_
  refine induction_on R b (p := fun b ↦ of R P = b) fun Q ↦ ?_
  let _ : Subsingleton P := Module.subsingleton Rᵐᵒᵖ P
  let _ : Subsingleton Q := Module.subsingleton Rᵐᵒᵖ Q
  exact (of_eq_iff R P Q).2 ⟨LinearEquiv.ofSubsingleton P Q⟩

/-- Every finite projective right-module class over a subsingleton ring is zero,
independently of the input carrier universe. -/
@[simp]
theorem of_eq_zero_of_subsingleton (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] : of R M = 0 :=
  Subsingleton.elim _ _

end ProjectiveClass

namespace K0

/-- The entire K₀ group of a subsingleton ring is a subsingleton, not only the
set of module generators. This is the zero-ring case of the group-completion
definition of K₀ in Weibel, *The K-book*, Chapter II. -/
instance subsingleton_of_subsingleton : Subsingleton (K0 R) :=
  AddSubmonoid.LocalizationMap.subsingleton_of_subsingleton
    (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass R)))

/-- Every finite projective right module over a subsingleton ring has zero
K₀ generator, independently of the input carrier universe. -/
@[simp]
theorem of_eq_zero_of_subsingleton (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] : of R M = 0 :=
  Subsingleton.elim _ _

end K0

end KTheory
