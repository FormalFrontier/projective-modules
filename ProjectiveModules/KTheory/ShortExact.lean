/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Short exact sequence additivity for projective classes and K₀

A short exact sequence of finite projective right modules gives an additive
relation in `KTheory.ProjectiveClass R` and hence in `KTheory.K0 R`. The ring
is arbitrary, and the three module carriers may lie in independent universes.

Projectivity of the quotient supplies a section internally. Mathlib's
split-exact linear equivalence identifies the middle module with the product
of the outer modules; no choice of section is required as input.

## References and credits

* Mathlib's projective lifting property and linear equivalence for right split
  exact sequences.
* The finite-projective isomorphism-class, product and group-completion APIs in
  `ProjectiveModules.KTheory.K0`.
-/

@[expose] public section

universe u v w x

namespace KTheory

variable (R : Type u) [Ring R]
variable (P : Type v) (E : Type w) (Q : Type x)
  [AddCommGroup P] [Module Rᵐᵒᵖ P]
  [AddCommGroup E] [Module Rᵐᵒᵖ E]
  [AddCommGroup Q] [Module Rᵐᵒᵖ Q]
  [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]
  [Module.Finite Rᵐᵒᵖ E] [Module.Projective Rᵐᵒᵖ E]
  [Module.Finite Rᵐᵒᵖ Q] [Module.Projective Rᵐᵒᵖ Q]

namespace ProjectiveClass

/-- A short exact sequence of finite projective right modules gives the
additive relation on their isomorphism classes, using Mathlib's projective
lifting property and split-exact linear equivalence. -/
theorem of_eq_add_of_exact (f : P →ₗ[Rᵐᵒᵖ] E) (g : E →ₗ[Rᵐᵒᵖ] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : LinearMap.range f = LinearMap.ker g) :
    of R E = of R P + of R Q := by
  obtain ⟨s, hs⟩ :=
    Module.projective_lifting_property g (LinearMap.id : Q →ₗ[Rᵐᵒᵖ] Q) hg
  let e : (P × Q) ≃ₗ[Rᵐᵒᵖ] E := lequivProdOfRightSplitExact hf hfg hs
  exact (of_eq_of_equiv R E e.symm).trans (of_prod R P Q)

end ProjectiveClass

namespace K0

/-- A short exact sequence of finite projective right modules gives the
additive relation on their K₀ generators by applying the canonical additive
map from isomorphism classes. -/
theorem of_eq_add_of_exact (f : P →ₗ[Rᵐᵒᵖ] E) (g : E →ₗ[Rᵐᵒᵖ] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : LinearMap.range f = LinearMap.ker g) :
    of R E = of R P + of R Q := by
  simpa only [map_add, ofClass_of] using
    congrArg (ofClass R) (ProjectiveClass.of_eq_add_of_exact R P E Q f g hf hg hfg)

end K0

end KTheory
