/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.CategoryTheory.Opposites

/-!
# The contravariant dual of right module categories

For a fixed, possibly noncommutative ring `R`, `ModuleCat.rightDual` sends a right
`R`-module `M` to the ordinary-carrier Hom `M →ₗ[Rᵐᵒᵖ] R`, regarded as a left
`R`-module. The codomain `R` has its canonical right regular action
`(MulOpposite.op a) • x = x * a`, and the left action on the Hom is pointwise:
`(r • f)(m) = r * f(m)`. These codomain actions commute by associativity, not
centrality. No left `R`-module structure on `M` is needed.

An opposite arrow acts by precomposition with its underlying right-linear map.
For each fixed arrow this is left `R`-linear; no left action on arbitrary spaces
of source morphisms is asserted. Scalar and module carrier universes are
independent, and the dual carrier inhabits their maximum.

The object, underlying-map, application and scalar lemmas expose the ordinary
Hom presentation. Identity and composition also have pointwise forms. This
construction does not assert finite projectivity, a bidual identification or an
evaluation isomorphism.

## References

* Mathlib contributors, revision `83abb3e776bdefcbc447a1e44d0debe4010039e5`:
  the ordinary opposite-module action, commuting regular actions, pointwise Hom
  module, `LinearMap.lcomp`, and the `ModuleCat` morphism interface.
* `ProjectiveModules.Module.RightRegular`, for the existing ordinary-carrier
  right regular module convention.
-/

@[expose] public section

universe uR uM

open CategoryTheory

namespace ModuleCat

variable (R : Type uR) [Ring R]

/-- The contravariant dual of right modules over a fixed ring. Its values are
ordinary right-linear maps into `R`, with the canonical pointwise left action,
and its morphisms are precomposition.

The definition is reducible so that elements of its values inherit the ordinary
`LinearMap` coercion to functions. -/
@[reducible, simps obj_carrier]
def rightDual :
    (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ ⥤ ModuleCat.{max uR uM} R where
  obj X := ModuleCat.of R (X.unop →ₗ[Rᵐᵒᵖ] R)
  map h := ModuleCat.ofHom (LinearMap.lcomp R R h.unop.hom)
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    rfl
  map_comp h k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro z
    rfl

/-- The right dual object is exactly the ordinary-carrier right-linear Hom,
bundled with its pointwise left `R`-module structure. -/
theorem rightDual_obj (X : (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ) :
    (rightDual R).obj X = ModuleCat.of R (X.unop →ₗ[Rᵐᵒᵖ] R) := rfl

/-- The underlying linear map of the right dual functor is Mathlib's
left-linear precomposition map for the fixed opposite arrow. -/
theorem rightDual_map_hom {X Y : (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ} (h : X ⟶ Y) :
    ((rightDual R).map h).hom = LinearMap.lcomp R R h.unop.hom := rfl

/-- Applying a dual morphism and then evaluating is precomposition with the
underlying right-module morphism. -/
@[simp]
theorem rightDual_map_apply {X Y : (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ} (h : X ⟶ Y)
    (f : (rightDual R).obj X) (y : Y.unop) :
    (rightDual R).map h f y = f (h.unop y) :=
  LinearMap.lcomp_apply h.unop.hom f y

/-- The left action on the ordinary-carrier right dual multiplies the value
on the left. Right linearity in the source remains the inherited `map_smul` law. -/
theorem rightDual_smul_apply {X : (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ} (r : R)
    (f : (rightDual R).obj X) (m : X.unop) :
    (r • f) m = r * f m :=
  LinearMap.smul_apply r f m

/-- Precomposition and evaluation preserve the pointwise left scalar action. -/
theorem rightDual_map_smul_apply {X Y : (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ} (h : X ⟶ Y)
    (r : R) (f : (rightDual R).obj X) (y : Y.unop) :
    (rightDual R).map h (r • f) y = r * f (h.unop y) := by
  rw [rightDual_map_apply, rightDual_smul_apply]

/-- Identity precomposition fixes every value of a right-linear functional. -/
theorem rightDual_map_id_apply (X : (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ)
    (f : (rightDual R).obj X) (x : X.unop) :
    (rightDual R).map (𝟙 X) f x = f x := by
  rw [(rightDual R).map_id]
  rfl

/-- A composite of opposite arrows precomposes in the contravariant order:
the underlying map of the first arrow is evaluated after that of the second. -/
theorem rightDual_map_comp_apply {X Y Z : (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ}
    (h : X ⟶ Y) (k : Y ⟶ Z) (f : (rightDual R).obj X) (z : Z.unop) :
    (rightDual R).map (h ≫ k) f z = f (h.unop (k.unop z)) := by
  rw [(rightDual R).map_comp]
  rfl

end ModuleCat
