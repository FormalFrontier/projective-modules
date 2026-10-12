/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
public import Mathlib.Algebra.Field.Opposite
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimension maps on right-module classes and K₀

For a division ring `K`, finite-dimensional right `K`-modules have a natural-valued
additive dimension invariant `KTheory.ProjectiveClass.finrankHom K`. Its extension
through group completion is the integer-valued map `KTheory.K0.finrankHom K`.
Both maps are characterized on module classes, including modules whose carrier
universe is independent of the scalar universe. The regular right module is
presented by the scalar-self module `Kᵐᵒᵖ` and has dimension one.

Dimension descends using `ProjectiveClass.lift`, with Mathlib's invariance under
linear equivalence, zero-space dimension and product dimension as its data.
The integer-valued map uses `K0.lift` and the canonical homomorphism `ℕ →+ ℤ`.
No classification of classes or K₀ by dimension is asserted here. Division-ring
scalars imply freeness and projectivity, so the evaluation laws require only
finite generation of the input module, not a separate projectivity hypothesis.

## References and credits

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter II, dimension and group completion for K₀.
* Mathlib's dimension, finite-module representatives, linear-equivalence and
  opposite-division-ring APIs, and the additive Grothendieck group.
* The finite-projective category and class/group-completion APIs in this library.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace KTheory

variable (K : Type u) [DivisionRing K]

namespace ProjectiveClass

/-- Dimension as an additive map on direct-sum classes of finite-dimensional
right modules over a division ring. -/
noncomputable def finrankHom : ProjectiveClass K →+ ℕ :=
  lift K
    (fun X : ModuleCat.FiniteProjective.{u, u} Kᵐᵒᵖ ↦ Module.finrank Kᵐᵒᵖ X)
    (fun e ↦ (ModuleCat.FiniteProjective.isoToLinearEquiv e).finrank_eq)
    Module.finrank_zero_of_subsingleton
    (fun X Y ↦ (Module.finrank_prod :
      Module.finrank Kᵐᵒᵖ (X × Y) = Module.finrank Kᵐᵒᵖ X + Module.finrank Kᵐᵒᵖ Y))

/-- The dimension map is the descent of Mathlib's module dimension, using its
isomorphism, zero and binary-product laws. -/
theorem finrankHom_eq_lift :
    finrankHom K = lift K
      (fun X : ModuleCat.FiniteProjective.{u, u} Kᵐᵒᵖ ↦ Module.finrank Kᵐᵒᵖ X)
      (fun e ↦ (ModuleCat.FiniteProjective.isoToLinearEquiv e).finrank_eq)
      Module.finrank_zero_of_subsingleton
      (fun X Y ↦ (Module.finrank_prod :
      Module.finrank Kᵐᵒᵖ (X × Y) = Module.finrank Kᵐᵒᵖ X + Module.finrank Kᵐᵒᵖ Y)) := rfl

/-- On reference-module classes, the dimension map evaluates to module dimension. -/
@[simp]
theorem finrankHom_of (X : ModuleCat.FiniteProjective.{u, u} Kᵐᵒᵖ) :
    finrankHom K (of K X) = Module.finrank Kᵐᵒᵖ X := by
  rw [finrankHom_eq_lift, lift_of]

/-- The dimension map evaluates on finite right modules in any carrier universe.
Projectivity follows from the division-ring hypothesis. -/
theorem finrankHom_of_module (M : Type v) [AddCommGroup M] [Module Kᵐᵒᵖ M]
    [Module.Finite Kᵐᵒᵖ M] :
    finrankHom K (of K M) = Module.finrank Kᵐᵒᵖ M := by
  rw [finrankHom_eq_lift, lift_of_module]
  exact (Module.Finite.reprEquiv Kᵐᵒᵖ M).finrank_eq

/-- The dimension map is the unique additive map with the specified values on
reference-module classes. -/
theorem finrankHom_unique (F : ProjectiveClass K →+ ℕ)
    (h : ∀ X : ModuleCat.FiniteProjective.{u, u} Kᵐᵒᵖ,
      F (of K X) = Module.finrank Kᵐᵒᵖ X) : F = finrankHom K := by
  apply addHom_ext K
  intro X
  exact (h X).trans (finrankHom_of K X).symm

/-- The regular right-module class has dimension one. -/
@[simp]
theorem finrankHom_of_self : finrankHom K (of K Kᵐᵒᵖ) = 1 := by
  rw [finrankHom_of_module, Module.finrank_self]

end ProjectiveClass

namespace K0

/-- The integer-valued dimension homomorphism on K₀ of a division ring,
extending the natural-valued dimension of finite-dimensional right modules. -/
noncomputable def finrankHom : K0 K →+ ℤ :=
  lift K ((Int.ofNatHom : ℕ →+ ℤ).comp (ProjectiveClass.finrankHom K))

/-- The integer dimension map is the universal extension of the class dimension
map followed by the canonical homomorphism from natural numbers to integers. -/
theorem finrankHom_eq_lift :
    finrankHom K =
      lift K ((Int.ofNatHom : ℕ →+ ℤ).comp (ProjectiveClass.finrankHom K)) := rfl

/-- On class generators, integer dimension agrees with natural dimension. -/
@[simp]
theorem finrankHom_ofClass (a : ProjectiveClass K) :
    finrankHom K (ofClass K a) = (ProjectiveClass.finrankHom K a : ℤ) := by
  rw [finrankHom_eq_lift, lift_ofClass, AddMonoidHom.comp_apply]
  rfl

/-- Restriction along the completion map recovers the natural-valued dimension
map followed by the canonical integer homomorphism. -/
theorem finrankHom_comp_ofClass :
    (finrankHom K).comp (ofClass K) =
      (Int.ofNatHom : ℕ →+ ℤ).comp (ProjectiveClass.finrankHom K) := by
  apply AddMonoidHom.ext
  intro a
  exact finrankHom_ofClass K a

/-- Integer dimension evaluates on finite right-module generators in any carrier
universe, with projectivity supplied by the division-ring hypothesis. -/
theorem finrankHom_of_module (M : Type v) [AddCommGroup M] [Module Kᵐᵒᵖ M]
    [Module.Finite Kᵐᵒᵖ M] :
    finrankHom K (of K M) = (Module.finrank Kᵐᵒᵖ M : ℤ) := by
  rw [finrankHom_eq_lift, lift_of, AddMonoidHom.comp_apply,
    ProjectiveClass.finrankHom_of_module]
  rfl

/-- On reference-module generators, integer dimension evaluates to module dimension. -/
@[simp]
theorem finrankHom_of (X : ModuleCat.FiniteProjective.{u, u} Kᵐᵒᵖ) :
    finrankHom K (of K X) = (Module.finrank Kᵐᵒᵖ X : ℤ) :=
  finrankHom_of_module K X

/-- The integer dimension map is the unique K₀ homomorphism with the specified
values on reference-module generators. -/
theorem finrankHom_unique (F : K0 K →+ ℤ)
    (h : ∀ X : ModuleCat.FiniteProjective.{u, u} Kᵐᵒᵖ,
      F (of K X) = (Module.finrank Kᵐᵒᵖ X : ℤ)) : F = finrankHom K := by
  apply hom_ext K
  intro X
  exact (h X).trans (finrankHom_of K X).symm

/-- The regular right-module generator has integer dimension one. -/
@[simp]
theorem finrankHom_of_self : finrankHom K (of K Kᵐᵒᵖ) = 1 := by
  rw [finrankHom_of_module, Module.finrank_self]
  exact Nat.cast_one

end K0

end KTheory
