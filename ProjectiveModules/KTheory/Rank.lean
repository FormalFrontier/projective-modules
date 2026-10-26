/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
public import ProjectiveModules.KTheory.Ring
public import ProjectiveModules.KTheory.ScalarExtension
public import ProjectiveModules.Module.LocalRing
public import ProjectiveModules.Module.PID
public import ProjectiveModules.Module.RightExtensionFree
public import Mathlib.Algebra.Field.Opposite
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Localization.FractionRing
public import StableRange.Local

import Mathlib.RingTheory.PrincipalIdealDomain

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
The natural-valued map is an additive equivalence
`ProjectiveClass.finrankEquiv K : ProjectiveClass K ≃+ ℕ`: equal finite dimensions
give linearly equivalent modules, and finite coordinate modules realize every
natural number. Its inverse sends `n` to the class of `Fin n → Kᵐᵒᵖ`.
The integer-valued map is an additive equivalence
`K0.finrankEquiv K : K0 K ≃+ ℤ`. Its inverse sends every integer `z` to `z`
times the regular right-module generator. Equality of finite-module generators
in K₀ is equivalent to right-linear isomorphism over a division ring; no such
classification is asserted for arbitrary rings. Division-ring scalars imply
freeness and projectivity, so the evaluation laws require only finite generation
of the input module, not a separate projectivity hypothesis.

Right scalar extension along any unital homomorphism between division rings
preserves both dimension homomorphisms. A finite basis and the right-free
coordinate comparison identify the extension with a coordinate module of the
same dimension; the integer-valued law follows through group completion.
Consequently both induced additive maps are bijective. The scalar homomorphism
itself need not be surjective. Independence from the choice of homomorphism
holds even for an arbitrary ring target, as proved in
`ProjectiveModules.KTheory.ScalarExtension`.

For a possibly noncommutative local ring `R`, `K0.localDimensionHom R` uses
scalar extension to the Jacobson residue division ring before taking dimension.
Its module formula is a residue-module dimension, not source-ring finrank.
For a commutative principal ideal domain, the corresponding scalar extension
uses Mathlib's fraction field.

For fields, commutative local rings and commutative principal ideal domains,
these integer-valued additive equivalences are ring equivalences for tensor
multiplication. Their entire underlying additive equivalences are unchanged.
The inverse is the canonical integer cast, by the existing formula in terms of
the regular right module. This proves multiplicativity without a new tensor-rank
calculation. These hypotheses exclude the zero ring; the generic K₀ ring and
scalar-extension constructions still include it.

## References and credits

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter II, dimension and group completion for K₀.
* Mathlib's dimension, finite-module representatives, linear-equivalence and
  opposite-division-ring APIs, and the additive Grothendieck group.
* The finite-projective category and class/group-completion APIs in this library,
  and its right scalar-extension and finite-coordinate comparisons, contributed
  by Prism and Lens.
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

section DimensionEquivalence

private theorem finrankHom_bijective : Function.Bijective (finrankHom K) := by
  constructor
  · intro a b h
    obtain ⟨X, rfl⟩ := of_surjective K a
    obtain ⟨Y, rfl⟩ := of_surjective K b
    apply (of_eq_iff K X Y).2
    apply (FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq
      (R := Kᵐᵒᵖ) (M := X) (M' := Y)).2
    simpa only [finrankHom_of] using h
  · intro n
    refine ⟨of K (Fin n → Kᵐᵒᵖ), ?_⟩
    rw [finrankHom_of_module, Module.finrank_fin_fun]

/-- Dimension classifies finite projective right-module classes over a division
ring as an additive monoid. The forward map is the canonical dimension map. -/
@[no_expose]
noncomputable def finrankEquiv : ProjectiveClass K ≃+ ℕ :=
  AddEquiv.ofBijective (finrankHom K) (finrankHom_bijective K)

/-- The whole forward homomorphism of the dimension equivalence is the
canonical dimension homomorphism. -/
theorem finrankEquiv_toAddMonoidHom :
    (finrankEquiv K).toAddMonoidHom = finrankHom K := by
  apply AddMonoidHom.ext
  intro a
  exact AddEquiv.ofBijective_apply (finrankHom K) (finrankHom_bijective K) a

/-- The dimension equivalence evaluates by the canonical dimension map. -/
theorem finrankEquiv_apply (a : ProjectiveClass K) :
    finrankEquiv K a = finrankHom K a :=
  congrArg (fun F : ProjectiveClass K →+ ℕ ↦ F a) (finrankEquiv_toAddMonoidHom K)

/-- The dimension equivalence evaluates on finite right modules in any carrier
universe. Projectivity follows from the division-ring hypothesis. -/
@[simp]
theorem finrankEquiv_of_module (M : Type v) [AddCommGroup M] [Module Kᵐᵒᵖ M]
    [Module.Finite Kᵐᵒᵖ M] :
    finrankEquiv K (of K M) = Module.finrank Kᵐᵒᵖ M := by
  rw [finrankEquiv_apply, finrankHom_of_module]

/-- The inverse dimension equivalence sends a natural number to the class of
its finite coordinate module. -/
theorem finrankEquiv_symm_apply (n : ℕ) :
    (finrankEquiv K).symm n = of K (Fin n → Kᵐᵒᵖ) := by
  apply (finrankEquiv K).injective
  rw [AddEquiv.apply_symm_apply, finrankEquiv_of_module, Module.finrank_fin_fun]

/-- Applying the inverse equivalence to the canonical dimension recovers the
original right-module class. -/
theorem finrankEquiv_symm_apply_finrank (a : ProjectiveClass K) :
    (finrankEquiv K).symm (finrankHom K a) = a := by
  rw [← finrankEquiv_apply]
  exact (finrankEquiv K).symm_apply_apply a

/-- The canonical dimension of the inverse equivalence is the original
natural number. -/
theorem finrankHom_finrankEquiv_symm (n : ℕ) :
    finrankHom K ((finrankEquiv K).symm n) = n := by
  rw [← finrankEquiv_apply]
  exact (finrankEquiv K).apply_symm_apply n

/-- Every finite right-module class is the inverse image of its dimension,
independently of its carrier universe. -/
theorem of_eq_finrankEquiv_symm (M : Type v) [AddCommGroup M] [Module Kᵐᵒᵖ M]
    [Module.Finite Kᵐᵒᵖ M] :
    of K M = (finrankEquiv K).symm (Module.finrank Kᵐᵒᵖ M) := by
  rw [← finrankEquiv_of_module K M]
  exact ((finrankEquiv K).symm_apply_apply (of K M)).symm

/-- The dimension equivalence sends the regular right-module class to one. -/
theorem finrankEquiv_of_self : finrankEquiv K (of K Kᵐᵒᵖ) = 1 := by
  rw [finrankEquiv_apply, finrankHom_of_self]

/-- The inverse dimension equivalence sends one to the regular right-module
class. -/
@[simp]
theorem finrankEquiv_symm_one : (finrankEquiv K).symm 1 = of K Kᵐᵒᵖ := by
  apply (finrankEquiv K).injective
  rw [AddEquiv.apply_symm_apply, finrankEquiv_of_self]

end DimensionEquivalence

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

section DimensionEquivalence

universe w

private noncomputable def finrankInverseHom : ℤ →+ K0 K :=
  zmultiplesHom (K0 K) (of K Kᵐᵒᵖ)

private theorem finrankHom_comp_finrankInverseHom :
    (finrankHom K).comp (finrankInverseHom K) = AddMonoidHom.id ℤ := by
  apply AddMonoidHom.ext
  intro z
  change finrankHom K (z • of K Kᵐᵒᵖ) = z
  rw [map_zsmul, finrankHom_of_self]
  simp

private theorem finrankInverseHom_comp_finrankHom :
    (finrankInverseHom K).comp (finrankHom K) = AddMonoidHom.id (K0 K) := by
  apply hom_ext K
  intro X
  rw [AddMonoidHom.comp_apply, finrankHom_of]
  change (Module.finrank Kᵐᵒᵖ X : ℤ) • of K Kᵐᵒᵖ = of K X
  rw [natCast_zsmul, ← ofClass_of K X,
    ProjectiveClass.of_eq_finrankEquiv_symm K X,
    ProjectiveClass.finrankEquiv_symm_apply, ProjectiveClass.of_fin_fun_eq_nsmul,
    map_nsmul, ofClass_of]

private theorem finrankHom_bijective : Function.Bijective (finrankHom K) := by
  have hleft : Function.LeftInverse (finrankInverseHom K) (finrankHom K) := fun x ↦
    congrArg (fun F : K0 K →+ K0 K ↦ F x) (finrankInverseHom_comp_finrankHom K)
  have hright : Function.RightInverse (finrankInverseHom K) (finrankHom K) := fun z ↦
    congrArg (fun F : ℤ →+ ℤ ↦ F z) (finrankHom_comp_finrankInverseHom K)
  exact ⟨hleft.injective, hright.surjective⟩

/-- Integer dimension classifies K₀ of a division ring as an additive group.
The forward map is the canonical dimension homomorphism, and the inverse is
integer multiplication of the regular right-module generator.
See Weibel, *The K-book*, Chapter II, for dimension and group completion. -/
@[no_expose]
noncomputable def finrankEquiv : K0 K ≃+ ℤ :=
  AddEquiv.ofBijective (finrankHom K) (finrankHom_bijective K)

/-- The whole forward homomorphism of the dimension equivalence is the
canonical integer dimension homomorphism. -/
theorem finrankEquiv_toAddMonoidHom :
    (finrankEquiv K).toAddMonoidHom = finrankHom K := by
  apply AddMonoidHom.ext
  intro x
  exact AddEquiv.ofBijective_apply (finrankHom K) (finrankHom_bijective K) x

/-- The integer dimension equivalence evaluates by the canonical dimension map. -/
theorem finrankEquiv_apply (x : K0 K) :
    finrankEquiv K x = finrankHom K x :=
  congrArg (fun F : K0 K →+ ℤ ↦ F x) (finrankEquiv_toAddMonoidHom K)

/-- The inverse dimension equivalence sends every integer, including negative
integers, to that multiple of the regular right-module generator. -/
theorem finrankEquiv_symm_apply (z : ℤ) :
    (finrankEquiv K).symm z = z • of K Kᵐᵒᵖ := by
  apply (finrankEquiv K).injective
  rw [AddEquiv.apply_symm_apply, finrankEquiv_apply, map_zsmul, finrankHom_of_self]
  simp

/-- Applying the inverse equivalence to the canonical integer dimension
recovers the original K₀ element. -/
theorem finrankEquiv_symm_apply_finrank (x : K0 K) :
    (finrankEquiv K).symm (finrankHom K x) = x := by
  rw [← finrankEquiv_apply]
  exact (finrankEquiv K).symm_apply_apply x

/-- The canonical integer dimension of the inverse equivalence is the
original integer. -/
theorem finrankHom_finrankEquiv_symm (z : ℤ) :
    finrankHom K ((finrankEquiv K).symm z) = z := by
  rw [← finrankEquiv_apply]
  exact (finrankEquiv K).apply_symm_apply z

/-- On class generators, the integer dimension equivalence is the natural
class dimension equivalence followed by the canonical integer cast. -/
theorem finrankEquiv_ofClass (a : ProjectiveClass K) :
    finrankEquiv K (ofClass K a) = (ProjectiveClass.finrankEquiv K a : ℤ) := by
  rw [finrankEquiv_apply, finrankHom_ofClass, ProjectiveClass.finrankEquiv_apply]

/-- The inverse dimension equivalence sends a natural number, cast to an
integer, to the generator of its finite coordinate module. -/
theorem finrankEquiv_symm_natCast (n : ℕ) :
    (finrankEquiv K).symm (n : ℤ) = of K (Fin n → Kᵐᵒᵖ) := by
  rw [finrankEquiv_symm_apply, natCast_zsmul,
    ← ofClass_of K (Fin n → Kᵐᵒᵖ), ProjectiveClass.of_fin_fun_eq_nsmul,
    map_nsmul, ofClass_of]

/-- The dimension equivalence sends the regular right-module generator to one. -/
theorem finrankEquiv_of_self : finrankEquiv K (of K Kᵐᵒᵖ) = 1 := by
  rw [finrankEquiv_apply, finrankHom_of_self]

/-- The inverse dimension equivalence sends one to the regular right-module
generator. -/
@[simp]
theorem finrankEquiv_symm_one : (finrankEquiv K).symm 1 = of K Kᵐᵒᵖ := by
  rw [finrankEquiv_symm_apply, one_zsmul]

section FiniteModules

variable (M : Type v) [AddCommGroup M] [Module Kᵐᵒᵖ M] [Module.Finite Kᵐᵒᵖ M]

/-- The integer dimension equivalence evaluates on finite right-module
generators in any carrier universe. Projectivity follows from the division-ring
hypothesis. -/
@[simp]
theorem finrankEquiv_of_module :
    finrankEquiv K (of K M) = (Module.finrank Kᵐᵒᵖ M : ℤ) := by
  rw [finrankEquiv_apply, finrankHom_of_module]

/-- Every finite right-module generator over a division ring is its dimension
times the regular right-module generator, independently of its carrier universe. -/
theorem of_eq_finrank_zsmul :
    of K M = (Module.finrank Kᵐᵒᵖ M : ℤ) • of K Kᵐᵒᵖ := by
  calc
    of K M = (finrankEquiv K).symm (Module.finrank Kᵐᵒᵖ M : ℤ) := by
      rw [← finrankEquiv_of_module K M]
      exact ((finrankEquiv K).symm_apply_apply (of K M)).symm
    _ = _ := finrankEquiv_symm_apply K _

variable (N : Type w) [AddCommGroup N] [Module Kᵐᵒᵖ N] [Module.Finite Kᵐᵒᵖ N]

/-- Over a division ring, equality of finite right-module generators in K₀
is equivalent to right-linear isomorphism, for unrelated carrier universes.
This classification does not hold for arbitrary rings. -/
theorem of_eq_iff_linearEquiv :
    of K M = of K N ↔ Nonempty (M ≃ₗ[Kᵐᵒᵖ] N) := by
  constructor
  · intro h
    apply (FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq
      (R := Kᵐᵒᵖ) (M := M) (M' := N)).2
    apply Int.ofNat_inj.mp
    simpa only [finrankHom_of_module] using congrArg (finrankHom K) h
  · rintro ⟨e⟩
    exact of_eq_of_equiv K M e

end FiniteModules

end DimensionEquivalence

end K0

section IntegerRetraction

universe uA uD

variable {A : Type uA} [Ring A] {D : Type uD} [DivisionRing D]

/-- Scalar extension to a division ring sends the regular right-module K₀
generator to an element of integer dimension one. -/
theorem K0.finrankHom_map_of_self (φ : A →+* D) :
    K0.finrankHom D (K0.map φ (K0.of A Aᵐᵒᵖ)) = 1 := by
  rw [K0.map_of_self, K0.finrankHom_of_self]

/-- A unital map from an arbitrary ring to a division ring gives a retraction
onto the integer multiples of the regular right-module class. No surjectivity
of the ring homomorphism is required. This is the split integer summand of
Weibel's *The K-book*, Chapter II, §2. -/
theorem K0.finrankHom_comp_map_zmultiplesHom (φ : A →+* D) :
    ((K0.finrankHom D).comp (K0.map φ)).comp
        (zmultiplesHom (K0 A) (K0.of A Aᵐᵒᵖ)) = AddMonoidHom.id ℤ := by
  apply AddMonoidHom.ext_int
  simpa only [AddMonoidHom.comp_apply, zmultiplesHom_apply, one_zsmul,
    AddMonoidHom.id_apply] using K0.finrankHom_map_of_self φ

end IntegerRetraction

end KTheory

universe uS

namespace KTheory

section ScalarExtensionNaturality

variable {D : Type u} [DivisionRing D] {S : Type uS} [DivisionRing S]

/-- Right scalar extension between division rings preserves the dimension
homomorphism on finite-projective classes. A finite basis identifies the
extension with a coordinate module of the same dimension. -/
theorem ProjectiveClass.finrankHom_comp_map (φ : D →+* S) :
    (ProjectiveClass.finrankHom S).comp (ProjectiveClass.map φ) =
      ProjectiveClass.finrankHom D := by
  apply ProjectiveClass.addHom_ext D
  intro X
  simp only [AddMonoidHom.comp_apply, ProjectiveClass.map_of,
    ProjectiveClass.finrankHom_of_module]
  let e : X ≃ₗ[Dᵐᵒᵖ] (Fin (Module.finrank Dᵐᵒᵖ X) → D) :=
    (Module.finBasis Dᵐᵒᵖ X).equivFun.trans (Module.rightFreeCoordEquiv D _)
  let eS : ModuleCat.RightExtension.Obj φ X ≃ₗ[Sᵐᵒᵖ]
      (Fin (Module.finrank Dᵐᵒᵖ X) → Sᵐᵒᵖ) :=
    (ModuleCat.RightExtension.mapLinearEquiv φ e).trans
      ((ModuleCat.RightExtension.rightFreeLinearEquiv φ _).trans
        (Module.rightFreeCoordEquiv S _).symm)
  exact eS.finrank_eq.trans (Module.finrank_fin_fun Sᵐᵒᵖ)

/-- Right scalar extension along a homomorphism between division rings is
bijective on finite-projective right-module classes. -/
theorem ProjectiveClass.map_bijective (φ : D →+* S) :
    Function.Bijective (ProjectiveClass.map φ) := by
  have hD : Function.Bijective (ProjectiveClass.finrankHom D) := by
    rw [← ProjectiveClass.finrankEquiv_toAddMonoidHom D]
    exact (ProjectiveClass.finrankEquiv D).bijective
  have hS : Function.Bijective (ProjectiveClass.finrankHom S) := by
    rw [← ProjectiveClass.finrankEquiv_toAddMonoidHom S]
    exact (ProjectiveClass.finrankEquiv S).bijective
  apply (hS.of_comp_iff' (ProjectiveClass.map φ)).mp
  change Function.Bijective
    ((ProjectiveClass.finrankHom S).comp (ProjectiveClass.map φ))
  rw [ProjectiveClass.finrankHom_comp_map]
  exact hD

/-- Right scalar extension between division rings preserves the integer-valued
K₀ dimension homomorphism. This follows from class dimension and the
universal property of group completion. -/
theorem K0.finrankHom_comp_map (φ : D →+* S) :
    (K0.finrankHom S).comp (K0.map φ) = K0.finrankHom D := by
  apply K0.hom_ext_ofClass D
  intro a
  simpa only [AddMonoidHom.comp_apply, K0.map_ofClass, K0.finrankHom_ofClass] using
    congrArg (fun n : ℕ ↦ (n : ℤ))
      (DFunLike.congr_fun (ProjectiveClass.finrankHom_comp_map φ) a)

/-- Right scalar extension between division rings induces a bijection on K₀. -/
theorem K0.map_bijective (φ : D →+* S) : Function.Bijective (K0.map φ) := by
  exact K0.map_bijective_of_projectiveClass_map_bijective φ
    (ProjectiveClass.map_bijective φ)

end ScalarExtensionNaturality

section ProjectiveFreeScalarExtension

variable {R : Type u} [Ring R] {D : Type uS} [DivisionRing D]

/-- Scalar extension to a division ring is bijective on finite-projective
right-module classes when every canonical finite-projective source object is
free. The scalar homomorphism need not be injective or surjective. -/
theorem ProjectiveClass.map_bijective_of_projective_free (q : R →+* D)
    (hfree : ∀ X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ,
      Module.Free Rᵐᵒᵖ X) :
    Function.Bijective (ProjectiveClass.map q) := by
  classical
  have hcoordinate (X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ) :
      ∃ n : ℕ, ProjectiveClass.of R X =
        ProjectiveClass.of R (Fin n → Rᵐᵒᵖ) := by
    let : Module.Free Rᵐᵒᵖ X := hfree X
    let ι := Module.Free.ChooseBasisIndex Rᵐᵒᵖ X
    let : Fintype ι := Module.Free.ChooseBasisIndex.fintype Rᵐᵒᵖ X
    let b : Module.Basis (Fin (Fintype.card ι)) Rᵐᵒᵖ X :=
      (Module.Free.chooseBasis Rᵐᵒᵖ X).reindex (Fintype.equivFin ι)
    exact ⟨Fintype.card ι, ProjectiveClass.of_eq_of_equiv R X b.equivFun⟩
  have hmap (n : ℕ) :
      ProjectiveClass.map q (ProjectiveClass.of R (Fin n → Rᵐᵒᵖ)) =
        ProjectiveClass.of D (Fin n → Dᵐᵒᵖ) := by
    rw [ProjectiveClass.of_fin_fun_eq_nsmul, map_nsmul,
      ProjectiveClass.map_of_self, ProjectiveClass.of_fin_fun_eq_nsmul]
  constructor
  · intro a b hab
    obtain ⟨X, rfl⟩ := ProjectiveClass.of_surjective R a
    obtain ⟨Y, rfl⟩ := ProjectiveClass.of_surjective R b
    obtain ⟨m, hm⟩ := hcoordinate X
    obtain ⟨n, hn⟩ := hcoordinate Y
    dsimp only at hab ⊢
    rw [hm, hn, hmap, hmap] at hab
    have hmn : m = n := by
      simpa only [ProjectiveClass.finrankHom_of_module, Module.finrank_fin_fun] using
        congrArg (ProjectiveClass.finrankHom D) hab
    rw [hm, hn, hmn]
  · intro a
    refine ⟨ProjectiveClass.of R (Fin (ProjectiveClass.finrankHom D a) → Rᵐᵒᵖ), ?_⟩
    rw [hmap, ← ProjectiveClass.finrankEquiv_symm_apply]
    exact ProjectiveClass.finrankEquiv_symm_apply_finrank D a

end ProjectiveFreeScalarExtension

/-!
## Local rings and principal ideal domains

The residue construction below uses Mathlib's standard ideal quotient and its
division-ring structure, with the canonical Jacobson maximality theorem from
`StableRange.Local`. Finite-projective freeness is provided by
`Module.Projective.free_of_isLocalRing` and `Module.Projective.free_of_pid` in
this library; applying these to opposite scalars gives the right-module inputs.
The PID calculation uses Mathlib's existing fraction field, with no new rank
or group-completion construction.
-/

namespace K0

section LocalDimension

variable (R : Type u) [Ring R] [IsLocalRing R]

/-- Integer dimension after scalar extension to the canonical Jacobson residue
division ring of a possibly noncommutative local ring. The quotient, its ring
structure and the scalar-extension action are the standard constructions. -/
noncomputable def localDimensionHom : K0 R →+ ℤ := by
  letI : (Ring.jacobson R).IsMaximal := IsLocalRing.isMaximal_ringJacobson R
  letI : DivisionRing (R ⧸ Ring.jacobson R) :=
    Ideal.Quotient.divisionRing (Ring.jacobson R)
  exact (finrankHom (R ⧸ Ring.jacobson R)).comp
    (map (Ideal.Quotient.mk (Ring.jacobson R)))

/-- The whole local dimension homomorphism is canonical residue scalar
extension followed by division-ring dimension. -/
theorem localDimensionHom_eq_comp :
    localDimensionHom R =
      (@finrankHom (R ⧸ Ring.jacobson R)
        (@Ideal.Quotient.divisionRing R _ (Ring.jacobson R) _
          (IsLocalRing.isMaximal_ringJacobson R))).comp
        (map (Ideal.Quotient.mk (Ring.jacobson R))) := rfl

/-- Local dimension evaluates by applying division-ring dimension to the
canonical residue scalar extension. -/
theorem localDimensionHom_apply (x : K0 R) :
    localDimensionHom R x =
      @finrankHom (R ⧸ Ring.jacobson R)
        (@Ideal.Quotient.divisionRing R _ (Ring.jacobson R) _
          (IsLocalRing.isMaximal_ringJacobson R))
        (map (Ideal.Quotient.mk (Ring.jacobson R)) x) := rfl

/-- On class generators, local dimension is residue class dimension followed
by the canonical integer cast. -/
theorem localDimensionHom_ofClass (a : ProjectiveClass R) :
    localDimensionHom R (ofClass R a) =
      (@ProjectiveClass.finrankHom (R ⧸ Ring.jacobson R)
        (@Ideal.Quotient.divisionRing R _ (Ring.jacobson R) _
          (IsLocalRing.isMaximal_ringJacobson R))
        (ProjectiveClass.map (Ideal.Quotient.mk (Ring.jacobson R)) a) : ℤ) := by
  let : (Ring.jacobson R).IsMaximal := IsLocalRing.isMaximal_ringJacobson R
  let : DivisionRing (R ⧸ Ring.jacobson R) :=
    Ideal.Quotient.divisionRing (Ring.jacobson R)
  change finrankHom (R ⧸ Ring.jacobson R)
    (map (Ideal.Quotient.mk (Ring.jacobson R)) (ofClass R a)) = _
  rw [map_ofClass, finrankHom_ofClass]

/-- On finite projective right modules in any carrier universe, local dimension
is the dimension of the canonical residue module, not source-ring finrank. -/
theorem localDimensionHom_of_module (M : Type v) [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    localDimensionHom R (of R M) =
      (Module.finrank (R ⧸ Ring.jacobson R)ᵐᵒᵖ
        (ModuleCat.RightExtension.Obj (Ideal.Quotient.mk (Ring.jacobson R)) M) : ℤ) := by
  let : (Ring.jacobson R).IsMaximal := IsLocalRing.isMaximal_ringJacobson R
  let : DivisionRing (R ⧸ Ring.jacobson R) :=
    Ideal.Quotient.divisionRing (Ring.jacobson R)
  change finrankHom (R ⧸ Ring.jacobson R)
    (map (Ideal.Quotient.mk (Ring.jacobson R)) (of R M)) = _
  rw [map_of, finrankHom_of_module]

/-- The regular right-module generator has local dimension one. -/
@[simp]
theorem localDimensionHom_of_self : localDimensionHom R (of R Rᵐᵒᵖ) = 1 := by
  let : (Ring.jacobson R).IsMaximal := IsLocalRing.isMaximal_ringJacobson R
  let : DivisionRing (R ⧸ Ring.jacobson R) :=
    Ideal.Quotient.divisionRing (Ring.jacobson R)
  exact finrankHom_map_of_self (Ideal.Quotient.mk (Ring.jacobson R))

/-- Dimension over the canonical Jacobson residue division ring classifies K₀
of a possibly noncommutative local ring. See Weibel's *The K-book*,
Chapter II, §2, for the local-ring K₀ calculation. -/
theorem localDimensionHom_bijective : Function.Bijective (localDimensionHom R) := by
  let : (Ring.jacobson R).IsMaximal := IsLocalRing.isMaximal_ringJacobson R
  let : DivisionRing (R ⧸ Ring.jacobson R) :=
    Ideal.Quotient.divisionRing (Ring.jacobson R)
  have hmap : Function.Bijective (map (Ideal.Quotient.mk (Ring.jacobson R))) :=
    map_bijective_of_projectiveClass_map_bijective _
      (ProjectiveClass.map_bijective_of_projective_free _ fun X ↦
        Module.Projective.free_of_isLocalRing (R := Rᵐᵒᵖ) (P := X))
  have hdimension : Function.Bijective (finrankHom (R ⧸ Ring.jacobson R)) := by
    rw [← finrankEquiv_toAddMonoidHom]
    exact (finrankEquiv (R ⧸ Ring.jacobson R)).bijective
  change Function.Bijective
    ((finrankHom (R ⧸ Ring.jacobson R)).comp
      (map (Ideal.Quotient.mk (Ring.jacobson R))))
  exact hdimension.comp hmap

end LocalDimension

section PrincipalIdealDomainDimension

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- Scalar extension to the fraction field followed by integer dimension
classifies K₀ of a commutative principal ideal domain. See Weibel's *The K-book*,
Chapter II, §2, for this calculation and its specialization to the integers. -/
theorem pidDimension_bijective :
    Function.Bijective
      ((finrankHom (FractionRing R)).comp (map (algebraMap R (FractionRing R)))) := by
  let : IsPrincipalIdealRing Rᵐᵒᵖ :=
    IsPrincipalIdealRing.of_surjective (RingEquiv.toOpposite R).toRingHom
      (RingEquiv.toOpposite R).surjective
  have hmap : Function.Bijective (map (algebraMap R (FractionRing R))) :=
    map_bijective_of_projectiveClass_map_bijective _
      (ProjectiveClass.map_bijective_of_projective_free _ fun X ↦
        Module.Projective.free_of_pid Rᵐᵒᵖ X)
  have hdimension : Function.Bijective (finrankHom (FractionRing R)) := by
    rw [← finrankEquiv_toAddMonoidHom]
    exact (finrankEquiv (FractionRing R)).bijective
  exact hdimension.comp hmap

end PrincipalIdealDomainDimension

end K0

end KTheory

/-!
## Integer-valued equivalences for local rings and principal ideal domains

`K0.localEquivInt` and `K0.pidEquivInt` bundle the canonical dimension maps as
additive equivalences. Their inverses send any integer to that multiple of the
regular right-module generator. Module evaluation uses residue dimension for
local rings and fraction-field dimension for principal ideal domains. In the
PID case this also agrees with the source module's finrank.
-/

namespace KTheory.K0

section LocalIntegerEquivalence

variable (R : Type u) [Ring R] [IsLocalRing R]

/-- K₀ of a possibly noncommutative local ring is additively equivalent to the
integers by dimension over its canonical Jacobson residue division ring.
See Weibel, *The K-book*, Chapter II, §2. -/
@[no_expose]
noncomputable def localEquivInt : K0 R ≃+ ℤ :=
  AddEquiv.ofBijective (localDimensionHom R) (localDimensionHom_bijective R)

/-- The whole forward homomorphism of the local K₀ equivalence is the canonical
residue dimension homomorphism. -/
theorem localEquivInt_toAddMonoidHom :
    (localEquivInt R).toAddMonoidHom = localDimensionHom R := by
  apply AddMonoidHom.ext
  intro x
  exact AddEquiv.ofBijective_apply (localDimensionHom R)
    (localDimensionHom_bijective R) x

/-- The local K₀ equivalence evaluates by the canonical residue dimension map. -/
theorem localEquivInt_apply (x : K0 R) :
    localEquivInt R x = localDimensionHom R x :=
  congrArg (fun F : K0 R →+ ℤ ↦ F x) (localEquivInt_toAddMonoidHom R)

/-- On finite projective right modules in any carrier universe, the local K₀
equivalence is the dimension of the canonical residue module, not source-ring
finrank. -/
@[simp]
theorem localEquivInt_of_module (M : Type v) [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    localEquivInt R (of R M) =
      (Module.finrank (R ⧸ Ring.jacobson R)ᵐᵒᵖ
        (ModuleCat.RightExtension.Obj (Ideal.Quotient.mk (Ring.jacobson R)) M) : ℤ) := by
  rw [localEquivInt_apply, localDimensionHom_of_module]

/-- The local K₀ equivalence sends the regular right-module generator to one. -/
@[simp↓]
theorem localEquivInt_of_self : localEquivInt R (of R Rᵐᵒᵖ) = 1 := by
  rw [localEquivInt_apply, localDimensionHom_of_self]

/-- The inverse local K₀ equivalence sends every integer, including negative
integers, to that multiple of the regular right-module generator. -/
theorem localEquivInt_symm_apply (z : ℤ) :
    (localEquivInt R).symm z = z • of R Rᵐᵒᵖ := by
  apply (localEquivInt R).injective
  rw [AddEquiv.apply_symm_apply, map_zsmul, localEquivInt_of_self]
  simp

/-- The inverse local K₀ equivalence sends one to the regular right-module
generator. -/
@[simp]
theorem localEquivInt_symm_one : (localEquivInt R).symm 1 = of R Rᵐᵒᵖ := by
  rw [localEquivInt_symm_apply, one_zsmul]

end LocalIntegerEquivalence

section PrincipalIdealDomainIntegerEquivalence

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- K₀ of a commutative principal ideal domain is additively equivalent to the
integers by scalar extension to its fraction field followed by dimension.
See Weibel, *The K-book*, Chapter II, §2. -/
@[no_expose]
noncomputable def pidEquivInt : K0 R ≃+ ℤ :=
  AddEquiv.ofBijective
    ((finrankHom (FractionRing R)).comp (map (algebraMap R (FractionRing R))))
    (pidDimension_bijective R)

/-- The whole forward homomorphism of the PID K₀ equivalence is canonical
fraction-field scalar extension followed by integer dimension. -/
theorem pidEquivInt_toAddMonoidHom :
    (pidEquivInt R).toAddMonoidHom =
      (finrankHom (FractionRing R)).comp (map (algebraMap R (FractionRing R))) := by
  apply AddMonoidHom.ext
  intro x
  exact AddEquiv.ofBijective_apply
    ((finrankHom (FractionRing R)).comp (map (algebraMap R (FractionRing R))))
    (pidDimension_bijective R) x

/-- The PID K₀ equivalence evaluates by dimension after canonical fraction-field
scalar extension. -/
theorem pidEquivInt_apply (x : K0 R) :
    pidEquivInt R x =
      finrankHom (FractionRing R) (map (algebraMap R (FractionRing R)) x) :=
  congrArg (fun F : K0 R →+ ℤ ↦ F x) (pidEquivInt_toAddMonoidHom R)

/-- On finite projective right modules in any carrier universe, the PID K₀
equivalence is the dimension of the canonical fraction-field extension. -/
@[simp]
theorem pidEquivInt_of_module (M : Type v) [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    pidEquivInt R (of R M) =
      (Module.finrank (FractionRing R)ᵐᵒᵖ
        (ModuleCat.RightExtension.Obj (algebraMap R (FractionRing R)) M) : ℤ) := by
  rw [pidEquivInt_apply, map_of, finrankHom_of_module]

/-- On finite projective right modules over a PID, fraction-field dimension
agrees with source-ring finrank. The carrier universe is independent of the
scalar universe, and projective freeness is supplied by the PID theorem. -/
theorem pidEquivInt_of_module_finrank (M : Type v) [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    pidEquivInt R (of R M) = (Module.finrank Rᵐᵒᵖ M : ℤ) := by
  let : IsPrincipalIdealRing Rᵐᵒᵖ :=
    IsPrincipalIdealRing.of_surjective (RingEquiv.toOpposite R).toRingHom
      (RingEquiv.toOpposite R).surjective
  let : Module.Free Rᵐᵒᵖ M := Module.Projective.free_of_pid Rᵐᵒᵖ M
  let e : M ≃ₗ[Rᵐᵒᵖ] (Fin (Module.finrank Rᵐᵒᵖ M) → R) :=
    (Module.finBasis Rᵐᵒᵖ M).equivFun.trans (Module.rightFreeCoordEquiv R _)
  let eF :
      ModuleCat.RightExtension.Obj (algebraMap R (FractionRing R)) M ≃ₗ[(FractionRing R)ᵐᵒᵖ]
        (Fin (Module.finrank Rᵐᵒᵖ M) → (FractionRing R)ᵐᵒᵖ) :=
    (ModuleCat.RightExtension.mapLinearEquiv (algebraMap R (FractionRing R)) e).trans
      ((ModuleCat.RightExtension.rightFreeLinearEquiv (algebraMap R (FractionRing R)) _).trans
        (Module.rightFreeCoordEquiv (FractionRing R) _).symm)
  rw [pidEquivInt_of_module, eF.finrank_eq, Module.finrank_fin_fun]

/-- The PID K₀ equivalence sends the regular right-module generator to one. -/
theorem pidEquivInt_of_self : pidEquivInt R (of R Rᵐᵒᵖ) = 1 := by
  rw [pidEquivInt_apply, map_of_self, finrankHom_of_self]

/-- The inverse PID K₀ equivalence sends every integer, including negative
integers, to that multiple of the regular right-module generator. -/
theorem pidEquivInt_symm_apply (z : ℤ) :
    (pidEquivInt R).symm z = z • of R Rᵐᵒᵖ := by
  apply (pidEquivInt R).injective
  rw [AddEquiv.apply_symm_apply, map_zsmul, pidEquivInt_of_self]
  simp

/-- The inverse PID K₀ equivalence sends one to the regular right-module
generator. -/
@[simp]
theorem pidEquivInt_symm_one : (pidEquivInt R).symm 1 = of R Rᵐᵒᵖ := by
  rw [pidEquivInt_symm_apply, one_zsmul]

end PrincipalIdealDomainIntegerEquivalence

end KTheory.K0

/-!
## Integer-valued ring equivalences

The inverse of each additive equivalence is integer multiplication of the
regular generator, hence the canonical integer cast into the tensor-product
ring. Multiplicativity follows from this inverse formula and `Int.cast_mul`.
The construction uses Mathlib's `AddEquiv.toRingEquiv`, retaining the whole
additive equivalence, including its inverse.
-/

namespace KTheory.K0

private theorem map_mul_of_symm_intCast {A : Type u} [Ring A]
    (e : A ≃+ ℤ) (h : ∀ z : ℤ, e.symm z = (z : A)) (x y : A) :
    e (x * y) = e x * e y := by
  have hx : (e x : A) = x := (h (e x)).symm.trans (e.symm_apply_apply x)
  have hy : (e y : A) = y := (h (e y)).symm.trans (e.symm_apply_apply y)
  apply e.symm.injective
  calc
    e.symm (e (x * y)) = x * y := e.symm_apply_apply _
    _ = (e x : A) * (e y : A) := congrArg₂ (fun a b : A ↦ a * b) hx.symm hy.symm
    _ = ((e x * e y : ℤ) : A) := (Int.cast_mul _ _).symm
    _ = e.symm (e x * e y) := (h _).symm

section FieldRingEquivalence

variable (K : Type u) [hK : Field K]

/-- The tensor-ring unit over a field has integer dimension one. -/
@[simp]
theorem finrankHom_one : finrankHom K (1 : K0 K) = 1 := by
  rw [one_eq_of, finrankHom_of_self]

/-- Integer dimension identifies the tensor-product ring K₀ of a field with
`ℤ`. Its additive equivalence is `finrankEquiv`, and its inverse is integer
multiplication of the regular right-module generator.
See Weibel, *The K-book*, Chapter II, §2. -/
noncomputable def finrankRingEquiv : K0 K ≃+* ℤ :=
  AddEquiv.toRingEquiv (finrankEquiv K) (by
    exact map_mul_of_symm_intCast (finrankEquiv K) fun z ↦
      (finrankEquiv_symm_apply K z).trans (intCast_eq_zsmul K z).symm)

/-- Forgetting multiplication retains the whole division-ring additive
equivalence, with the field's original division-ring dictionary. -/
theorem finrankRingEquiv_toAddEquiv :
    (finrankRingEquiv K).toAddEquiv = @finrankEquiv K hK.toDivisionRing := rfl

/-- The whole additive map is the canonical integer dimension homomorphism. -/
theorem finrankRingEquiv_toAddMonoidHom :
    (finrankRingEquiv K).toAddMonoidHom = finrankHom K :=
  finrankEquiv_toAddMonoidHom K

/-- The ring equivalence evaluates by the integer dimension homomorphism. -/
theorem finrankRingEquiv_apply (x : K0 K) :
    finrankRingEquiv K x = finrankHom K x :=
  finrankEquiv_apply K x

/-- Integer dimension of a finite right-module generator over a field is its
finrank, independently of its carrier universe. -/
@[simp]
theorem finrankRingEquiv_of_module (M : Type v) [AddCommGroup M]
    [Module Kᵐᵒᵖ M] [Module.Finite Kᵐᵒᵖ M] :
    finrankRingEquiv K (of K M) = (Module.finrank Kᵐᵒᵖ M : ℤ) :=
  finrankEquiv_of_module K M

/-- The inverse sends every integer to that multiple of the regular generator. -/
theorem finrankRingEquiv_symm_apply (z : ℤ) :
    (finrankRingEquiv K).symm z = z • of K Kᵐᵒᵖ :=
  finrankEquiv_symm_apply K z

/-- The inverse dimension equivalence is the canonical integer cast. -/
theorem finrankRingEquiv_symm_intCast (z : ℤ) :
    (finrankRingEquiv K).symm z = (z : K0 K) :=
  (finrankRingEquiv_symm_apply K z).trans (intCast_eq_zsmul K z).symm

/-- The dimension ring equivalence sends an integer cast to that integer. -/
theorem finrankRingEquiv_intCast (z : ℤ) :
    finrankRingEquiv K (z : K0 K) = z :=
  map_intCast (finrankRingEquiv K) z

/-- On projective-class generators the ring equivalence is the natural-valued
class dimension equivalence followed by the integer cast. -/
theorem finrankRingEquiv_ofClass (a : ProjectiveClass K) :
    finrankRingEquiv K (ofClass K a) = (ProjectiveClass.finrankEquiv K a : ℤ) :=
  finrankEquiv_ofClass K a

/-- Restriction along group completion recovers class dimension followed by
the canonical integer homomorphism. -/
theorem finrankRingEquiv_comp_ofClass :
    (finrankRingEquiv K).toAddMonoidHom.comp (ofClass K) =
      (Int.ofNatHom : ℕ →+ ℤ).comp (ProjectiveClass.finrankHom K) := by
  rw [finrankRingEquiv_toAddMonoidHom, finrankHom_comp_ofClass]

end FieldRingEquivalence

section LocalRingEquivalence

variable (R : Type u) [hR : CommRing R] [hlocal : IsLocalRing R]

/-- Canonical Jacobson-residue dimension identifies the tensor-product ring
K₀ of a commutative local ring with `ℤ`. Its entire additive equivalence is
`localEquivInt`, whose inverse is integer multiplication of the regular generator.
See Weibel, *The K-book*, Chapter II, §2. -/
noncomputable def localRingEquivInt : K0 R ≃+* ℤ :=
  AddEquiv.toRingEquiv (localEquivInt R) (by
    exact map_mul_of_symm_intCast (localEquivInt R) fun z ↦
      (localEquivInt_symm_apply R z).trans (intCast_eq_zsmul R z).symm)

/-- Forgetting multiplication retains the whole additive equivalence with the
original underlying ring dictionary, including its noncommutative-ring API. -/
theorem localRingEquivInt_toAddEquiv :
    (localRingEquivInt R).toAddEquiv = @localEquivInt R hR.toRing hlocal := rfl

/-- The whole additive map is canonical Jacobson-residue dimension. -/
theorem localRingEquivInt_toAddMonoidHom :
    (localRingEquivInt R).toAddMonoidHom = localDimensionHom R :=
  localEquivInt_toAddMonoidHom R

/-- The ring equivalence evaluates by canonical Jacobson-residue dimension. -/
theorem localRingEquivInt_apply (x : K0 R) :
    localRingEquivInt R x = localDimensionHom R x :=
  localEquivInt_apply R x

/-- On finite projective right modules, the local ring equivalence gives the
dimension of the residue module, not source-ring finrank. -/
@[simp]
theorem localRingEquivInt_of_module (M : Type v) [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    localRingEquivInt R (of R M) =
      (Module.finrank (R ⧸ Ring.jacobson R)ᵐᵒᵖ
        (ModuleCat.RightExtension.Obj (Ideal.Quotient.mk (Ring.jacobson R)) M) : ℤ) :=
  localEquivInt_of_module R M

/-- The inverse sends every integer to that multiple of the regular generator. -/
theorem localRingEquivInt_symm_apply (z : ℤ) :
    (localRingEquivInt R).symm z = z • of R Rᵐᵒᵖ :=
  localEquivInt_symm_apply R z

/-- The inverse local ring equivalence is the canonical integer cast. -/
theorem localRingEquivInt_symm_intCast (z : ℤ) :
    (localRingEquivInt R).symm z = (z : K0 R) :=
  (localRingEquivInt_symm_apply R z).trans (intCast_eq_zsmul R z).symm

/-- The local ring equivalence sends an integer cast to that integer. -/
theorem localRingEquivInt_intCast (z : ℤ) :
    localRingEquivInt R (z : K0 R) = z :=
  map_intCast (localRingEquivInt R) z

end LocalRingEquivalence

section PrincipalIdealDomainRingEquivalence

variable (R : Type u) [hR : CommRing R] [hdomain : IsDomain R]
  [hpid : IsPrincipalIdealRing R]

/-- Fraction-field dimension identifies the tensor-product ring K₀ of a
commutative principal ideal domain with `ℤ`. Its entire additive equivalence is
`pidEquivInt`, whose inverse is integer multiplication of the regular generator.
See Weibel, *The K-book*, Chapter II, §2. -/
noncomputable def pidRingEquivInt : K0 R ≃+* ℤ :=
  AddEquiv.toRingEquiv (pidEquivInt R) (by
    exact map_mul_of_symm_intCast (pidEquivInt R) fun z ↦
      (pidEquivInt_symm_apply R z).trans (intCast_eq_zsmul R z).symm)

/-- Forgetting multiplication retains the entire original PID additive equivalence. -/
theorem pidRingEquivInt_toAddEquiv :
    (pidRingEquivInt R).toAddEquiv = @pidEquivInt R hR hdomain hpid := rfl

/-- The whole additive map is fraction-field extension followed by integer dimension. -/
theorem pidRingEquivInt_toAddMonoidHom :
    (pidRingEquivInt R).toAddMonoidHom =
      (finrankHom (FractionRing R)).comp (map (algebraMap R (FractionRing R))) :=
  pidEquivInt_toAddMonoidHom R

/-- The PID ring equivalence evaluates by dimension after fraction-field extension. -/
theorem pidRingEquivInt_apply (x : K0 R) :
    pidRingEquivInt R x =
      finrankHom (FractionRing R) (map (algebraMap R (FractionRing R)) x) :=
  pidEquivInt_apply R x

/-- On finite projective right modules, the PID ring equivalence gives the
dimension of the fraction-field extension, independently of the carrier universe. -/
@[simp]
theorem pidRingEquivInt_of_module (M : Type v) [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    pidRingEquivInt R (of R M) =
      (Module.finrank (FractionRing R)ᵐᵒᵖ
        (ModuleCat.RightExtension.Obj (algebraMap R (FractionRing R)) M) : ℤ) :=
  pidEquivInt_of_module R M

/-- On finite projective right modules over a PID, fraction-field dimension
agrees with source-ring finrank. -/
theorem pidRingEquivInt_of_module_finrank (M : Type v) [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    pidRingEquivInt R (of R M) = (Module.finrank Rᵐᵒᵖ M : ℤ) :=
  pidEquivInt_of_module_finrank R M

/-- The inverse sends every integer to that multiple of the regular generator. -/
theorem pidRingEquivInt_symm_apply (z : ℤ) :
    (pidRingEquivInt R).symm z = z • of R Rᵐᵒᵖ :=
  pidEquivInt_symm_apply R z

/-- The inverse PID ring equivalence is the canonical integer cast. -/
theorem pidRingEquivInt_symm_intCast (z : ℤ) :
    (pidRingEquivInt R).symm z = (z : K0 R) :=
  (pidRingEquivInt_symm_apply R z).trans (intCast_eq_zsmul R z).symm

/-- The PID ring equivalence sends an integer cast to that integer. -/
theorem pidRingEquivInt_intCast (z : ℤ) :
    pidRingEquivInt R (z : K0 R) = z :=
  map_intCast (pidRingEquivInt R) z

end PrincipalIdealDomainRingEquivalence

end KTheory.K0
