/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
public import ProjectiveModules.KTheory.ScalarExtension
public import ProjectiveModules.Module.RightExtensionFree
public import Mathlib.Algebra.Field.Opposite
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free

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
@[simp]
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
@[simp]
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

end KTheory
