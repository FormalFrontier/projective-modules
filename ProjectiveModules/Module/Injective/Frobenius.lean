/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import ProjectiveModules.Module.Injective

/-!
# Self-injectivity from a Frobenius functional

A finite-dimensional algebra over a field is left self-injective if it admits a
linear functional whose multiplication pairing is nondegenerate. The algebra
need not be commutative, and the functional need not take the value one at one.

The proof uses the transposed pairing `χ(a)(x) = λ(x * a)`. For an injection
`i : X →ₗ[A] Y` and a map `f : X →ₗ[A] A`, extend `λ ∘ f` to a scalar functional
`ℓ` on `Y`. The extension to `A` is characterized by
`λ(x * g(y)) = ℓ(x • y)`. Associativity gives left `A`-linearity without placing
an `A`-module structure on the dual.

The conclusion is Mathlib's `Module.Injective A A`. Its
`Module.Injective.extension_property` applies to arbitrary original left modules,
including modules in independent universes: its size premise here is the canonical
`Small.{uA} A`. No finiteness assumption on those modules is needed.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, Graduate Texts in Mathematics 189,
  Springer, 1999, for background on Frobenius and quasi-Frobenius rings and
  self-injectivity.

The mathematical antecedent is the classical Frobenius-algebra self-injectivity
implication. The proof here is independently derived from finite-dimensional
duality and extension of scalar functionals. The formalization reuses Mathlib's
`LinearMap.BilinForm.toDual` for the transposed form and
`LinearMap.exists_leftInverse_of_injective` for scalar-functional extension.
-/

@[expose] public section

universe uK uA

namespace Module

/-- A finite-dimensional algebra with a nondegenerate multiplication functional is
injective as its regular left module. This is the classical Frobenius-to-self-injectivity
implication; see T. Y. Lam, *Lectures on Modules and Rings* (1999) for background.
The proof here is independently derived using the transposed form and extension of
scalar functionals; no symmetry of the form or commutativity of the algebra is required. -/
theorem injective_of_nondegenerate_mul
    {K : Type uK} {A : Type uA} [Field K] [Ring A] [Algebra K A]
    [Module.Finite K A] (l : A →ₗ[K] K)
    (hl : ((LinearMap.mul K A).compr₂ l).Nondegenerate) : Module.Injective A A := by
  classical
  let B : LinearMap.BilinForm K A := (LinearMap.mul K A).compr₂ l
  have hB : B.Nondegenerate := hl
  let χ : A ≃ₗ[K] Module.Dual K A := B.flip.toDual hB.flip
  have hχ (a x : A) : χ a x = l (x * a) := by
    simp only [χ, LinearMap.BilinForm.toDual_def]
    rfl
  have hχsymm (φ : Module.Dual K A) (x : A) : l (x * χ.symm φ) = φ x := by
    rw [← hχ (χ.symm φ) x]
    exact congrArg (fun ψ : Module.Dual K A => ψ x) (χ.apply_symm_apply φ)
  refine ⟨?_⟩
  intro X Y _ _ _ _ i hi f
  -- Restrict only the test modules: the original scalar structure on A is unchanged.
  let : Module K X := Module.restrictScalars K A X
  let : Module K Y := Module.restrictScalars K A Y
  let : IsScalarTower K A X := IsScalarTower.restrictScalars K A X
  let : IsScalarTower K A Y := IsScalarTower.restrictScalars K A Y
  let iK : X →ₗ[K] Y := i.restrictScalars K
  let fK : X →ₗ[K] A := f.restrictScalars K
  obtain ⟨s, hs⟩ := LinearMap.exists_leftInverse_of_injective iK
    (LinearMap.ker_eq_bot.mpr (show Function.Injective iK from hi))
  let ℓ : Y →ₗ[K] K := (l.comp fK).comp s
  have hℓ (x : X) : ℓ (i x) = l (f x) := by
    have hsi : s (i x) = x := congrArg (fun e : X →ₗ[K] X => e x) hs
    change l (f (s (i x))) = l (f x)
    rw [hsi]
  let Ψ (y : Y) : Module.Dual K A :=
    { toFun := fun x => ℓ (x • y)
      map_add' := by
        intro x z
        rw [add_smul, map_add]
      map_smul' := by
        intro k x
        rw [smul_assoc, map_smul]
        rfl }
  let g₀ (y : Y) : A := χ.symm (Ψ y)
  have hg₀ (y : Y) (x : A) : l (x * g₀ y) = ℓ (x • y) := hχsymm (Ψ y) x
  let g : Y →ₗ[A] A :=
    { toFun := g₀
      map_add' := by
        intro y z
        apply χ.injective
        ext x
        change χ (g₀ (y + z)) x = χ (g₀ y + g₀ z) x
        rw [map_add χ]
        change χ (g₀ (y + z)) x = χ (g₀ y) x + χ (g₀ z) x
        simp only [hχ, hg₀, smul_add, map_add]
      map_smul' := by
        intro a y
        apply χ.injective
        ext x
        change χ (g₀ (a • y)) x = χ (a * g₀ y) x
        calc
          χ (g₀ (a • y)) x = ℓ (x • (a • y)) := (hχ _ _).trans (hg₀ _ _)
          _ = ℓ ((x * a) • y) := by rw [mul_smul]
          _ = l ((x * a) * g₀ y) := (hg₀ _ _).symm
          _ = χ (a * g₀ y) x := by rw [hχ, mul_assoc] }
  refine ⟨g, ?_⟩
  intro x
  change g₀ (i x) = f x
  apply χ.injective
  ext a
  calc
    χ (g₀ (i x)) a = ℓ (a • i x) := (hχ _ _).trans (hg₀ _ _)
    _ = ℓ (i (a • x)) := congrArg ℓ (i.map_smul a x).symm
    _ = l (f (a • x)) := hℓ (a • x)
    _ = χ (f x) a := by rw [hχ, f.map_smul a x, smul_eq_mul]

end Module
