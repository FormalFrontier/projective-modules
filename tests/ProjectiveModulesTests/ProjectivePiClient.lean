/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.ProjectivePi
import Mathlib.Data.Matrix.Mul

/-!
# Finite dependent products as projective sources

The lifting property uses the inferred projectivity of a finite dependent product,
with independent scalar, index and carrier universes and no finite-generation
assumption. Concrete instance checks use the noncommutative semiring of two-by-two
natural-number matrices and infinite free factors, for both a three-element index
and the empty index. All operations and module structures are Mathlib's canonical
ones; the examples introduce no new actions.

The lifting, free-module projectivity and dependent finitely supported interfaces
are from Mathlib's module formalization; the matrix semiring is from Mathlib's
matrix multiplication interface.
-/

universe uR uι uM uA uB

section Lifting

variable {R : Type uR} [Semiring R] {ι : Type uι} [Finite ι]
variable {M : ι → Type uM} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable [∀ i, Module.Projective R (M i)]
variable {A : Type uA} [AddCommMonoid A] [Module R A]
variable {B : Type uB} [AddCommMonoid B] [Module R B]

example (f : A →ₗ[R] B) (g : (∀ i, M i) →ₗ[R] B) (hf : Function.Surjective f) :
    ∃ h : (∀ i, M i) →ₗ[R] A, f.comp h = g :=
  Module.projective_lifting_property f g hf

end Lifting

example : Module.Projective (Matrix (Fin 2) (Fin 2) ℕ)
    (Fin 3 → (ℕ →₀ Matrix (Fin 2) (Fin 2) ℕ)) := inferInstance

example : Module.Projective (Matrix (Fin 2) (Fin 2) ℕ)
    (Fin 0 → (ℕ →₀ Matrix (Fin 2) (Fin 2) ℕ)) := inferInstance
