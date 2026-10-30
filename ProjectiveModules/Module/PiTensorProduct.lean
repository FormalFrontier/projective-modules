/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

The tensor-product APIs used here are from Mathlib:
PiTensorProduct/Generators.lean:
Copyright (c) 2026 Joël Riou. All rights reserved.
PiTensorProduct/Basis.lean:
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Authors: Daniel Morrison, Sophie Morel
RingTheory/TensorProduct/Finite.lean:
Copyright (c) 2020 Kim Morrison. All rights reserved.
Authors: Kim Morrison, Johan Commelin
These files are released under Apache 2.0 as described in their LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite generation of multiple tensor products

A finite tensor product of finitely generated semimodules over a commutative
semiring is finitely generated. The proof separates off one factor at a time
and does not use quotient modules or additive inverses.

The ring-specialized `PiTensorProduct.finite` API remains available through
the public import; `Module.Finite.piTensorProduct` applies to semirings.
-/

@[expose] public section

open TensorProduct

universe u v w

namespace Module.Finite

variable {R : Type u} [CommSemiring R]

/-- A finite family of finite semimodules has a finite multiple tensor product. -/
theorem piTensorProduct {ι : Type v} [_root_.Finite ι] {M : ι → Type w}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Finite R (M i)] : Module.Finite R (⨂[R] i, M i) := by
  classical
  obtain ⟨n, hι⟩ : ∃ n : ℕ, Nat.card ι = n := ⟨_, rfl⟩
  induction n generalizing ι with
  | zero =>
    have : IsEmpty ι := (Nat.card_eq_zero.1 hι).resolve_right <| _root_.Finite.not_infinite ‹_›
    exact Module.Finite.of_basis (_root_.Basis.piTensorProduct
      (fun i : ι => (isEmptyElim i : Module.Basis Unit R (M i))))
  | succ n hn =>
    have : Nonempty ι := ((Nat.card_pos_iff (α := ι)).1 (by omega)).1
    let i₀ : ι := Classical.arbitrary ι
    have : Module.Finite R (⨂[R] (i : ({i₀}ᶜ : Set ι)), M i) := by
      apply hn
      exact Set.ncard_compl_of_ncard_eq_add _ (by simpa)
    exact Module.Finite.of_surjective
      (PiTensorProduct.equivPiTensorComplSingletonTensor R M i₀).symm.toLinearMap
      (PiTensorProduct.equivPiTensorComplSingletonTensor R M i₀).symm.surjective

end Module.Finite
