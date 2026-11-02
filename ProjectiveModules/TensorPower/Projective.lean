/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective
public import ProjectiveModules.TensorPower.BaseChange

/-!
# Projective tensor powers

Every tensor power of a projective module over a commutative semiring is projective.
The empty tensor product is the regular scalar module. Successor tensor powers
are obtained by tensoring with one more copy of the module.
-/

@[expose] public section

open scoped TensorProduct

universe uR uM

namespace TensorPower

/-- A tensor power of a projective module is projective. -/
instance projective (S : Type uR) [CommSemiring S]
    (M : Type uM) [AddCommMonoid M] [Module S M]
    [Module.Projective S M] (n : ℕ) :
    Module.Projective S (TensorPower S n M) := by
  induction n with
  | zero =>
      have : Module.Projective S S := inferInstance
      exact Module.Projective.of_equiv
        (PiTensorProduct.isEmptyEquiv (R := S)
          (s := fun _ : Fin 0 => M) (Fin 0)).symm
  | succ n ih =>
      have : Module.Projective S (TensorPower S n M) := ih
      exact Module.Projective.of_equiv (TensorPower.appendEquiv S M n)

end TensorPower
