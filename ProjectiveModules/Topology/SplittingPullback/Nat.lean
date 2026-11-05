/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Topology.SplittingPullback
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Topology.Order

/-!
# A non-group pullback over the natural numbers

For the first projection `ℤ × ℤ → ℤ` and the inclusion `ℕ → ℤ`, the equalizer
submodule in `(ℤ × ℤ) × ℕ` contains `((1, 0), 1)`, which has no additive inverse.
The pullback splitting applies to this same submodule, with its induced topology,
even though its addition is not a group operation. The natural numbers and integers
carry their discrete topologies and their canonical `ℕ`-module structures.

## References

* Mathlib's `Nat.castAddMonoidHom`, `AddMonoidHom.toNatLinearMap`, and discrete
  topology instances supply the inclusion with its canonical scalar action.
* The canonical splitting `ContinuousLinearMap.equivProdKerOfRightInverse` and its
  pullback construction `ContinuousLinearMap.pullbackEquivProdKerOfRightInverse`.
-/

@[expose] public section

namespace ContinuousLinearMap

/-- The pullback of the first projection along the natural-number inclusion has
an element with no additive inverse. Nevertheless, the pullback construction from
the canonical continuous splitting identifies it with the product of `ℕ` and the
original first-projection kernel. -/
theorem exists_not_add_eq_zero_pullback_fst_natCast :
    let f := fst ℕ ℤ ℤ
    let h : ℕ →L[ℕ] ℤ :=
      { toLinearMap := (Nat.castAddMonoidHom ℤ).toNatLinearMap
        cont := continuous_of_discreteTopology }
    (∃ p : LinearMap.eqLocus
        (f.toLinearMap.comp (LinearMap.fst ℕ (ℤ × ℤ) ℕ))
        (h.toLinearMap.comp (LinearMap.snd ℕ (ℤ × ℤ) ℕ)),
      ∀ q, p + q ≠ 0) ∧
      Nonempty
        ((LinearMap.eqLocus
          (f.toLinearMap.comp (LinearMap.fst ℕ (ℤ × ℤ) ℕ))
          (h.toLinearMap.comp (LinearMap.snd ℕ (ℤ × ℤ) ℕ))) ≃L[ℕ] (ℕ × f.ker)) := by
  dsimp only
  constructor
  · refine ⟨⟨(((1 : ℤ), 0), (1 : ℕ)), rfl⟩, ?_⟩
    intro q hpq
    have hnat : (1 : ℕ) + q.1.2 = 0 :=
      congrArg (fun p => Prod.snd (Subtype.val p)) hpq
    simp at hnat
  · exact ⟨(fst ℕ ℤ ℤ).pullbackEquivProdKerOfRightInverse
      (inl ℕ ℤ ℤ) (fun _ => rfl)
      { toLinearMap := (Nat.castAddMonoidHom ℤ).toNatLinearMap
        cont := continuous_of_discreteTopology }⟩

end ContinuousLinearMap
