/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.ScalarExtension
public import ProjectiveModules.Module.DirectLimit

import ProjectiveModules.Module.RightExtensionMatrixRange

/-!
# Finite-projective classes over directed ring limits

Canonical scalar extension to a nonempty directed limit of unital rings detects
equality of finite-projective right-module classes at a common upper stage.
Every class over the limit comes from some stage. The maps are the additive
homomorphisms `KTheory.ProjectiveClass.map` along `DirectLimit.Ring.of`.

The rings need not be commutative, and transition maps need not be injective.
The index and coefficient universes are independent. The stage witnessing
equality may depend on the two classes; descent is not asserted from a prescribed
stage. These statements concern isomorphism classes before group completion,
not K₀.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  the finite-idempotent description of projective modules and directed-limit argument.
* Projective Modules' right scalar extension, finite-projective class maps,
  idempotent-range classification and common-stage range-equivalence criterion.
-/

@[expose] public section

universe uι uR

namespace KTheory.ProjectiveClass

/-- Equality of two stage classes after canonical scalar extension to the
limit is detected at a common upper stage. -/
theorem map_eq_iff_exists_common_stage
    {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (R : ι → Type uR) [∀ i, Ring (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]
    (i j : ι) (x : KTheory.ProjectiveClass (R i))
    (y : KTheory.ProjectiveClass (R j)) :
    KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i) x =
        KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f j) y ↔
      ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
        KTheory.ProjectiveClass.map (f i k hik) x =
          KTheory.ProjectiveClass.map (f j k hjk) y := by
  classical
  constructor
  · intro h
    obtain ⟨X, rfl⟩ := of_surjective (R i) x
    obtain ⟨Y, rfl⟩ := of_surjective (R j) y
    rw [map_of, map_of] at h
    obtain ⟨e⟩ := (of_eq_iff _ _ _).mp h
    obtain ⟨n, A, hA, ⟨eA⟩⟩ :=
      Module.Projective.exists_equiv_range_idempotent_matrix (R := R i) (P := X)
    obtain ⟨m, B, hB, ⟨eB⟩⟩ :=
      Module.Projective.exists_equiv_range_idempotent_matrix (R := R j) (P := Y)
    obtain ⟨k, hik, hjk, ⟨eK⟩⟩ :=
      (DirectLimit.nonempty_rightExtension_rangeEquiv_iff_exists_common_stage
        R f i j A B hA hB).mp
          ⟨(ModuleCat.RightExtension.mapLinearEquiv (DirectLimit.Ring.of R f i) eA).symm.trans
            (e.trans
              (ModuleCat.RightExtension.mapLinearEquiv (DirectLimit.Ring.of R f j) eB))⟩
    refine ⟨k, hik, hjk, ?_⟩
    rw [map_of, map_of]
    -- The common-stage criterion returns mapped ranges, not scalar extensions.
    let eAk := (ModuleCat.RightExtension.mapLinearEquiv (f i k hik) eA).trans
      (ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv (f i k hik) A hA)
    let eBk := (ModuleCat.RightExtension.mapLinearEquiv (f j k hjk) eB).trans
      (ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv (f j k hjk) B hB)
    exact of_eq_of_equiv (R k) _ (eAk.trans (eK.trans eBk.symm))
  · rintro ⟨k, hik, hjk, h⟩
    have hi : (DirectLimit.Ring.of R f k).comp (f i k hik) =
        DirectLimit.Ring.of R f i := by
      ext a
      exact DirectLimit.Ring.of_f (G := R) (f := f) hik a
    have hj : (DirectLimit.Ring.of R f k).comp (f j k hjk) =
        DirectLimit.Ring.of R f j := by
      ext a
      exact DirectLimit.Ring.of_f (G := R) (f := f) hjk a
    calc
      map (DirectLimit.Ring.of R f i) x =
          map (DirectLimit.Ring.of R f k) (map (f i k hik) x) := by
        rw [← hi, map_comp, AddMonoidHom.comp_apply]
      _ = map (DirectLimit.Ring.of R f k) (map (f j k hjk) y) :=
        congrArg (map (DirectLimit.Ring.of R f k)) h
      _ = map (DirectLimit.Ring.of R f j) y := by
        rw [← hj, map_comp, AddMonoidHom.comp_apply]

/-- Every finite-projective right-module class over a nonempty directed
ring limit comes by canonical scalar extension from some stage. -/
theorem exists_map_eq
    {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (R : ι → Type uR) [∀ i, Ring (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]
    (y : KTheory.ProjectiveClass (DirectLimit R f)) :
    ∃ (i : ι) (x : KTheory.ProjectiveClass (R i)),
      KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i) x = y := by
  classical
  obtain ⟨M, rfl⟩ := of_surjective (DirectLimit R f) y
  obtain ⟨i, n, A, hA, ⟨e⟩⟩ :=
    DirectLimit.exists_rightExtension_range_idempotent_matrix_equiv R f M
  let Q := LinearMap.range (Matrix.mulVecBilin (R i) (R i)ᵐᵒᵖ A)
  have hQ : Module.Finite (R i)ᵐᵒᵖ Q ∧ Module.Projective (R i)ᵐᵒᵖ Q :=
    (Module.finite_projective_iff_exists_equiv_range_idempotent_matrix
      (R := R i) (P := Q)).2 ⟨n, A, hA.eq, ⟨LinearEquiv.refl (R i)ᵐᵒᵖ Q⟩⟩
  let : Module.Finite (R i)ᵐᵒᵖ Q := hQ.1
  let : Module.Projective (R i)ᵐᵒᵖ Q := hQ.2
  refine ⟨i, of (R i) Q, ?_⟩
  rw [map_of]
  exact of_eq_of_equiv (DirectLimit R f) _ e

end KTheory.ProjectiveClass
