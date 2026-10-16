/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.Projective
public import ProjectiveModules.Invertible.OfRankOne
import Mathlib.RingTheory.Flat.Localization
import ProjectiveModules.ExteriorPower.BaseChange

/-!
# Invertibility of top exterior powers

The `n`th exterior power of a finite projective module of constant stalk rank
`n` is invertible. The rank hypothesis is expressed over the module's scalar
ring and requires neither a chosen basis nor a nontrivial ring.
-/

@[expose] public section

universe uR uM

open scoped TensorProduct

namespace exteriorPower

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- The top exterior power of a finite projective module of constant stalk
rank `n` is invertible, including degree zero and the zero ring. -/
theorem invertible_of_rankAtStalk_eq
    [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) (h : Module.rankAtStalk (R := R) M = fun _ ↦ n) :
    Module.Invertible R (⋀[R]^n M) := by
  classical
  apply Module.invertible_of_rankAtStalk_eq_one
  funext p
  let A := Localization.AtPrime p.asIdeal
  -- Flatness here is supplied by localization, not imposed on the theorem.
  letI : Module.Flat R A := IsLocalization.flat A p.asIdeal.primeCompl
  letI : Module.Free A (A ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  let e := (ExteriorAlgebra.equivBaseChange (R := R) (S := A) (M := M)).toLinearEquiv
  -- First identify the image submodule; this alone is not a carrier equivalence.
  let ep : (⋀[A]^n (A ⊗[R] M)) ≃ₗ[A] (⋀[R]^n M).baseChange A :=
    (Submodule.equivMapOfInjective e.toLinearMap e.injective _).trans
      (LinearEquiv.ofEq _ _
        (ExteriorAlgebra.equivBaseChange_map_exteriorPower (R := R) (S := A) (M := M) n))
  -- The actual tensor-to-range equivalence uses the proved flatness of A over R.
  let eE : (A ⊗[R] (⋀[R]^n M)) ≃ₗ[A] (⋀[A]^n (A ⊗[R] M)) :=
    (Submodule.toBaseChange.toLinearEquiv A (⋀[R]^n M)).trans ep.symm
  have hM : Module.finrank A (A ⊗[R] M) = n := by
    rw [← (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M).finrank_eq]
    exact congrFun h p
  change Module.finrank A (LocalizedModule p.asIdeal.primeCompl (⋀[R]^n M)) = 1
  calc
    Module.finrank A (LocalizedModule p.asIdeal.primeCompl (⋀[R]^n M)) =
        Module.finrank A (A ⊗[R] (⋀[R]^n M)) :=
      (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl (⋀[R]^n M)).finrank_eq
    _ = Module.finrank A (⋀[A]^n (A ⊗[R] M)) := eE.finrank_eq
    _ = (Module.finrank A (A ⊗[R] M)).choose n :=
      exteriorPower.finrank_eq A (A ⊗[R] M) n
    _ = 1 := by rw [hM, Nat.choose_self]

end exteriorPower
