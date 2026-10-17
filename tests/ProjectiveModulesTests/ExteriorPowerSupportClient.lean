/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.ExteriorPower.BaseChange
import ProjectiveModules.ExteriorPower.Invertible
import ProjectiveModules.ExteriorPower.StalkRank
import ProjectiveModules.ExteriorPower.DeterminantLine
import ProjectiveModules.Module.RankFiberDecomposition
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis

/-!
# Clients of homogeneous base change, invertibility and exterior vanishing

The positive example is the integer plane in degree two. Scalar extension to
`ZMod 2` uses the public image equality, not a fixed-degree carrier equivalence.
The top-exterior client supplies the exact constant-stalk-rank equation using
the standard basis and Mathlib's free-module rank computation. The degree-zero
control over `ZMod 1` also checks that no nontrivial-ring assumption is required.
The integer plane vanishes in degree three, and the rational zero module in
degree zero shows that the stalk-rank bound must be strict.
The determinant-line clients use isomorphism transport and a rank-fiber component
of the same plane, the zero module over the zero ring, and the regular module.
-/

open scoped TensorProduct

namespace ProjectiveModulesTests.ExteriorPowerSupportClient

private instance planeFree : Module.Free ℤ (Fin 2 → ℤ) :=
  Module.Free.of_basis (Pi.basisFun ℤ (Fin 2))

private instance planeFinite : Module.Finite ℤ (Fin 2 → ℤ) :=
  Module.Finite.of_basis (Pi.basisFun ℤ (Fin 2))

private instance planeProjective : Module.Projective ℤ (Fin 2 → ℤ) :=
  Module.Projective.of_basis (Pi.basisFun ℤ (Fin 2))

private theorem integerPlane_baseChange :
    (⋀[ZMod 2]^2 (ZMod 2 ⊗[ℤ] (Fin 2 → ℤ))).map
        (ExteriorAlgebra.equivBaseChange
          (R := ℤ) (S := ZMod 2) (M := Fin 2 → ℤ)).toLinearEquiv.toLinearMap =
      (⋀[ℤ]^2 (Fin 2 → ℤ)).baseChange (ZMod 2) :=
  ExteriorAlgebra.equivBaseChange_map_exteriorPower
    (R := ℤ) (S := ZMod 2) (M := Fin 2 → ℤ) 2

private theorem integerPlane_topExterior_invertible : Module.Invertible ℤ (⋀[ℤ]^2 (Fin 2 → ℤ)) := by
  apply exteriorPower.invertible_of_rankAtStalk_eq (R := ℤ) (M := Fin 2 → ℤ) 2
  funext p
  simpa [Module.finrank_fin_fun] using
    congrFun (Module.rankAtStalk_eq_finrank_of_free (R := ℤ) (M := Fin 2 → ℤ)) p

private theorem zeroRing_degreeZero_invertible : Module.Invertible (ZMod 1) (⋀[ZMod 1]^0 (ZMod 1)) :=
  exteriorPower.invertible_of_rankAtStalk_eq (R := ZMod 1) (M := ZMod 1) 0
    (Module.rankAtStalk_eq_zero_of_subsingleton (R := ZMod 1) (M := ZMod 1))

private theorem integerPlane_degreeThree_subsingleton : Subsingleton (⋀[ℤ]^3 (Fin 2 → ℤ)) := by
  apply exteriorPower.subsingleton_of_rankAtStalk_lt (R := ℤ) (M := Fin 2 → ℤ) 3
  intro p
  have hr : Module.rankAtStalk (R := ℤ) (Fin 2 → ℤ) p = 2 := by
    simpa [Module.finrank_fin_fun] using
      congrFun (Module.rankAtStalk_eq_finrank_of_free (R := ℤ) (M := Fin 2 → ℤ)) p
  rw [hr]
  exact Nat.lt_succ_self 2

private theorem zeroRing_degreeZero_subsingleton : Subsingleton (⋀[ZMod 1]^0 (ZMod 1)) :=
  exteriorPower.subsingleton_of_rankAtStalk_lt (R := ZMod 1) (M := ZMod 1) 0
    (fun p ↦ isEmptyElim p)

private theorem rationalZeroModule_degreeZero_strictness : (∀ p : PrimeSpectrum ℚ,
    Module.rankAtStalk (R := ℚ) (Fin 0 → ℚ) p ≤ 0) ∧
    ¬ Subsingleton (⋀[ℚ]^0 (Fin 0 → ℚ)) := by
  constructor
  · intro p
    have hr : Module.rankAtStalk (R := ℚ) (Fin 0 → ℚ) p = 0 := by
      simpa [Module.finrank_fin_fun] using
        congrFun (Module.rankAtStalk_eq_finrank_of_free (R := ℚ) (M := Fin 0 → ℚ)) p
    exact hr.le
  · intro hs
    let e := exteriorPower.zeroEquiv ℚ (Fin 0 → ℚ)
    have h := congrArg e (@Subsingleton.elim _ hs (e.symm 0) (e.symm 1))
    exact (zero_ne_one : (0 : ℚ) ≠ 1) (by simpa using h)

private theorem integerPlane_determinantLine_invertible
    : Module.Invertible ℤ (Module.DeterminantLine ℤ (Fin 2 → ℤ)) := by
  have hAction : Module.DeterminantLine.instModule ℤ (Fin 2 → ℤ) =
      AddCommGroup.toIntModule (Module.DeterminantLine ℤ (Fin 2 → ℤ)) :=
    Subsingleton.elim _ _
  exact hAction ▸ Module.determinantLine_invertible ℤ (Fin 2 → ℤ)

private theorem zeroRing_determinantLine_invertible
    : Module.Invertible (ZMod 1) (Module.DeterminantLine (ZMod 1) (ZMod 1)) :=
  Module.determinantLine_invertible (ZMod 1) (ZMod 1)

private theorem integerPlane_determinantLine_congr
    : Nonempty (Module.DeterminantLine ℤ (Fin 2 → ℤ) ≃ₗ[ℤ]
    Module.DeterminantLine ℤ (Fin 2 → ℤ)) := by
  have hAction : Module.DeterminantLine.instModule ℤ (Fin 2 → ℤ) =
      AddCommGroup.toIntModule (Module.DeterminantLine ℤ (Fin 2 → ℤ)) :=
    Subsingleton.elim _ _
  exact hAction ▸
    Module.determinantLine_congr ℤ (Fin 2 → ℤ) (Fin 2 → ℤ) (LinearEquiv.refl ℤ _)

private theorem integerPlane_determinantLine_component (i : Module.rankFiberIndex ℤ (Fin 2 → ℤ)) :
    Nonempty ((Module.rankFiberRing ℤ (Fin 2 → ℤ) i) ⊗[ℤ]
      Module.DeterminantLine ℤ (Fin 2 → ℤ) ≃ₗ[Module.rankFiberRing ℤ (Fin 2 → ℤ) i]
        Module.DeterminantLineComponent ℤ (Fin 2 → ℤ) i) := by
  have hAction : Module.DeterminantLine.instModule ℤ (Fin 2 → ℤ) =
      AddCommGroup.toIntModule (Module.DeterminantLine ℤ (Fin 2 → ℤ)) :=
    Subsingleton.elim _ _
  have hQuotientAction :
      Submodule.Quotient.module
          (Ideal.span {1 - Module.rankFiberIdempotent ℤ (Fin 2 → ℤ) i}) =
        AddCommGroup.toIntModule (Module.rankFiberRing ℤ (Fin 2 → ℤ) i) :=
    Subsingleton.elim _ _
  let Q := Module.rankFiberRing ℤ (Fin 2 → ℤ) i
  let D := Module.DeterminantLine ℤ (Fin 2 → ℤ)
  let C := Module.DeterminantLineComponent ℤ (Fin 2 → ℤ) i
  let commute (q : Module ℤ Q) : Prop :=
    @SMulCommClass ℤ Q Q q.toDistribMulAction.toDistribSMul.toSMul instSMulOfMul
  -- Both integer actions and their dependent compatibility proofs vary together.
  let joint (q : Module ℤ Q) (d : Module ℤ D) (hc : commute q) : Prop :=
    Nonempty (@LinearEquiv Q Q _ _ (RingHom.id Q) (RingHom.id Q) _ _
      (@TensorProduct ℤ _ Q D _ _ q d) C
      (@TensorProduct.addCommMonoid ℤ _ Q D _ _ q d) _
      (@TensorProduct.leftModule ℤ Q _ _ Q D _ _ Semiring.toModule q d hc) _)
  have transport :
      ∀ (q₀ q₁ : Module ℤ Q) (d₀ d₁ : Module ℤ D)
        (hc₀ : commute q₀) (hc₁ : commute q₁),
        q₀ = q₁ → d₀ = d₁ → joint q₀ d₀ hc₀ → joint q₁ d₁ hc₁ := by
    intro q₀ q₁ d₀ d₁ hc₀ hc₁ hq hd witness
    cases hq
    cases hd
    exact witness
  let targetCommute : commute (AddCommGroup.toIntModule Q) :=
    Eq.mp (congrArg commute hQuotientAction)
      (Algebra.to_smulCommClass : commute
        (Submodule.Quotient.module
          (Ideal.span {1 - Module.rankFiberIdempotent ℤ (Fin 2 → ℤ) i})))
  exact transport
    (Submodule.Quotient.module
      (Ideal.span {1 - Module.rankFiberIdempotent ℤ (Fin 2 → ℤ) i}))
    (AddCommGroup.toIntModule Q) (Module.DeterminantLine.instModule ℤ (Fin 2 → ℤ))
    (AddCommGroup.toIntModule D) Algebra.to_smulCommClass
    targetCommute hQuotientAction hAction
    (Module.determinantLine_component ℤ (Fin 2 → ℤ) i)

private theorem zeroRing_determinantLine_zero
    : Nonempty (Module.DeterminantLine (ZMod 1) (Fin 0 → ZMod 1) ≃ₗ[ZMod 1]
    ZMod 1) :=
  Module.determinantLine_zero (ZMod 1)

private theorem integer_determinantLine_invertibleModule
    : Nonempty (Module.DeterminantLine ℤ ℤ ≃ₗ[ℤ] ℤ) := by
  have hAction : Module.DeterminantLine.instModule ℤ ℤ =
      AddCommGroup.toIntModule (Module.DeterminantLine ℤ ℤ) :=
    Subsingleton.elim _ _
  exact hAction ▸ Module.determinantLine_invertibleModule ℤ ℤ

/-- Every rank-fiber component of the integer plane is flat over the integers.
The plane instances above are supplied by its standard basis. -/
private theorem integerPlane_rankFiberRing_flat
    (i : Module.rankFiberIndex ℤ (Fin 2 → ℤ)) :
    Module.Flat ℤ (Module.rankFiberRing ℤ (Fin 2 → ℤ) i) :=
  Module.rankFiberRing_flat ℤ (Fin 2 → ℤ) i

end ProjectiveModulesTests.ExteriorPowerSupportClient
