/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.ZMod.Defs

/-!
# Locally constant rank on right-module classes

A rational coordinate module has rank two even when both its finite index and
its coefficient carrier are independently lifted. A finite projective right
module over `ℚ × ℚ`, produced by the existing clopen-rank realization, has ranks
one and zero at the two coordinate primes. Its class rank is therefore not a
constant function. The final example treats the empty spectrum of the zero ring.

The examples use Mathlib's equivalence, finite-product and characteristic-function
APIs and this library's `ModuleCat.FiniteProjective.ofLocallyConstantRank` and
`rankAtStalk_ofLocallyConstantRank` realization theorem.
-/

@[expose] public section

open scoped BigOperators

universe uM uι

namespace KTheory.ProjectiveClass

-- This is the canonical right module, with scalar ring ℚᵐᵒᵖ, not a new left ℚ-action.
private theorem rankLocallyConstant_rationalCoordinates :
    rankLocallyConstant ℚ
      (of ℚ (ULift.{uι} (Fin 2) → ULift.{uM} ℚᵐᵒᵖ)) = 2 := by
  classical
  have hline : Module.rankLocallyConstant ℚᵐᵒᵖ (ULift.{uM} ℚᵐᵒᵖ) = 1 := by
    calc
      Module.rankLocallyConstant ℚᵐᵒᵖ (ULift.{uM} ℚᵐᵒᵖ) =
          Module.rankLocallyConstant ℚᵐᵒᵖ ℚᵐᵒᵖ :=
        Module.rankLocallyConstant_eq_of_equiv ℚᵐᵒᵖ _ _
          (ULift.moduleEquiv (R := ℚᵐᵒᵖ) (M := ℚᵐᵒᵖ))
      _ = 1 := Module.rankLocallyConstant_self ℚᵐᵒᵖ
  have hcoordinates :
      Module.rankLocallyConstant ℚᵐᵒᵖ
        (ULift.{uι} (Fin 2) → ULift.{uM} ℚᵐᵒᵖ) = 2 := by
    rw [Module.rankLocallyConstant_pi ℚᵐᵒᵖ (ULift.{uι} (Fin 2))
      (fun _ ↦ ULift.{uM} ℚᵐᵒᵖ)]
    simp [hline, finsum_eq_sum_of_fintype]
  rw [rankLocallyConstant_of_module, hcoordinates]
  ext p
  rfl

-- The witness is an existing finite-projective realization over the opposite ring.
-- The two displayed primes are the pullbacks of (0) along the coordinate maps.
private theorem rankLocallyConstant_product_nonconstant :
    ∃ M : ModuleCat.FiniteProjective.{0, 0} (ℚ × ℚ)ᵐᵒᵖ,
      rankLocallyConstant (ℚ × ℚ) (of (ℚ × ℚ) M)
          (PrimeSpectrum.comap (RingHom.fst ℚ ℚ) ⟨⊥, inferInstance⟩) = 1 ∧
      rankLocallyConstant (ℚ × ℚ) (of (ℚ × ℚ) M)
          (PrimeSpectrum.comap (RingHom.snd ℚ ℚ) ⟨⊥, inferInstance⟩) = 0 ∧
      ¬ ∃ n : ℕ, rankLocallyConstant (ℚ × ℚ) (of (ℚ × ℚ) M) =
        LocallyConstant.const (PrimeSpectrum (ℚ × ℚ)) n := by
  classical
  let e : {e : (ℚ × ℚ)ᵐᵒᵖ // IsIdempotentElem e} :=
    ⟨MulOpposite.op ((1 : ℚ), (0 : ℚ)), by
      change MulOpposite.op (((1 : ℚ), (0 : ℚ)) * (1, 0)) =
        MulOpposite.op ((1 : ℚ), (0 : ℚ))
      simp⟩
  let U := PrimeSpectrum.isIdempotentElemEquivClopens e
  let f := LocallyConstant.charFn ℕ U.isClopen
  let M := ModuleCat.FiniteProjective.ofLocallyConstantRank (ℚ × ℚ)ᵐᵒᵖ f
  let q : PrimeSpectrum ℚ := ⟨⊥, inferInstance⟩
  let p₁ := PrimeSpectrum.comap (RingHom.fst ℚ ℚ) q
  let p₂ := PrimeSpectrum.comap (RingHom.snd ℚ ℚ) q
  have hU : (U : Set (PrimeSpectrum (ℚ × ℚ)ᵐᵒᵖ)) =
      PrimeSpectrum.basicOpen e.1 :=
    PrimeSpectrum.coe_isIdempotentElemEquivClopens_apply e
  have heval (p : PrimeSpectrum (ℚ × ℚ)) :
      rankLocallyConstant (ℚ × ℚ) (of (ℚ × ℚ) M) p =
        f (PrimeSpectrum.comap (RingEquiv.toOpposite (ℚ × ℚ)).symm.toRingHom p) := by
    rw [rankLocallyConstant_of_module_apply]
    exact congrFun
      (ModuleCat.FiniteProjective.rankAtStalk_ofLocallyConstantRank f) _
  have h₁ : rankLocallyConstant (ℚ × ℚ) (of (ℚ × ℚ) M) p₁ = 1 := by
    rw [heval]
    apply (LocallyConstant.charFn_eq_one ℕ _ U.isClopen).2
    rw [hU]
    change (1 : ℚ) ∉ (⊥ : Ideal ℚ)
    simp
  have h₂ : rankLocallyConstant (ℚ × ℚ) (of (ℚ × ℚ) M) p₂ = 0 := by
    rw [heval]
    apply (LocallyConstant.charFn_eq_zero ℕ _ U.isClopen).2
    rw [hU]
    change ¬ ((0 : ℚ) ∉ (⊥ : Ideal ℚ))
    simp
  refine ⟨M, h₁, h₂, ?_⟩
  rintro ⟨n, hn⟩
  have hn₁ : 1 = n := h₁.symm.trans (congrArg (fun g ↦ g p₁) hn)
  have hn₂ : 0 = n := h₂.symm.trans (congrArg (fun g ↦ g p₂) hn)
  exact Nat.zero_ne_one (hn₂.trans hn₁.symm)

-- Empty-domain uniqueness is supplied explicitly; neither helper is an instance.
-- Equality of the LC constants does not assert that the integers zero and one agree.
private theorem rankLocallyConstant_zeroRing :
    rankLocallyConstant (ZMod 1) (of (ZMod 1) (ZMod 1)ᵐᵒᵖ) = 0 ∧
      (0 : LocallyConstant (PrimeSpectrum (ZMod 1)) ℤ) = 1 := by
  letI : Subsingleton (LocallyConstant (PrimeSpectrum (ZMod 1)) ℕ) :=
    DFunLike.subsingleton_dom
  letI : Unique (LocallyConstant (PrimeSpectrum (ZMod 1)) ℤ) :=
    { default := 0
      uniq := fun _ ↦ LocallyConstant.ext fun p ↦ isEmptyElim p }
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end KTheory.ProjectiveClass

namespace KTheory.ProjectiveClass

universe uR uN

open scoped TensorProduct

/-- The bundled rank retains the whole original class-rank function. -/
private theorem rankLocallyConstantRingHom_whole_function
    (R : Type uR) [CommRing R] :
    (rankLocallyConstantRingHom R : ProjectiveClass R →
      LocallyConstant (PrimeSpectrum R) ℕ) = rankLocallyConstant R := rfl

/-- The integer-valued rank retains `KTheory.K0.lift` on the whole domain. -/
private theorem rankLocallyConstantRingHom_whole_additive_projection
    (R : Type uR) [CommRing R] :
    (KTheory.K0.rankLocallyConstantRingHom R).toAddMonoidHom =
      KTheory.K0.lift R
        (((LocallyConstant.mapRingHom (Nat.castRingHom ℤ)).comp
          (rankLocallyConstantRingHom R)).toAddMonoidHom) := rfl

/-- The original independently lifted rational coordinate modules test both ring laws. -/
private theorem rankLocallyConstantRingHom_rational_arithmetic :
    let M₂ := ULift.{uι} (Fin 2) → ULift.{uM} ℚᵐᵒᵖ
    let M₃ := ULift.{uι} (Fin 3) → ULift.{uN} ℚᵐᵒᵖ
    rankLocallyConstantRingHom ℚ (of ℚ M₂) = 2 ∧
    rankLocallyConstantRingHom ℚ (of ℚ M₃) = 3 ∧
    rankLocallyConstantRingHom ℚ (of ℚ (M₂ × M₃)) = 5 ∧
    rankLocallyConstantRingHom ℚ (of ℚ (M₂ ⊗[ℚᵐᵒᵖ] M₃)) = 6 ∧
    KTheory.K0.rankLocallyConstantRingHom ℚ (KTheory.K0.of ℚ M₂) = 2 ∧
    KTheory.K0.rankLocallyConstantRingHom ℚ (KTheory.K0.of ℚ M₃) = 3 ∧
    KTheory.K0.rankLocallyConstantRingHom ℚ (KTheory.K0.of ℚ (M₂ × M₃)) = 5 ∧
    KTheory.K0.rankLocallyConstantRingHom ℚ
      (KTheory.K0.of ℚ (M₂ ⊗[ℚᵐᵒᵖ] M₃)) = 6 := by
  classical
  dsimp only
  let M₂ := ULift.{uι} (Fin 2) → ULift.{uM} ℚᵐᵒᵖ
  let M₃ := ULift.{uι} (Fin 3) → ULift.{uN} ℚᵐᵒᵖ
  have h₂ : rankLocallyConstantRingHom ℚ (of ℚ M₂) = 2 :=
    rankLocallyConstant_rationalCoordinates
  have hline : Module.rankLocallyConstant ℚᵐᵒᵖ (ULift.{uN} ℚᵐᵒᵖ) = 1 := by
    calc
      _ = Module.rankLocallyConstant ℚᵐᵒᵖ ℚᵐᵒᵖ :=
        Module.rankLocallyConstant_eq_of_equiv ℚᵐᵒᵖ _ _
          (ULift.moduleEquiv (R := ℚᵐᵒᵖ) (M := ℚᵐᵒᵖ))
      _ = 1 := Module.rankLocallyConstant_self ℚᵐᵒᵖ
  have hcoordinates : Module.rankLocallyConstant ℚᵐᵒᵖ M₃ = 3 := by
    rw [Module.rankLocallyConstant_pi ℚᵐᵒᵖ (ULift.{uι} (Fin 3))
      (fun _ ↦ ULift.{uN} ℚᵐᵒᵖ)]
    simp [hline, finsum_eq_sum_of_fintype]
  have h₃ : rankLocallyConstantRingHom ℚ (of ℚ M₃) = 3 := by
    rw [rankLocallyConstantRingHom_of_module, hcoordinates]
    ext p
    rfl
  have hp : rankLocallyConstantRingHom ℚ (of ℚ (M₂ × M₃)) = 5 := by
    rw [of_prod, map_add, h₂, h₃]
    norm_num
  have ht : rankLocallyConstantRingHom ℚ (of ℚ (M₂ ⊗[ℚᵐᵒᵖ] M₃)) = 6 := by
    rw [← of_mul, map_mul, h₂, h₃]
    norm_num
  refine ⟨h₂, h₃, hp, ht, ?_, ?_, ?_, ?_⟩ <;>
    rw [← KTheory.K0.ofClass_of, KTheory.K0.rankLocallyConstantRingHom_ofClass]
  · exact (congrArg (LocallyConstant.mapRingHom (Nat.castRingHom ℤ)) h₂).trans
      (map_natCast (LocallyConstant.mapRingHom (Nat.castRingHom ℤ)) 2)
  · exact (congrArg (LocallyConstant.mapRingHom (Nat.castRingHom ℤ)) h₃).trans
      (map_natCast (LocallyConstant.mapRingHom (Nat.castRingHom ℤ)) 3)
  · exact (congrArg (LocallyConstant.mapRingHom (Nat.castRingHom ℤ)) hp).trans
      (map_natCast (LocallyConstant.mapRingHom (Nat.castRingHom ℤ)) 5)
  · exact (congrArg (LocallyConstant.mapRingHom (Nat.castRingHom ℤ)) ht).trans
      (map_natCast (LocallyConstant.mapRingHom (Nat.castRingHom ℤ)) 6)

/-- The same genuine finite-projective product corner tests rank and both naturality diagrams. -/
private theorem rankLocallyConstantRingHom_product_corner :
    ∃ M : ModuleCat.FiniteProjective.{0, 0} (ℚ × ℚ)ᵐᵒᵖ,
      let q : PrimeSpectrum ℚ := ⟨⊥, inferInstance⟩
      let p₁ := PrimeSpectrum.comap (RingHom.fst ℚ ℚ) q
      let p₂ := PrimeSpectrum.comap (RingHom.snd ℚ ℚ) q
      rankLocallyConstantRingHom (ℚ × ℚ) (of (ℚ × ℚ) M) p₁ = 1 ∧
      rankLocallyConstantRingHom (ℚ × ℚ) (of (ℚ × ℚ) M) p₂ = 0 ∧
      (¬ ∃ n : ℕ, rankLocallyConstantRingHom (ℚ × ℚ) (of (ℚ × ℚ) M) =
        LocallyConstant.const (PrimeSpectrum (ℚ × ℚ)) n) ∧
      KTheory.K0.rankLocallyConstantRingHom (ℚ × ℚ) (KTheory.K0.of (ℚ × ℚ) M) p₁ = 1 ∧
      KTheory.K0.rankLocallyConstantRingHom (ℚ × ℚ) (KTheory.K0.of (ℚ × ℚ) M) p₂ = 0 ∧
      rankLocallyConstantRingHom ℚ (mapRingHom (RingHom.fst ℚ ℚ) (of (ℚ × ℚ) M)) q = 1 ∧
      rankLocallyConstantRingHom ℚ (mapRingHom (RingHom.snd ℚ ℚ) (of (ℚ × ℚ) M)) q = 0 ∧
      KTheory.K0.rankLocallyConstantRingHom ℚ
        (KTheory.K0.map (RingHom.fst ℚ ℚ) (KTheory.K0.of (ℚ × ℚ) M)) q = 1 ∧
      KTheory.K0.rankLocallyConstantRingHom ℚ
        (KTheory.K0.map (RingHom.snd ℚ ℚ) (KTheory.K0.of (ℚ × ℚ) M)) q = 0 := by
  obtain ⟨M, h₁, h₂, hn⟩ := rankLocallyConstant_product_nonconstant
  let q : PrimeSpectrum ℚ := ⟨⊥, inferInstance⟩
  have hk₁ : KTheory.K0.rankLocallyConstantRingHom (ℚ × ℚ)
      (KTheory.K0.of (ℚ × ℚ) M) (PrimeSpectrum.comap (RingHom.fst ℚ ℚ) q) = 1 := by
    rw [← KTheory.K0.ofClass_of, KTheory.K0.rankLocallyConstantRingHom_ofClass]
    change ((rankLocallyConstant (ℚ × ℚ) (of (ℚ × ℚ) M)
      (PrimeSpectrum.comap (RingHom.fst ℚ ℚ) q) : ℕ) : ℤ) = 1
    rw [h₁]
    rfl
  have hk₂ : KTheory.K0.rankLocallyConstantRingHom (ℚ × ℚ)
      (KTheory.K0.of (ℚ × ℚ) M) (PrimeSpectrum.comap (RingHom.snd ℚ ℚ) q) = 0 := by
    rw [← KTheory.K0.ofClass_of, KTheory.K0.rankLocallyConstantRingHom_ofClass]
    change ((rankLocallyConstant (ℚ × ℚ) (of (ℚ × ℚ) M)
      (PrimeSpectrum.comap (RingHom.snd ℚ ℚ) q) : ℕ) : ℤ) = 0
    rw [h₂]
    rfl
  refine ⟨M, h₁, h₂, hn, hk₁, hk₂, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun F : ProjectiveClass (ℚ × ℚ) →+*
        LocallyConstant (PrimeSpectrum ℚ) ℕ ↦ F (of (ℚ × ℚ) M) q)
      (rankLocallyConstantRingHom_naturality (RingHom.fst ℚ ℚ))).trans h₁
  · exact (congrArg (fun F : ProjectiveClass (ℚ × ℚ) →+*
        LocallyConstant (PrimeSpectrum ℚ) ℕ ↦ F (of (ℚ × ℚ) M) q)
      (rankLocallyConstantRingHom_naturality (RingHom.snd ℚ ℚ))).trans h₂
  · rw [KTheory.K0.rankLocallyConstantRingHom_map_apply]
    exact hk₁
  · rw [KTheory.K0.rankLocallyConstantRingHom_map_apply]
    exact hk₂

/-- Empty-spectrum values concern locally constant functions, not equality of integers. -/
private theorem rankLocallyConstantRingHom_empty_spectrum :
    rankLocallyConstantRingHom (ZMod 1) (of (ZMod 1) (ZMod 1)ᵐᵒᵖ) = 0 ∧
    KTheory.K0.rankLocallyConstantRingHom (ZMod 1)
      (KTheory.K0.of (ZMod 1) (ZMod 1)ᵐᵒᵖ) = 0 ∧
    (0 : LocallyConstant (PrimeSpectrum (ZMod 1)) ℕ) = 1 ∧
    (0 : LocallyConstant (PrimeSpectrum (ZMod 1)) ℤ) = 1 := by
  refine ⟨rankLocallyConstant_zeroRing.1, ?_, ?_, rankLocallyConstant_zeroRing.2⟩
  all_goals
    ext p
    exact isEmptyElim p

end KTheory.ProjectiveClass
