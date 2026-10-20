/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.KTheory.RankLocallyConstant
import ProjectiveModules.KTheory.Ring
import ProjectiveModules.KTheory.RingScalarExtension
import ProjectiveModulesTests.ProjectiveClassRankLocallyConstantClient

/-!
# Conditional locally constant rank contracts

The existing natural-valued rank function on projective-module classes can be
bundled as a ring homomorphism conditional on four raw law hypotheses: preservation
of zero, one, addition and multiplication. These hypotheses are parameters, not
proofs supplied here; the bundled map retains the whole existing rank function.

For a hypothetical class-rank ring homomorphism `q`, the released Grothendieck-group
completion gives a map from the existing `KTheory.K0 R` to integer-valued locally
constant functions. This construction does not assert unconditional existence of
`q` or of a compatible rank map.

The remaining proposition-valued contracts specify generator and module values,
prime evaluation, uniqueness, opposite-spectrum compatibility and naturality,
together with rational, product-corner and empty-spectrum controls. They are
specifications, not proofs of these assertions. The two equality probes state
expected equalities for the whole existing function and the old additive
completion projection.
-/

open scoped TensorProduct

universe uR uS uM uN uι

namespace LocallyConstantRankConditionalSource

/-- CONDITIONAL lambda: each of these four raw-law slots is UNPROVED. -/
private noncomputable def classLawSlots (R : Type uR) [CommRing R] :
    (KTheory.ProjectiveClass.rankLocallyConstant R 0 = 0) →
    (KTheory.ProjectiveClass.rankLocallyConstant R 1 = 1) →
    (∀ a b : KTheory.ProjectiveClass R,
      KTheory.ProjectiveClass.rankLocallyConstant R (a + b) =
        KTheory.ProjectiveClass.rankLocallyConstant R a +
          KTheory.ProjectiveClass.rankLocallyConstant R b) →
    (∀ a b : KTheory.ProjectiveClass R,
      KTheory.ProjectiveClass.rankLocallyConstant R (a * b) =
        KTheory.ProjectiveClass.rankLocallyConstant R a *
          KTheory.ProjectiveClass.rankLocallyConstant R b) →
    (KTheory.ProjectiveClass R →+* LocallyConstant (PrimeSpectrum R) ℕ) :=
  fun raw_zero raw_one raw_add raw_mul ↦
    { toFun := KTheory.ProjectiveClass.rankLocallyConstant R
      map_zero' := raw_zero
      map_one' := raw_one
      map_add' := raw_add
      map_mul' := raw_mul }

/-- SOURCE-ONLY rfl probe for retention of the WHOLE old function. -/
private noncomputable def originalFunctionProbe (R : Type uR) [CommRing R]
    (raw_zero : KTheory.ProjectiveClass.rankLocallyConstant R 0 = 0)
    (raw_one : KTheory.ProjectiveClass.rankLocallyConstant R 1 = 1)
    (raw_add : ∀ a b : KTheory.ProjectiveClass R,
      KTheory.ProjectiveClass.rankLocallyConstant R (a + b) =
        KTheory.ProjectiveClass.rankLocallyConstant R a +
          KTheory.ProjectiveClass.rankLocallyConstant R b)
    (raw_mul : ∀ a b : KTheory.ProjectiveClass R,
      KTheory.ProjectiveClass.rankLocallyConstant R (a * b) =
        KTheory.ProjectiveClass.rankLocallyConstant R a *
          KTheory.ProjectiveClass.rankLocallyConstant R b) :
    (classLawSlots R raw_zero raw_one raw_add raw_mul :
      KTheory.ProjectiveClass R → LocallyConstant (PrimeSpectrum R) ℕ) =
        KTheory.ProjectiveClass.rankLocallyConstant R := rfl

/-- Direct released lift of a HYPOTHETICAL q, at the OLD K0 target. -/
private noncomputable def completionTerm (R : Type uR) [CommRing R]
    (q : KTheory.ProjectiveClass R →+* LocallyConstant (PrimeSpectrum R) ℕ) :
    KTheory.K0 R →+* LocallyConstant (PrimeSpectrum R) ℤ :=
  Algebra.GrothendieckAddGroup.liftRingHom
    ((LocallyConstant.mapRingHom (Nat.castRingHom ℤ)).comp q)

/-- SOURCE-ONLY rfl probe for the WHOLE OLD additive lift, not pointwise equality. -/
private noncomputable def oldAdditiveProjectionProbe (R : Type uR) [CommRing R]
    (q : KTheory.ProjectiveClass R →+* LocallyConstant (PrimeSpectrum R) ℕ) :
    (completionTerm R q).toAddMonoidHom =
      KTheory.K0.lift R
        (((LocallyConstant.mapRingHom (Nat.castRingHom ℤ)).comp q).toAddMonoidHom) :=
  rfl

/-- Unproved generator/bundled compatibility contract for hypothetical q and rho. -/
private def generatorContract (R : Type uR) [CommRing R]
    (q : KTheory.ProjectiveClass R →+* LocallyConstant (PrimeSpectrum R) ℕ)
    (rho : KTheory.K0 R →+* LocallyConstant (PrimeSpectrum R) ℤ) : Prop :=
  (∀ a : KTheory.ProjectiveClass R,
    rho (KTheory.K0.ofClass R a) =
      LocallyConstant.mapRingHom (Nat.castRingHom ℤ) (q a)) ∧
  rho.comp (KTheory.K0.ofClassRingHom R) =
    (LocallyConstant.mapRingHom (Nat.castRingHom ℤ)).comp q

/-- Unproved module/prime formulas: the ORIGINAL right-module dictionaries. -/
private def originalModuleContract (R : Type uR) [CommRing R]
    (q : KTheory.ProjectiveClass R →+* LocallyConstant (PrimeSpectrum R) ℕ)
    (rho : KTheory.K0 R →+* LocallyConstant (PrimeSpectrum R) ℤ)
    (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] : Prop :=
  (q (KTheory.ProjectiveClass.of R M) =
    LocallyConstant.comap
      (toContinuousMap (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.toOpposite R)))
      (Module.rankLocallyConstant Rᵐᵒᵖ M)) ∧
  (rho (KTheory.K0.of R M) =
    LocallyConstant.mapRingHom (Nat.castRingHom ℤ)
      (LocallyConstant.comap
        (toContinuousMap (PrimeSpectrum.homeomorphOfRingEquiv (RingEquiv.toOpposite R)))
        (Module.rankLocallyConstant Rᵐᵒᵖ M))) ∧
  (∀ p : PrimeSpectrum R,
    q (KTheory.ProjectiveClass.of R M) p =
      Module.rankAtStalk (R := Rᵐᵒᵖ) M
        (PrimeSpectrum.comap (RingEquiv.toOpposite R).symm.toRingHom p)) ∧
  (∀ p : PrimeSpectrum R,
    rho (KTheory.K0.of R M) p =
      ((Module.rankAtStalk (R := Rᵐᵒᵖ) M
        (PrimeSpectrum.comap (RingEquiv.toOpposite R).symm.toRingHom p) : ℕ) : ℤ))

/-- Unproved class extensionality/uniqueness on reference FP generators. -/
private def classUniquenessContract (R : Type uR) [CommRing R]
    (q : KTheory.ProjectiveClass R →+* LocallyConstant (PrimeSpectrum R) ℕ) : Prop :=
  ∀ q' : KTheory.ProjectiveClass R →+* LocallyConstant (PrimeSpectrum R) ℕ,
    (∀ X : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ,
      q' (KTheory.ProjectiveClass.of R X) = q (KTheory.ProjectiveClass.of R X)) →
    q' = q

/-- Unproved completion extensionality, and uniqueness of the direct lift from q. -/
private def completionUniquenessContract (R : Type uR) [CommRing R]
    (q : KTheory.ProjectiveClass R →+* LocallyConstant (PrimeSpectrum R) ℕ)
    (rho : KTheory.K0 R →+* LocallyConstant (PrimeSpectrum R) ℤ) : Prop :=
  (∀ rho' : KTheory.K0 R →+* LocallyConstant (PrimeSpectrum R) ℤ,
    (∀ a : KTheory.ProjectiveClass R,
      rho' (KTheory.K0.ofClass R a) = rho (KTheory.K0.ofClass R a)) → rho' = rho) ∧
  (∀ rho' : KTheory.K0 R →+* LocallyConstant (PrimeSpectrum R) ℤ,
    (∀ a : KTheory.ProjectiveClass R,
      rho' (KTheory.K0.ofClass R a) =
        LocallyConstant.mapRingHom (Nat.castRingHom ℤ) (q a)) →
    rho' = completionTerm R q) ∧
  (∀ rho' : KTheory.K0 R →+* LocallyConstant (PrimeSpectrum R) ℤ,
    (∀ X : ModuleCat.FiniteProjective.{uR, uR} Rᵐᵒᵖ,
      rho' (KTheory.K0.of R X) = rho (KTheory.K0.of R X)) → rho' = rho)

/-- Unproved alpha_S.comp f.op = f.comp alpha_R and the correctly directed Spec square. -/
private def oppositeSpectrumSquareContract
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  ((RingEquiv.toOpposite S).symm.toRingHom.comp f.op =
    f.comp (RingEquiv.toOpposite R).symm.toRingHom) ∧
  ((PrimeSpectrum.comap f.op) ∘
      (PrimeSpectrum.comap (RingEquiv.toOpposite S).symm.toRingHom) =
    (PrimeSpectrum.comap (RingEquiv.toOpposite R).symm.toRingHom) ∘
      (PrimeSpectrum.comap f))

/-- Unproved naturality; the K0 diagram uses ONLY the OLD additive K0.map. -/
private def oldMapNaturalityContract
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S] (f : R →+* S)
    (qR : KTheory.ProjectiveClass R →+* LocallyConstant (PrimeSpectrum R) ℕ)
    (qS : KTheory.ProjectiveClass S →+* LocallyConstant (PrimeSpectrum S) ℕ)
    (rhoR : KTheory.K0 R →+* LocallyConstant (PrimeSpectrum R) ℤ)
    (rhoS : KTheory.K0 S →+* LocallyConstant (PrimeSpectrum S) ℤ) : Prop :=
  (qS.comp (KTheory.ProjectiveClass.mapRingHom f) =
    (LocallyConstant.comapRingHom
      ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩).comp qR) ∧
  (rhoS.toAddMonoidHom.comp (KTheory.K0.map f) =
    (LocallyConstant.comapRingHom
      ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩ :
        LocallyConstant (PrimeSpectrum R) ℤ →+* LocallyConstant (PrimeSpectrum S) ℤ
    ).toAddMonoidHom.comp rhoR.toAddMonoidHom) ∧
  (∀ (x : KTheory.K0 R) (p : PrimeSpectrum S),
    rhoS (KTheory.K0.map f x) p = rhoR x (PrimeSpectrum.comap f p))

/-- Unproved 2,3 / product 5 / tensor 6 controls on the frozen client's carriers. -/
private def rationalArithmeticContract
    (q : KTheory.ProjectiveClass ℚ →+* LocallyConstant (PrimeSpectrum ℚ) ℕ)
    (rho : KTheory.K0 ℚ →+* LocallyConstant (PrimeSpectrum ℚ) ℤ) : Prop :=
  let M₂ := ULift.{uι} (Fin 2) → ULift.{uM} ℚᵐᵒᵖ
  let M₃ := ULift.{uι} (Fin 3) → ULift.{uN} ℚᵐᵒᵖ
  q (KTheory.ProjectiveClass.of ℚ M₂) = 2 ∧
  q (KTheory.ProjectiveClass.of ℚ M₃) = 3 ∧
  q (KTheory.ProjectiveClass.of ℚ (M₂ × M₃)) = 5 ∧
  q (KTheory.ProjectiveClass.of ℚ (M₂ ⊗[ℚᵐᵒᵖ] M₃)) = 6 ∧
  rho (KTheory.K0.of ℚ M₂) = 2 ∧
  rho (KTheory.K0.of ℚ M₃) = 3 ∧
  rho (KTheory.K0.of ℚ (M₂ × M₃)) = 5 ∧
  rho (KTheory.K0.of ℚ (M₂ ⊗[ℚᵐᵒᵖ] M₃)) = 6

/-- The frozen raw client's genuine FP 1/0 corner, not an assumed free model.
This only states the desired q/rho control; no new witness is constructed. -/
private def productCornerContract
    (q : KTheory.ProjectiveClass (ℚ × ℚ) →+*
      LocallyConstant (PrimeSpectrum (ℚ × ℚ)) ℕ)
    (rho : KTheory.K0 (ℚ × ℚ) →+* LocallyConstant (PrimeSpectrum (ℚ × ℚ)) ℤ) : Prop :=
  ∃ M : ModuleCat.FiniteProjective.{0, 0} (ℚ × ℚ)ᵐᵒᵖ,
    let p₁ := PrimeSpectrum.comap (RingHom.fst ℚ ℚ) ⟨⊥, inferInstance⟩
    let p₂ := PrimeSpectrum.comap (RingHom.snd ℚ ℚ) ⟨⊥, inferInstance⟩
    KTheory.ProjectiveClass.rankLocallyConstant (ℚ × ℚ)
      (KTheory.ProjectiveClass.of (ℚ × ℚ) M) p₁ = 1 ∧
    KTheory.ProjectiveClass.rankLocallyConstant (ℚ × ℚ)
      (KTheory.ProjectiveClass.of (ℚ × ℚ) M) p₂ = 0 ∧
    (¬ ∃ n : ℕ, KTheory.ProjectiveClass.rankLocallyConstant (ℚ × ℚ)
      (KTheory.ProjectiveClass.of (ℚ × ℚ) M) =
        LocallyConstant.const (PrimeSpectrum (ℚ × ℚ)) n) ∧
    q (KTheory.ProjectiveClass.of (ℚ × ℚ) M) p₁ = 1 ∧
    q (KTheory.ProjectiveClass.of (ℚ × ℚ) M) p₂ = 0 ∧
    rho (KTheory.K0.of (ℚ × ℚ) M) p₁ = 1 ∧
    rho (KTheory.K0.of (ℚ × ℚ) M) p₂ = 0

/-- Unproved empty-spectrum control; LC zero=one does NOT mean integer zero=one. -/
private def emptySpectrumContract
    (q : KTheory.ProjectiveClass (ZMod 1) →+*
      LocallyConstant (PrimeSpectrum (ZMod 1)) ℕ)
    (rho : KTheory.K0 (ZMod 1) →+* LocallyConstant (PrimeSpectrum (ZMod 1)) ℤ) : Prop :=
  (∀ p : PrimeSpectrum (ZMod 1), False) ∧
  (0 : LocallyConstant (PrimeSpectrum (ZMod 1)) ℕ) = 1 ∧
  (0 : LocallyConstant (PrimeSpectrum (ZMod 1)) ℤ) = 1 ∧
  q (KTheory.ProjectiveClass.of (ZMod 1) (ZMod 1)ᵐᵒᵖ) = 0 ∧
  rho (KTheory.K0.of (ZMod 1) (ZMod 1)ᵐᵒᵖ) = 0

end LocallyConstantRankConditionalSource
