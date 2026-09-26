/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism and the worker contributors identified in README.md and Git history
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Topology.FiberPartition

/-!
# Rank-fiber decomposition of a finite projective module

A finite projective module has locally constant stalk rank.  This file indexes
the nonempty fibers of that rank function and uses their clopen idempotents to
decompose both the base ring and the module.  No connectedness or nontriviality
hypothesis is needed; in particular, the construction also covers the zero
ring and its empty prime spectrum.
-/

public section

open Function Set

universe u v

namespace Module

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- The stalk-rank function of a finite projective module, bundled as a locally
constant function. -/
@[expose] noncomputable def rankLocallyConstant : LocallyConstant (PrimeSpectrum R) ℕ :=
  ⟨rankAtStalk (R := R) M, by
    let _ := Module.finitePresentation_of_projective R M
    exact isLocallyConstant_rankAtStalk⟩

@[simp]
theorem rankLocallyConstant_apply (p : PrimeSpectrum R) :
    rankLocallyConstant R M p = rankAtStalk (R := R) M p :=
  rfl

/-- The finite type of nonempty fibers of the stalk-rank function. -/
abbrev rankFiberIndex := Function.Fiber (rankLocallyConstant R M)

noncomputable instance rankFiberIndexFintype : Fintype (rankFiberIndex R M) :=
  Fintype.ofFinite _

/-- The clopen subset of the prime spectrum underlying a rank fiber. -/
def rankFiberClopen (i : rankFiberIndex R M) :
    TopologicalSpace.Clopens (PrimeSpectrum R) :=
  ⟨i.1, by
    rw [Function.Fiber.eq_fiber_image]
    exact (rankLocallyConstant R M).isLocallyConstant.isClopen_fiber _⟩

/-- The common stalk rank on a rank fiber. -/
noncomputable def rankFiberRank (i : rankFiberIndex R M) : ℕ :=
  Function.Fiber.image (rankLocallyConstant R M) i

/-- The idempotent corresponding to a rank fiber. -/
noncomputable def rankFiberIdempotent (i : rankFiberIndex R M) : R :=
  (PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm
    (rankFiberClopen R M i)

/-- A rank-fiber idempotent is idempotent. -/
theorem rankFiberIdempotent_isIdempotent (i : rankFiberIndex R M) :
    IsIdempotentElem (rankFiberIdempotent R M i) :=
  ((PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm
    (rankFiberClopen R M i)).2

/-- A rank-fiber idempotent avoids exactly the primes in its fiber. -/
theorem rankFiberIdempotent_notMem_iff (i : rankFiberIndex R M)
    (p : PrimeSpectrum R) :
    rankFiberIdempotent R M i ∉ p.asIdeal ↔ p ∈ i.1 := by
  change p ∈ PrimeSpectrum.basicOpen (rankFiberIdempotent R M i) ↔ _
  unfold rankFiberIdempotent
  rw [PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm]
  rfl

/-- Membership in a rank fiber computes the stalk rank as that fiber's
displayed rank. -/
theorem rankAtStalk_eq_rankFiberRank_of_mem (i : rankFiberIndex R M)
    (p : PrimeSpectrum R) (hp : p ∈ i.1) :
    rankAtStalk (R := R) M p = rankFiberRank R M i :=
  (Function.Fiber.mem_iff_eq_image (rankLocallyConstant R M) p i).1 hp

private theorem rankFiberIdempotents_orthogonal :
    OrthogonalIdempotents (rankFiberIdempotent R M) where
  idem := rankFiberIdempotent_isIdempotent R M
  ortho i j hij := by
    have hinter : rankFiberClopen R M i ⊓ rankFiberClopen R M j = ⊥ := by
      apply TopologicalSpace.Clopens.ext
      ext p
      simp only [TopologicalSpace.Clopens.coe_inf, Set.mem_inter_iff,
        TopologicalSpace.Clopens.coe_bot, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hpi, hpj⟩
      apply hij
      apply Subtype.ext
      rw [Function.Fiber.eq_fiber_image, Function.Fiber.eq_fiber_image]
      have hi := (Function.Fiber.mem_iff_eq_image
        (rankLocallyConstant R M) p i).1 hpi
      have hj := (Function.Fiber.mem_iff_eq_image
        (rankLocallyConstant R M) p j).1 hpj
      rw [← hi, ← hj]
    have h := PrimeSpectrum.isIdempotentElemEquivClopens_symm_inf
      (R := R) (rankFiberClopen R M i) (rankFiberClopen R M j)
    rw [hinter, PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot] at h
    exact congrArg Subtype.val h.symm

/-- The idempotents attached to the nonempty rank fibers form a complete
orthogonal family. -/
theorem rankFiberIdempotents_complete :
    CompleteOrthogonalIdempotents (rankFiberIdempotent R M) := by
  let e := PrimeSpectrum.isIdempotentElemEquivClopens (R := R)
  let horth := rankFiberIdempotents_orthogonal R M
  refine ⟨horth, ?_⟩
  have hsumIdem : IsIdempotentElem (∑ i, rankFiberIdempotent R M i) :=
    horth.isIdempotentElem_sum
  have hsumTop :
      e ⟨∑ i, rankFiberIdempotent R M i, hsumIdem⟩ = ⊤ := by
    apply TopologicalSpace.Clopens.ext
    ext p
    simp only [TopologicalSpace.Clopens.coe_top, Set.mem_univ, iff_true]
    change (∑ i, rankFiberIdempotent R M i) ∉ p.asIdeal
    intro hsum
    let i : rankFiberIndex R M := Function.Fiber.mk (rankLocallyConstant R M) p
    have hi : rankFiberIdempotent R M i ∉ p.asIdeal :=
      (rankFiberIdempotent_notMem_iff R M i p).2
        (Function.Fiber.mkSelf (rankLocallyConstant R M) p).2
    apply hi
    have hmul : rankFiberIdempotent R M i *
        (∑ j, rankFiberIdempotent R M j) ∈ p.asIdeal :=
      p.asIdeal.mul_mem_left _ hsum
    rw [horth.mul_sum_of_mem (Finset.mem_univ i)] at hmul
    exact hmul
  have honeTop : e ⟨(1 : R), IsIdempotentElem.one⟩ = ⊤ := by
    rw [← PrimeSpectrum.isIdempotentElemEquivClopens_symm_top (R := R)]
    exact e.apply_symm_apply ⊤
  exact congrArg Subtype.val (e.injective (hsumTop.trans honeTop.symm))

/-- The component ring supported on a rank fiber. -/
abbrev rankFiberRing (i : rankFiberIndex R M) :=
  R ⧸ Ideal.span {1 - rankFiberIdempotent R M i}

/-- Base change of the module to a rank-fiber component ring. -/
abbrev rankFiberModule (i : rankFiberIndex R M) :=
  TensorProduct R (rankFiberRing R M i) M

noncomputable instance rankFiberModuleFinite (i : rankFiberIndex R M) :
    Module.Finite (rankFiberRing R M i) (rankFiberModule R M i) :=
  Module.Finite.base_change R (rankFiberRing R M i) M

noncomputable instance rankFiberModuleProjective (i : rankFiberIndex R M) :
    Module.Projective (rankFiberRing R M i) (rankFiberModule R M i) :=
  Module.Projective.tensorProduct

/-- The base ring is the product of its rank-fiber component rings. -/
noncomputable def rankFiberRingEquiv :
    R ≃ₐ[R] ∀ i : rankFiberIndex R M, rankFiberRing R M i :=
  { __ := AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ R
      (Ideal.span {1 - rankFiberIdempotent R M i})
    __ := Equiv.ofBijective _ (rankFiberIdempotents_complete R M).bijective_pi }

/-- On a rank-fiber component, the base-changed module has the fiber's
constant stalk rank. -/
theorem rankAtStalk_rankFiberModule (i : rankFiberIndex R M)
    (p : PrimeSpectrum (rankFiberRing R M i)) :
    rankAtStalk (R := rankFiberRing R M i) (rankFiberModule R M i) p =
      rankFiberRank R M i := by
  rw [rankAtStalk_baseChange]
  let q : PrimeSpectrum R := p.comap (algebraMap R (rankFiberRing R M i))
  have heq : algebraMap R (rankFiberRing R M i) (rankFiberIdempotent R M i) = 1 := by
    change Ideal.Quotient.mk _ (rankFiberIdempotent R M i) = 1
    rw [← (Ideal.Quotient.mk _).map_one, eq_comm,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton]
  have hnot : rankFiberIdempotent R M i ∉ q.asIdeal := by
    intro hmem
    change algebraMap R (rankFiberRing R M i) (rankFiberIdempotent R M i) ∈ p.asIdeal at hmem
    rw [heq] at hmem
    exact p.asIdeal.one_notMem hmem
  have hq : q ∈ i.1 := (rankFiberIdempotent_notMem_iff R M i q).1 hnot
  exact (Function.Fiber.mem_iff_eq_image (rankLocallyConstant R M) q i).1 hq

/-- Reconstruct a finite projective module from its rank-fiber base changes,
viewed by restriction of scalars to the original ring. -/
noncomputable def rankFiberLinearEquiv :
    M ≃ₗ[R] ∀ i : rankFiberIndex R M, rankFiberModule R M i := by
  classical
  exact (TensorProduct.lid R M).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr
        (rankFiberRingEquiv R M).toLinearEquiv (LinearEquiv.refl R M) ≪≫ₗ
      TensorProduct.piLeft R M (fun i : rankFiberIndex R M ↦ rankFiberRing R M i)

end Module
