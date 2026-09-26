/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.PicardGroup
public import ProjectiveModules.Contraction.BaseChange

/-!
# Invertibility of finite projective modules of rank one

This file proves that a finite projective module whose rank at every stalk is
one is invertible. The proof checks the canonical evaluation map after
localization at every maximal ideal and descends its bijectivity.
-/

@[expose] public section

open TensorProduct LocalizedModule

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A finite projective module of constant stalk rank one is invertible. -/
theorem invertible_of_rankAtStalk_eq_one
    [Module.Finite R M] [Module.Projective R M]
    (h : Module.rankAtStalk (R := R) M = 1) : Module.Invertible R M where
  bijective := by
    apply bijective_of_localized_maximal (contractLeft R M)
    intro J hJ
    let A := Localization.AtPrime J
    let W := LocalizedModule J.primeCompl M
    let j : M →ₗ[R] W := LocalizedModule.mkLinearMap J.primeCompl M
    let ibc : IsBaseChange A j := LocalizedModule.isBaseChange J.primeCompl M
    let f : (Dual R M ⊗[R] M) →ₗ[R] Dual A W ⊗[A] W :=
      ibc.toContractBaseChangeOfProjective
    let g : R →ₗ[R] A := Algebra.linearMap R A
    let _ : IsLocalizedModule J.primeCompl f :=
      (isLocalizedModule_iff_isBaseChange J.primeCompl A f).mpr
        ibc.contract_of_projective
    let _ : IsLocalizedModule J.primeCompl g := inferInstance
    rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective f g]
    let _ : Module.Finite A W := Module.Finite.of_isLocalizedModule J.primeCompl j
    let _ : Module.Flat A W := Module.Flat.of_isLocalizedModule A J.primeCompl j
    let _ : Module.Free A W := Module.free_of_flat_of_isLocalRing
    have hfin : Module.finrank A W = 1 := congrFun h ⟨J, hJ.isPrime⟩
    let _ : Module.Invertible A W := Module.Invertible.congr
      (Module.nonempty_linearEquiv_of_finrank_eq_one hfin).some
    have hmap : IsLocalizedModule.map J.primeCompl f g (contractLeft R M) =
        (contractLeft A W).restrictScalars R := by
      apply IsLocalizedModule.ext J.primeCompl f (IsLocalizedModule.map_units g)
      rw [IsLocalizedModule.map_comp]
      exact ibc.contractLeft_comp_toContractBaseChangeOfProjective.symm
    rw [hmap]
    exact Module.Invertible.bijective

/-- A module over a commutative ring is invertible if and only if it is finite
projective and has constant stalk rank one. -/
theorem invertible_iff_finite_projective_rankAtStalk_eq_one :
    Module.Invertible R M ↔
      Module.Finite R M ∧ Module.Projective R M ∧
        Module.rankAtStalk (R := R) M = 1 := by
  constructor
  · intro h
    let _ := h
    refine ⟨inferInstance, inferInstance, ?_⟩
    ext p
    simp [Module.rankAtStalk, Module.Invertible.finrank_eq_one]
  · rintro ⟨hfinite, hprojective, hrank⟩
    let _ := hfinite
    let _ := hprojective
    exact Module.invertible_of_rankAtStalk_eq_one hrank

end Module
