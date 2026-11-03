/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.ProjectiveReduction
import ProjectiveModules.Module.ReductionEndomorphism

/-!
# Detecting bijectivity after nilpotent reduction

A linear map to a projective module is bijective if its reduction modulo a
nilpotent two-sided ideal is bijective. The source need not be projective or
finitely generated. Lifting the inverse of the reduced map gives two composites
that differ from the identity by nilpotent endomorphisms.
-/

@[expose] public section

universe u p q

namespace Module

variable {R : Type u} [Ring R] (I : Ideal R) [I.IsTwoSided]

private theorem isUnit_of_reductionEnd_eq_one (hI : IsNilpotent I)
    {M : Type p} [AddCommGroup M] [Module R M]
    (f : Module.End R M) (hf : reductionEnd I M f = 1) : IsUnit f := by
  have hmem : f - 1 ∈ RingHom.ker (reductionEnd I M) := by
    rw [RingHom.mem_ker, map_sub, hf, map_one, sub_self]
  obtain ⟨n, hn⟩ := reductionEnd_ker_isNilpotent I M hI
  have hnil : IsNilpotent (f - 1) :=
    ⟨n, Ideal.pow_eq_zero_of_mem hn le_rfl hmem⟩
  simpa only [sub_add_cancel] using hnil.isUnit_add_one

/-- A linear map to a projective module is bijective if its canonical reduction
modulo a nilpotent two-sided ideal is bijective. No projectivity or finite
generation is required of the source. -/
theorem bijective_of_reduction_bijective (hI : IsNilpotent I)
    {M : Type p} {Q : Type q}
    [AddCommGroup M] [Module R M]
    [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    (f : M →ₗ[R] Q) (hf : Function.Bijective (reductionMap I f)) :
    Function.Bijective f := by
  let e := LinearEquiv.ofBijective (reductionMap I f) hf
  obtain ⟨g, hg⟩ := exists_reductionMap_eq_of_projective I e.symm.toLinearMap
  have hgf : reductionEnd I M (g.comp f) = 1 := by
    rw [reductionEnd_apply, reductionMap_comp, hg]
    apply LinearMap.ext
    intro x
    exact LinearEquiv.ofBijective_symm_apply_apply (reductionMap I f) (h := hf) x
  have hfg : reductionEnd I Q (f.comp g) = 1 := by
    rw [reductionEnd_apply, reductionMap_comp, hg]
    apply LinearMap.ext
    intro x
    exact LinearEquiv.apply_ofBijective_symm_apply (reductionMap I f) (h := hf) x
  have hgf_bij : Function.Bijective (g.comp f) :=
    (Module.End.isUnit_iff (g.comp f)).mp
      (isUnit_of_reductionEnd_eq_one I hI (g.comp f) hgf)
  have hfg_bij : Function.Bijective (f.comp g) :=
    (Module.End.isUnit_iff (f.comp g)).mp
      (isUnit_of_reductionEnd_eq_one I hI (f.comp g) hfg)
  constructor
  · intro x y hxy
    exact hgf_bij.1 (congrArg g hxy)
  · intro y
    obtain ⟨x, hx⟩ := hfg_bij.2 y
    exact ⟨g x, hx⟩

/-- For a linear map to a projective module, reduction modulo a nilpotent
two-sided ideal preserves and detects bijectivity. -/
theorem reductionMap_bijective_iff (hI : IsNilpotent I)
    {M : Type p} {Q : Type q}
    [AddCommGroup M] [Module R M]
    [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    (f : M →ₗ[R] Q) :
    Function.Bijective (reductionMap I f) ↔ Function.Bijective f := by
  constructor
  · exact bijective_of_reduction_bijective I hI f
  · intro hf
    exact (reductionEquiv I (LinearEquiv.ofBijective f hf)).bijective

end Module
