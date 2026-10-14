/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Category.FiniteProjective
import ProjectiveModules.Module.ProjectiveKernel
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Kernels of surjections between finite projective modules

A section obtained from projectivity makes the kernel subtype finite and
projective by the split-kernel API. The subtype inclusion forms a kernel fork,
whose limit property reflects from the category of modules. The fork's lift,
factorization and uniqueness APIs then apply in the finite projective category.

The construction uses Projective Modules' finite projective category and
split-kernel API, together with Mathlib's module kernels, full subcategories
and fully faithful limit reflection. The first projection from two copies of
the scalar ring gives a surjection with nonzero kernel over a nontrivial ring.
-/

open CategoryTheory CategoryTheory.Limits

universe uR uC

namespace ProjectiveModulesTests.SurjectiveKernel

theorem hasKernelOfSurjective {R : Type uR} [Ring R]
    {P Q : ModuleCat.FiniteProjective.{uR, uC} R}
    (f : P ⟶ Q) (hf : Function.Surjective f.hom.hom) : HasKernel f := by
  let r : P →ₗ[R] Q := f.hom.hom
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective r
    (LinearMap.range_eq_top.mpr hf)
  have hK : ModuleCat.isFiniteProjective R
      (ModuleCat.of R (LinearMap.ker f.hom.hom)) :=
    ⟨LinearMap.finite_splitKernel s r hs,
      LinearMap.projective_splitKernel s r hs⟩
  let K : ModuleCat.FiniteProjective.{uR, uC} R :=
    ⟨ModuleCat.of R (LinearMap.ker f.hom.hom), hK⟩
  let i : K ⟶ P := ObjectProperty.homMk
    (ModuleCat.ofHom (LinearMap.ker f.hom.hom).subtype)
  let I := (ModuleCat.isFiniteProjective.{uR, uC} R).ι
  have hi : i ≫ f = 0 := by
    apply I.map_injective
    exact KernelFork.condition (ModuleCat.kernelCone f.hom)
  let c : KernelFork f := KernelFork.ofι i hi
  have w : i ≫ f = i ≫ (0 : P ⟶ Q) := by
    simpa only [HasZeroMorphisms.comp_zero] using hi
  have hc : IsLimit c :=
    isLimitOfIsLimitForkMap I w (ModuleCat.kernelIsLimit f.hom)
  have hi_apply (x : LinearMap.ker f.hom.hom) : i.hom.hom x = x.val := rfl
  have hUniversal (X : ModuleCat.FiniteProjective.{uR, uC} R) (g : X ⟶ P)
      (hg : g ≫ f = 0) : ∃! l : X ⟶ K,
        l ≫ i = g ∧ ∀ x : X, (l.hom.hom x).val = g.hom.hom x := by
    let l : X ⟶ K := (KernelFork.IsLimit.lift' hc g hg).1
    have hl : l ≫ i = g := (KernelFork.IsLimit.lift' hc g hg).2
    refine ⟨l, ⟨hl, ?_⟩, ?_⟩
    · intro x
      change (l ≫ i).hom.hom x = g.hom.hom x
      rw [hl]
    · intro m hm
      exact Fork.IsLimit.hom_ext hc (hm.1.trans hl.symm)
  let : HasKernel f := HasLimit.mk ⟨c, hc⟩
  let e : kernel f ≅ K := limit.isoLimitCone ⟨c, hc⟩
  have he : e.inv ≫ kernel.ι f = i :=
    limit.isoLimitCone_inv_π ⟨c, hc⟩ WalkingParallelPair.zero
  have hChosenLift (X : ModuleCat.FiniteProjective.{uR, uC} R) (g : X ⟶ P)
      (hg : g ≫ f = 0) : kernel.lift f g hg ≫ kernel.ι f = g :=
    kernel.lift_ι f g hg
  exact inferInstance

example (R : Type uR) [Ring R] [Nontrivial R] :
    let P := ModuleCat.FiniteProjective.of R (R × R)
    let Q := ModuleCat.FiniteProjective.of R R
    let f : P ⟶ Q := ModuleCat.FiniteProjective.ofHom R (LinearMap.fst R R R)
    HasKernel f ∧ Function.Surjective f.hom.hom ∧
      ∃ k : LinearMap.ker f.hom.hom, k.val ≠ 0 := by
  refine ⟨hasKernelOfSurjective _ LinearMap.fst_surjective,
    LinearMap.fst_surjective, ?_⟩
  refine ⟨⟨(0, 1), rfl⟩, ?_⟩
  intro h
  exact one_ne_zero (congrArg Prod.snd h)

end ProjectiveModulesTests.SurjectiveKernel
