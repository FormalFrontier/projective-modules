/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import ProjectiveModules.Module.MinimalSupport
public import ProjectiveModules.Module.RightEndomorphismMatrix

/-!
# Finite free summands containing one element

This file proves the first, finite layer of Kaplansky's theorem for projective
modules over a possibly noncommutative local ring.  Every element of an
arbitrary projective right module is contained in the range of a split
injection from a finite standard free module.
-/

@[expose] public section

universe uR uP

namespace Module.Projective

variable {R : Type uR} [Ring R]
variable {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P]
variable [Module.Projective Rᵐᵒᵖ P]

/-- Every element of a projective right module over a ring with a proper
two-sided ideal whose complement consists of units lies in a finite free direct
summand.  The maps `f` and `g` exhibit the range of `f` as that summand. -/
theorem exists_fin_rightFree_split_containing
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤)
    (hunit : ∀ r ∉ I, IsUnit r) (x : P) :
    ∃ (n : ℕ) (f : (Fin n → R) →ₗ[Rᵐᵒᵖ] P)
      (g : P →ₗ[Rᵐᵒᵖ] (Fin n → R)),
      g.comp f = LinearMap.id ∧ x ∈ LinearMap.range f := by
  classical
  obtain ⟨F, hFgroup, hFmodule, hFfree, i, s, hs⟩ :=
    Module.Projective.iff_split.mp (inferInstance : Module.Projective Rᵐᵒᵖ P)
  let _ : AddCommMonoid F := hFgroup
  let _ : Module Rᵐᵒᵖ F := hFmodule
  let _ : AddCommGroup F := Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ
  let _ : Module.Free Rᵐᵒᵖ F := hFfree
  let ι := Module.Free.ChooseBasisIndex Rᵐᵒᵖ F
  let b₀ : Basis ι Rᵐᵒᵖ F := Module.Free.chooseBasis Rᵐᵒᵖ F
  let xF : F := i x
  obtain ⟨b, hb⟩ := Module.Basis.exists_hasMinimalSupport b₀ xF
  let e : F →ₗ[Rᵐᵒᵖ] F := i.comp s
  have hex : e xF = xF := by
    change i (s (i x)) = i x
    exact congrArg i (LinearMap.congr_fun hs x)
  let σ := {j : ι // j ∈ (b.repr xF).support}
  let inc : (σ → R) →ₗ[Rᵐᵒᵖ] F :=
    (Fintype.linearCombination Rᵐᵒᵖ (fun j : σ ↦ b j.1)).comp
      (Module.rightFreeCoordEquiv R σ).symm.toLinearMap
  let out : F →ₗ[Rᵐᵒᵖ] (σ → R) :=
    (Module.rightFreeCoordEquiv R σ).toLinearMap.comp
      (LinearMap.pi fun j : σ ↦ b.coord j.1)
  let block : Module.End Rᵐᵒᵖ (σ → R) := out.comp (e.comp inc)
  have hinc_single (j : σ) : inc (Pi.single j 1) = b j.1 := by
    have hcoord :
        (Module.rightFreeCoordEquiv R σ).symm (Pi.single j 1) =
          Pi.single j (1 : Rᵐᵒᵖ) := by
      ext k
      by_cases h : k = j <;> simp [h]
    change (Fintype.linearCombination Rᵐᵒᵖ (fun j : σ ↦ b j.1))
      ((Module.rightFreeCoordEquiv R σ).symm (Pi.single j 1)) = b j.1
    rw [hcoord, Fintype.linearCombination_apply_single, one_smul]
  have hblock_single (k : σ) :
      block (Pi.single k 1) =
        fun j : σ ↦ MulOpposite.unop (b.coord j.1 (e (b k.1))) := by
    ext j
    simp [block, out, hinc_single]
  have hmatrix (j k : σ) :
      Module.rightEndomorphismMatrixEquiv R σ block j k =
        MulOpposite.unop (b.coord j.1 (e (b k.1))) := by
    rw [Module.rightEndomorphismMatrixEquiv_apply, hblock_single]
  have hmem_of_not_isUnit {z : Rᵐᵒᵖ} (hz : ¬ IsUnit z) : z.unop ∈ I := by
    by_contra hmem
    apply hz
    simpa using (isUnit_op.mpr (hunit z.unop hmem))
  have hoff (j k : σ) (hjk : j ≠ k) :
      MulOpposite.unop (b.coord j.1 (e (b k.1))) ∈ I := by
    apply hmem_of_not_isUnit
    apply hb.not_isUnit_coord_comp_apply_of_ne e hex k.2
    exact fun h ↦ hjk (Subtype.ext h.symm)
  have hdiag (j : σ) :
      1 - MulOpposite.unop (b.coord j.1 (e (b j.1))) ∈ I := by
    have h := hmem_of_not_isUnit
      (hb.not_isUnit_one_sub_coord_comp_apply e hex j.2)
    simpa using h
  have hquasi : I.IsQuasiregular :=
    (I.isQuasiregular_iff_forall_isUnit_one_add).mpr (by
      intro r hr
      apply hunit (1 + r)
      intro hone
      have hmem := I.add_mem hone (I.neg_mem hr)
      exact hI (I.eq_top (by simpa using hmem)))
  have hquotient :
      (Ideal.Quotient.mk I.asIdeal).mapMatrix
          (Module.rightEndomorphismMatrixEquiv R σ block) = 1 := by
    ext j k
    change Ideal.Quotient.mk I.asIdeal
      (Module.rightEndomorphismMatrixEquiv R σ block j k) =
        (1 : Matrix σ σ (R ⧸ I.asIdeal)) j k
    rw [hmatrix]
    by_cases hjk : j = k
    · subst k
      have hz : Ideal.Quotient.mk I.asIdeal
          (1 - MulOpposite.unop (b.coord j.1 (e (b j.1)))) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (hdiag j)
      have hz' : 1 - Ideal.Quotient.mk I.asIdeal
          (MulOpposite.unop (b.coord j.1 (e (b j.1)))) = 0 := by
        simpa using hz
      simpa [Matrix.one_apply] using (sub_eq_zero.mp hz').symm
    · have hz : Ideal.Quotient.mk I.asIdeal
          (MulOpposite.unop (b.coord j.1 (e (b k.1)))) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (hoff j k hjk)
      simpa [Matrix.one_apply, hjk] using hz
  have hblock : Function.Bijective block :=
    Module.rightEndomorphism_bijective_of_mapMatrix_quotient_isUnit
      R σ I hquasi block (by rw [hquotient]; exact isUnit_one)
  let blockEquiv : (σ → R) ≃ₗ[Rᵐᵒᵖ] (σ → R) :=
    LinearEquiv.ofBijective block hblock
  let f : (σ → R) →ₗ[Rᵐᵒᵖ] P := s.comp inc
  let g : P →ₗ[Rᵐᵒᵖ] (σ → R) :=
    blockEquiv.symm.toLinearMap.comp (out.comp i)
  have hgf : g.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro v
    change blockEquiv.symm (out (i (s (inc v)))) = v
    have hv : out (i (s (inc v))) = block v := rfl
    rw [hv]
    exact blockEquiv.symm_apply_apply v
  have hinc_out : inc (out xF) = xF := by
    change ∑ j : σ, (b.repr xF j.1) • b j.1 = xF
    calc
      _ = ∑ k ∈ (b.repr xF).support, (b.repr xF k) • b k := by
        rw [← Finset.attach_eq_univ]
        exact Finset.sum_attach (b.repr xF).support
          (fun k ↦ (b.repr xF k) • b k)
      _ = xF := by
        simpa [Finsupp.linearCombination_apply, Finsupp.sum] using
          (b.linearCombination_repr xF)
  let reindex : (Fin (Fintype.card σ) → R) ≃ₗ[Rᵐᵒᵖ] (σ → R) :=
    LinearEquiv.piCongrLeft Rᵐᵒᵖ (fun _ : σ ↦ R) (Fintype.equivFin σ).symm
  refine ⟨Fintype.card σ, f.comp reindex.toLinearMap,
    reindex.symm.toLinearMap.comp g, ?_, ?_⟩
  · apply LinearMap.ext
    intro v
    change reindex.symm (g (f (reindex v))) = v
    have hv := LinearMap.congr_fun hgf (reindex v)
    change g (f (reindex v)) = reindex v at hv
    rw [hv, reindex.symm_apply_apply]
  · refine ⟨reindex.symm (out xF), ?_⟩
    change f (reindex (reindex.symm (out xF))) = x
    rw [reindex.apply_symm_apply]
    change s (inc (out xF)) = x
    rw [hinc_out]
    exact LinearMap.congr_fun hs x

end Module.Projective
