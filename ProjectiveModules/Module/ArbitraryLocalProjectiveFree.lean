/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import ProjectiveModules.Module.CountableLocalProjectiveFree
public import ProjectiveModules.Module.TransfiniteRangeBasis

/-!
# Arbitrary projective right modules over local rings

This file proves the arbitrary-rank form of Kaplansky's theorem for projective
right modules over a possibly noncommutative ring with a proper two-sided ideal
whose complement consists of units.

The proof chooses a free module containing the projective module as a direct
summand and transports the resulting idempotent to standard free coordinates.
The countable invariant-coordinate filtration has projective, countably
generated split increments, hence free increments.  Transfinite range assembly
then gives a basis of the idempotent range, which is linearly equivalent to the
original projective module.
-/

@[expose] public section

universe uR uP

namespace Module.Projective

variable {R : Type uR} [Ring R]
variable {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P]

/-- Every arbitrary-rank projective right module over a possibly
noncommutative ring with a proper two-sided ideal whose complement consists of
units is free. -/
theorem free_of_isUnit_compl_arbitraryRank
    [Module.Projective Rᵐᵒᵖ P]
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤)
    (hunit : ∀ r ∉ I, IsUnit r) :
    Module.Free Rᵐᵒᵖ P := by
  classical
  obtain ⟨M, hMmonoid, hMmodule, hMfree, i, s, hs⟩ :=
    (Module.Projective.iff_split (R := Rᵐᵒᵖ) (P := P)).mp inferInstance
  let _ : AddCommMonoid M := hMmonoid
  let _ : Module Rᵐᵒᵖ M := hMmodule
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ
  let _ : Module.Free Rᵐᵒᵖ M := hMfree
  let κ := Module.Free.ChooseBasisIndex Rᵐᵒᵖ M
  let b : Basis κ Rᵐᵒᵖ M := Module.Free.chooseBasis Rᵐᵒᵖ M
  let q : (κ →₀ Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] (κ →₀ Rᵐᵒᵖ) :=
    b.repr.toLinearMap.comp (i.comp (s.comp b.repr.symm.toLinearMap))
  have hsi (x : P) : s (i x) = x := LinearMap.congr_fun hs x
  have hq : IsIdempotentElem q := by
    rw [isIdempotentElem_iff]
    apply LinearMap.ext
    intro x
    change q (q x) = q x
    simp only [q, LinearMap.comp_apply]
    simp [hsi]
  let F : LinearMap.CountableInvariantCoordinateFiltration q :=
    Classical.choice q.exists_countable_invariant_coordinate_filtration
  have hfreeIncrement (j : κ) : Module.Free Rᵐᵒᵖ (F.increment j) := by
    let _ : AddCommGroup (F.increment j) :=
      Module.addCommMonoidToAddCommGroup Rᵐᵒᵖ
    let _ : Module.Projective Rᵐᵒᵖ (F.increment j) :=
      F.increment_projective hq j
    exact Module.Projective.free_of_countablyGenerated I hI hunit
      (F.increment_countablyGenerated hq j)
  have hfreeRange : Module.Free Rᵐᵒᵖ (LinearMap.range q) :=
    F.range_free_of_free_increments hq hfreeIncrement
  let j : P →ₗ[Rᵐᵒᵖ] (κ →₀ Rᵐᵒᵖ) := b.repr.toLinearMap.comp i
  have hj_mem (x : P) : j x ∈ LinearMap.range q := by
    refine ⟨j x, ?_⟩
    simp only [q, j, LinearMap.comp_apply]
    simp [hsi]
  let e : P →ₗ[Rᵐᵒᵖ] LinearMap.range q :=
    LinearMap.codRestrict (LinearMap.range q) j hj_mem
  have he_injective : Function.Injective e := by
    intro x y hxy
    have hval : j x = j y := congrArg Subtype.val hxy
    have h := congrArg (fun z : κ →₀ Rᵐᵒᵖ ↦ s (b.repr.symm z)) hval
    simpa [j, hsi] using h
  have he_surjective : Function.Surjective e := by
    rintro ⟨y, z, hz⟩
    refine ⟨s (b.repr.symm z), Subtype.ext ?_⟩
    change j (s (b.repr.symm z)) = y
    change q z = y
    exact hz
  exact Module.Free.of_equiv' hfreeRange
    (LinearEquiv.ofBijective e ⟨he_injective, he_surjective⟩).symm

end Module.Projective
