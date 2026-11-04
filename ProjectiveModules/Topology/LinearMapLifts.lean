/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Logic.Equiv.Prod
public import ProjectiveModules.Topology.Splitting

/-!
# Continuous linear lifts along a split map

A given continuous linear right inverse identifies the lifts of a continuous linear map
with continuous linear maps into the kernel. This is an ordinary equivalence: neither
the space of continuous linear maps nor the fibre is equipped with a scalar-module
structure. Only the original source needs continuous additive group operations.

The construction postcomposes with `ContinuousLinearMap.equivProdKerOfRightInverse`
and uses the ordinary equivalences for maps into a product and for its fixed-first-
coordinate fibre. The coordinate laws also classify all continuous linear right inverses.
-/

@[expose] public section

universe uR uE uF uG

namespace ContinuousLinearMap

variable {R : Type uR} {E : Type uE} {F : Type uF} {G : Type uG}
  [Semiring R]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [AddCommMonoid F] [TopologicalSpace F]
  [AddCommMonoid G] [TopologicalSpace G]
  [Module R E] [Module R F] [Module R G]

variable (f : E →L[R] F) (s : F →L[R] E) (hs : Function.RightInverse s f)

/-- A continuous linear section parametrizes all lifts of `h` by continuous linear maps
into the original kernel of `f`. No scalar-module structure on a space of maps is used. -/
noncomputable def liftsEquivKerOfRightInverse (h : G →L[R] F) :
    {l : G →L[R] E // f.comp l = h} ≃ (G →L[R] f.ker) := by
  let e : (G →L[R] E) ≃ (G →L[R] F) × (G →L[R] f.ker) :=
    (ContinuousLinearEquiv.arrowCongrEquiv (ContinuousLinearEquiv.refl R G)
      (f.equivProdKerOfRightInverse s hs)).trans
      (ContinuousLinearMap.prodEquiv (R := R) (M := G) (M₂ := F) (M₃ := f.ker)).symm
  letI : Unique {g : G →L[R] F // g = h} :=
    { default := ⟨h, rfl⟩
      uniq := fun g => Subtype.ext g.property }
  exact (e.subtypeEquiv (p := fun l => f.comp l = h) (q := fun p => p.1 = h)
    (fun l => by
      have he : (e l).1 = f.comp l := by
        apply ContinuousLinearMap.ext
        intro x
        exact f.fst_equivProdKerOfRightInverse s hs (l x)
      rw [he])).trans
    ((Equiv.prodSubtypeFstEquivSubtypeProd
      (α := G →L[R] F) (β := G →L[R] f.ker) (p := fun g => g = h)).trans
      (Equiv.uniqueProd (G →L[R] f.ker) {g : G →L[R] F // g = h}))

/-- The parameter of a lift is its residual from the lift selected by `s`. -/
@[simp]
theorem coe_liftsEquivKerOfRightInverse_apply (h : G →L[R] F)
    (l : {l : G →L[R] E // f.comp l = h}) (x : G) :
    ((f.liftsEquivKerOfRightInverse s hs h l) x : E) = l.val x - s (h x) := by
  change ((f.equivProdKerOfRightInverse s hs (l.val x)).2 : E) = _
  rw [coe_snd_equivProdKerOfRightInverse]
  have hl : f (l.val x) = h x :=
    congrArg (fun g : G →L[R] F => g x) l.property
  rw [hl]

/-- The inverse parametrization adds a kernel-valued map to the selected lift. -/
@[simp]
theorem liftsEquivKerOfRightInverse_symm_apply (h : G →L[R] F)
    (k : G →L[R] f.ker) (x : G) :
    ((f.liftsEquivKerOfRightInverse s hs h).symm k).val x = s (h x) + (k x : E) := by
  change (f.equivProdKerOfRightInverse s hs).symm (h x, k x) = _
  rw [equivProdKerOfRightInverse_symm_apply, add_comm]

/-- The whole inverse map, expressed using the original continuous kernel inclusion. -/
theorem liftsEquivKerOfRightInverse_symm_coe (h : G →L[R] F)
    (k : G →L[R] f.ker) :
    ((f.liftsEquivKerOfRightInverse s hs h).symm k).val =
      s.comp h + f.ker.subtypeL.comp k := by
  apply ContinuousLinearMap.ext
  intro x
  exact f.liftsEquivKerOfRightInverse_symm_apply s hs h k x

/-- The lift selected by the given section has zero parameter. -/
@[simp]
theorem liftsEquivKerOfRightInverse_comp (h : G →L[R] F) :
    f.liftsEquivKerOfRightInverse s hs h
      ⟨s.comp h, by
        apply ContinuousLinearMap.ext
        intro x
        exact hs (h x)⟩ = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change ((f.liftsEquivKerOfRightInverse s hs h
    ⟨s.comp h, by
      apply ContinuousLinearMap.ext
      intro y
      exact hs (h y)⟩) x : E) = 0
  rw [coe_liftsEquivKerOfRightInverse_apply]
  exact sub_self (s (h x))

/-- A parameter determines a lift uniquely, with the displayed reconstruction formula. -/
theorem liftsEquivKerOfRightInverse_eq_iff (h : G →L[R] F)
    (l : {l : G →L[R] E // f.comp l = h}) (k : G →L[R] f.ker) :
    f.liftsEquivKerOfRightInverse s hs h l = k ↔
      l.val = s.comp h + f.ker.subtypeL.comp k := by
  let e := f.liftsEquivKerOfRightInverse s hs h
  constructor
  · intro hl
    have hpre : l = e.symm k := by
      apply e.injective
      exact hl.trans (e.apply_symm_apply k).symm
    exact (congrArg Subtype.val hpre).trans
      (f.liftsEquivKerOfRightInverse_symm_coe s hs h k)
  · intro hl
    have hpre : l = e.symm k :=
      Subtype.ext (hl.trans (f.liftsEquivKerOfRightInverse_symm_coe s hs h k).symm)
    calc
      e l = e (e.symm k) := congrArg e hpre
      _ = k := e.apply_symm_apply k

include hs

/-- All continuous linear right inverses are obtained uniquely by adding a continuous
kernel-valued map to the given right inverse. This is the lift parametrization at `h = id`. -/
theorem rightInverse_iff_existsUnique_eq_add (t : F →L[R] E) :
    Function.RightInverse t f ↔ ∃! k : F →L[R] f.ker, t = s + f.ker.subtypeL.comp k := by
  constructor
  · intro ht
    let l : {l : F →L[R] E // f.comp l = ContinuousLinearMap.id R F} :=
      ⟨t, by
        apply ContinuousLinearMap.ext
        intro x
        exact ht x⟩
    refine ⟨f.liftsEquivKerOfRightInverse s hs (ContinuousLinearMap.id R F) l, ?_, ?_⟩
    · have hr := (f.liftsEquivKerOfRightInverse_eq_iff s hs
          (ContinuousLinearMap.id R F) l
          (f.liftsEquivKerOfRightInverse s hs (ContinuousLinearMap.id R F) l)).mp rfl
      simpa only [comp_id] using hr
    · intro k hk
      have hparam := (f.liftsEquivKerOfRightInverse_eq_iff s hs
        (ContinuousLinearMap.id R F) l k).mpr (by simpa only [comp_id] using hk)
      exact hparam.symm
  · rintro ⟨k, hk, _⟩
    let l : {l : F →L[R] E // f.comp l = ContinuousLinearMap.id R F} :=
      (f.liftsEquivKerOfRightInverse s hs (ContinuousLinearMap.id R F)).symm k
    have hl : l.val = s + f.ker.subtypeL.comp k := by
      simpa only [comp_id] using
        f.liftsEquivKerOfRightInverse_symm_coe s hs (ContinuousLinearMap.id R F) k
    have ht : t = l.val := hk.trans hl.symm
    intro x
    rw [ht]
    exact congrArg (fun g : F →L[R] F => g x) l.property

end ContinuousLinearMap
