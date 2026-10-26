/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import ProjectiveModules.Topology.Projective

/-!
# Splitting a continuous linear map with a right inverse

A continuous linear section gives a product decomposition into the target and the
kernel, over a semiring, when the source has continuous additive group operations.
For a projective target with its given module topology, continuous addition on the
source suffices; neither result requires additive inverses in the target.

The arbitrary-section construction generalizes Mathlib's
`ContinuousLinearEquiv.equivOfRightInverse`; the two constructions agree over a
ring whenever the latter is defined.
-/

@[expose] public section

universe uR uM uN

namespace ContinuousLinearMap

private def linearEquivProdKerOfRightInverse
    {R : Type uR} {M : Type uM} {N : Type uN}
    [Semiring R] [AddCommGroup M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (s : N →ₗ[R] M)
    (hs : Function.RightInverse s f) : M ≃ₗ[R] (N × f.ker) := by
  let q : M →ₗ[R] M := LinearMap.id - s.comp f
  have hq (x : M) : f (q x) = 0 := by
    apply hs.injective
    rw [map_zero]
    change (s.comp f) (x - s (f x)) = 0
    rw [map_sub]
    change s (f x) - s (f (s (f x))) = 0
    rw [hs, sub_self]
  let t : M →ₗ[R] f.ker := q.codRestrict f.ker hq
  let a : M →ₗ[R] (N × f.ker) := f.prod t
  let b : N × f.ker →ₗ[R] M :=
    f.ker.subtype.comp (LinearMap.snd R N f.ker) +
      s.comp (LinearMap.fst R N f.ker)
  have hk (k : f.ker) : f k = 0 := k.property
  exact LinearEquiv.ofLinearMap a b
    (by
      apply LinearMap.ext
      intro z
      apply Prod.ext
      · change f ((z.2 : M) + s z.1) = z.1
        rw [map_add, hk, hs, zero_add]
      · apply Subtype.ext
        change (z.2 : M) + s z.1 - s (f ((z.2 : M) + s z.1)) = z.2
        rw [map_add, hk, hs, zero_add, add_sub_cancel_right])
    (by
      apply LinearMap.ext
      intro x
      change x - s (f x) + s (f x) = x
      exact sub_add_cancel _ _)

private theorem linearRightInverseSplittingLaws
    {R : Type uR} {M : Type uM} {N : Type uN}
    [Semiring R] [AddCommGroup M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (s : N →ₗ[R] M) (hs : Function.RightInverse s f) :
    (∀ x, f (x - s (f x)) = 0) ∧
      (∀ x, x - s (f x) + s (f x) = x) ∧
      (∀ z : N × f.ker,
        f ((z.2 : M) + s z.1) = z.1 ∧
          (z.2 : M) + s z.1 - s (f ((z.2 : M) + s z.1)) = z.2) := by
  let e := linearEquivProdKerOfRightInverse f s hs
  refine ⟨(fun x ↦ (e x).2.property), e.left_inv, ?_⟩
  intro z
  exact ⟨congrArg Prod.fst (e.right_inv z),
    congrArg (fun w : N × f.ker ↦ (w.2 : M)) (e.right_inv z)⟩

section Semiring

variable {R : Type uR} {M : Type uM} {N : Type uN}
  [Semiring R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommMonoid N] [Module R N] [TopologicalSpace N]
  [IsTopologicalAddGroup M]

/-- The product decomposition associated to a continuous linear right inverse.
The coordinates are `f x` and `x - s (f x)`; this construction depends on the given
section `s`. No continuity of the target's operations is needed. -/
def equivProdKerOfRightInverse (f : M →L[R] N) (s : N →L[R] M)
    (hs : Function.RightInverse s f) : M ≃L[R] (N × f.ker) := by
  let q : M →L[R] M :=
    { toLinearMap := LinearMap.id - s.toLinearMap.comp f.toLinearMap
      cont := continuous_id.sub (s.continuous.comp f.continuous) }
  let t : M →L[R] f.ker := q.codRestrict f.ker (by
    intro x
    exact (linearRightInverseSplittingLaws f.toLinearMap s.toLinearMap hs).1 x)
  let a : M →L[R] (N × f.ker) := f.prod t
  let b : N × f.ker →L[R] M :=
    f.ker.subtypeL.comp (ContinuousLinearMap.snd R N f.ker) +
      s.comp (ContinuousLinearMap.fst R N f.ker)
  exact
    { toLinearEquiv :=
        { a.toLinearMap with
          invFun := b
          left_inv := by
            intro x
            exact (linearRightInverseSplittingLaws f.toLinearMap s.toLinearMap hs).2.1 x
          right_inv := by
            intro z
            apply Prod.ext
            · exact ((linearRightInverseSplittingLaws f.toLinearMap s.toLinearMap hs).2.2 z).1
            · apply Subtype.ext
              exact ((linearRightInverseSplittingLaws f.toLinearMap s.toLinearMap hs).2.2 z).2 }
      continuous_toFun := a.continuous
      continuous_invFun := b.continuous }

@[simp]
theorem fst_equivProdKerOfRightInverse (f : M →L[R] N) (s : N →L[R] M)
    (hs : Function.RightInverse s f) (x : M) :
    (f.equivProdKerOfRightInverse s hs x).1 = f x := rfl

@[simp]
theorem coe_snd_equivProdKerOfRightInverse (f : M →L[R] N) (s : N →L[R] M)
    (hs : Function.RightInverse s f) (x : M) :
    ((f.equivProdKerOfRightInverse s hs x).2 : M) = x - s (f x) := rfl

@[simp]
theorem equivProdKerOfRightInverse_symm_apply (f : M →L[R] N) (s : N →L[R] M)
    (hs : Function.RightInverse s f) (z : N × f.ker) :
    (f.equivProdKerOfRightInverse s hs).symm z = (z.2 : M) + s z.1 := rfl

end Semiring

section Ring

variable {R : Type uR} {M : Type uM} {N : Type uN}
  [Ring R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]
  [IsTopologicalAddGroup M]

/-- Over a ring, the semiring splitting agrees with Mathlib's right-inverse splitting. -/
theorem equivProdKerOfRightInverse_eq_equivOfRightInverse
    (f : M →L[R] N) (s : N →L[R] M) (hs : Function.RightInverse s f) :
    f.equivProdKerOfRightInverse s hs =
      ContinuousLinearEquiv.equivOfRightInverse (R := R) f s hs := by
  apply DFunLike.ext
  intro x
  apply Prod.ext
  · simp only [fst_equivProdKerOfRightInverse,
      ContinuousLinearEquiv.fst_equivOfRightInverse]
  · apply Subtype.ext
    simp only [coe_snd_equivProdKerOfRightInverse,
      ContinuousLinearEquiv.snd_equivOfRightInverse]

end Ring

/-- A surjection onto a projective module with the module topology splits as the product
of its kernel and its target, with the surjection as the second coordinate. Only
continuous addition and scalar multiplication are required on the source. -/
theorem exists_equiv_ker_prod
    {R : Type uR} {M : Type uM} {N : Type uN}
    [Semiring R] [TopologicalSpace R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [ContinuousAdd M] [ContinuousSMul R M]
    [Module.Projective R N] [IsModuleTopology R N]
    (f : M →L[R] N) (hf : Function.Surjective f) :
    ∃ e : M ≃L[R] (f.ker × N), ∀ x, (e x).2 = f x := by
  obtain ⟨s, hs⟩ := projective_lifting_property f (ContinuousLinearMap.id R N) hf
  have hfs (x : N) : f (s x) = x := DFunLike.congr_fun hs x
  let e := linearEquivProdKerOfRightInverse f.toLinearMap s.toLinearMap hfs
  let ns : N →L[R] M :=
    { toLinearMap := -s.toLinearMap
      cont := IsModuleTopology.continuous_of_linearMap (-s.toLinearMap) }
  let q : M →L[R] M :=
    { toLinearMap := LinearMap.id - s.toLinearMap.comp f.toLinearMap
      cont := by
        change Continuous (fun x : M ↦ x - s (f x))
        have h := continuous_id.add (ns.continuous.comp f.continuous)
        change Continuous (fun x : M ↦ x + -(s (f x))) at h
        simpa only [sub_eq_add_neg] using h }
  let t : M →L[R] f.ker := q.codRestrict f.ker (fun x ↦ (e x).2.property)
  let a : M →L[R] (N × f.ker) := f.prod t
  let b : N × f.ker →L[R] M :=
    f.ker.subtypeL.comp (ContinuousLinearMap.snd R N f.ker) +
      s.comp (ContinuousLinearMap.fst R N f.ker)
  let ce : M ≃L[R] (N × f.ker) :=
    { e with
      continuous_toFun := a.continuous
      continuous_invFun := b.continuous }
  refine ⟨ce.trans (ContinuousLinearEquiv.prodComm R N f.ker), ?_⟩
  intro x
  rfl

end ContinuousLinearMap
