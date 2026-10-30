/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism, Iris
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import StableRange.Module.SplitSurjective
public import Mathlib.LinearAlgebra.Projection

/-!
# Projective summands and kernels of split linear maps

A section of a linear map gives a projection onto its kernel. This projection
retracts the kernel inclusion. A split kernel is finite when the source is
finite, and projective when the source is projective. These independent closure
statements require no finiteness or projectivity assumption on the target.
Only the source needs additive inverses; the target may be an additive monoid.

The range of an idempotent endomorphism of a projective module is projective,
using Mathlib's projection onto its original range. This range closure needs
only a semiring and an additive monoid.

The splitting and projective-retract arguments use Mathlib's projective-module
API. The split-kernel projection and retraction formalization follow the earlier
work of Prism in Formal Frontier.

## References

* Mathlib, `Mathlib.LinearAlgebra.Projection`, `Mathlib.Algebra.Module.Projective`,
  `Mathlib.Algebra.Module.Submodule.Range`, and
  `Mathlib.RingTheory.Finiteness.Basic`.
* Prism (Formal Frontier), split-kernel projections and projective complements.
-/

@[expose] public section

universe uR uA uM

namespace LinearMap

/-- Projection from a split module onto the kernel of its retraction. -/
def splitKernelProjection
    {R : Type uR} [Semiring R]
    {A : Type uA} [AddCommMonoid A] [Module R A]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (i : A →ₗ[R] M) (r : M →ₗ[R] A)
    (h : r.comp i = LinearMap.id) : M →ₗ[R] LinearMap.ker r :=
  LinearMap.codRestrict (LinearMap.ker r)
    (LinearMap.id - i.comp r) fun x ↦ by
      rw [LinearMap.mem_ker]
      change r (x - i (r x)) = 0
      apply LinearMap.injective_of_comp_eq_id i r h
      rw [map_zero]
      change (i.comp r) (x - i (r x)) = 0
      rw [map_sub, show (i.comp r) (i (r x)) = (i.comp r) x by
        change i (r (i (r x))) = i (r x)
        rw [show r (i (r x)) = r x by
          rw [← LinearMap.comp_apply, h, LinearMap.id_apply]], sub_self]

/-- The split-kernel projection subtracts the image of the retracted coordinate. -/
@[simp] theorem splitKernelProjection_apply
    {R : Type uR} [Semiring R]
    {A : Type uA} [AddCommMonoid A] [Module R A]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (i : A →ₗ[R] M) (r : M →ₗ[R] A)
    (h : r.comp i = LinearMap.id) (x : M) :
    ((splitKernelProjection i r h x : LinearMap.ker r) : M) = x - i (r x) :=
  rfl

/-- The split-kernel projection retracts the kernel subtype. -/
theorem splitKernelProjection_comp_subtype
    {R : Type uR} [Semiring R]
    {A : Type uA} [AddCommMonoid A] [Module R A]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (i : A →ₗ[R] M) (r : M →ₗ[R] A)
    (h : r.comp i = LinearMap.id) :
    (splitKernelProjection i r h).comp (LinearMap.ker r).subtype =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change x - i (r x) = x
  rw [LinearMap.mem_ker.mp x.2, map_zero, sub_zero]

/-- Pairing the split-kernel projection with the retraction gives the inverse of
the kernel-product equivalence for the same specified section. -/
theorem splitKernelProjection_prod_eq_kerProdEquivOfRightInverse_symm
    {R : Type uR} [Semiring R]
    {A : Type uA} [AddCommMonoid A] [Module R A]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] A) (g : A →ₗ[R] M)
    (hfg : f.comp g = LinearMap.id) :
    (splitKernelProjection g f hfg).prod f =
      (kerProdEquivOfRightInverse f g hfg).symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · apply Subtype.ext
    exact (splitKernelProjection_apply g f hfg x).trans
      (kerProdEquivOfRightInverse_symm_fst f g hfg x).symm
  · exact (kerProdEquivOfRightInverse_symm_snd f g hfg x).symm

/-- The split-kernel projection fixes each element of the kernel. -/
@[simp] theorem splitKernelProjection_apply_coe
    {R : Type uR} [Semiring R]
    {A : Type uA} [AddCommMonoid A] [Module R A]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (i : A →ₗ[R] M) (r : M →ₗ[R] A)
    (h : r.comp i = LinearMap.id) (x : LinearMap.ker r) :
    splitKernelProjection i r h (x : M) = x :=
  LinearMap.congr_fun (splitKernelProjection_comp_subtype i r h) x

/-- The kernel of a retraction from a finite module is finite. -/
theorem finite_splitKernel
    {R : Type uR} [Semiring R]
    {A : Type uA} [AddCommMonoid A] [Module R A]
    {M : Type uM} [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (i : A →ₗ[R] M) (r : M →ₗ[R] A)
    (h : r.comp i = LinearMap.id) :
    Module.Finite R (LinearMap.ker r) :=
  Module.Finite.of_surjective (splitKernelProjection i r h)
    (LinearMap.surjective_of_comp_eq_id (LinearMap.ker r).subtype
      (splitKernelProjection i r h) (splitKernelProjection_comp_subtype i r h))

/-- The kernel of a retraction from a projective module is projective. -/
theorem projective_splitKernel
    {R : Type uR} [Semiring R]
    {A : Type uA} [AddCommMonoid A] [Module R A]
    {M : Type uM} [AddCommGroup M] [Module R M]
    [Module.Projective R M]
    (i : A →ₗ[R] M) (r : M →ₗ[R] A)
    (h : r.comp i = LinearMap.id) :
    Module.Projective R (LinearMap.ker r) :=
  Module.Projective.of_split (LinearMap.ker r).subtype
    (splitKernelProjection i r h)
    (splitKernelProjection_comp_subtype i r h)

end LinearMap

namespace Module.Projective

/-- The range of an idempotent endomorphism of a projective module is projective. -/
theorem range_of_isIdempotentElem
    {S : Type uR} [Semiring S]
    {P : Type uM} [AddCommMonoid P] [Module S P]
    [Module.Projective S P]
    (e : Module.End S P) (he : IsIdempotentElem e) :
    Module.Projective S e.range := by
  have hproj : LinearMap.IsProj e.range e :=
    (LinearMap.isProj_range_iff_isIdempotentElem e).mpr he
  apply Module.Projective.of_split e.range.subtype hproj.codRestrict
  exact LinearMap.ext fun x => hproj.codRestrict_apply_cod x

end Module.Projective
