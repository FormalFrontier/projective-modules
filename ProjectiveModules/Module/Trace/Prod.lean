/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Finiteness.Prod
public import ProjectiveModules.Module.Trace.Basic

/-!
# Finite-projective trace on products

The contraction trace is additive on products of finite projective modules over
a commutative semiring. Inclusion and projection maps identify diagonal blocks
with their factor endomorphisms, while off-diagonal blocks have trace zero.
The off-diagonal formulas require finite projectivity only of the product.
No basis or additive inverses are required.

The existing product and coproduct constructors represent an arbitrary block
endomorphism as `(f.prod k).coprod (h.prod g)`, sending `(x, y)` to
`(f x + h y, k x + g y)`. For finite-projective factors, its trace is the
sum of the diagonal traces, without introducing a separate block-map construction.

## References

The contraction and dual tensor–Hom formalization is by Oliver Nash and Antoine
Labelle in `Mathlib.LinearAlgebra.Contraction`. The product-map formalization is
by Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov and Eric Wieser
in `Mathlib.LinearAlgebra.Prod`. Product projectivity is formalized by Kevin
Buzzard and Antoine Labelle in `Mathlib.Algebra.Module.Projective`, and product
finiteness by Johan Commelin in `Mathlib.RingTheory.Finiteness.Prod`.

The finite-free product-trace formulas are from the formalization by Johannes
Hölzl, Patrick Massot, Casper Putz, Anne Baanen and Antoine Labelle in
`Mathlib.LinearAlgebra.Trace`.
-/

@[expose] public section

universe uR uM uN

open scoped TensorProduct

namespace LinearMap

variable (R : Type uR) [CommSemiring R]
variable (M : Type uM) [AddCommMonoid M] [Module R M]
variable (N : Type uN) [AddCommMonoid N] [Module R N]

section FiniteProjectiveFactors

variable [Module.Finite R M] [Module.Projective R M]
variable [Module.Finite R N] [Module.Projective R N]

private theorem traceOfFiniteProjective_prodMap_zero (f : M →ₗ[R] M) :
    traceOfFiniteProjective R (M × N) (prodMap f (0 : N →ₗ[R] N)) =
      traceOfFiniteProjective R M f := by
  have h (t : Module.Dual R M ⊗[R] M) :
      traceOfFiniteProjective R (M × N)
          (prodMap (dualTensorHom R M M t) (0 : N →ₗ[R] N)) =
        traceOfFiniteProjective R M (dualTensorHom R M M t) := by
    induction t using TensorProduct.inductionOn with
    | tmul φ x =>
      simp only [dualTensorHom_prodMap_zero, traceOfFiniteProjective_dualTensorHom,
        contractLeft_apply, comp_apply, fst_apply, inl_apply]
    | add t₁ t₂ ht₁ ht₂ =>
      have hadd := prodMap_add (dualTensorHom R M M t₁) (dualTensorHom R M M t₂)
        (0 : N →ₗ[R] N) (0 : N →ₗ[R] N)
      simp only [add_zero] at hadd
      rw [(dualTensorHom R M M).map_add, hadd,
        (traceOfFiniteProjective R (M × N)).map_add,
        (traceOfFiniteProjective R M).map_add, ht₁, ht₂]
  simpa only [dualTensorHom_dualTensorHomEquiv_symm] using
    h ((dualTensorHomEquiv R M M).symm f)

private theorem traceOfFiniteProjective_zero_prodMap (g : N →ₗ[R] N) :
    traceOfFiniteProjective R (M × N) (prodMap (0 : M →ₗ[R] M) g) =
      traceOfFiniteProjective R N g := by
  have h (t : Module.Dual R N ⊗[R] N) :
      traceOfFiniteProjective R (M × N)
          (prodMap (0 : M →ₗ[R] M) (dualTensorHom R N N t)) =
        traceOfFiniteProjective R N (dualTensorHom R N N t) := by
    induction t using TensorProduct.inductionOn with
    | tmul φ x =>
      simp only [zero_prodMap_dualTensorHom, traceOfFiniteProjective_dualTensorHom,
        contractLeft_apply, comp_apply, snd_apply, inr_apply]
    | add t₁ t₂ ht₁ ht₂ =>
      have hadd := prodMap_add (0 : M →ₗ[R] M) (0 : M →ₗ[R] M)
        (dualTensorHom R N N t₁) (dualTensorHom R N N t₂)
      simp only [zero_add] at hadd
      rw [(dualTensorHom R N N).map_add, hadd,
        (traceOfFiniteProjective R (M × N)).map_add,
        (traceOfFiniteProjective R N).map_add, ht₁, ht₂]
  simpa only [dualTensorHom_dualTensorHomEquiv_symm] using
    h ((dualTensorHomEquiv R N N).symm g)

/-- The finite-projective trace of a product endomorphism is the sum of the
traces of its two factors. -/
theorem traceOfFiniteProjective_prodMap (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    traceOfFiniteProjective R (M × N) (prodMap f g) =
      traceOfFiniteProjective R M f + traceOfFiniteProjective R N g := by
  have h : prodMap f g =
      prodMap f (0 : N →ₗ[R] N) + prodMap (0 : M →ₗ[R] M) g := by
    simpa only [add_zero, zero_add] using
      prodMap_add f (0 : M →ₗ[R] M) (0 : N →ₗ[R] N) g
  rw [h, (traceOfFiniteProjective R (M × N)).map_add,
    traceOfFiniteProjective_prodMap_zero, traceOfFiniteProjective_zero_prodMap]

/-- The finite-projective trace of the first diagonal block equals the trace
of its endomorphism on the first factor. -/
theorem traceOfFiniteProjective_inl_fst (f : M →ₗ[R] M) :
    traceOfFiniteProjective R (M × N)
        ((inl R M N).comp (f.comp (fst R M N))) =
      traceOfFiniteProjective R M f := by
  have h : (inl R M N).comp (f.comp (fst R M N)) =
      prodMap f (0 : N →ₗ[R] N) := by
    apply LinearMap.ext
    intro x
    simp only [comp_apply, inl_apply, fst_apply, prodMap_apply, zero_apply]
  rw [h, traceOfFiniteProjective_prodMap_zero]

/-- The finite-projective trace of the second diagonal block equals the trace
of its endomorphism on the second factor. -/
theorem traceOfFiniteProjective_inr_snd (g : N →ₗ[R] N) :
    traceOfFiniteProjective R (M × N)
        ((inr R M N).comp (g.comp (snd R M N))) =
      traceOfFiniteProjective R N g := by
  have h : (inr R M N).comp (g.comp (snd R M N)) =
      prodMap (0 : M →ₗ[R] M) g := by
    apply LinearMap.ext
    intro x
    simp only [comp_apply, inr_apply, snd_apply, prodMap_apply, zero_apply]
  rw [h, traceOfFiniteProjective_zero_prodMap]

end FiniteProjectiveFactors

private theorem traceOfFiniteProjective_dualTensorHom_comp
    [Module.Finite R M] [Module.Projective R M]
    (p : M →ₗ[R] N) (t : Module.Dual R N ⊗[R] M) :
    traceOfFiniteProjective R M ((dualTensorHom R N M t).comp p) =
      contractLeft R M (p.dualMap.rTensor M t) := by
  have hcomp : dualTensorHom R M M (p.dualMap.rTensor M t) =
      (dualTensorHom R N M t).comp p := by
    simpa only [comp_apply, lcomp_apply'] using
      congrArg (fun f => f t) (dualTensorHom_comp_rTensor_dualMap (P := M) p)
  rw [← hcomp, traceOfFiniteProjective_dualTensorHom]

section FiniteProjectiveProduct

variable [Module.Finite R (M × N)] [Module.Projective R (M × N)]

/-- The finite-projective trace of an off-diagonal block from the second
factor to the first is zero. -/
theorem traceOfFiniteProjective_inl_snd (h : N →ₗ[R] M) :
    traceOfFiniteProjective R (M × N)
      ((inl R M N).comp (h.comp (snd R M N))) = 0 := by
  let : Module.Finite R N :=
    Module.Finite.of_surjective (snd R M N) snd_surjective
  let : Module.Projective R N :=
    Module.Projective.of_split (inr R M N) (snd R M N) (snd_comp_inr R M N)
  have ht (t : Module.Dual R N ⊗[R] M) :
      traceOfFiniteProjective R (M × N)
        ((inl R M N).comp ((dualTensorHom R N M t).comp (snd R M N))) = 0 := by
    have hpost :
        dualTensorHom R N (M × N) ((inl R M N).lTensor (Module.Dual R N) t) =
          (inl R M N).comp (dualTensorHom R N M t) := by
      simpa only [comp_apply, compRight_apply] using
        congrArg (fun f => f t) (dualTensorHom_comp_lTensor (M := N) (inl R M N))
    rw [← comp_assoc, ← hpost, traceOfFiniteProjective_dualTensorHom_comp]
    clear hpost
    induction t using TensorProduct.inductionOn with
    | tmul φ x =>
        simp only [lTensor_tmul, rTensor_tmul, contractLeft_apply, dualMap_apply,
          inl_apply, snd_apply, map_zero]
    | add t₁ t₂ h₁ h₂ =>
        rw [map_add, map_add, map_add, h₁, h₂, add_zero]
  simpa only [dualTensorHom_dualTensorHomEquiv_symm] using
    ht ((dualTensorHomEquiv R N M).symm h)

/-- The finite-projective trace of an off-diagonal block from the first
factor to the second is zero. -/
theorem traceOfFiniteProjective_inr_fst (k : M →ₗ[R] N) :
    traceOfFiniteProjective R (M × N)
      ((inr R M N).comp (k.comp (fst R M N))) = 0 := by
  let : Module.Finite R M :=
    Module.Finite.of_surjective (fst R M N) fst_surjective
  let : Module.Projective R M :=
    Module.Projective.of_split (inl R M N) (fst R M N) (fst_comp_inl R M N)
  have ht (t : Module.Dual R M ⊗[R] N) :
      traceOfFiniteProjective R (M × N)
        ((inr R M N).comp ((dualTensorHom R M N t).comp (fst R M N))) = 0 := by
    have hpost :
        dualTensorHom R M (M × N) ((inr R M N).lTensor (Module.Dual R M) t) =
          (inr R M N).comp (dualTensorHom R M N t) := by
      simpa only [comp_apply, compRight_apply] using
        congrArg (fun f => f t) (dualTensorHom_comp_lTensor (M := M) (inr R M N))
    rw [← comp_assoc, ← hpost, traceOfFiniteProjective_dualTensorHom_comp]
    clear hpost
    induction t using TensorProduct.inductionOn with
    | tmul φ y =>
        simp only [lTensor_tmul, rTensor_tmul, contractLeft_apply, dualMap_apply,
          inr_apply, fst_apply, map_zero]
    | add t₁ t₂ h₁ h₂ =>
        rw [map_add, map_add, map_add, h₁, h₂, add_zero]
  simpa only [dualTensorHom_dualTensorHomEquiv_symm] using
    ht ((dualTensorHomEquiv R M N).symm k)

end FiniteProjectiveProduct

/-- The finite-projective trace of a block endomorphism is the sum of its diagonal traces. -/
theorem traceOfFiniteProjective_coprod_prod
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (h : N →ₗ[R] M) (k : M →ₗ[R] N) :
    traceOfFiniteProjective R (M × N) ((f.prod k).coprod (h.prod g)) =
      traceOfFiniteProjective R M f + traceOfFiniteProjective R N g := by
  have hBlocks : (f.prod k).coprod (h.prod g) =
      ((LinearMap.inl R M N).comp (f.comp (LinearMap.fst R M N)) +
        (LinearMap.inl R M N).comp (h.comp (LinearMap.snd R M N))) +
      ((LinearMap.inr R M N).comp (k.comp (LinearMap.fst R M N)) +
        (LinearMap.inr R M N).comp (g.comp (LinearMap.snd R M N))) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;>
      simp [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply]
  rw [hBlocks, map_add, map_add, map_add,
    LinearMap.traceOfFiniteProjective_inl_fst,
    LinearMap.traceOfFiniteProjective_inl_snd,
    LinearMap.traceOfFiniteProjective_inr_fst,
    LinearMap.traceOfFiniteProjective_inr_snd, add_zero, zero_add]

end LinearMap
