/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Trace.Basic
public import ProjectiveModules.Module.Trace.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Partial trace over a finite projective tensor factor

The partial trace contracts the first tensor factor of an arbitrary linear map
`M ⊗[R] N →ₗ[R] M ⊗[R] P`, producing a linear map `N →ₗ[R] P`. The scalar
semiring is commutative, only the traced factor `M` is finite projective, and the
untraced factors `N` and `P` are arbitrary semimodules at independent universes.
The construction is itself linear in the entire input map, not only in maps
of pure tensor form.

Currying and flipping the input gives `n ↦ (m ↦ f (m ⊗ₜ[R] n))`. The inverse
of the canonical right tensor–Hom equivalence then gives an element of
`(M →ₗ[R] M) ⊗[R] P`; tensoring the existing finite-projective trace with the
identity of `P` and applying the left unitor gives the output in `P`.
This is the ordinary, unnormalized partial trace: the pure-tensor formula is
`partialTrace (TensorProduct.map a b) = traceOfFiniteProjective R M a • b`,
without division by a dimension or rank.

The characteristic formulas below express the contraction on arbitrary maps
and identify its value on pure tensor maps. The associativity formula compares
tracing a tensor product of two finite-projective factors with tracing them
successively, first `M` and then `N`. The remaining input and output factors
are arbitrary; the input is transported by the inverse associator and the
output by the forward associator.

## References

The construction reuses the finite-projective trace in
`ProjectiveModules.Module.Trace.Basic` and the tensor–Hom equivalence and
contraction formalization by Oliver Nash and Antoine Labelle in
`Mathlib.LinearAlgebra.Contraction`. The tensor-product currying, symmetry,
and linear-map interfaces are from the Mathlib formalization by Kenny Lau
and Mario Carneiro. The associativity formula uses these tensor interfaces
and the finite-projective tensor-trace API in
`ProjectiveModules.Module.Trace.TensorProduct`.
-/

@[expose] public section

universe uR uM uN uP

open scoped TensorProduct

namespace LinearMap

variable (R : Type uR) [CommSemiring R]
variable (M : Type uM) [AddCommMonoid M] [Module R M]
variable (N : Type uN) [AddCommMonoid N] [Module R N]
variable (P : Type uP) [AddCommMonoid P] [Module R P]
variable [Module.Finite R M] [Module.Projective R M]

/-- The partial trace over the first, finite-projective tensor factor, bundled
as a linear map on all linear maps `M ⊗[R] N →ₗ[R] M ⊗[R] P`. -/
noncomputable def partialTraceOfFiniteProjective :
    (M ⊗[R] N →ₗ[R] M ⊗[R] P) →ₗ[R] (N →ₗ[R] P) :=
  let K : (M →ₗ[R] M ⊗[R] P) →ₗ[R] P :=
    (TensorProduct.lid R P).toLinearMap.comp
      (((traceOfFiniteProjective R M).rTensor P).comp
        (rTensorHomEquivHomRTensor R M M P).symm.toLinearMap)
  (LinearMap.llcomp R N (M →ₗ[R] M ⊗[R] P) P K).comp
    ((LinearMap.lflip (R₀ := R)).toLinearMap.comp
      (TensorProduct.lcurry (.id R) M N (M ⊗[R] P)))

/-- The inverse tensor–Hom contraction formula for the partial trace of every
input map at every argument. -/
theorem partialTraceOfFiniteProjective_apply
    (f : M ⊗[R] N →ₗ[R] M ⊗[R] P) (n : N) :
    partialTraceOfFiniteProjective R M N P f n =
      TensorProduct.lid R P
        ((traceOfFiniteProjective R M).rTensor P
          ((rTensorHomEquivHomRTensor R M M P).symm
            ((TensorProduct.curry f).flip n))) := by
  rfl

/-- Partial trace of a pure tensor is scalar trace on the first factor times
the arbitrary second-factor map. -/
theorem partialTraceOfFiniteProjective_tensorProduct
    (a : M →ₗ[R] M) (b : N →ₗ[R] P) :
    partialTraceOfFiniteProjective R M N P (TensorProduct.map a b) =
      traceOfFiniteProjective R M a • b := by
  ext n
  rw [partialTraceOfFiniteProjective_apply]
  have h : (rTensorHomEquivHomRTensor R M M P).symm
      ((TensorProduct.curry (TensorProduct.map a b)).flip n) = a ⊗ₜ[R] b n := by
    apply (rTensorHomEquivHomRTensor R M M P).symm_apply_eq.mpr
    ext m
    simp only [flip_apply, TensorProduct.curry_apply, TensorProduct.map_tmul,
      rTensorHomEquivHomRTensor_apply, TensorProduct.rTensorHomToHomRTensor_apply]
  rw [h, rTensor_tmul, TensorProduct.lid_tmul, smul_apply]

universe uNprime uPprime

variable (Nprime : Type uNprime) [AddCommMonoid Nprime] [Module R Nprime]
variable (Pprime : Type uPprime) [AddCommMonoid Pprime] [Module R Pprime]

/-- Precomposing the untraced input with `b : Nprime →ₗ[R] N` commutes with
partial trace over the first factor `M`. Here `b.lTensor M` is the tensor map
`id_M ⊗ b`; only `M` is finite projective. -/
theorem partialTraceOfFiniteProjective_comp_lTensor
    (f : M ⊗[R] N →ₗ[R] M ⊗[R] P) (b : Nprime →ₗ[R] N) :
    partialTraceOfFiniteProjective R M Nprime P (f.comp (b.lTensor M)) =
      (partialTraceOfFiniteProjective R M N P f).comp b := by
  ext n
  rw [comp_apply, partialTraceOfFiniteProjective_apply,
    partialTraceOfFiniteProjective_apply]
  have h : (TensorProduct.curry (f.comp (b.lTensor M))).flip n =
      (TensorProduct.curry f).flip (b n) := by
    ext m
    simp only [flip_apply, TensorProduct.curry_apply, comp_apply, lTensor_tmul]
  rw [h]

/-- Postcomposing the untraced output with `c : P →ₗ[R] Pprime` commutes with
partial trace over the first factor `M`. Here `c.lTensor M` is the tensor map
`id_M ⊗ c`; only `M` is finite projective. -/
theorem partialTraceOfFiniteProjective_lTensor_comp
    (f : M ⊗[R] N →ₗ[R] M ⊗[R] P) (c : P →ₗ[R] Pprime) :
    partialTraceOfFiniteProjective R M N Pprime ((c.lTensor M).comp f) =
      c.comp (partialTraceOfFiniteProjective R M N P f) := by
  ext n
  rw [comp_apply, partialTraceOfFiniteProjective_apply,
    partialTraceOfFiniteProjective_apply]
  have h : (TensorProduct.curry ((c.lTensor M).comp f)).flip n =
      (c.lTensor M).comp ((TensorProduct.curry f).flip n) := by
    ext m
    simp only [flip_apply, TensorProduct.curry_apply, comp_apply]
  rw [h]
  generalize (TensorProduct.curry f).flip n = g
  obtain ⟨t, rfl⟩ := (rTensorHomEquivHomRTensor R M M P).surjective g
  rw [LinearEquiv.symm_apply_apply]
  -- The one-sided equivalence represents every curried map, even when `P`
  -- is not finite projective. Contraction is linear on that entire tensor.
  induction t using TensorProduct.inductionOn with
  | tmul a p =>
      have ht : (c.lTensor M).comp
          (rTensorHomEquivHomRTensor R M M P (a ⊗ₜ[R] p)) =
          rTensorHomEquivHomRTensor R M M Pprime (a ⊗ₜ[R] c p) := by
        ext m
        simp only [comp_apply, rTensorHomEquivHomRTensor_apply,
          TensorProduct.rTensorHomToHomRTensor_apply, lTensor_tmul]
      simp only [ht, LinearEquiv.symm_apply_apply, rTensor_tmul,
        TensorProduct.lid_tmul, map_smul]
  | add x y hx hy =>
      simpa only [map_add, comp_add] using congrArg₂ (· + ·) hx hy

/-- Partial trace over the first factor `M` commutes with simultaneous
precomposition on the untraced input and postcomposition on the untraced
output. The tensor maps are `id_M ⊗ b` and `id_M ⊗ c`, and composition is
right-to-left. The four untraced semimodules are arbitrary and have independent
universes; only `M` is finite projective. -/
theorem partialTraceOfFiniteProjective_naturality
    (f : M ⊗[R] N →ₗ[R] M ⊗[R] P) (b : Nprime →ₗ[R] N) (c : P →ₗ[R] Pprime) :
    partialTraceOfFiniteProjective R M Nprime Pprime
        ((c.lTensor M).comp (f.comp (b.lTensor M))) =
      c.comp ((partialTraceOfFiniteProjective R M N P f).comp b) := by
  rw [partialTraceOfFiniteProjective_lTensor_comp,
    partialTraceOfFiniteProjective_comp_lTensor]

universe uQ

variable (Q : Type uQ) [AddCommMonoid Q] [Module R Q]

/-- Slicing the last input factor commutes with partial trace, after transport
by the inverse associator on the input. Only `M` is finite projective. -/
theorem partialTraceOfFiniteProjective_curry_assoc
    (f : ((M ⊗[R] N) ⊗[R] P) →ₗ[R] M ⊗[R] Q) (p : P) :
    (TensorProduct.curry
      (partialTraceOfFiniteProjective R M (N ⊗[R] P) Q
        (f.comp (TensorProduct.assoc R M N P).symm.toLinearMap))).flip p =
      partialTraceOfFiniteProjective R M N Q ((TensorProduct.curry f).flip p) := by
  ext n
  simp only [flip_apply, TensorProduct.curry_apply]
  rw [partialTraceOfFiniteProjective_apply, partialTraceOfFiniteProjective_apply]
  have h : (TensorProduct.curry
        (f.comp (TensorProduct.assoc R M N P).symm.toLinearMap)).flip (n ⊗ₜ[R] p) =
      (TensorProduct.curry ((TensorProduct.curry f).flip p)).flip n := by
    ext m
    simp only [flip_apply, TensorProduct.curry_apply, comp_apply,
      LinearEquiv.coe_toLinearMap, TensorProduct.assoc_symm_tmul]
  rw [h]

variable [Module.Finite R N] [Module.Projective R N]

/-- Partial trace over `M ⊗[R] N` equals successive partial traces, first over
`M` and then over `N`, after transport by tensor associativity. The input uses
the inverse associator and the output uses the forward associator. Only the
two traced factors are finite projective; `P` and `Q` are arbitrary. -/
theorem partialTraceOfFiniteProjective_assoc
    (f : ((M ⊗[R] N) ⊗[R] P) →ₗ[R] ((M ⊗[R] N) ⊗[R] Q)) :
    partialTraceOfFiniteProjective R (M ⊗[R] N) P Q f =
      partialTraceOfFiniteProjective R N P Q
        (partialTraceOfFiniteProjective R M (N ⊗[R] P) (N ⊗[R] Q)
          ((TensorProduct.assoc R M N Q).toLinearMap.comp
            (f.comp (TensorProduct.assoc R M N P).symm.toLinearMap))) := by
  ext p
  rw [partialTraceOfFiniteProjective_apply, partialTraceOfFiniteProjective_apply]
  have hs : (TensorProduct.curry
        (partialTraceOfFiniteProjective R M (N ⊗[R] P) (N ⊗[R] Q)
          ((TensorProduct.assoc R M N Q).toLinearMap.comp
            (f.comp (TensorProduct.assoc R M N P).symm.toLinearMap)))).flip p =
      partialTraceOfFiniteProjective R M N (N ⊗[R] Q)
        ((TensorProduct.assoc R M N Q).toLinearMap.comp
          ((TensorProduct.curry f).flip p)) := by
    have hc : (TensorProduct.curry
          ((TensorProduct.assoc R M N Q).toLinearMap.comp f)).flip p =
        (TensorProduct.assoc R M N Q).toLinearMap.comp
          ((TensorProduct.curry f).flip p) := by
      rfl
    simpa only [comp_assoc, hc] using
      partialTraceOfFiniteProjective_curry_assoc R M N P (N ⊗[R] Q)
        ((TensorProduct.assoc R M N Q).toLinearMap.comp f) p
  rw [hs]
  -- Represent only the slice at `p`; the untraced factors need not be finite.
  generalize (TensorProduct.curry f).flip p = g
  obtain ⟨t, rfl⟩ :=
    (rTensorHomEquivHomRTensor R (M ⊗[R] N) (M ⊗[R] N) Q).surjective g
  rw [LinearEquiv.symm_apply_apply]
  induction t using TensorProduct.inductionOn with
  | tmul a q =>
      simp only [rTensor_tmul, TensorProduct.lid_tmul]
      obtain ⟨s, rfl⟩ := (homTensorHomEquiv R M N M N).surjective a
      induction s using TensorProduct.inductionOn with
      | tmul a b =>
          simp only [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]
          have ht : (TensorProduct.assoc R M N Q).toLinearMap.comp
                (rTensorHomEquivHomRTensor R (M ⊗[R] N) (M ⊗[R] N) Q
                  (TensorProduct.map a b ⊗ₜ[R] q)) =
              TensorProduct.map a
                (rTensorHomEquivHomRTensor R N N Q (b ⊗ₜ[R] q)) := by
            apply TensorProduct.ext'
            intro m n
            simp only [comp_apply, rTensorHomEquivHomRTensor_apply,
              TensorProduct.rTensorHomToHomRTensor_apply, TensorProduct.map_tmul,
              LinearEquiv.coe_toLinearMap, TensorProduct.assoc_tmul]
          simp only [ht, partialTraceOfFiniteProjective_tensorProduct, map_smul,
            LinearEquiv.symm_apply_apply, rTensor_tmul, TensorProduct.lid_tmul,
            traceOfFiniteProjective_tensorProduct', smul_smul]
      | add x y hx hy =>
          simpa only [map_add, TensorProduct.add_tmul, comp_add, add_smul] using
            congrArg₂ (· + ·) hx hy
  | add x y hx hy =>
      simpa only [map_add, comp_add] using congrArg₂ (· + ·) hx hy

end LinearMap
