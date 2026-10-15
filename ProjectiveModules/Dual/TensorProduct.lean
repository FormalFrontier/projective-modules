/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dual tensor separation and canonical tensor–Hom injectivity

Over a commutative semiring, products of linear forms detect zero in `M ⊗[R] N`
when `M` is projective and the canonical evaluation pairing `Module.Dual.eval R N`
is left-separating. The factors may have arbitrary rank, their additive structures
need only be commutative monoids, and the scalar and carrier universes are independent.
Left separation here means detection of zero, not separation of arbitrary pairs of
points in semimodules.

The two-projective criterion `TensorProduct.forall_dualDistrib_apply_eq_zero_iff`
is a corollary. The scalar-submodule application
`TensorProduct.forall_dualDistrib_apply_eq_zero_iff_submodule` applies to every
`I : Submodule R R`, including ideals, without assuming projectivity of `I`.

The proof generalizes the projective-factor splitting argument, using Mathlib's
projective splitting, finitely supported tensor coordinates and dual evaluation APIs.

Over a commutative semiring, the canonical map `dualTensorHom R M N` from
`Module.Dual R M ⊗[R] N` to `M →ₗ[R] N` is injective whenever the output module `N`
is projective. Both modules may be additive commutative monoids of arbitrary rank;
no projectivity of `M` or finite-generation assumption is required.

## References

- Mathlib's Contraction formalization by Oliver Nash and Antoine Labelle
  (`Mathlib.LinearAlgebra.Contraction`). The injectivity proof follows its Finsupp
  factorization, naturality and retract approach.
- Mathlib's Finsupp-Hom formalization by Johan Commelin
  (`Mathlib.RingTheory.Finiteness.Finsupp`).
- Mathlib's projective-module formalization by Kevin Buzzard and Antoine Labelle
  (`Mathlib.Algebra.Module.Projective`), used for the canonical free-module splitting.
-/

@[expose] public section

open scoped TensorProduct

universe uR uM uN

namespace TensorProduct

/-- A tensor with projective first factor vanishes exactly when every rank-one product
of linear forms vanishes on it, provided the canonical dual evaluation on the second
factor detects zero. No finite-generation or second-factor projectivity is required. -/
theorem forall_dualDistrib_apply_eq_zero_iff_of_eval_separatingLeft
    (R : Type uR) [CommSemiring R]
    (M : Type uM) (N : Type uN)
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    [Module.Projective R M]
    (hN : (Module.Dual.eval R N).SeparatingLeft)
    (t : M ⊗[R] N) :
    (∀ f : Module.Dual R M, ∀ g : Module.Dual R N,
      TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) t = 0) ↔ t = 0 := by
  constructor
  · intro h
    classical
    obtain ⟨sM, hsM⟩ :=
      Module.projective_def'.mp (inferInstance : Module.Projective R M)
    -- Testing an N-valued coordinate gives a product with a pulled-back coordinate form.
    have hcoord (i : M) (g : Module.Dual R N) :
        g.comp ((Finsupp.lapply i).comp
            ((TensorProduct.finsuppScalarLeft R N M).toLinearMap.comp (sM.rTensor N))) =
          TensorProduct.dualDistrib R M N ((Finsupp.lapply i).comp sM ⊗ₜ[R] g) := by
      apply TensorProduct.ext'
      intro m n
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
        Finsupp.lapply_apply, TensorProduct.finsuppScalarLeft_apply_tmul_apply, map_smul,
        TensorProduct.dualDistrib_apply, smul_eq_mul]
    have hzero : sM.rTensor N t = 0 := by
      apply (TensorProduct.finsuppScalarLeft R N M).map_eq_zero_iff.mp
      apply Finsupp.ext
      intro i
      change TensorProduct.finsuppScalarLeft R N M (sM.rTensor N t) i = 0
      apply hN
      intro g
      exact (LinearMap.congr_fun (hcoord i g) t).trans (h ((Finsupp.lapply i).comp sM) g)
    -- Tensoring the sole projective splitting with the identity gives a retraction.
    calc
      t = (Finsupp.linearCombination R (id : M → M)).rTensor N (sM.rTensor N t) := by
        rw [← LinearMap.rTensor_comp_apply, hsM, LinearMap.rTensor_id, LinearMap.id_apply]
      _ = 0 := by rw [hzero, map_zero]
  · intro ht f g
    rw [ht, map_zero]

/-- A tensor of two projective modules vanishes exactly when every rank-one product of
linear forms vanishes on it. No finite-generation assumption is required. -/
theorem forall_dualDistrib_apply_eq_zero_iff
    (R : Type uR) [CommSemiring R]
    (M : Type uM) (N : Type uN)
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    [Module.Projective R M] [Module.Projective R N]
    (t : M ⊗[R] N) :
    (∀ f : Module.Dual R M, ∀ g : Module.Dual R N,
      TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) t = 0) ↔ t = 0 := by
  exact forall_dualDistrib_apply_eq_zero_iff_of_eval_separatingLeft R M N
    LinearMap.SeparatingLeft.eval t

/-- Products of linear forms detect zero in the tensor product of a projective module
with any scalar submodule. No projectivity of the scalar submodule is assumed. -/
theorem forall_dualDistrib_apply_eq_zero_iff_submodule
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    [Module.Projective R M]
    (I : Submodule R R) (t : M ⊗[R] I) :
    (∀ f : Module.Dual R M, ∀ g : Module.Dual R I,
      TensorProduct.dualDistrib R M I (f ⊗ₜ[R] g) t = 0) ↔ t = 0 := by
  exact forall_dualDistrib_apply_eq_zero_iff_of_eval_separatingLeft R M I
    (fun x hx => Subtype.ext (hx I.subtype)) t

end TensorProduct

/-- Over a commutative semiring, the canonical map from `Module.Dual R M ⊗[R] N`
to `M →ₗ[R] N` is injective if the output module `N` is projective. Neither module
needs to be finitely generated, and `M` need not be projective. The proof follows
Mathlib's Finsupp factorization and output-retract approach in Contraction. -/
theorem dualTensorHom_injective_of_projective_right
    (R : Type uR) [CommSemiring R]
    (M : Type uM) (N : Type uN)
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module.Projective R N] :
    Function.Injective (dualTensorHom R M N) := by
  classical
  have hscalar : Function.Injective (dualTensorHom R M R) := by
    rw [dualTensorHom_self_right]
    exact (TensorProduct.rid R (Module.Dual R M)).injective
  -- For a free output, all three maps in the Finsupp factorization are injective.
  have hfree : Function.Injective (dualTensorHom R M (N →₀ R)) := by
    rw [dualTensorHom_finsupp, LinearMap.coe_comp, LinearMap.coe_comp]
    exact (LinearMap.finsuppLinearMap_injective (S := R) (R := R) (M := M)
      (N := R) (ι := N)).comp
        ((Finsupp.mapRange_injective _ (map_zero _) hscalar).comp
          (TensorProduct.finsuppRight R R (Module.Dual R M) R N).injective)
  obtain ⟨s, hs⟩ :=
    Module.projective_def'.mp (inferInstance : Module.Projective R N)
  -- The section of the output remains a section after tensoring with the dual.
  have hsTensor : Function.Injective (s.lTensor (Module.Dual R M)) := by
    apply LinearMap.injective_of_comp_eq_id _
      ((Finsupp.linearCombination R (id : N → N)).lTensor (Module.Dual R M))
    rw [← LinearMap.lTensor_comp, hs, LinearMap.lTensor_id]
  intro x y h
  apply hsTensor
  apply hfree
  calc
    dualTensorHom R M (N →₀ R) (s.lTensor (Module.Dual R M) x) =
        s.comp (dualTensorHom R M N x) :=
      LinearMap.congr_fun (dualTensorHom_comp_lTensor (M := M) s) x
    _ = s.comp (dualTensorHom R M N y) := congrArg (fun f => s.comp f) h
    _ = dualTensorHom R M (N →₀ R) (s.lTensor (Module.Dual R M) y) :=
      (LinearMap.congr_fun (dualTensorHom_comp_lTensor (M := M) s) y).symm
