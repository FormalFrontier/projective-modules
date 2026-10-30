/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Dual tensor separation and injectivity reflection

Over a commutative semiring, products of linear forms detect zero in `M ⊗[R] N`
when `M` is projective and the canonical evaluation pairing `Module.Dual.eval R N`
is left-separating. The factors may have arbitrary rank, their additive structures
need only be commutative monoids, and the scalar and carrier universes are independent.
Left separation here means detection of zero, not separation of arbitrary pairs of
points in semimodules.

Products of linear forms distinguish arbitrary tensor points when `M` is projective
and the canonical dual evaluation on `N` is injective. If both factors are projective,
Mathlib's `Module.eval_apply_injective` supplies this injectivity. Specializing the
two-projective equality criterion to comparison with zero gives the original
two-projective zero criterion by linearity. This does not replace the weaker
zero-detection hypothesis in the one-projective zero criterion.

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

Tensoring with a module `P` with faithful scalar action reflects injectivity of
`f : M →ₗ[R] N` whenever the canonical dual evaluation on `M` is injective.
Projective domains satisfy this condition by Mathlib's `Module.eval_apply_injective`.
The coefficient module need not be flat, and the domain and codomain need not be
finitely generated. Applying this reflection to `Finsupp.linearCombination` shows
that injectivity of the tensor-valued finite-support `P`-coefficient relation map
of an arbitrary family implies its `R`-linear independence.

The reflection proof compares pairs using each dual form and the tensor right
unitor, then uses faithfulness of the scalar action. It uses no subtraction or
preservation of injectivity. Faithful action alone does not suffice for arbitrary
domains: over `ℤ`, tensoring the zero map `ZMod 2 → 0` with `ℚ` makes it injective.
Nor does faithful action imply preservation: for `P = ℤ × ZMod 2`, tensoring
multiplication by two on `ℤ` is not injective. These results are reflection only.

## References

- Mathlib's Contraction formalization by Oliver Nash and Antoine Labelle
  (`Mathlib.LinearAlgebra.Contraction`). The injectivity proof follows its Finsupp
  factorization, naturality and retract approach.
- Mathlib's Finsupp-Hom formalization by Johan Commelin
  (`Mathlib.RingTheory.Finiteness.Finsupp`).
- Mathlib's projective-module formalization by Kevin Buzzard and Antoine Labelle
  (`Mathlib.Algebra.Module.Projective`), used for the canonical free-module splitting.
- Mathlib's dual formalization by Johan Commelin, Fabian Glöckle and Kyle Miller
  (`Mathlib.LinearAlgebra.Dual.Lemmas`), including projective dual-evaluation injectivity.
- Mathlib's tensor maps and unitors by Kenny Lau and Mario Carneiro, and its
  Finsupp/direct-sum formalizations by Johannes Hölzl and Antoine Chambert-Loir.
  Injectivity reflection uses these canonical maps; the family application uses
  `TensorProduct.finsuppScalarRight` rather than a new free-module identification.
-/

@[expose] public section

open scoped TensorProduct

universe uR uP uM uN uι

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

/-- Two tensors with projective first factor are equal exactly when every rank-one
product of linear forms takes equal values on them, provided the canonical dual
evaluation on the second factor is injective. Ordinary point injectivity is required,
not merely detection of zero; neither factor needs to be finitely generated. -/
theorem forall_dualDistrib_apply_eq_iff_of_eval_injective
    (R : Type uR) [CommSemiring R]
    (M : Type uM) (N : Type uN)
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    [Module.Projective R M]
    (hN : Function.Injective (Module.Dual.eval R N))
    (t u : M ⊗[R] N) :
    (∀ f : Module.Dual R M, ∀ g : Module.Dual R N,
      TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) t =
        TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) u) ↔ t = u := by
  constructor
  · intro h
    classical
    obtain ⟨sM, hsM⟩ :=
      Module.projective_def'.mp (inferInstance : Module.Projective R M)
    -- Pull each dual form back along an N-valued split coordinate.
    have hcoord (i : M) (g : Module.Dual R N) :
        g.comp ((Finsupp.lapply i).comp
            ((TensorProduct.finsuppScalarLeft R N M).toLinearMap.comp (sM.rTensor N))) =
          TensorProduct.dualDistrib R M N ((Finsupp.lapply i).comp sM ⊗ₜ[R] g) := by
      apply TensorProduct.ext'
      intro m n
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
        Finsupp.lapply_apply, TensorProduct.finsuppScalarLeft_apply_tmul_apply, map_smul,
        TensorProduct.dualDistrib_apply, smul_eq_mul]
    have hsplit : sM.rTensor N t = sM.rTensor N u := by
      apply (TensorProduct.finsuppScalarLeft R N M).injective
      apply Finsupp.ext
      intro i
      change TensorProduct.finsuppScalarLeft R N M (sM.rTensor N t) i =
        TensorProduct.finsuppScalarLeft R N M (sM.rTensor N u) i
      apply hN
      apply LinearMap.ext
      intro g
      change g (TensorProduct.finsuppScalarLeft R N M (sM.rTensor N t) i) =
        g (TensorProduct.finsuppScalarLeft R N M (sM.rTensor N u) i)
      exact ((LinearMap.congr_fun (hcoord i g) t).trans
        (h ((Finsupp.lapply i).comp sM) g)).trans (LinearMap.congr_fun (hcoord i g) u).symm
    -- Apply the tensor of the sole projective retraction to both split images.
    calc
      t = (Finsupp.linearCombination R (id : M → M)).rTensor N (sM.rTensor N t) := by
        rw [← LinearMap.rTensor_comp_apply, hsM, LinearMap.rTensor_id, LinearMap.id_apply]
      _ = (Finsupp.linearCombination R (id : M → M)).rTensor N (sM.rTensor N u) := by
        rw [hsplit]
      _ = u := by
        rw [← LinearMap.rTensor_comp_apply, hsM, LinearMap.rTensor_id, LinearMap.id_apply]
  · intro htu f g
    rw [htu]

/-- Two tensors of projective modules are equal exactly when every rank-one product
of linear forms takes equal values on them. The modules may have arbitrary rank
and need only have additive commutative monoid structures. -/
theorem forall_dualDistrib_apply_eq_iff
    (R : Type uR) [CommSemiring R]
    (M : Type uM) (N : Type uN)
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    [Module.Projective R M] [Module.Projective R N]
    (t u : M ⊗[R] N) :
    (∀ f : Module.Dual R M, ∀ g : Module.Dual R N,
      TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) t =
        TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) u) ↔ t = u := by
  exact forall_dualDistrib_apply_eq_iff_of_eval_injective R M N
    (Module.eval_apply_injective R (V := N)) t u

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

namespace LinearMap

/-- Tensoring with a module with faithful scalar action reflects injectivity when
linear forms separate pairs of points in the domain. Neither flatness of the
coefficient module nor finite generation of any module is required. -/
theorem injective_of_lTensor_injective_of_eval_injective
    {R : Type uR} {P : Type uP} {M : Type uM} {N : Type uN}
    [CommSemiring R]
    [AddCommMonoid P] [AddCommMonoid M] [AddCommMonoid N]
    [Module R P] [Module R M] [Module R N] [FaithfulSMul R P]
    (hM : Function.Injective (Module.Dual.eval R M))
    (f : M →ₗ[R] N) (hf : Function.Injective (f.lTensor P)) :
    Function.Injective f := by
  intro x y hxy
  apply hM
  apply LinearMap.ext
  intro φ
  change φ x = φ y
  apply eq_of_smul_eq_smul (α := P)
  intro p
  have ht : p ⊗ₜ[R] x = p ⊗ₜ[R] y := by
    apply hf
    simpa only [lTensor_tmul] using congrArg (fun n => p ⊗ₜ[R] n) hxy
  have hφ := congrArg (fun t => TensorProduct.rid R P (φ.lTensor P t)) ht
  simpa only [lTensor_tmul, TensorProduct.rid_tmul] using hφ

/-- Tensoring with a module with faithful scalar action reflects injectivity of
maps from projective modules of arbitrary rank. The dual-separation hypothesis
is supplied by Mathlib's projective dual-evaluation injectivity theorem. -/
theorem injective_of_lTensor_injective_of_projective
    {R : Type uR} {P : Type uP} {M : Type uM} {N : Type uN}
    [CommSemiring R]
    [AddCommMonoid P] [AddCommMonoid M] [AddCommMonoid N]
    [Module R P] [Module R M] [Module R N] [FaithfulSMul R P]
    [Module.Projective R M]
    (f : M →ₗ[R] N) (hf : Function.Injective (f.lTensor P)) :
    Function.Injective f := by
  exact f.injective_of_lTensor_injective_of_eval_injective
    (Module.eval_apply_injective R (V := M)) hf

end LinearMap

/-- If the tensor-valued finite-support `P`-coefficient relation map of a family
is injective and the scalar action on `P` is faithful, the family is linearly
independent over `R`. The index type is arbitrary, and no flatness assumption
on `P` or finiteness assumption on the family is needed. -/
theorem linearIndependent_of_injective_sum_tmul
    {R : Type uR} {P : Type uP} {N : Type uN} {ι : Type uι}
    [CommSemiring R] [AddCommMonoid P] [AddCommMonoid N]
    [Module R P] [Module R N] [FaithfulSMul R P]
    (v : ι → N)
    (hv : Function.Injective
      (Finsupp.lsum R (fun i => (TensorProduct.mk R P N).flip (v i)))) :
    LinearIndependent R v := by
  classical
  let e := TensorProduct.finsuppScalarRight R R P ι
  -- Compare the relation map with tensoring the scalar linear-combination map.
  have hcomp : ((Finsupp.linearCombination R v).lTensor P).comp e.symm.toLinearMap =
      Finsupp.lsum R (fun i => (TensorProduct.mk R P N).flip (v i)) := by
    apply Finsupp.lhom_ext
    intro i p
    simp [e, Finsupp.lsum_single]
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  apply LinearMap.injective_of_lTensor_injective_of_projective (P := P)
  intro x y hxy
  apply e.injective
  apply hv
  rw [← hcomp]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using hxy
