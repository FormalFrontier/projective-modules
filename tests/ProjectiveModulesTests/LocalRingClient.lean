/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.LocalRing
public import ProjectiveModulesTests.IdempotentSpanClient
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.LocalRing.NonLocalRing
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Tactic.NormNum

/-!
# Local-ring projective-module clients

The coordinate models below are projective and free by existing Mathlib
instances, independently of the general local-ring theorem. They include
empty, finite and genuinely infinite direct-sum coordinates. Infinite
coordinates are `Finsupp` modules, not infinite function products.

The first idempotent ideal over the opposite of a product of two fields is
nontrivial, finite projective, and nonfree over a nonlocal scalar ring. This
right-module control uses the idempotent-ideal clients independently of the
local-ring freeness theorem; its projectivity comes from an idempotent
splitting, not from a freeness instance.

Dual numbers over the real quaternions supply a noncommutative local ring
with a nonzero nonunit of square zero. The scalar action on the module is
just the canonical action of that ring, or of its opposite for right
modules. Clients that apply `Module.Projective.free_of_isLocalRing` are
uses of that theorem, not independent proofs of it.
-/

universe uR uP uι

section Coordinates

variable (R : Type uR) [Ring R]

private theorem zero_coordinates :
    Module.Projective R (Fin 0 →₀ R) ∧ Module.Free R (Fin 0 →₀ R) := by
  constructor <;> infer_instance

private theorem finite_coordinates (n : ℕ) :
    Module.Finite R (Fin n →₀ R) ∧
      Module.Projective R (Fin n →₀ R) ∧ Module.Free R (Fin n →₀ R) := by
  exact ⟨Module.Finite.of_basis (Finsupp.basisSingleOne (R := R)),
    inferInstance, inferInstance⟩

private theorem infinite_coordinates :
    Module.Projective R (ℕ →₀ R) ∧ Module.Free R (ℕ →₀ R) := by
  constructor <;> infer_instance

private theorem infinite_coordinates_not_finite [Nontrivial R] :
    ¬ Module.Finite R (ℕ →₀ R) := by
  intro h
  rcases Module.finite_finsupp_self_iff.mp h with hR | hι
  · exact not_subsingleton R hR
  · let : Finite ℕ := hι
    exact not_finite ℕ

private theorem right_infinite_coordinates :
    Module.Projective Rᵐᵒᵖ (ℕ →₀ Rᵐᵒᵖ) ∧
      Module.Free Rᵐᵒᵖ (ℕ →₀ Rᵐᵒᵖ) := by
  constructor <;> infer_instance

variable [IsLocalRing R]

private theorem local_zero_coordinates : Module.Free R (Fin 0 →₀ R) :=
  Module.Projective.free_of_isLocalRing

private theorem local_finite_coordinates (n : ℕ) : Module.Free R (Fin n →₀ R) :=
  Module.Projective.free_of_isLocalRing

private theorem local_infinite_coordinates : Module.Free R (ℕ →₀ R) :=
  Module.Projective.free_of_isLocalRing

private theorem local_infinite_coordinates_lift :
    Module.Free R (ULift.{uι} ℕ →₀ R) :=
  Module.Projective.free_of_isLocalRing

private theorem local_right_infinite_coordinates :
    Module.Free Rᵐᵒᵖ (ℕ →₀ Rᵐᵒᵖ) :=
  Module.Projective.free_of_isLocalRing (R := Rᵐᵒᵖ)

-- The source's right-module convention needs only the opposite scalar action.
private theorem right_local_projective
    (P : Type uP) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Projective Rᵐᵒᵖ P] : Module.Free Rᵐᵒᵖ P :=
  Module.Projective.free_of_isLocalRing (R := Rᵐᵒᵖ)

end Coordinates

section NonlocalBoundary

private theorem product_op_not_local (R : Type uR) (S : Type uP)
    [Semiring R] [Semiring S] [Nontrivial R] [Nontrivial S] :
    ¬ IsLocalRing (R × S)ᵐᵒᵖ := by
  intro h
  let : IsLocalRing (R × S)ᵐᵒᵖ := h
  have h' : IsLocalRing (R × S) := (RingEquiv.opOp (R × S)).symm.isLocalRing
  exact IsLocalRing.not_isLocalRing_of_prod_of_nontrivial R S h'

/-- The first product-field ideal is a nontrivial finite projective right
module that is not free, over a scalar ring that is not local. Its projectivity
uses the idempotent splitting independently of the local-ring freeness theorem. -/
public theorem ProjectiveModulesTests.product_op_projective_nonfree
    (K : Type uR) (L : Type uP) [Field K] [Field L] :
    Module.Finite (K × L)ᵐᵒᵖ (Ideal.span {MulOpposite.op ((1 : K), (0 : L))}) ∧
      Module.Projective (K × L)ᵐᵒᵖ (Ideal.span {MulOpposite.op ((1 : K), (0 : L))}) ∧
      Nontrivial (Ideal.span {MulOpposite.op ((1 : K), (0 : L))} : Ideal (K × L)ᵐᵒᵖ) ∧
      ¬ Module.Free (K × L)ᵐᵒᵖ (Ideal.span {MulOpposite.op ((1 : K), (0 : L))}) ∧
      ¬ IsLocalRing (K × L)ᵐᵒᵖ := by
  obtain ⟨hfinite, hprojective, hnontrivial, hnonfree⟩ :=
    ProjectiveModulesTests.IdempotentSpanClient.product_fields_first K L
  exact ⟨hfinite, hprojective, hnontrivial, hnonfree, product_op_not_local K L⟩

end NonlocalBoundary

section QuaternionDualNumbers

private theorem quaternion_dual_local : IsLocalRing (DualNumber (Quaternion ℝ)) :=
  inferInstance

-- A nonzero nonunit of square zero rules out a division ring.
private theorem quaternion_dual_nonzero_nonunit_square_zero :
    ∃ x : DualNumber (Quaternion ℝ), x ≠ 0 ∧ ¬ IsUnit x ∧ x * x = 0 := by
  refine ⟨DualNumber.eps, ?_, ?_, DualNumber.eps_mul_eps⟩
  · intro h
    have h' := congrArg (fun x : DualNumber (Quaternion ℝ) ↦ x.snd) h
    simp at h'
  · rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, DualNumber.fst_eps]
    exact not_isUnit_zero

-- Constant dual numbers retain quaternionic noncommutativity.
private theorem quaternion_dual_noncommutative :
    ∃ a b : DualNumber (Quaternion ℝ), a * b ≠ b * a := by
  let i : Quaternion ℝ := ⟨0, 1, 0, 0⟩
  let j : Quaternion ℝ := ⟨0, 0, 1, 0⟩
  refine ⟨TrivSqZeroExt.inl i, TrivSqZeroExt.inl j, ?_⟩
  intro h
  have h' := congrArg (fun x : DualNumber (Quaternion ℝ) ↦ x.fst.imK) h
  norm_num [i, j, TrivSqZeroExt.fst_mul] at h'

/-- The countable direct sum of quaternionic dual numbers is projective and free
over its scalar ring. This fixture uses Mathlib's standard `Finsupp` coordinate
instances, independently of `Module.Projective.free_of_isLocalRing`. -/
public theorem ProjectiveModulesTests.quaternion_dual_coordinates :
    Module.Projective (DualNumber (Quaternion ℝ))
        (ℕ →₀ DualNumber (Quaternion ℝ)) ∧
      Module.Free (DualNumber (Quaternion ℝ))
        (ℕ →₀ DualNumber (Quaternion ℝ)) := by
  constructor <;> infer_instance

private theorem quaternion_dual_coordinates_not_finite :
    ¬ Module.Finite (DualNumber (Quaternion ℝ))
      (ℕ →₀ DualNumber (Quaternion ℝ)) :=
  infinite_coordinates_not_finite _

private theorem quaternion_dual_local_coordinates :
    Module.Free (DualNumber (Quaternion ℝ)) (ℕ →₀ DualNumber (Quaternion ℝ)) :=
  Module.Projective.free_of_isLocalRing

private theorem quaternion_dual_local_right_coordinates :
    Module.Free (DualNumber (Quaternion ℝ))ᵐᵒᵖ
      (ℕ →₀ (DualNumber (Quaternion ℝ))ᵐᵒᵖ) :=
  Module.Projective.free_of_isLocalRing

end QuaternionDualNumbers
