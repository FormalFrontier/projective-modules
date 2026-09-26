/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Scalar extension of exterior algebras

This file constructs `ExteriorAlgebra.equivBaseChange`, the canonical equivalence between the
exterior algebra after extending scalars and the scalar extension of the exterior algebra.

The proof works over arbitrary commutative rings. In particular, it does not require that two is
invertible: the square-zero relation for the scalar-extended degree-one map is proved directly by
tensor-product induction.
-/

public section

open scoped TensorProduct

universe uR uS uM

namespace ExteriorAlgebra

variable {R : Type uR} {S : Type uS} {M : Type uM}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

private noncomputable def degreeOneToTensor :
    S ⊗[R] M →ₗ[S] S ⊗[R] ExteriorAlgebra R M :=
  TensorProduct.AlgebraTensorModule.map
    (LinearMap.id : S →ₗ[S] S) (ExteriorAlgebra.ι R)

private theorem degreeOneToTensor_anticomm (x y : S ⊗[R] M) :
    degreeOneToTensor x * degreeOneToTensor y +
      degreeOneToTensor y * degreeOneToTensor x = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ =>
      simp only [map_add, add_mul, mul_add]
      rw [add_assoc, add_left_comm (degreeOneToTensor x₂ * degreeOneToTensor y),
        ← add_assoc, hx₁, zero_add, hx₂]
  | tmul s m =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ hy₁ hy₂ =>
          simp only [map_add, mul_add, add_mul]
          rw [add_assoc, add_left_comm (degreeOneToTensor (s ⊗ₜ[R] m) * degreeOneToTensor y₂),
            ← add_assoc, hy₁, zero_add, hy₂]
      | tmul t n =>
          simp only [degreeOneToTensor, TensorProduct.AlgebraTensorModule.map_tmul,
            LinearMap.id_apply, Algebra.TensorProduct.tmul_mul_tmul]
          rw [mul_comm t s, ← TensorProduct.tmul_add, ExteriorAlgebra.ι_add_mul_swap]
          simp

private theorem degreeOneToTensor_sq (x : S ⊗[R] M) :
    degreeOneToTensor x * degreeOneToTensor x = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      simp only [map_add, add_mul, mul_add, hx, hy, zero_add, add_zero]
      simpa [add_comm] using degreeOneToTensor_anticomm x y
  | tmul s m =>
      simp [degreeOneToTensor]

/-- The canonical map from the exterior algebra after extending scalars to the scalar extension
of the original exterior algebra. -/
noncomputable def toBaseChange :
    ExteriorAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] ExteriorAlgebra R M :=
  ExteriorAlgebra.lift S ⟨degreeOneToTensor, degreeOneToTensor_sq⟩

private noncomputable def ofBaseChangeAux :
    ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra S (S ⊗[R] M) :=
  ExteriorAlgebra.lift R ⟨
    (ExteriorAlgebra.ι S).restrictScalars R ∘ₗ TensorProduct.mk R S M 1,
    fun m ↦ by simp⟩

/-- The canonical map from the scalar extension of an exterior algebra to the exterior algebra
after extending scalars. -/
noncomputable def ofBaseChange :
    S ⊗[R] ExteriorAlgebra R M →ₐ[S] ExteriorAlgebra S (S ⊗[R] M) :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) ofBaseChangeAux
    fun _ _ ↦ Algebra.commutes _ _

@[simp] theorem ofBaseChange_tmul_ι (s : S) (m : M) :
    ofBaseChange (R := R) (S := S) (M := M)
        (s ⊗ₜ[R] ExteriorAlgebra.ι R m) =
      ExteriorAlgebra.ι S (s ⊗ₜ[R] m) := by
  change algebraMap S (ExteriorAlgebra S (S ⊗[R] M)) s *
      ofBaseChangeAux (R := R) (S := S) (M := M) (ExteriorAlgebra.ι R m) = _
  rw [ofBaseChangeAux, ExteriorAlgebra.lift_ι_apply]
  change algebraMap S _ s * ExteriorAlgebra.ι S (1 ⊗ₜ[R] m) = _
  rw [← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul']
  simp only [smul_eq_mul, mul_one]

@[simp] private theorem toBaseChange_ι (x : S ⊗[R] M) :
    toBaseChange (R := R) (S := S) (M := M) (ExteriorAlgebra.ι S x) =
      degreeOneToTensor (R := R) (S := S) x := by
  rw [toBaseChange, ExteriorAlgebra.lift_ι_apply]

@[simp] theorem toBaseChange_ι_tmul (s : S) (m : M) :
    toBaseChange (R := R) (S := S) (M := M)
        (ExteriorAlgebra.ι S (s ⊗ₜ[R] m)) =
      s ⊗ₜ[R] ExteriorAlgebra.ι R m := by
  simp [degreeOneToTensor]

private theorem toBaseChange_comp_ofBaseChange :
    (toBaseChange (R := R) (S := S) (M := M)).comp
      (ofBaseChange (R := R) (S := S) (M := M)) = AlgHom.id S _ := by
  ext m
  simp [toBaseChange, degreeOneToTensor]

private theorem ofBaseChange_comp_toBaseChange :
    (ofBaseChange (R := R) (S := S) (M := M)).comp
      (toBaseChange (R := R) (S := S) (M := M)) = AlgHom.id S _ := by
  apply ExteriorAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  change ofBaseChange (toBaseChange (ExteriorAlgebra.ι S x)) = ExteriorAlgebra.ι S x
  rw [toBaseChange_ι]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul s m => simp [degreeOneToTensor]

/-- Extending scalars in an exterior algebra agrees with taking the exterior algebra after
extending scalars. This equivalence is valid without assuming that two is invertible. -/
noncomputable def equivBaseChange :
    ExteriorAlgebra S (S ⊗[R] M) ≃ₐ[S] S ⊗[R] ExteriorAlgebra R M :=
  AlgEquiv.ofAlgHom (toBaseChange (R := R) (S := S) (M := M))
    (ofBaseChange (R := R) (S := S) (M := M))
    (toBaseChange_comp_ofBaseChange (R := R) (S := S) (M := M))
    (ofBaseChange_comp_toBaseChange (R := R) (S := S) (M := M))

@[simp] theorem equivBaseChange_apply_ι_tmul (s : S) (m : M) :
    equivBaseChange (R := R) (S := S) (M := M)
        (ExteriorAlgebra.ι S (s ⊗ₜ[R] m)) =
      s ⊗ₜ[R] ExteriorAlgebra.ι R m := by
  exact toBaseChange_ι_tmul s m

@[simp] theorem equivBaseChange_symm_apply_tmul_ι (s : S) (m : M) :
    (equivBaseChange (R := R) (S := S) (M := M)).symm
        (s ⊗ₜ[R] ExteriorAlgebra.ι R m) =
      ExteriorAlgebra.ι S (s ⊗ₜ[R] m) := by
  exact ofBaseChange_tmul_ι s m

end ExteriorAlgebra
