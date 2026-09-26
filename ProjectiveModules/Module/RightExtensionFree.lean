/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import ProjectiveModules.Module.RightExtensionQuotient
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Scalar extension of finite free right modules

This file identifies scalar extension of the canonical finite free right
`R`-module `ι → R` along an arbitrary ring homomorphism `R →+* S` with the
canonical finite free right `S`-module `ι → S`.  It also specializes the
equivalence to quotients by two-sided ideals.
-/

@[expose] public section

universe uR uS uι

namespace Module

variable (R : Type uR) [Ring R]
variable (ι : Type uι)

/-- The standard free module over `Rᵐᵒᵖ`, written with coordinates in `R`. -/
noncomputable def rightFreeCoordEquiv :
    (ι → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (ι → R) :=
  LinearEquiv.piCongrRight fun _ ↦
    (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm

@[simp]
theorem rightFreeCoordEquiv_apply (x : ι → Rᵐᵒᵖ) (i : ι) :
    rightFreeCoordEquiv R ι x i = MulOpposite.unop (x i) :=
  rfl

@[simp]
theorem rightFreeCoordEquiv_symm_apply (x : ι → R) (i : ι) :
    (rightFreeCoordEquiv R ι).symm x i = MulOpposite.op (x i) :=
  rfl

end Module

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (f : R →+* S)
variable (ι : Type uι) [Fintype ι] [DecidableEq ι]

/-- Coordinatewise scalar extension on a finite canonical right-free module. -/
def rightFreeToSemilinear :
    (ι → R) →ₛₗ[RingHom.op f] (ι → S) where
  toFun x i := f (x i)
  map_add' x y := by
    ext i
    exact f.map_add (x i) (y i)
  map_smul' r x := by
    induction r using MulOpposite.rec' with
    | _ r =>
      ext i
      exact f.map_mul (x i) r

/-- The forward map from scalar extension of a finite canonical right-free
module to the corresponding right-free module over the target ring. -/
def rightFreeTo :
    Obj f (ι → R) →ₗ[Sᵐᵒᵖ] (ι → S) :=
  fromSemilinear f (rightFreeToSemilinear f ι)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem rightFreeTo_tmul (x : ι → R) (s : S) :
    rightFreeTo f ι (tmul f x s) = fun i ↦ f (x i) * s := by
  ext i
  rw [rightFreeTo, fromSemilinear_tmul]
  rfl

/-- The inverse to `rightFreeTo`, given by the target coefficients of the
scalar-extended standard basis. -/
noncomputable def rightFreeFrom :
    (ι → S) →ₗ[Sᵐᵒᵖ] Obj f (ι → R) :=
  (Fintype.linearCombination Sᵐᵒᵖ
      (fun i ↦ tmul f (Pi.single i 1) 1)).comp
    (Module.rightFreeCoordEquiv S ι).symm.toLinearMap

@[simp]
theorem rightFreeFrom_apply (x : ι → S) :
    rightFreeFrom f ι x = ∑ i, tmul f (Pi.single i 1) (x i) := by
  simp [rightFreeFrom, Fintype.linearCombination_apply, tmul_smul]

@[simp]
theorem rightFreeTo_rightFreeFrom (x : ι → S) :
    rightFreeTo f ι (rightFreeFrom f ι x) = x := by
  rw [rightFreeFrom_apply, map_sum]
  ext j
  simp [rightFreeTo_tmul, Pi.single_apply]

@[simp]
theorem rightFreeFrom_rightFreeTo (z : Obj f (ι → R)) :
    rightFreeFrom f ι (rightFreeTo f ι z) = z := by
  let _ : Module R S := f.toModule
  suffices (rightFreeFrom f ι).comp (rightFreeTo f ι) = LinearMap.id by
    exact DFunLike.congr_fun this z
  apply linearMap_ext f
  intro x s
  rw [LinearMap.comp_apply, rightFreeTo_tmul, rightFreeFrom_apply]
  calc
    (∑ i, tmul f (Pi.single i 1) (f (x i) * s)) =
        ∑ i, tmul f
          (MulOpposite.op (x i) • (Pi.single i (1 : R) : ι → R)) s := by
          apply Finset.sum_congr rfl
          intro i _
          exact (smul_tmul f (x i) (Pi.single i (1 : R) : ι → R) s).symm
    _ = tmul f
        (∑ i, MulOpposite.op (x i) • (Pi.single i (1 : R) : ι → R)) s := by
          induction (Finset.univ : Finset ι) using Finset.induction_on with
          | empty => simp [tmul, BalancedTensorProduct.zero_tmul]
          | @insert i t hi ih =>
              rw [Finset.sum_insert hi, Finset.sum_insert hi, ih]
              exact (BalancedTensorProduct.add_tmul _ _ _).symm
    _ = tmul f x s := by
          congr 1
          ext j
          simp [Pi.single_apply]

/-- Scalar extension of a finite canonical right-free module is the canonical
right-free module over the target ring. -/
noncomputable def rightFreeLinearEquiv :
    Obj f (ι → R) ≃ₗ[Sᵐᵒᵖ] (ι → S) :=
  LinearEquiv.ofLinearMap (rightFreeTo f ι) (rightFreeFrom f ι)
    (by
      apply LinearMap.ext
      intro x
      exact rightFreeTo_rightFreeFrom f ι x)
    (by
      apply LinearMap.ext
      intro z
      exact rightFreeFrom_rightFreeTo f ι z)

@[simp]
theorem rightFreeLinearEquiv_tmul (x : ι → R) (s : S) :
    rightFreeLinearEquiv f ι (tmul f x s) = fun i ↦ f (x i) * s := by
  exact rightFreeTo_tmul f ι x s

section IdealQuotient

variable {R : Type uR} [Ring R]

/-- The quotient by the right action of a two-sided ideal on a finite
canonical right-free module is coordinatewise ring quotient. -/
noncomputable def idealQuotientRightFreeLinearEquiv
    (I : Ideal R) [I.IsTwoSided] :
    IdealQuotient (M := ι → R) I ≃ₗ[(R ⧸ I)ᵐᵒᵖ] (ι → R ⧸ I) :=
  (idealQuotientLinearEquiv (M := ι → R) I).symm.trans
    (rightFreeLinearEquiv (Ideal.Quotient.mk I) ι)

@[simp]
theorem idealQuotientRightFreeLinearEquiv_mk
    (I : Ideal R) [I.IsTwoSided] (x : ι → R) :
    idealQuotientRightFreeLinearEquiv ι I
        (Submodule.Quotient.mk
          (p := idealSubmodule (M := ι → R) I) x) =
      fun i ↦ Ideal.Quotient.mk I (x i) := by
  simp [idealQuotientRightFreeLinearEquiv]

end IdealQuotient

end ModuleCat.RightExtension
