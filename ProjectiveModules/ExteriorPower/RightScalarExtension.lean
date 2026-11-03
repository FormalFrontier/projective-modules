/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.Equiv
public import ProjectiveModules.ExteriorPower.TensorProduct
public import ProjectiveModules.Module.RightExtensionTensorProduct
public import ProjectiveModules.Module.ScalarExtensionTensorProduct

/-!
# Exterior powers and extension of scalars for right modules

The comparison uses the existing opposite-scalar comparison, the coefficient
tensor comparison, and the existing exterior-power base-change equivalence.
It is characterized on extended wedge generators.
-/

@[expose] public section

universe uR uS uP

open scoped TensorProduct ChangeOfRings

namespace exteriorPower

/-- Exterior powers commute with extension of scalars for right modules. -/
noncomputable def rightExtensionEquiv
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (P : Type uP)
    [AddCommGroup P] [Module Rᵐᵒᵖ P] :
    ModuleCat.RightExtension.Obj f (⋀[Rᵐᵒᵖ]^n P) ≃ₗ[Sᵐᵒᵖ]
      (⋀[Sᵐᵒᵖ]^n (ModuleCat.RightExtension.Obj f P)) :=
  let coefficient :=
    (ModuleCat.RightExtension.oppositeScalarEquiv f
        (ModuleCat.of (Rᵐᵒᵖ) P)).trans
      (@ModuleCat.extendScalarsTensorEquiv
        (A := Rᵐᵒᵖ) (B := Sᵐᵒᵖ)
        inferInstance inferInstance (RingHom.op f).toAlgebra
        (ModuleCat.of (Rᵐᵒᵖ) P))
  let degree :=
    (ModuleCat.RightExtension.oppositeScalarEquiv f
        (ModuleCat.of (Rᵐᵒᵖ) (⋀[Rᵐᵒᵖ]^n P))).trans
      (@ModuleCat.extendScalarsTensorEquiv
        (A := Rᵐᵒᵖ) (B := Sᵐᵒᵖ)
        inferInstance inferInstance (RingHom.op f).toAlgebra
        (ModuleCat.of (Rᵐᵒᵖ) (⋀[Rᵐᵒᵖ]^n P)))
  degree.trans
    ((@baseChangeEquiv
      (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ) (M := P)
      inferInstance inferInstance (RingHom.op f).toAlgebra
      inferInstance inferInstance n).trans
        (congr n coefficient.symm))

/-- The scalar-extension comparison sends an extended wedge generator to the
corresponding wedge of extended vectors, with its coefficient acting on the result. -/
theorem rightExtensionEquiv_tmul_ιMulti
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (P : Type uP)
    [AddCommGroup P] [Module Rᵐᵒᵖ P]
    (v : Fin n → P) (s : S) :
    rightExtensionEquiv f n P
        (ModuleCat.RightExtension.tmul f
          (exteriorPower.ιMulti (Rᵐᵒᵖ) n v) s) =
      MulOpposite.op s •
        exteriorPower.ιMulti (Sᵐᵒᵖ) n
          (fun i => ModuleCat.RightExtension.tmul f (v i) 1) := by
  let coefficient :=
    (ModuleCat.RightExtension.oppositeScalarEquiv f
        (ModuleCat.of (Rᵐᵒᵖ) P)).trans
      (@ModuleCat.extendScalarsTensorEquiv
        (A := Rᵐᵒᵖ) (B := Sᵐᵒᵖ)
        inferInstance inferInstance (RingHom.op f).toAlgebra
        (ModuleCat.of (Rᵐᵒᵖ) P))
  let degree :=
    (ModuleCat.RightExtension.oppositeScalarEquiv f
        (ModuleCat.of (Rᵐᵒᵖ) (⋀[Rᵐᵒᵖ]^n P))).trans
      (@ModuleCat.extendScalarsTensorEquiv
        (A := Rᵐᵒᵖ) (B := Sᵐᵒᵖ)
        inferInstance inferInstance (RingHom.op f).toAlgebra
        (ModuleCat.of (Rᵐᵒᵖ) (⋀[Rᵐᵒᵖ]^n P)))
  change congr n coefficient.symm
      ((@baseChangeEquiv
        (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ) (M := P)
        inferInstance inferInstance (RingHom.op f).toAlgebra
        inferInstance inferInstance n)
          (degree (ModuleCat.RightExtension.tmul f
            (exteriorPower.ιMulti (Rᵐᵒᵖ) n v) s))) =
    MulOpposite.op s •
      exteriorPower.ιMulti (Sᵐᵒᵖ) n
        (fun i => ModuleCat.RightExtension.tmul f (v i) 1)
  have hdegree :
      degree (ModuleCat.RightExtension.tmul f
          (exteriorPower.ιMulti (Rᵐᵒᵖ) n v) s) =
        @ModuleCat.extendScalarsTensorEquiv
          (A := Rᵐᵒᵖ) (B := Sᵐᵒᵖ)
          inferInstance inferInstance (RingHom.op f).toAlgebra
          (ModuleCat.of (Rᵐᵒᵖ) (⋀[Rᵐᵒᵖ]^n P))
          (MulOpposite.op s ⊗ₜ[Rᵐᵒᵖ, RingHom.op f]
            exteriorPower.ιMulti (Rᵐᵒᵖ) n v) := by
    exact congrArg
      (@ModuleCat.extendScalarsTensorEquiv
        (A := Rᵐᵒᵖ) (B := Sᵐᵒᵖ)
        inferInstance inferInstance (RingHom.op f).toAlgebra
        (ModuleCat.of (Rᵐᵒᵖ) (⋀[Rᵐᵒᵖ]^n P)))
      (ModuleCat.RightExtension.oppositeScalarEquiv_tmul f
        (ModuleCat.of (Rᵐᵒᵖ) (⋀[Rᵐᵒᵖ]^n P))
        (exteriorPower.ιMulti (Rᵐᵒᵖ) n v) s)
  rw [hdegree,
    @ModuleCat.extendScalarsTensorEquiv_tmul
      (A := Rᵐᵒᵖ) (B := Sᵐᵒᵖ)
      inferInstance inferInstance (RingHom.op f).toAlgebra
      (ModuleCat.of (Rᵐᵒᵖ) (⋀[Rᵐᵒᵖ]^n P)),
    @baseChangeEquiv_tmul_ιMulti
      (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ) (M := P)
      inferInstance inferInstance (RingHom.op f).toAlgebra
      inferInstance inferInstance,
    LinearEquiv.map_smul, congr_ιMulti]
  apply congrArg (fun x => MulOpposite.op s • x)
  apply congrArg (exteriorPower.ιMulti (Sᵐᵒᵖ) n)
  funext i
  apply coefficient.injective
  simp only [LinearEquiv.apply_symm_apply]
  have hcoefficient :
      coefficient (ModuleCat.RightExtension.tmul f (v i) 1) =
        @ModuleCat.extendScalarsTensorEquiv
          (A := Rᵐᵒᵖ) (B := Sᵐᵒᵖ)
          inferInstance inferInstance (RingHom.op f).toAlgebra
          (ModuleCat.of (Rᵐᵒᵖ) P)
          (MulOpposite.op (1 : S) ⊗ₜ[Rᵐᵒᵖ, RingHom.op f] v i) := by
    exact congrArg
      (@ModuleCat.extendScalarsTensorEquiv
        (A := Rᵐᵒᵖ) (B := Sᵐᵒᵖ)
        inferInstance inferInstance (RingHom.op f).toAlgebra
        (ModuleCat.of (Rᵐᵒᵖ) P))
      (ModuleCat.RightExtension.oppositeScalarEquiv_tmul f
        (ModuleCat.of (Rᵐᵒᵖ) P) (v i) 1)
  rw [hcoefficient,
    @ModuleCat.extendScalarsTensorEquiv_tmul
      (A := Rᵐᵒᵖ) (B := Sᵐᵒᵖ)
      inferInstance inferInstance (RingHom.op f).toAlgebra
      (ModuleCat.of (Rᵐᵒᵖ) P)]
  rfl

end exteriorPower
