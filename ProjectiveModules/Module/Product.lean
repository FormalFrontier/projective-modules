/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.RightProduct

/-!
# Modules over finite products of coefficient semirings

A family of left modules carries Mathlib's pointwise `Pi.module'` action of the
product of its coefficient semirings. For a finite index type, finite generation
and projectivity of the factors give the corresponding properties over the
coefficient product. The scalar, index and module-carrier universes are independent.

The complementary right-action results are `Module.finite_piRight` and
`Module.projective_piRight`.

## References

Mathlib's pointwise module structures are due to Simon Hudon and Patrick Massot,
its finite-generation API to Johan Commelin, and its projectivity API to
Kevin Buzzard and Antoine Labelle.
-/

@[expose] public section

universe uι uR uM

namespace Module

-- Scalar transport only: the closure arguments below are the right-product
-- theorems, applied to the opposite coefficient family.
private def doubleOppositeEquiv
    (R : Type uR) (M : Type uM) [Semiring R] [AddCommMonoid M] [Module R M] :
    letI : Module Rᵐᵒᵖᵐᵒᵖ M :=
      Module.compHom M (RingEquiv.opOp R).symm.toRingHom
    letI _opOpInvPair :
        RingHomInvPair (RingEquiv.opOp R).toRingHom (RingEquiv.opOp R).symm.toRingHom :=
      RingHomInvPair.of_ringEquiv (RingEquiv.opOp R)
    letI _opOpInvPairSymm :
        RingHomInvPair (RingEquiv.opOp R).symm.toRingHom (RingEquiv.opOp R).toRingHom :=
      RingHomInvPair.of_ringEquiv_symm (RingEquiv.opOp R)
    LinearEquiv (RingEquiv.opOp R).toRingHom
      (σ' := (RingEquiv.opOp R).symm.toRingHom) M M := by
  letI : Module Rᵐᵒᵖᵐᵒᵖ M :=
    Module.compHom M (RingEquiv.opOp R).symm.toRingHom
  letI opOpInvPair :
      RingHomInvPair (RingEquiv.opOp R).toRingHom (RingEquiv.opOp R).symm.toRingHom :=
    RingHomInvPair.of_ringEquiv (RingEquiv.opOp R)
  letI opOpInvPairSymm :
      RingHomInvPair (RingEquiv.opOp R).symm.toRingHom (RingEquiv.opOp R).toRingHom :=
    RingHomInvPair.of_ringEquiv_symm (RingEquiv.opOp R)
  exact
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private def doubleOppositePiRingEquiv
    {ι : Type uι} (Ri : ι → Type uR) [∀ i, Semiring (Ri i)] :
    (∀ i, (Ri i)ᵐᵒᵖ)ᵐᵒᵖ ≃+* (∀ i, Ri i) :=
  (RingEquiv.piMulOpposite (fun i => (Ri i)ᵐᵒᵖ)).trans
    (RingEquiv.piCongrRight fun i => (RingEquiv.opOp (Ri i)).symm)

variable {ι : Type uι} (Ri : ι → Type uR) (Mi : ι → Type uM)
variable [∀ i, Semiring (Ri i)] [∀ i, AddCommMonoid (Mi i)]
variable [∀ i, Module (Ri i) (Mi i)]

-- Both carrier maps are the identity. The scalar check explicitly identifies
-- the transported right-product action with the canonical left Pi action.
private def doubleOppositePiEquiv :
    letI : ∀ i, Module (Ri i)ᵐᵒᵖᵐᵒᵖ (Mi i) := fun i =>
      Module.compHom (Mi i) (RingEquiv.opOp (Ri i)).symm.toRingHom
    letI : Module (∀ i, (Ri i)ᵐᵒᵖ)ᵐᵒᵖ (∀ i, Mi i) :=
      piRightModule (fun i => (Ri i)ᵐᵒᵖ) Mi
    letI : Module (∀ i, Ri i) (∀ i, Mi i) := Pi.module'
    letI _piInvPair :
        RingHomInvPair (doubleOppositePiRingEquiv Ri).toRingHom
          (doubleOppositePiRingEquiv Ri).symm.toRingHom :=
      RingHomInvPair.of_ringEquiv (doubleOppositePiRingEquiv Ri)
    letI _piInvPairSymm :
        RingHomInvPair (doubleOppositePiRingEquiv Ri).symm.toRingHom
          (doubleOppositePiRingEquiv Ri).toRingHom :=
      RingHomInvPair.of_ringEquiv_symm (doubleOppositePiRingEquiv Ri)
    LinearEquiv (doubleOppositePiRingEquiv Ri).toRingHom
      (σ' := (doubleOppositePiRingEquiv Ri).symm.toRingHom)
      (∀ i, Mi i) (∀ i, Mi i) := by
  letI : ∀ i, Module (Ri i)ᵐᵒᵖᵐᵒᵖ (Mi i) := fun i =>
    Module.compHom (Mi i) (RingEquiv.opOp (Ri i)).symm.toRingHom
  letI : Module (∀ i, (Ri i)ᵐᵒᵖ)ᵐᵒᵖ (∀ i, Mi i) :=
    piRightModule (fun i => (Ri i)ᵐᵒᵖ) Mi
  letI : Module (∀ i, Ri i) (∀ i, Mi i) := Pi.module'
  letI piInvPair :
      RingHomInvPair (doubleOppositePiRingEquiv Ri).toRingHom
        (doubleOppositePiRingEquiv Ri).symm.toRingHom :=
    RingHomInvPair.of_ringEquiv (doubleOppositePiRingEquiv Ri)
  letI piInvPairSymm :
      RingHomInvPair (doubleOppositePiRingEquiv Ri).symm.toRingHom
        (doubleOppositePiRingEquiv Ri).toRingHom :=
    RingHomInvPair.of_ringEquiv_symm (doubleOppositePiRingEquiv Ri)
  exact
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => funext fun i =>
        (show ((a.unop i).unop : Ri i) • x i =
          ((a.unop i).unop : Ri i) • x i from rfl) }

/-- A finite family of finitely generated modules is finitely generated over the
product of its coefficient semirings, with the pointwise left action. -/
theorem finite_pi [_root_.Finite ι] [∀ i, Module.Finite (Ri i) (Mi i)] :
    Module.Finite (∀ i, Ri i) (∀ i, Mi i) := by
  let : ∀ i, Module (Ri i)ᵐᵒᵖᵐᵒᵖ (Mi i) := fun i =>
    Module.compHom (Mi i) (RingEquiv.opOp (Ri i)).symm.toRingHom
  let : ∀ i, Module.Finite (Ri i)ᵐᵒᵖᵐᵒᵖ (Mi i) := fun i => by
    let opOpInvPair :
        RingHomInvPair (RingEquiv.opOp (Ri i)).toRingHom (RingEquiv.opOp (Ri i)).symm.toRingHom :=
      RingHomInvPair.of_ringEquiv (RingEquiv.opOp (Ri i))
    let opOpInvPairSymm :
        RingHomInvPair (RingEquiv.opOp (Ri i)).symm.toRingHom (RingEquiv.opOp (Ri i)).toRingHom :=
      RingHomInvPair.of_ringEquiv_symm (RingEquiv.opOp (Ri i))
    exact @Module.Finite.of_surjective (Ri i) (Mi i) _ _ inferInstance
      (Ri i)ᵐᵒᵖᵐᵒᵖ (Mi i) _ _
      (Module.compHom (Mi i) (RingEquiv.opOp (Ri i)).symm.toRingHom)
      (RingEquiv.opOp (Ri i)).toRingHom inferInstance
      (doubleOppositeEquiv (Ri i) (Mi i)).toLinearMap
      (doubleOppositeEquiv (Ri i) (Mi i)).surjective
  let : Module (∀ i, (Ri i)ᵐᵒᵖ)ᵐᵒᵖ (∀ i, Mi i) :=
    piRightModule (fun i => (Ri i)ᵐᵒᵖ) Mi
  let : Module.Finite (∀ i, (Ri i)ᵐᵒᵖ)ᵐᵒᵖ (∀ i, Mi i) :=
    finite_piRight (fun i => (Ri i)ᵐᵒᵖ) Mi
  let piInvPair :
      RingHomInvPair (doubleOppositePiRingEquiv Ri).toRingHom
        (doubleOppositePiRingEquiv Ri).symm.toRingHom :=
    RingHomInvPair.of_ringEquiv (doubleOppositePiRingEquiv Ri)
  let piInvPairSymm :
      RingHomInvPair (doubleOppositePiRingEquiv Ri).symm.toRingHom
        (doubleOppositePiRingEquiv Ri).toRingHom :=
    RingHomInvPair.of_ringEquiv_symm (doubleOppositePiRingEquiv Ri)
  exact @Module.Finite.of_surjective
    (∀ i, (Ri i)ᵐᵒᵖ)ᵐᵒᵖ (∀ i, Mi i) _ _
    (piRightModule (fun i => (Ri i)ᵐᵒᵖ) Mi)
    (∀ i, Ri i) (∀ i, Mi i) _ _ Pi.module'
    (doubleOppositePiRingEquiv Ri).toRingHom inferInstance
    (doubleOppositePiEquiv Ri Mi).toLinearMap
    (doubleOppositePiEquiv Ri Mi).surjective

/-- A finite family of projective modules is projective over the product of its
coefficient semirings, with the pointwise left action. -/
theorem projective_pi [_root_.Finite ι] [∀ i, Module.Projective (Ri i) (Mi i)] :
    Module.Projective (∀ i, Ri i) (∀ i, Mi i) := by
  let : ∀ i, Module (Ri i)ᵐᵒᵖᵐᵒᵖ (Mi i) := fun i =>
    Module.compHom (Mi i) (RingEquiv.opOp (Ri i)).symm.toRingHom
  let : ∀ i, Module.Projective (Ri i)ᵐᵒᵖᵐᵒᵖ (Mi i) := fun i => by
    let opOpInvPair :
        RingHomInvPair (RingEquiv.opOp (Ri i)).toRingHom (RingEquiv.opOp (Ri i)).symm.toRingHom :=
      RingHomInvPair.of_ringEquiv (RingEquiv.opOp (Ri i))
    let opOpInvPairSymm :
        RingHomInvPair (RingEquiv.opOp (Ri i)).symm.toRingHom (RingEquiv.opOp (Ri i)).toRingHom :=
      RingHomInvPair.of_ringEquiv_symm (RingEquiv.opOp (Ri i))
    exact @Module.Projective.of_equiv (Ri i) (Ri i)ᵐᵒᵖᵐᵒᵖ _ _
      (Mi i) (Mi i) _ _ inferInstance
      (Module.compHom (Mi i) (RingEquiv.opOp (Ri i)).symm.toRingHom)
      (RingEquiv.opOp (Ri i)).toRingHom
      (RingEquiv.opOp (Ri i)).symm.toRingHom inferInstance inferInstance
      (doubleOppositeEquiv (Ri i) (Mi i)) inferInstance
  let : Module (∀ i, (Ri i)ᵐᵒᵖ)ᵐᵒᵖ (∀ i, Mi i) :=
    piRightModule (fun i => (Ri i)ᵐᵒᵖ) Mi
  let : Module.Projective (∀ i, (Ri i)ᵐᵒᵖ)ᵐᵒᵖ (∀ i, Mi i) :=
    projective_piRight (fun i => (Ri i)ᵐᵒᵖ) Mi
  let piInvPair :
      RingHomInvPair (doubleOppositePiRingEquiv Ri).toRingHom
        (doubleOppositePiRingEquiv Ri).symm.toRingHom :=
    RingHomInvPair.of_ringEquiv (doubleOppositePiRingEquiv Ri)
  let piInvPairSymm :
      RingHomInvPair (doubleOppositePiRingEquiv Ri).symm.toRingHom
        (doubleOppositePiRingEquiv Ri).toRingHom :=
    RingHomInvPair.of_ringEquiv_symm (doubleOppositePiRingEquiv Ri)
  exact @Module.Projective.of_equiv
    (∀ i, (Ri i)ᵐᵒᵖ)ᵐᵒᵖ (∀ i, Ri i) _ _
    (∀ i, Mi i) (∀ i, Mi i) _ _
    (piRightModule (fun i => (Ri i)ᵐᵒᵖ) Mi) Pi.module'
    (doubleOppositePiRingEquiv Ri).toRingHom
    (doubleOppositePiRingEquiv Ri).symm.toRingHom inferInstance inferInstance
    (doubleOppositePiEquiv Ri Mi) inferInstance

end Module
