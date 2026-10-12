/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.RightExtensionComparison

/-!
# Unit and associativity laws for right-extension comparisons

For arbitrary rings and right modules, the identity and composition comparisons
satisfy pointwise unit and triple-composition laws. The left unit compares the
composition comparison with scalar extension of the identity comparison. The
right unit identifies the composition comparison with the identity comparison
on the extended module. Triple associativity compares two linear maps from a
threefold extension to extension along the composite ring homomorphism.

The scalar universes `uR`, `uS`, `uT`, `uU` and the module universe `uM` are
independent. The threefold extension has carrier universe `max uM uS uT uU`;
the direct extension has carrier universe `max uM uU`. On a pure tensor
`((m ⊗ s) ⊗ t) ⊗ u`, the two routes have coefficients
`θ (ψ s * t) * u` and `θ (ψ s) * (θ t * u)`. The order is preserved: only
multiplicativity of `θ` and associativity in `U` are needed, not commutativity.

## Limitations

These are unbundled equalities of comparison maps, not categorical triangle or
pentagon laws. They do not construct common-universe carrier lifts, natural
isomorphisms, or compatibility between scalar extension and such lifts.

## Formalization references

The statements use this library's balanced tensor and right-extension APIs,
originally contributed by Prism and maintained by Prism and Lens, and its
identity and composition comparisons contributed by Lens. Mathlib's
`ModuleCat.extendScalars_id_comp`, `ModuleCat.extendScalars_comp_id` and
`ModuleCat.extendScalars_assoc` describe the analogous categorical laws for
commutative rings; the statements here concern module-first balanced tensors
over arbitrary rings instead. Ring-homomorphism composition and linear-map
composition use Mathlib's interfaces.
-/

@[expose] public section

universe uR uS uT uU uM

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} {T : Type uT} {U : Type uU}
variable [Ring R] [Ring S] [Ring T] [Ring U]
variable (φ : R →+* S) (ψ : S →+* T) (θ : T →+* U)
variable (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- The composition comparison with an identity first is scalar extension of
that identity comparison. Both maps send `(m ⊗ r) ⊗ s` to `m ⊗ (φ r * s)`. -/
@[simp]
theorem compLinearEquiv_id_left :
    (compLinearEquiv (RingHom.id R) φ M).toLinearMap =
      map φ (idLinearEquiv R M).toLinearMap := by
  apply linearMap_ext φ
  intro z s
  let : Module R S := φ.toModule
  let tensor : Obj (RingHom.id R) M →+ Obj φ (Obj (RingHom.id R) M) :=
    { toFun := fun x => tmul φ x s
      map_zero' := BalancedTensorProduct.zero_tmul s
      map_add' := fun x y => BalancedTensorProduct.add_tmul x y s }
  -- At a fixed outer coefficient the inner maps are only additive.
  let lhs : Obj (RingHom.id R) M →+ Obj φ M :=
    (compLinearEquiv (RingHom.id R) φ M).toLinearMap.toAddMonoidHom.comp tensor
  let rhs : Obj (RingHom.id R) M →+ Obj φ M :=
    (map φ (idLinearEquiv R M).toLinearMap).toAddMonoidHom.comp tensor
  let : Module R R := (RingHom.id R).toModule
  have h : lhs = rhs := by
    apply BalancedTensorProduct.hom_ext (R := R) (M := M) (N := R)
    intro m r
    change compLinearEquiv (RingHom.id R) φ M
        (tmul φ (tmul (RingHom.id R) m r) s) =
      map φ (idLinearEquiv R M).toLinearMap
        (tmul φ (tmul (RingHom.id R) m r) s)
    simp only [compLinearEquiv_tmul, map_tmul, LinearEquiv.coe_toLinearMap,
      idLinearEquiv_tmul, smul_tmul]
    rfl
  exact DFunLike.congr_fun h z

/-- The composition comparison with an identity last is the identity
comparison on the extended module. Both evaluate `z ⊗ s` by the right
`S`-action on `z`. -/
@[simp]
theorem compLinearEquiv_id_right :
    compLinearEquiv φ (RingHom.id S) M = idLinearEquiv S (Obj φ M) := by
  apply LinearEquiv.toLinearMap_injective
  apply linearMap_ext (RingHom.id S)
  intro z s
  let : Module S S := (RingHom.id S).toModule
  let tensor : Obj φ M →+ Obj (RingHom.id S) (Obj φ M) :=
    { toFun := fun x => tmul (RingHom.id S) x s
      map_zero' := BalancedTensorProduct.zero_tmul s
      map_add' := fun x y => BalancedTensorProduct.add_tmul x y s }
  -- At a fixed outer coefficient the inner maps are only additive.
  let lhs : Obj φ M →+ Obj φ M :=
    (compLinearEquiv φ (RingHom.id S) M).toLinearMap.toAddMonoidHom.comp tensor
  let rhs : Obj φ M →+ Obj φ M :=
    (idLinearEquiv S (Obj φ M)).toLinearMap.toAddMonoidHom.comp tensor
  let : Module R S := φ.toModule
  have h : lhs = rhs := by
    apply BalancedTensorProduct.hom_ext (R := R) (M := M) (N := S)
    intro m a
    change compLinearEquiv φ (RingHom.id S) M
        (tmul (RingHom.id S) (tmul φ m a) s) =
      idLinearEquiv S (Obj φ M) (tmul (RingHom.id S) (tmul φ m a) s)
    simp only [compLinearEquiv_tmul, idLinearEquiv_tmul, RingHom.id_apply,
      tmul_smul, op_smul_eq_mul]
    rfl
  exact DFunLike.congr_fun h z

/-- Comparing the first two extensions and then the third gives the same
linear map as comparing the last two and then the first. On a threefold pure
tensor, the ordered coefficient identity is
`θ (ψ s * t) * u = θ (ψ s) * (θ t * u)`. -/
theorem compLinearEquiv_assoc :
    (compLinearEquiv (ψ.comp φ) θ M).toLinearMap.comp
        (map θ (compLinearEquiv φ ψ M).toLinearMap) =
      (compLinearEquiv φ (θ.comp ψ) M).toLinearMap.comp
        (compLinearEquiv ψ θ (Obj φ M)).toLinearMap := by
  let : Module R S := φ.toModule
  let : Module S T := ψ.toModule
  let : Module T U := θ.toModule
  let firstRoute : Obj θ (Obj ψ (Obj φ M)) →ₗ[Uᵐᵒᵖ] Obj (θ.comp (ψ.comp φ)) M :=
    (compLinearEquiv (ψ.comp φ) θ M).toLinearMap.comp
      (map θ (compLinearEquiv φ ψ M).toLinearMap)
  let secondRoute : Obj θ (Obj ψ (Obj φ M)) →ₗ[Uᵐᵒᵖ] Obj (θ.comp (ψ.comp φ)) M :=
    (compLinearEquiv φ (θ.comp ψ) M).toLinearMap.comp
      (compLinearEquiv ψ θ (Obj φ M)).toLinearMap
  have pure (m : M) (s : S) (t : T) (u : U) :
      firstRoute (tmul θ (tmul ψ (tmul φ m s) t) u) =
        secondRoute (tmul θ (tmul ψ (tmul φ m s) t) u) := by
    simp only [firstRoute, secondRoute, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, map_tmul, compLinearEquiv_tmul,
      RingHom.comp_apply, θ.map_mul, mul_assoc, RingHom.comp_assoc]
  suffices firstRoute = secondRoute from this
  apply linearMap_ext θ
  intro z u
  -- Fixing the outer coefficient gives additive maps, not T-linear maps.
  let outerTensor : Obj ψ (Obj φ M) →+ Obj θ (Obj ψ (Obj φ M)) :=
    { toFun := fun x => tmul θ x u
      map_zero' := BalancedTensorProduct.zero_tmul u
      map_add' := fun x y => BalancedTensorProduct.add_tmul x y u }
  let lhs : Obj ψ (Obj φ M) →+ Obj (θ.comp (ψ.comp φ)) M :=
    firstRoute.toAddMonoidHom.comp outerTensor
  let rhs : Obj ψ (Obj φ M) →+ Obj (θ.comp (ψ.comp φ)) M :=
    secondRoute.toAddMonoidHom.comp outerTensor
  have outer : lhs = rhs := by
    apply BalancedTensorProduct.hom_ext (R := S) (M := Obj φ M) (N := T)
      (g := lhs) (h := rhs)
    intro x t
    -- Fixing the next coefficient likewise gives additive, not S-linear, maps.
    let innerTensor : Obj φ M →+ Obj ψ (Obj φ M) :=
      { toFun := fun y => tmul ψ y t
        map_zero' := BalancedTensorProduct.zero_tmul t
        map_add' := fun y w => BalancedTensorProduct.add_tmul y w t }
    let lhs' : Obj φ M →+ Obj (θ.comp (ψ.comp φ)) M := lhs.comp innerTensor
    let rhs' : Obj φ M →+ Obj (θ.comp (ψ.comp φ)) M := rhs.comp innerTensor
    have inner : lhs' = rhs' := by
      apply BalancedTensorProduct.hom_ext (R := R) (M := M) (N := S)
        (g := lhs') (h := rhs')
      intro m s
      exact pure m s t u
    exact DFunLike.congr_fun inner x
  exact DFunLike.congr_fun outer z

end ModuleCat.RightExtension
