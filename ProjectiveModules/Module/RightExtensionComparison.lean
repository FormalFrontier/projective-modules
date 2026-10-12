/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Lens
module

public import ProjectiveModules.Module.RightExtension

/-!
# Identity and composition comparisons for right scalar extension

For arbitrary rings and right modules, this file constructs the canonical
linear equivalences for extension along an identity and along a composite of
ring homomorphisms. Tensors are module-first: the composition comparison sends
`(m ⊗ s) ⊗ t` to `m ⊗ (ψ(s) * t)`, with multiplication in the original target
ring. Its inverse sends `m ⊗ t` to `(m ⊗ 1) ⊗ t`.

The scalar universes `uR`, `uS`, `uT` and module universe `uM` are independent.
The identity extension has carrier universe `max uM uR`, the direct composite
`max uM uT`, and the iterated extension `max uM uS uT`. `LinearEquiv` supports
different carrier universes, so these pointwise comparisons need no carrier
lifts. Later categorical packaging in a common `ModuleCat` universe requires
suitable `ULift`s. These comparisons do not supply categorical natural
isomorphisms or unit, associativity or pseudofunctor coherence laws.

## Formalization references

The constructions use the balanced and semilinear universal properties of
`BalancedTensorProduct` and `ModuleCat.RightExtension`, originally contributed
by Prism and subsequently maintained in this library. They use Mathlib's
semilinear-map and linear-equivalence interfaces for the comparison data and
inverse laws.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe uR uS uT uM

namespace ModuleCat.RightExtension

section PureTensors

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (f : R →+* S)
variable {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M]

private theorem tmul_zero_left (s : S) : tmul f (0 : M) s = 0 := by
  let _ : Module R S := f.toModule
  exact BalancedTensorProduct.zero_tmul s

private theorem tmul_add_left (m n : M) (s : S) :
    tmul f (m + n) s = tmul f m s + tmul f n s := by
  let _ : Module R S := f.toModule
  exact BalancedTensorProduct.add_tmul m n s

private theorem tmul_zero_right (m : M) : tmul f m 0 = 0 := by
  let _ : Module R S := f.toModule
  exact BalancedTensorProduct.tmul_zero m

private theorem tmul_add_right (m : M) (s t : S) :
    tmul f m (s + t) = tmul f m s + tmul f m t := by
  let _ : Module R S := f.toModule
  exact BalancedTensorProduct.tmul_add m s t

private def tmulAddHom (s : S) : M →+ Obj f M where
  toFun m := tmul f m s
  map_zero' := tmul_zero_left f s
  map_add' m n := tmul_add_left f m n s

end PureTensors

section Identity

variable (R : Type uR) [Ring R]
variable (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]

private def idTo : Obj (RingHom.id R) M →ₗ[Rᵐᵒᵖ] M :=
  fromSemilinear (RingHom.id R)
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        change r • m = r • m
        rfl }

private theorem idTo_tmul (m : M) (r : R) :
    idTo R M (tmul (RingHom.id R) m r) = MulOpposite.op r • m := by
  exact fromSemilinear_tmul (RingHom.id R) _ m r

private def idFrom : M →ₗ[Rᵐᵒᵖ] Obj (RingHom.id R) M where
  toFun := tmulOne (RingHom.id R)
  map_add' := (tmulOne (RingHom.id R)).map_add
  map_smul' r m := by
    exact (tmulOne (RingHom.id R)).map_smulₛₗ r m

private theorem idFrom_apply (m : M) :
    idFrom R M m = tmul (RingHom.id R) m 1 := rfl

/-- The canonical right-linear equivalence for extension along the identity
ring homomorphism. It sends `m ⊗ r` to `op r • m`, with inverse `m ↦ m ⊗ 1`. -/
noncomputable def idLinearEquiv : Obj (RingHom.id R) M ≃ₗ[Rᵐᵒᵖ] M where
  __ := private LinearEquiv.ofLinearMap
    (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids) (idTo R M) (idFrom R M)
    (by
      apply LinearMap.ext
      intro m
      change idTo R M (tmul (RingHom.id R) m 1) = m
      rw [idTo_tmul]
      exact one_smul Rᵐᵒᵖ m)
    (by
      apply linearMap_ext (RingHom.id R)
      intro m r
      change tmul (RingHom.id R) (idTo R M (tmul (RingHom.id R) m r)) 1 =
        tmul (RingHom.id R) m r
      rw [idTo_tmul, smul_tmul]
      simp)

variable {R M}

/-- The identity comparison evaluates a pure tensor by the right action. -/
@[simp]
theorem idLinearEquiv_tmul (m : M) (r : R) :
    idLinearEquiv R M (tmul (RingHom.id R) m r) = MulOpposite.op r • m :=
  idTo_tmul R M m r

/-- The inverse identity comparison inserts the coefficient `1`. -/
@[simp]
theorem idLinearEquiv_symm_apply (m : M) :
    (idLinearEquiv R M).symm m = tmul (RingHom.id R) m 1 :=
  idFrom_apply R M m

end Identity

section Composition

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [Ring R] [Ring S] [Ring T]
variable (φ : R →+* S) (ψ : S →+* T)
variable {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M]

private def compToAddHom : Obj φ M →+ Obj (ψ.comp φ) M := by
  letI : Module R S := φ.toModule
  apply BalancedTensorProduct.lift
  exact
    { toFun := fun m s => tmul (ψ.comp φ) m (ψ s)
      map_zero_left := fun s => tmul_zero_left (ψ.comp φ) (ψ s)
      map_add_left := fun m n s => tmul_add_left (ψ.comp φ) m n (ψ s)
      map_zero_right := fun m => by
        rw [ψ.map_zero]
        exact tmul_zero_right (ψ.comp φ) m
      map_add_right := fun m s t => by
        rw [ψ.map_add]
        exact tmul_add_right (ψ.comp φ) m (ψ s) (ψ t)
      balance := fun r m s => by
        change tmul (ψ.comp φ) (MulOpposite.op r • m) (ψ s) =
          tmul (ψ.comp φ) m (ψ (φ r * s))
        rw [smul_tmul]
        change tmul (ψ.comp φ) m (ψ (φ r) * ψ s) =
          tmul (ψ.comp φ) m (ψ (φ r * s))
        rw [ψ.map_mul] }

private theorem compToAddHom_tmul (m : M) (s : S) :
    compToAddHom φ ψ (tmul φ m s) = tmul (ψ.comp φ) m (ψ s) := by
  let _ : Module R S := φ.toModule
  change BalancedTensorProduct.lift _ (BalancedTensorProduct.tmul m s) = _
  exact BalancedTensorProduct.lift_tmul _ m s

private def compToSemilinear : Obj φ M →ₛₗ[RingHom.op ψ] Obj (ψ.comp φ) M where
  __ := compToAddHom φ ψ
  map_smul' a z := by
    let _ : Module R S := φ.toModule
    let _ : SMulCommClass R Sᵐᵒᵖ S := smulCommClass φ
    let lhs : Obj φ M →+ Obj (ψ.comp φ) M :=
      (compToAddHom φ ψ).comp (BalancedTensorProduct.smulAddHom a)
    let rhs : Obj φ M →+ Obj (ψ.comp φ) M :=
      { toFun := fun x => (RingHom.op ψ a) • compToAddHom φ ψ x
        map_zero' := by rw [(compToAddHom φ ψ).map_zero, smul_zero]
        map_add' := fun x y => by rw [(compToAddHom φ ψ).map_add, smul_add] }
    exact DFunLike.congr_fun
      (BalancedTensorProduct.hom_ext (R := R) (M := M) (N := S)
        (g := lhs) (h := rhs) fun m s => by
          change compToAddHom φ ψ (a • tmul φ m s) =
            (RingHom.op ψ a) • compToAddHom φ ψ (tmul φ m s)
          rw [tmul_smul, compToAddHom_tmul, compToAddHom_tmul, tmul_smul]
          change tmul (ψ.comp φ) m (ψ (s * MulOpposite.unop a)) =
            tmul (ψ.comp φ) m (ψ s * ψ (MulOpposite.unop a))
          rw [ψ.map_mul]) z

private def compTo : Obj ψ (Obj φ M) →ₗ[Tᵐᵒᵖ] Obj (ψ.comp φ) M :=
  fromSemilinear ψ (compToSemilinear φ ψ)

private theorem compTo_tmul (m : M) (s : S) (t : T) :
    compTo φ ψ (tmul ψ (tmul φ m s) t) = tmul (ψ.comp φ) m (ψ s * t) := by
  calc
    compTo φ ψ (tmul ψ (tmul φ m s) t) =
        MulOpposite.op t • compToAddHom φ ψ (tmul φ m s) :=
      fromSemilinear_tmul ψ (compToSemilinear φ ψ) (tmul φ m s) t
    _ = MulOpposite.op t • tmul (ψ.comp φ) m (ψ s) :=
      congrArg (fun x : Obj (ψ.comp φ) M => MulOpposite.op t • x)
        (compToAddHom_tmul φ ψ m s)
    _ = tmul (ψ.comp φ) m (ψ s * t) :=
      tmul_smul (ψ.comp φ) m (ψ s) (MulOpposite.op t)

private def compFromSemilinear : M →ₛₗ[RingHom.op (ψ.comp φ)] Obj ψ (Obj φ M) where
  toFun m := tmulOne ψ (tmulOne φ m)
  map_add' m n := by
    rw [(tmulOne φ).map_add, (tmulOne ψ).map_add]
  map_smul' r m :=
    (congrArg (tmulOne ψ) ((tmulOne φ).map_smulₛₗ r m)).trans
      ((tmulOne ψ).map_smulₛₗ (RingHom.op φ r) (tmulOne φ m))

private def compFrom : Obj (ψ.comp φ) M →ₗ[Tᵐᵒᵖ] Obj ψ (Obj φ M) :=
  fromSemilinear (ψ.comp φ) (compFromSemilinear φ ψ)

private theorem compFrom_tmul (m : M) (t : T) :
    compFrom φ ψ (tmul (ψ.comp φ) m t) = tmul ψ (tmul φ m 1) t := by
  rw [compFrom, fromSemilinear_tmul]
  change MulOpposite.op t • tmul ψ (tmul φ m 1) 1 = _
  rw [tmul_smul]
  change tmul ψ (tmul φ m 1) (1 * t) = _
  rw [one_mul]

private theorem compTo_compFrom :
    (compTo (M := M) φ ψ).comp (compFrom φ ψ) = LinearMap.id := by
  apply linearMap_ext (ψ.comp φ)
  intro m t
  change compTo φ ψ (compFrom φ ψ (tmul (ψ.comp φ) m t)) =
    tmul (ψ.comp φ) m t
  rw [compFrom_tmul, compTo_tmul, ψ.map_one, one_mul]

private theorem compFrom_compTo :
    (compFrom (M := M) φ ψ).comp (compTo φ ψ) = LinearMap.id := by
  apply linearMap_ext ψ
  intro z t
  let _ : Module R S := φ.toModule
  -- At a fixed outer coefficient the inner maps are additive, not S-linear.
  let lhs : Obj φ M →+ Obj ψ (Obj φ M) :=
    ((compFrom φ ψ).toAddMonoidHom.comp (compTo φ ψ).toAddMonoidHom).comp
      (tmulAddHom ψ t)
  let rhs : Obj φ M →+ Obj ψ (Obj φ M) := tmulAddHom ψ t
  exact DFunLike.congr_fun
    (BalancedTensorProduct.hom_ext (R := R) (M := M) (N := S)
      (g := lhs) (h := rhs) fun m s => by
        change compFrom φ ψ (compTo φ ψ (tmul ψ (tmul φ m s) t)) =
          tmul ψ (tmul φ m s) t
        rw [compTo_tmul, compFrom_tmul]
        calc
          tmul ψ (tmul φ m 1) (ψ s * t) =
              tmul ψ (MulOpposite.op s • tmul φ m 1) t :=
            (smul_tmul ψ s (tmul φ m 1) t).symm
          _ = tmul ψ (tmul φ m s) t := by
            rw [tmul_smul]
            change tmul ψ (tmul φ m (1 * s)) t = _
            rw [one_mul]) z

/-- Iterated right scalar extension is canonically equivalent to extension
along the composite. On nested pure tensors the coefficient is `ψ(s) * t` in
`T`; the inverse inserts `1` in the intermediate coefficient. -/
noncomputable def compLinearEquiv (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    Obj ψ (Obj φ M) ≃ₗ[Tᵐᵒᵖ] Obj (ψ.comp φ) M where
  __ := private LinearEquiv.ofLinearMap (compTo (M := M) φ ψ) (compFrom φ ψ)
    (by exact compTo_compFrom φ ψ) (by exact compFrom_compTo φ ψ)

/-- The composition comparison multiplies the intermediate coefficient on
the left of the outer coefficient, in the original target ring. -/
@[simp]
theorem compLinearEquiv_tmul (m : M) (s : S) (t : T) :
    compLinearEquiv φ ψ M (tmul ψ (tmul φ m s) t) =
      tmul (ψ.comp φ) m (ψ s * t) :=
  compTo_tmul φ ψ m s t

/-- The inverse composition comparison inserts the intermediate coefficient
`1` and retains the target coefficient. -/
@[simp]
theorem compLinearEquiv_symm_tmul (m : M) (t : T) :
    (compLinearEquiv φ ψ M).symm (tmul (ψ.comp φ) m t) =
      tmul ψ (tmul φ m 1) t :=
  compFrom_tmul φ ψ m t

end Composition

end ModuleCat.RightExtension
