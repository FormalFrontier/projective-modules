/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs

/-!
# Semilinear maps and restriction of scalars

`LinearMap.semilinearCompHomEquiv` identifies `σ`-semilinear maps with linear
maps into the target equipped with the canonical action `Module.compHom M σ`.
It preserves the underlying function in both directions and is linear for any
auxiliary scalar action commuting with the target's original scalar action.
The source, target and three scalar universes are independent, and none of the
semirings need be commutative.

The pointwise formulas are `LinearMap.semilinearCompHomEquiv_apply` and
`LinearMap.semilinearCompHomEquiv_symm_apply`. Inverse cancellation and
preservation of auxiliary scalar multiplication are supplied by the usual
`LinearEquiv` API.

## References

Scalar restriction in finitely supported Hom uses the additive part of this
equivalence. The categorical ring specialization is Jujian Zhang's
`ModuleCat.semilinearMapAddEquiv` in Mathlib; its comparison with this
equivalence is in `ProjectiveModules.Category.ChangeOfScalars`.
-/

@[expose] public section

universe uR uS uT uL uM

namespace LinearMap

variable {R : Type uR} {S : Type uS} (T : Type uT)
variable [Semiring R] [Semiring S] [Semiring T]
variable {L : Type uL} {M : Type uM}
variable [AddCommMonoid L] [AddCommMonoid M]
variable [Module R L] [Module S M] [Module T M] [SMulCommClass S T M]
variable (σ : R →+* S)

/-- Semilinear maps identify with linear maps into the canonically restricted
target. The identification leaves the underlying function unchanged in both
directions and is linear for every auxiliary scalar action commuting with the
original target action. Commutation with the restricted action is derived
from commutation with the original action. -/
def semilinearCompHomEquiv :
    letI := Module.compHom M σ
    letI : SMulCommClass R T M := SMul.comp.smulCommClass σ
    (L →ₛₗ[σ] M) ≃ₗ[T] (L →ₗ[R] M) :=
  letI := Module.compHom M σ
  letI : SMulCommClass R T M := SMul.comp.smulCommClass σ
  { toFun := fun f =>
      { toFun := f
        map_add' := f.map_add
        map_smul' := f.map_smulₛₗ }
    invFun := fun f =>
      { toFun := f
        map_add' := f.map_add
        map_smul' := f.map_smul }
    left_inv := fun _ => by ext; rfl
    right_inv := fun _ => by ext; rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- Restricting the target scalars of a semilinear map does not change its values. -/
@[simp]
theorem semilinearCompHomEquiv_apply (f : L →ₛₗ[σ] M) (l : L) :
    semilinearCompHomEquiv T σ f l = f l := rfl

/-- Interpreting a linear map into the canonically restricted target as a
semilinear map does not change its values. -/
@[simp]
theorem semilinearCompHomEquiv_symm_apply
    (f : @LinearMap R R _ _ (RingHom.id R) L M _ _ _ (Module.compHom M σ)) (l : L) :
    (semilinearCompHomEquiv T σ).symm f l = f l := rfl

end LinearMap
