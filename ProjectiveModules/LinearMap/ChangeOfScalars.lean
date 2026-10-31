/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.TransferInstance

/-!
# Semilinear maps and restriction of scalars

`LinearMap.semilinearCompHomAddEquiv` identifies semilinear maps with ordinary
linear maps into the canonically restricted target, preserving their values.
It requires no auxiliary scalar action.

`LinearMap.semilinearModule` gives the original space of `σ`-semilinear maps
its pointwise auxiliary `T`-module structure. Only commutation of the `T`-action
with the image of `σ` is required: the restricted action on the target is
selected explicitly as `Module.compHom M σ`. This module structure is a
non-instance, so it does not overlap with the usual pointwise module instance.

`LinearMap.semilinearCompHomEquivOfImageComm` identifies this module with the
ordinary linear maps into the canonically restricted target. Both directions
preserve the underlying function. The source, target and three scalar universes
are independent, and none of the semirings need be commutative.

`LinearMap.semilinearCompHomEquiv` is the specialization to auxiliary actions
commuting with the whole original target action. It uses the usual pointwise
module instance on semilinear maps. The pointwise formulas and the full-action
and identity comparisons relate the two module structures and identifications.

## References

Scalar restriction in finitely supported Hom uses the additive part of this
identification. The categorical ring specialization is Jujian Zhang's
`ModuleCat.semilinearMapAddEquiv` in Mathlib; its comparison with
`LinearMap.semilinearCompHomEquiv` is in
`ProjectiveModules.Category.ChangeOfScalars`. Module structures are transported
using Mathlib's `AddEquiv.module` and `AddEquiv.linearEquiv`.
-/

@[expose] public section

universe uR uS uT uL uM

namespace LinearMap

variable {R : Type uR} {S : Type uS} (T : Type uT)
variable [Semiring R] [Semiring S] [Semiring T]
variable {L : Type uL} {M : Type uM}
variable [AddCommMonoid L] [AddCommMonoid M]
variable [Module R L] [Module S M] [Module T M]
variable (σ : R →+* S)

/-- The additive equivalence between semilinear maps and ordinary linear maps
into the target with its canonical scalar action restricted along `σ`.
Both directions preserve the underlying function. -/
def semilinearCompHomAddEquiv :
    (L →ₛₗ[σ] M) ≃+
      @LinearMap R R _ _ (RingHom.id R) L M _ _ _ (Module.compHom M σ) :=
  letI := Module.compHom M σ
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
    map_add' := fun _ _ => rfl }

/-- Restricting the target action preserves a semilinear map's values. -/
@[simp]
theorem semilinearCompHomAddEquiv_apply (f : L →ₛₗ[σ] M) (l : L) :
    semilinearCompHomAddEquiv (L := L) (M := M) σ f l = f l :=
  rfl

/-- Reinterpreting a map into the restricted target preserves its values. -/
@[simp]
theorem semilinearCompHomAddEquiv_symm_apply
    (f : @LinearMap R R _ _ (RingHom.id R) L M _ _ _ (Module.compHom M σ)) (l : L) :
    (semilinearCompHomAddEquiv (L := L) (M := M) σ).symm f l = f l :=
  rfl

section ImageComm

variable [hσ : @SMulCommClass R T M (Module.compHom M σ).toSMul inferInstance]

/-- The usual pointwise auxiliary module on linear maps into the target with
its canonical scalar action restricted along `σ`. -/
@[instance_reducible]
def compHomLinearMapModule :
    Module T (@LinearMap R R _ _ (RingHom.id R) L M _ _ _ (Module.compHom M σ)) := by
  letI := Module.compHom M σ
  exact inferInstance

/-- The canonical pointwise auxiliary module on `σ`-semilinear maps. Only
commutation with the image of `σ` is required. This is a non-instance and uses
the original semilinear-map type, with no action on the source by `T`. -/
@[instance_reducible]
def semilinearModule : Module T (L →ₛₗ[σ] M) := by
  letI := Module.compHom M σ
  letI := compHomLinearMapModule (L := L) (M := M) T σ (hσ := hσ)
  exact (semilinearCompHomAddEquiv (L := L) (M := M) σ).module T

/-- The auxiliary action on linear maps into the canonically restricted target
is pointwise. -/
@[simp]
theorem compHomLinearMapModule_smul_apply (t : T)
    (f : @LinearMap R R _ _ (RingHom.id R) L M _ _ _ (Module.compHom M σ)) (l : L) :
    (@SMul.smul T _ (compHomLinearMapModule (L := L) (M := M) T σ
      (hσ := hσ)).toSMul t f) l = t • f l :=
  rfl

/-- The canonical auxiliary action on semilinear maps is pointwise. -/
@[simp]
theorem semilinearModule_smul_apply (t : T) (f : L →ₛₗ[σ] M) (l : L) :
    (@SMul.smul T _ (semilinearModule (L := L) (M := M) T σ (hσ := hσ)).toSMul t f) l = t • f l :=
  rfl

/-- Coercion to a function preserves the canonical auxiliary scalar action. -/
@[simp]
theorem semilinearModule_coe_smul (t : T) (f : L →ₛₗ[σ] M) :
    ⇑(@SMul.smul T _ (semilinearModule (L := L) (M := M) T σ (hσ := hσ)).toSMul t f) =
      t • (f : L → M) :=
  rfl

/-- Semilinear maps with the canonical auxiliary module identify with linear
maps into the canonically restricted target. Commutation is required only
between the auxiliary action and the image of the scalar homomorphism. The
identification preserves the underlying function in both directions. -/
def semilinearCompHomEquivOfImageComm :
    @LinearEquiv T T _ _ (RingHom.id T) (RingHom.id T) _ _
      (L →ₛₗ[σ] M)
      (@LinearMap R R _ _ (RingHom.id R) L M _ _ _ (Module.compHom M σ))
      _ _ (semilinearModule (L := L) (M := M) T σ (hσ := hσ))
      (compHomLinearMapModule (L := L) (M := M) T σ (hσ := hσ)) := by
  letI := Module.compHom M σ
  letI := compHomLinearMapModule (L := L) (M := M) T σ (hσ := hσ)
  exact (semilinearCompHomAddEquiv (L := L) (M := M) σ).linearEquiv T

/-- Restricting the target scalars does not change a semilinear map's values. -/
@[simp]
theorem semilinearCompHomEquivOfImageComm_apply (f : L →ₛₗ[σ] M) (l : L) :
    semilinearCompHomEquivOfImageComm (M := M) T σ (hσ := hσ) f l = f l :=
  rfl

/-- Interpreting a map into the restricted target as semilinear does not change
its values. -/
@[simp]
theorem semilinearCompHomEquivOfImageComm_symm_apply
    (f : @LinearMap R R _ _ (RingHom.id R) L M _ _ _ (Module.compHom M σ)) (l : L) :
    (semilinearCompHomEquivOfImageComm (M := M) T σ (hσ := hσ)).symm f l = f l :=
  rfl

end ImageComm

section FullComm

variable [SMulCommClass S T M]

/-- Under commutation with the whole target scalar action, the canonical
semilinear module agrees with the usual pointwise module. -/
theorem semilinearModule_eq :
    semilinearModule (L := L) (M := M) T σ (hσ := SMul.comp.smulCommClass (α := M) (β := T) σ) =
      (inferInstance : Module T (L →ₛₗ[σ] M)) := by
  apply Module.ext'
  intro t f
  ext l
  rfl

/-- Semilinear maps identify with linear maps into the canonically restricted
target, using the usual pointwise auxiliary module on semilinear maps. Full
commutation supplies the image-commutation condition for
`semilinearCompHomEquivOfImageComm`. -/
def semilinearCompHomEquiv :
    @LinearEquiv T T _ _ (RingHom.id T) (RingHom.id T) _ _
      (L →ₛₗ[σ] M)
      (@LinearMap R R _ _ (RingHom.id R) L M _ _ _ (Module.compHom M σ))
      _ _ inferInstance
      (compHomLinearMapModule (L := L) (M := M) T σ
        (hσ := SMul.comp.smulCommClass (α := M) (β := T) σ)) := by
  letI := Module.compHom M σ
  letI : SMulCommClass R T M := SMul.comp.smulCommClass (α := M) (β := T) σ
  letI := compHomLinearMapModule (L := L) (M := M) T σ
    (hσ := SMul.comp.smulCommClass (α := M) (β := T) σ)
  exact
    { (@LinearEquiv.toAddEquiv T T _ _ (RingHom.id T) (RingHom.id T) _ _ _ _ _ _
        (semilinearModule (L := L) (M := M) T σ
          (hσ := SMul.comp.smulCommClass (α := M) (β := T) σ))
        (compHomLinearMapModule (L := L) (M := M) T σ
          (hσ := SMul.comp.smulCommClass (α := M) (β := T) σ))
        (semilinearCompHomEquivOfImageComm (L := L) (M := M) T σ
          (hσ := SMul.comp.smulCommClass (α := M) (β := T) σ))) with
      map_smul' := fun _ _ => rfl }

/-- Restricting the target scalars of a semilinear map does not change its values. -/
@[simp]
theorem semilinearCompHomEquiv_apply (f : L →ₛₗ[σ] M) (l : L) :
    semilinearCompHomEquiv (M := M) T σ f l = f l :=
  rfl

/-- Interpreting a linear map into the canonically restricted target as a
semilinear map does not change its values. -/
@[simp]
theorem semilinearCompHomEquiv_symm_apply
    (f : @LinearMap R R _ _ (RingHom.id R) L M _ _ _ (Module.compHom M σ)) (l : L) :
    (semilinearCompHomEquiv (M := M) T σ).symm f l = f l :=
  rfl

/-- The full-commutation and image-commutation identifications have the same
underlying additive equivalence. -/
theorem semilinearCompHomEquiv_toAddEquiv :
    @LinearEquiv.toAddEquiv T T _ _ (RingHom.id T) (RingHom.id T) _ _ _ _ _ _
      inferInstance
      (compHomLinearMapModule (L := L) (M := M) T σ
        (hσ := SMul.comp.smulCommClass (α := M) (β := T) σ))
      (semilinearCompHomEquiv (L := L) (M := M) T σ) =
    @LinearEquiv.toAddEquiv T T _ _ (RingHom.id T) (RingHom.id T) _ _ _ _ _ _
      (semilinearModule (L := L) (M := M) T σ
        (hσ := SMul.comp.smulCommClass (α := M) (β := T) σ))
      (compHomLinearMapModule (L := L) (M := M) T σ
        (hσ := SMul.comp.smulCommClass (α := M) (β := T) σ))
      (semilinearCompHomEquivOfImageComm (L := L) (M := M) T σ
        (hσ := SMul.comp.smulCommClass (α := M) (β := T) σ)) :=
  rfl

end FullComm

section Identity

variable [Module R M] [SMulCommClass R T M]

/-- For the identity scalar homomorphism, the canonical semilinear module is
the usual auxiliary module on ordinary linear maps. -/
@[simp]
theorem semilinearModule_id :
    semilinearModule (L := L) (M := M) T (RingHom.id R)
        (hσ := SMul.comp.smulCommClass (α := M) (β := T) (RingHom.id R)) =
      (inferInstance : Module T (L →ₗ[R] M)) := by
  apply Module.ext'
  intro t f
  ext l
  rfl

/-- For the identity scalar homomorphism, scalar restriction is the identity
on the additive monoid of linear maps. -/
@[simp]
theorem semilinearCompHomEquivOfImageComm_id_toAddEquiv :
    @LinearEquiv.toAddEquiv T T _ _ (RingHom.id T) (RingHom.id T) _ _ _ _ _ _
      (semilinearModule (L := L) (M := M) T (RingHom.id R)
        (hσ := SMul.comp.smulCommClass (α := M) (β := T) (RingHom.id R)))
      (compHomLinearMapModule (L := L) (M := M) T (RingHom.id R)
        (hσ := SMul.comp.smulCommClass (α := M) (β := T) (RingHom.id R)))
      (semilinearCompHomEquivOfImageComm (L := L) (M := M) T (RingHom.id R)
        (hσ := SMul.comp.smulCommClass (α := M) (β := T) (RingHom.id R))) =
      AddEquiv.refl (L →ₗ[R] M) := by
  ext f l
  rfl

/-- For the identity scalar homomorphism, the full-commutation identification
is the identity linear equivalence on ordinary linear maps. -/
@[simp]
theorem semilinearCompHomEquiv_id :
    semilinearCompHomEquiv (L := L) (M := M) T (RingHom.id R) =
      LinearEquiv.refl T (L →ₗ[R] M) := by
  ext f l
  rfl

end Identity

end LinearMap
