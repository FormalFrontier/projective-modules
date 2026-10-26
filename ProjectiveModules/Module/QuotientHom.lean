/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Linear maps out of a quotient

For a submodule `P` of an `A`-module `M`, precomposition with `P.mkQ` identifies linear maps
`M ⧸ P →ₗ[A] C` with the kernel of restriction to `P`. If the coefficient module `C` also has
an `S`-action commuting with its `A`-action, this identification is `S`-linear. No `S`-action
on `M` is needed.

## Main declarations

* `Submodule.quotientHomEquivKer`: the coefficient-linear quotient-Hom correspondence.
* `Submodule.quotientHomEquivKer_apply`: the forward map evaluated on an element of `M`.
* `Submodule.quotientHomEquivKer_symm_apply_mkQ`: the inverse evaluated on a quotient
  representative.
* `Submodule.quotientHomEquivKer_symm_apply`: identification of the inverse with `liftQ`.

## References

The construction uses Mathlib's quotient universal property (`Submodule.liftQ` and
`Submodule.linearMap_qext`) and its bilinear-map operations (`LinearMap.lcomp` and
`LinearMap.flip`). It generalizes Mathlib's `Submodule.dualQuotEquivDualAnnihilator` from
commutative scalars and scalar-valued duals to independent scalar actions on a coefficient
module. The ring and additive-group assumptions are those of the existing submodule quotient
and `liftQ` constructions.
-/

@[expose] public section

universe uA uS uM uC

namespace Submodule

variable {A : Type uA} {S : Type uS} {M : Type uM} {C : Type uC}
variable [Ring A] [Semiring S] [AddCommGroup M] [AddCommGroup C]
variable [Module A M] [Module A C] [Module S C] [SMulCommClass A S C]

/-- Precomposition with the quotient map identifies linear maps out of `M ⧸ P` with the
kernel of restriction to `P`. The equivalence is linear over any coefficient semiring `S`
whose action on `C` commutes with the `A`-action; no action of `S` on `M` is required. -/
def quotientHomEquivKer (P : Submodule A M) :
    ((M ⧸ P) →ₗ[A] C) ≃ₗ[S]
      LinearMap.ker (LinearMap.lcomp S C P.subtype) := by
  letI : SMulCommClass S A C := SMulCommClass.symm A S C
  let K := LinearMap.ker (LinearMap.lcomp S C P.subtype)
  let forward : ((M ⧸ P) →ₗ[A] C) →ₗ[S] K :=
    (LinearMap.lcomp S C P.mkQ).codRestrict K fun f => by
      apply LinearMap.mem_ker.mpr
      change (f.comp P.mkQ).comp P.subtype = 0
      apply LinearMap.le_ker_iff_comp_subtype_eq_zero.mp
      simpa only [ker_mkQ] using LinearMap.ker_le_ker_comp P.mkQ f
  have hvanish : P ≤ LinearMap.ker K.subtype.flip := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro f
    have hf : f.val.comp P.subtype = 0 := LinearMap.mem_ker.mp f.property
    exact LinearMap.congr_fun hf ⟨x, hx⟩
  let inverse : K →ₗ[S] ((M ⧸ P) →ₗ[A] C) :=
    (P.liftQ K.subtype.flip hvanish).flip
  refine LinearEquiv.ofLinearMap forward inverse ?_ ?_
  · apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    rfl
  · apply LinearMap.ext
    intro f
    apply P.linearMap_qext
    apply LinearMap.ext
    intro x
    rfl

/-- The quotient-Hom correspondence sends a map to its precomposition with the quotient map. -/
@[simp]
theorem quotientHomEquivKer_apply (P : Submodule A M) (f : (M ⧸ P) →ₗ[A] C) (x : M) :
    (P.quotientHomEquivKer (S := S) f).val x = f (P.mkQ x) :=
  rfl

/-- The inverse quotient-Hom correspondence takes the value of the original map on each
quotient representative. -/
theorem quotientHomEquivKer_symm_apply_mkQ (P : Submodule A M)
    (f : LinearMap.ker (LinearMap.lcomp S C P.subtype)) (x : M) :
    (P.quotientHomEquivKer (S := S)).symm f (P.mkQ x) = f.val x :=
  rfl

/-- The inverse quotient-Hom correspondence is `liftQ`, with factorability derived from
membership in the restriction kernel. -/
theorem quotientHomEquivKer_symm_apply (P : Submodule A M)
    (f : LinearMap.ker (LinearMap.lcomp S C P.subtype)) :
    (P.quotientHomEquivKer (S := S)).symm f =
      P.liftQ f.val (LinearMap.le_ker_iff_comp_subtype_eq_zero.mpr
        (LinearMap.mem_ker.mp f.property)) := by
  apply P.linearMap_qext
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.comp_apply, mkQ_apply, liftQ_apply] using
    quotientHomEquivKer_symm_apply_mkQ P f x

end Submodule
