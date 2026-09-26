/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import ProjectiveModules.Module.RightExtensionQuotient
public import Mathlib.Algebra.Field.Opposite
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite residue modules for right-module extension

This file packages two elementary compatibility properties of extension of
scalars for right modules: it carries linear equivalences to linear
equivalences and preserves binary products.  Combining these constructions
with `ModuleCat.RightExtension.idealQuotientLinearEquiv` gives corresponding
maps for quotients by the action of a two-sided ideal, as well as finite-
generation and dimension consequences over a division-ring quotient.
-/

@[expose] public section

universe uR uS uM uN

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (f : R →+* S)
variable {M : Type uM} {N : Type uN}
variable [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable [AddCommGroup N] [Module Rᵐᵒᵖ N]

/-- Extension of scalars sends the zero right-linear map to zero. -/
@[simp]
theorem map_zero : map f (0 : M →ₗ[Rᵐᵒᵖ] N) = 0 := by
  apply linearMap_ext f
  intro m s
  rw [map_tmul]
  let _ : Module R S := f.toModule
  change BalancedTensorProduct.tmul (R := R) (0 : N) s = 0
  exact BalancedTensorProduct.zero_tmul s

/-- Extension of scalars carries a right-linear equivalence to a
right-linear equivalence. -/
def mapLinearEquiv (e : M ≃ₗ[Rᵐᵒᵖ] N) :
    Obj f M ≃ₗ[Sᵐᵒᵖ] Obj f N :=
  LinearEquiv.ofLinearMap (map f e.toLinearMap) (map f e.symm.toLinearMap)
    (by
      apply linearMap_ext f
      intro n s
      simp)
    (by
      apply linearMap_ext f
      intro m s
      simp)

@[simp]
theorem mapLinearEquiv_tmul (e : M ≃ₗ[Rᵐᵒᵖ] N) (m : M) (s : S) :
    mapLinearEquiv f e (tmul f m s) = tmul f (e m) s := by
  exact map_tmul f e.toLinearMap m s

/-- Extension of scalars commutes with a binary product of right modules. -/
def prodLinearEquiv :
    Obj f (M × N) ≃ₗ[Sᵐᵒᵖ] Obj f M × Obj f N := by
  let toProd : Obj f (M × N) →ₗ[Sᵐᵒᵖ] Obj f M × Obj f N :=
    (map f (LinearMap.fst Rᵐᵒᵖ M N)).prod
      (map f (LinearMap.snd Rᵐᵒᵖ M N))
  let fromProd : Obj f M × Obj f N →ₗ[Sᵐᵒᵖ] Obj f (M × N) :=
    LinearMap.coprod
      (map f (LinearMap.inl Rᵐᵒᵖ M N))
      (map f (LinearMap.inr Rᵐᵒᵖ M N))
  apply LinearEquiv.ofLinearMap toProd fromProd
  · apply LinearMap.ext
    rintro ⟨x, y⟩
    apply Prod.ext
    · change map f (LinearMap.fst Rᵐᵒᵖ M N)
          (map f (LinearMap.inl Rᵐᵒᵖ M N) x +
            map f (LinearMap.inr Rᵐᵒᵖ M N) y) = x
      rw [(map f (LinearMap.fst Rᵐᵒᵖ M N)).map_add]
      simp only [← LinearMap.comp_apply, ← map_comp,
        LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, map_id,
        map_zero, LinearMap.id_apply, LinearMap.zero_apply, add_zero]
    · change map f (LinearMap.snd Rᵐᵒᵖ M N)
          (map f (LinearMap.inl Rᵐᵒᵖ M N) x +
            map f (LinearMap.inr Rᵐᵒᵖ M N) y) = y
      rw [(map f (LinearMap.snd Rᵐᵒᵖ M N)).map_add]
      simp only [← LinearMap.comp_apply, ← map_comp,
        LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, map_id,
        map_zero, LinearMap.id_apply, LinearMap.zero_apply, zero_add]
  · apply linearMap_ext f
    intro mn s
    rcases mn with ⟨m, n⟩
    change map f (LinearMap.inl Rᵐᵒᵖ M N)
          (map f (LinearMap.fst Rᵐᵒᵖ M N) (tmul f (m, n) s)) +
        map f (LinearMap.inr Rᵐᵒᵖ M N)
          (map f (LinearMap.snd Rᵐᵒᵖ M N) (tmul f (m, n) s)) =
      tmul f (m, n) s
    simp only [map_tmul, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.inl_apply, LinearMap.inr_apply]
    let _ : Module R S := f.toModule
    change BalancedTensorProduct.tmul (R := R) (m, 0) s +
        BalancedTensorProduct.tmul (R := R) (0, n) s =
      BalancedTensorProduct.tmul (R := R) (m, n) s
    rw [← BalancedTensorProduct.add_tmul]
    simp

@[simp]
theorem prodLinearEquiv_tmul (m : M) (n : N) (s : S) :
    prodLinearEquiv (f := f) (M := M) (N := N) (tmul f (m, n) s) =
      (tmul f m s, tmul f n s) := by
  rfl

section IdealQuotient

variable {R : Type uR} [Ring R]
variable {M : Type uM} {N : Type uN}
variable [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable [AddCommGroup N] [Module Rᵐᵒᵖ N]

/-- A right-linear equivalence descends to the quotients by the action of a
two-sided ideal. -/
def idealQuotientMapLinearEquiv (I : Ideal R) [I.IsTwoSided]
    (e : M ≃ₗ[Rᵐᵒᵖ] N) :
    IdealQuotient (M := M) I ≃ₗ[(R ⧸ I)ᵐᵒᵖ]
      IdealQuotient (M := N) I :=
  (idealQuotientLinearEquiv (M := M) I).symm.trans <|
    (mapLinearEquiv (Ideal.Quotient.mk I) e).trans <|
      idealQuotientLinearEquiv (M := N) I

@[simp]
theorem idealQuotientMapLinearEquiv_mk (I : Ideal R) [I.IsTwoSided]
    (e : M ≃ₗ[Rᵐᵒᵖ] N) (m : M) :
    idealQuotientMapLinearEquiv I e
        (Submodule.Quotient.mk (p := idealSubmodule (M := M) I) m) =
      Submodule.Quotient.mk (p := idealSubmodule (M := N) I) (e m) := by
  simp [idealQuotientMapLinearEquiv]

/-- Quotienting a product of right modules by the action of a two-sided ideal
is the product of the corresponding quotient modules. -/
def idealQuotientProdLinearEquiv (I : Ideal R) [I.IsTwoSided] :
    IdealQuotient (M := M × N) I ≃ₗ[(R ⧸ I)ᵐᵒᵖ]
      IdealQuotient (M := M) I × IdealQuotient (M := N) I :=
  (idealQuotientLinearEquiv (M := M × N) I).symm.trans <|
    (prodLinearEquiv (f := Ideal.Quotient.mk I) (M := M) (N := N)).trans <|
      (idealQuotientLinearEquiv (M := M) I).prodCongr
        (idealQuotientLinearEquiv (M := N) I)

@[simp]
theorem idealQuotientProdLinearEquiv_mk (I : Ideal R) [I.IsTwoSided]
    (m : M) (n : N) :
    idealQuotientProdLinearEquiv (M := M) (N := N) I
        (Submodule.Quotient.mk
          (p := idealSubmodule (M := M × N) I) (m, n)) =
      (Submodule.Quotient.mk (p := idealSubmodule (M := M) I) m,
        Submodule.Quotient.mk (p := idealSubmodule (M := N) I) n) := by
  simp [idealQuotientProdLinearEquiv]

/-- A finitely generated right module has a finitely generated quotient by
the action of a two-sided ideal. -/
instance idealQuotientFinite (I : Ideal R) [I.IsTwoSided]
    [Module.Finite Rᵐᵒᵖ M] :
    Module.Finite (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M) I) :=
  Module.Finite.equiv (idealQuotientLinearEquiv (M := M) I)

/-- Freeness of the extension of scalars transfers to the quotient by the
action of a two-sided ideal. -/
theorem idealQuotientFree (I : Ideal R) [I.IsTwoSided]
    [Module.Free (R ⧸ I)ᵐᵒᵖ (Obj (Ideal.Quotient.mk I) M)] :
    Module.Free (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M) I) :=
  Module.Free.of_equiv (idealQuotientLinearEquiv (M := M) I)

/-- The quotient of a right module by the action of a two-sided maximal ideal
is free over the resulting division ring. -/
theorem idealQuotientFree_of_isMaximal (I : Ideal R) [I.IsTwoSided]
    [I.IsMaximal] :
    Module.Free (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M) I) := by
  let _ := Ideal.Quotient.divisionRing I
  let _ : Module.Free (R ⧸ I)ᵐᵒᵖ (Obj (Ideal.Quotient.mk I) M) :=
    Module.Free.of_divisionRing (R ⧸ I)ᵐᵒᵖ (Obj (Ideal.Quotient.mk I) M)
  exact idealQuotientFree I

/-- The dimension of the quotient of a product is the sum of the dimensions
of the two quotient modules whenever dimension is available over the quotient
scalar ring. -/
theorem finrank_idealQuotient_prod (I : Ideal R) [I.IsTwoSided]
    [StrongRankCondition (R ⧸ I)ᵐᵒᵖ]
    [Module.Free (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M) I)]
    [Module.Free (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := N) I)]
    [Module.Finite Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ N] :
    Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M × N) I) =
      Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M) I) +
        Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := N) I) := by
  rw [(idealQuotientProdLinearEquiv (M := M) (N := N) I).finrank_eq,
    Module.finrank_prod]

/-- Modulo a two-sided maximal ideal, the dimension of the quotient of a product
is the sum of the dimensions of the two quotient modules. -/
theorem finrank_idealQuotient_prod_of_isMaximal
    (I : Ideal R) [I.IsTwoSided] [I.IsMaximal]
    [Module.Finite Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ N] :
    Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M × N) I) =
      Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := M) I) +
        Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient (M := N) I) := by
  let _ := Ideal.Quotient.divisionRing I
  let _ := idealQuotientFree_of_isMaximal (M := M) I
  let _ := idealQuotientFree_of_isMaximal (M := N) I
  let _ : StrongRankCondition (R ⧸ I)ᵐᵒᵖ :=
    IsNoetherianRing.strongRankCondition (R ⧸ I)ᵐᵒᵖ
  exact finrank_idealQuotient_prod I

end IdealQuotient

end ModuleCat.RightExtension
