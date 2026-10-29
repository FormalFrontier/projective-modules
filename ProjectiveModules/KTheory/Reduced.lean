/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Stabilization
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

import ProjectiveModules.Free.StablePresentation
import ProjectiveModules.KTheory.FiniteFree
import Mathlib.LinearAlgebra.Pi

/-!
# Reduced Grothendieck groups of finite projective right modules

The additive group `KTheory.ReducedK0 R` is the quotient of `KTheory.K0 R` by the
integer multiples of the class of the regular right module. Equivalently, it is the
additive cokernel of the homomorphism sending an integer `z` to `z • KTheory.K0.of R Rᵐᵒᵖ`.
This construction does not require the regular class to generate a direct summand.

The map `KTheory.ReducedK0.mk` is the canonical additive quotient map.
`KTheory.ReducedK0.mk_of_eq_zero_iff_exists_free_stabilization` characterizes vanishing
of the reduced class of a finite projective module by stable freeness.

Every reduced class has a finite projective representative, since a finite free
summand vanishes under the projection. The construction `KTheory.ReducedK0.lift`
and the equivalence `KTheory.ReducedK0.liftEquiv` express the universal property:
additive maps from reduced K₀ correspond to additive maps from K₀ killing the
regular class.

## References

- C. A. Weibel, *The K-book: An introduction to algebraic K-theory*,
  American Mathematical Society, 2013, Chapter II.
-/

@[expose] public section

universe u v w

namespace KTheory

variable (R : Type u) [Ring R]

/-- The reduced Grothendieck group of finite projective right `R`-modules, obtained by
quotienting `K0 R` by the additive subgroup of integer multiples of the regular class. -/
abbrev ReducedK0 : Type u :=
  K0 R ⧸ AddSubgroup.zmultiples (K0.of R Rᵐᵒᵖ)

namespace ReducedK0

/-- The canonical additive projection from `K0 R` to its reduced Grothendieck group. -/
noncomputable def mk : K0 R →+ ReducedK0 R :=
  QuotientAddGroup.mk' (AddSubgroup.zmultiples (K0.of R Rᵐᵒᵖ))

private theorem of_fin_fun_eq_nsmul (n : ℕ) :
    K0.of R (Fin n → Rᵐᵒᵖ) = n • K0.of R Rᵐᵒᵖ := by
  simpa only [K0.ofClass_of, map_nsmul] using
    congrArg (K0.ofClass R) (ProjectiveClass.of_fin_fun_eq_nsmul R n)

/-- The projection to reduced K₀ is the projection to the additive cyclic quotient. -/
theorem mk_apply (x : K0 R) :
    mk R x = (x : K0 R ⧸ AddSubgroup.zmultiples (K0.of R Rᵐᵒᵖ)) :=
  QuotientAddGroup.mk'_apply _ x

/-- Every reduced class is the image of a K₀ class. -/
theorem mk_surjective : Function.Surjective (mk R) :=
  QuotientAddGroup.mk'_surjective _

/-- A K₀ class vanishes in reduced K₀ exactly when it belongs to the cyclic subgroup
of the regular class. -/
theorem mk_eq_zero_iff (x : K0 R) :
    mk R x = 0 ↔ x ∈ AddSubgroup.zmultiples (K0.of R Rᵐᵒᵖ) :=
  QuotientAddGroup.eq_zero_iff x

/-- A K₀ class vanishes in reduced K₀ exactly when it is an integer multiple of the
regular class. -/
theorem mk_eq_zero_iff_exists_zsmul (x : K0 R) :
    mk R x = 0 ↔ ∃ z : ℤ, z • K0.of R Rᵐᵒᵖ = x :=
  (mk_eq_zero_iff R x).trans AddSubgroup.mem_zmultiples_iff

/-- The regular right module has zero reduced class. -/
@[simp]
theorem mk_regular : mk R (K0.of R Rᵐᵒᵖ) = 0 :=
  (mk_eq_zero_iff R _).mpr (AddSubgroup.mem_zmultiples _)

/-- Every finite free right module has zero reduced class. -/
@[simp]
theorem mk_of_fin_fun (n : ℕ) : mk R (K0.of R (Fin n → Rᵐᵒᵖ)) = 0 := by
  rw [of_fin_fun_eq_nsmul, map_nsmul, mk_regular, nsmul_zero]

/-- Every reduced class has a finite projective representative, without a negative
finite free summand. -/
theorem exists_eq_mk_of (x : ReducedK0 R) :
    ∃ P : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ, x = mk R (K0.of R P) := by
  obtain ⟨z, rfl⟩ := mk_surjective R x
  obtain ⟨P, n, hz⟩ := K0.exists_sub_free R z
  refine ⟨P, ?_⟩
  rw [hz, map_sub, mk_of_fin_fun, sub_zero]

section Lift

variable {H : Type w} [AddMonoid H]

/-- Additive maps from reduced K₀ are determined by their values on K₀ classes. -/
@[ext]
theorem hom_ext {f g : ReducedK0 R →+ H}
    (h : ∀ x : K0 R, f (mk R x) = g (mk R x)) : f = g := by
  apply AddMonoidHom.ext
  intro y
  obtain ⟨x, rfl⟩ := mk_surjective R y
  exact h x

/-- An additive map on K₀ killing the regular class descends to reduced K₀. -/
noncomputable def lift (f : K0 R →+ H) (hf : f (K0.of R Rᵐᵒᵖ) = 0) :
    ReducedK0 R →+ H :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (K0.of R Rᵐᵒᵖ)) f
    (AddSubgroup.zmultiples_le.mpr hf)

/-- The descended map agrees with the original map on projected classes. -/
@[simp]
theorem lift_mk (f : K0 R →+ H) (hf : f (K0.of R Rᵐᵒᵖ) = 0) (x : K0 R) :
    lift R f hf (mk R x) = f x := rfl

/-- Composing a descended map with the projection recovers the original map. -/
@[simp]
theorem lift_comp_mk (f : K0 R →+ H) (hf : f (K0.of R Rᵐᵒᵖ) = 0) :
    (lift R f hf).comp (mk R) = f :=
  AddMonoidHom.ext (lift_mk R f hf)

/-- A descended map is the unique additive map factoring the given map through the
projection to reduced K₀. -/
theorem lift_unique (f : K0 R →+ H) (hf : f (K0.of R Rᵐᵒᵖ) = 0)
    (g : ReducedK0 R →+ H) (hg : g.comp (mk R) = f) : g = lift R f hf := by
  apply hom_ext R
  intro x
  exact (DFunLike.congr_fun hg x).trans (lift_mk R f hf x).symm

/-- Additive maps out of reduced K₀ correspond to additive maps out of K₀ killing
the regular class. No commutativity of the target is required. -/
noncomputable def liftEquiv :
    {f : K0 R →+ H // f (K0.of R Rᵐᵒᵖ) = 0} ≃ (ReducedK0 R →+ H) where
  toFun f := lift R f.1 f.2
  invFun g := ⟨g.comp (mk R), by simp only [AddMonoidHom.comp_apply, mk_regular, map_zero]⟩
  left_inv f := Subtype.ext (lift_comp_mk R f.1 f.2)
  right_inv g := by
    apply hom_ext R
    intro x
    exact lift_mk R _ _ x

/-- The forward correspondence is the descended map. -/
@[simp]
theorem liftEquiv_apply (f : {f : K0 R →+ H // f (K0.of R Rᵐᵒᵖ) = 0}) :
    liftEquiv R f = lift R f.1 f.2 := rfl

/-- The inverse correspondence is composition with the canonical projection. -/
@[simp]
theorem liftEquiv_symm_apply (g : ReducedK0 R →+ H) :
    ((liftEquiv R).symm g).1 = g.comp (mk R) := rfl

end Lift

private def finFreeProdEquiv (m n : ℕ) :
    ((Fin m → Rᵐᵒᵖ) × (Fin n → Rᵐᵒᵖ)) ≃ₗ[Rᵐᵒᵖ] (Fin (m + n) → Rᵐᵒᵖ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin n) Rᵐᵒᵖ Rᵐᵒᵖ).symm.trans
    (LinearEquiv.piCongrLeft Rᵐᵒᵖ (fun _ : Fin (m + n) => Rᵐᵒᵖ) finSumFinEquiv)

/-- A finite projective right module has zero reduced class if and only if its product
with some finite free module is finite free.

This is the stable-freeness criterion for reduced K₀; see C. A. Weibel,
*The K-book: An introduction to algebraic K-theory*, Chapter II. -/
theorem mk_of_eq_zero_iff_exists_free_stabilization
    (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P] :
    mk R (K0.of R P) = 0 ↔
      ∃ m n : ℕ, Nonempty ((P × (Fin m → Rᵐᵒᵖ)) ≃ₗ[Rᵐᵒᵖ]
        (Fin n → Rᵐᵒᵖ)) := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (mk_eq_zero_iff_exists_zsmul R (K0.of R P)).mp h
    have hnat : ∃ a b : ℕ,
        K0.of R P + a • K0.of R Rᵐᵒᵖ = b • K0.of R Rᵐᵒᵖ := by
      cases z with
      | ofNat n => exact ⟨0, n, by simpa using hz.symm⟩
      | negSucc n =>
          refine ⟨n + 1, 0, ?_⟩
          rw [← hz]
          simp
    obtain ⟨a, b, hab⟩ := hnat
    have hclasses : K0.of R (P × (Fin a → Rᵐᵒᵖ)) =
        K0.of R (Fin b → Rᵐᵒᵖ) := by
      simpa only [K0.of_prod, of_fin_fun_eq_nsmul] using hab
    obtain ⟨k, ⟨e⟩⟩ :=
      (K0.of_eq_iff_exists_free_stabilizer R
        (P × (Fin a → Rᵐᵒᵖ)) (Fin b → Rᵐᵒᵖ)).mp hclasses
    refine ⟨a + k, b + k, ⟨?_⟩⟩
    exact (((LinearEquiv.refl Rᵐᵒᵖ P).prodCongr
      (finFreeProdEquiv R a k).symm).trans
        (LinearEquiv.prodAssoc Rᵐᵒᵖ P (Fin a → Rᵐᵒᵖ) (Fin k → Rᵐᵒᵖ)).symm).trans
          (e.trans (finFreeProdEquiv R b k))
  · rintro ⟨m, n, ⟨e⟩⟩
    have hclasses := K0.of_eq_of_equiv R (P × (Fin m → Rᵐᵒᵖ)) e
    have h := congrArg (mk R) hclasses
    simpa only [K0.of_prod, map_add, mk_of_fin_fun, add_zero] using h

/-- A finite projective right module has zero reduced class if and only if it is
stably free. -/
theorem mk_of_eq_zero_iff_isStablyFree
    (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P] :
    mk R (K0.of R P) = 0 ↔ Module.IsStablyFree Rᵐᵒᵖ P := by
  rw [mk_of_eq_zero_iff_exists_free_stabilization,
    Module.exists_fin_prod_linearEquiv_iff_finite_isStablyFree]
  exact ⟨fun h => h.2, fun h => ⟨inferInstance, h⟩⟩

end ReducedK0

end KTheory
