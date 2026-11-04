/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.ScalarExtension
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Scalar retractions on projective classes and K₀

A retraction of ring homomorphisms induces a left inverse on finite-projective
classes and additive K₀. Constant coefficient splits the polynomial constant
inclusion, so its induced maps are injective over arbitrary rings.
-/

@[expose] public section

universe u v

namespace KTheory

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

namespace ProjectiveClass

/-- A ring retraction induces a left inverse on finite-projective classes. -/
theorem map_leftInverse_of_comp_eq_id (f : R →+* S) (g : S →+* R)
    (hgf : g.comp f = RingHom.id R) : Function.LeftInverse (map g) (map f) := by
  have hm : (map g).comp (map f) = AddMonoidHom.id (ProjectiveClass R) := by
    rw [← map_comp, hgf, map_id]
  intro x
  simpa only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] using DFunLike.congr_fun hm x

/-- Extension along the polynomial constant inclusion is injective on projective classes. -/
theorem map_polynomial_C_injective :
    Function.Injective (map (Polynomial.C : R →+* Polynomial R)) := by
  apply (map_leftInverse_of_comp_eq_id (Polynomial.C : R →+* Polynomial R)
    (Polynomial.constantCoeff : Polynomial R →+* R) ?_).injective
  ext r
  simp

end ProjectiveClass

namespace K0

/-- A ring retraction induces a left inverse on additive K₀. -/
theorem map_leftInverse_of_comp_eq_id (f : R →+* S) (g : S →+* R)
    (hgf : g.comp f = RingHom.id R) : Function.LeftInverse (map g) (map f) := by
  have hm : (map g).comp (map f) = AddMonoidHom.id (K0 R) := by
    rw [← map_comp, hgf, map_id]
  intro x
  simpa only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] using DFunLike.congr_fun hm x

/-- Extension along the polynomial constant inclusion is injective on additive K₀. -/
theorem map_polynomial_C_injective :
    Function.Injective (map (Polynomial.C : R →+* Polynomial R)) := by
  apply (map_leftInverse_of_comp_eq_id (Polynomial.C : R →+* Polynomial R)
    (Polynomial.constantCoeff : Polynomial R →+* R) ?_).injective
  ext r
  simp

end K0

end KTheory
