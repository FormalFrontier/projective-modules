/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Determinant
public import ProjectiveModules.KTheory.ScalarExtension
public import ProjectiveModules.ExteriorPower.DeterminantLineBaseChange

/-!
# Naturality of the determinant on K₀

For commutative rings, the determinant homomorphism on K₀ is compatible with
extension of scalars and the induced homomorphism on Picard groups.

## References

For the determinant construction, see C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*, §I.3. The compatibility
here passes the scalar-extension comparison for determinant lines to K₀.
The Picard-group and invertible-module interfaces are Mathlib's formalization
by Junyan Xu. The right-module extension, determinant-line comparisons and K₀
universal properties are the formalizations by Formal Frontier Agents in this library.
-/

public section

universe u v

namespace KTheory.K0

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The determinant commutes with scalar extension along a unital homomorphism
of commutative rings. This is the K₀ form of scalar-extension compatibility for
Weibel's determinant construction in *The K-book*, §I.3. -/
theorem determinantHom_comp_map (f : R →+* S) :
    (determinantHom S).comp (map f) =
      (MonoidHom.toAdditive (CommRing.Pic.mapRingHom f)).comp (determinantHom R) := by
  apply hom_ext R
  intro P
  simp only [AddMonoidHom.comp_apply, map_of, determinantHom_of,
    MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul]
  rw [ModuleCat.RightExtension.determinantLine_mk]
  -- The opposite-ring normalizations commute with the original ring map.
  have h : (RingEquiv.toOpposite S).symm.toRingHom.comp f.op =
      f.comp (RingEquiv.toOpposite R).symm.toRingHom := by
    ext r
    rfl
  simp only [CommRing.Pic.mapRingHom_mapRingHom, h]

/-- The pointwise form of scalar-extension compatibility for the determinant
construction of Weibel's *The K-book*, §I.3. -/
theorem determinantHom_map (f : R →+* S) (x : K0 R) :
    determinantHom S (map f x) =
      MonoidHom.toAdditive (CommRing.Pic.mapRingHom f) (determinantHom R x) := by
  simpa only [AddMonoidHom.comp_apply] using
    DFunLike.congr_fun (determinantHom_comp_map f) x

end KTheory.K0
