/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.Free
public import Mathlib.Algebra.Module.ULift

/-!
# Coefficient sums and independent universes for free modules

The collapse of two distinct integer unit generators adds their coefficients.
The other two calculations separate the ring and generator universes in both
directions and extend into the ordinary integers, below the free carrier's
universe. All structures on lifted coefficients are Mathlib's registered ones.
The empty-generator example exercises the zero-module boundary.

## References

* Mathlib's `ULift` ring and module structures, by Kim Morrison.
-/

public section

open CategoryTheory

namespace ModuleCat

/-- A genuinely noninjective map sums the two distinct unit coefficients. -/
theorem freeOn_finTwo_collapse :
    (freeOn ℤ).map (↾fun _ : Fin 2 => (PUnit.unit : PUnit))
        (freeOnMk ℤ (0 : Fin 2) + freeOnMk ℤ (1 : Fin 2)) =
      Finsupp.single PUnit.unit (2 : ℤ) := by
  let f : Fin 2 → PUnit := fun _ => PUnit.unit
  exact Eq.trans
    (Eq.trans
      (((freeOn ℤ).map (↾f)).hom.map_add _ _)
      (congrArg₂ (fun x y : (freeOn ℤ).obj PUnit => x + y)
        (show (freeOn ℤ).map (↾f) (freeOnMk ℤ (0 : Fin 2)) = freeOnMk ℤ (f 0) from
          by simpa using (freeOn_map_mk ℤ f (0 : Fin 2)))
        (show (freeOn ℤ).map (↾f) (freeOnMk ℤ (1 : Fin 2)) = freeOnMk ℤ (f 1) from
          by simpa using (freeOn_map_mk ℤ f (1 : Fin 2)))))
    (Eq.trans
      (Finsupp.single_add PUnit.unit (1 : ℤ) 1).symm
      rfl)

/-- Generators in `Type 1` over coefficients in `Type 0` extend to a target in
`Type 0`, strictly below the free carrier's universe. The two values are 1 and 2. -/
theorem freeOn_liftedIndices_smallTarget :
    freeOnDescLinear ℤ (fun a : ULift.{1} (Fin 2) => (a.down.val : ℤ) + 1)
        (freeOnMk ℤ (ULift.up (0 : Fin 2) : ULift.{1} (Fin 2)) +
          freeOnMk ℤ (ULift.up (1 : Fin 2) : ULift.{1} (Fin 2))) =
      (3 : ℤ) := by
  let h : ULift.{1} (Fin 2) → ℤ := fun a => (a.down.val : ℤ) + 1
  let a : ULift.{1} (Fin 2) := ULift.up (0 : Fin 2)
  let b : ULift.{1} (Fin 2) := ULift.up (1 : Fin 2)
  calc
    _ = freeOnDescLinear ℤ h (freeOnMk ℤ a) +
        freeOnDescLinear ℤ h (freeOnMk ℤ b) :=
      (freeOnDescLinear ℤ h).map_add _ _
    _ = h a + h b := by simp
    _ = (3 : ℤ) := rfl

/-- Coefficients in `Type 1` and generators in `Type 0` admit both a collapse
map and extension to the ordinary integers in `Type 0`, using the canonical
`Module (ULift ℤ) ℤ` action. No ring or module dictionary is replaced. -/
theorem freeOn_liftedRing_smallTarget :
    freeOnDescLinear (ULift.{1} ℤ) (fun _ : PUnit => (1 : ℤ))
        ((freeOn (ULift.{1} ℤ) : Type 0 ⥤ ModuleCat.{1} (ULift.{1} ℤ)).map
          (↾fun _ : Fin 2 => (PUnit.unit : PUnit))
          (freeOnMk (ULift.{1} ℤ) (0 : Fin 2) +
            freeOnMk (ULift.{1} ℤ) (1 : Fin 2))) =
      (2 : ℤ) := by
  let f : Fin 2 → PUnit := fun _ => PUnit.unit
  let h : PUnit → ℤ := fun _ => 1
  calc
    _ = freeOnDescLinear (ULift.{1} ℤ) h
        (freeOnMk (ULift.{1} ℤ) (f 0) + freeOnMk (ULift.{1} ℤ) (f 1)) :=
      congrArg (fun c : (freeOn (ULift.{1} ℤ)).obj PUnit =>
        freeOnDescLinear (ULift.{1} ℤ) h c)
        ((((freeOn (ULift.{1} ℤ)).map (↾f)).hom.map_add _ _).trans
          (congrArg₂ (fun x y : (freeOn (ULift.{1} ℤ)).obj PUnit => x + y)
            (freeOn_map_mk (ULift.{1} ℤ) f (0 : Fin 2))
            (freeOn_map_mk (ULift.{1} ℤ) f (1 : Fin 2))))
    _ = freeOnDescLinear (ULift.{1} ℤ) h (freeOnMk (ULift.{1} ℤ) (f 0)) +
        freeOnDescLinear (ULift.{1} ℤ) h (freeOnMk (ULift.{1} ℤ) (f 1)) :=
      (freeOnDescLinear (ULift.{1} ℤ) h).map_add _ _
    _ = h (f 0) + h (f 1) :=
      congrArg₂ (fun x y : ℤ => x + y)
        (freeOnDescLinear_mk (ULift.{1} ℤ) h (f 0))
        (freeOnDescLinear_mk (ULift.{1} ℤ) h (f 1))
    _ = (2 : ℤ) := rfl

/-- The free module on the empty type has no nonzero elements. -/
theorem freeOn_pempty_eq_zero (c : (freeOn ℤ).obj PEmpty) : c = 0 :=
  freeOn_eq_zero_of_isEmpty ℤ c

end ModuleCat
