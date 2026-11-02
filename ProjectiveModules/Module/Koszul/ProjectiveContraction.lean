/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Koszul.FreeContraction
public import ProjectiveModules.Module.Koszul.FreeHomotopy
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Contraction through a finite free retraction

A finite projective module is a retract of a finite coordinate module.
Choose such a retraction and transport the finite free Koszul contraction
through the exterior-symmetric tensor maps of its inclusion and retraction.
The construction uses the given scalar action and does not choose a basis
of the projective module. The contraction depends on the chosen retraction.
The coefficient ring and module may lie in independent universes.

The three identities concern positive total degree, with the two boundary
degrees stated separately. There is no assertion in bidegree `(0, 0)`.

## References

- C. Weibel, *The K-book: An Introduction to Algebraic K-theory* (2013),
  for the Koszul construction and passage to projective summands.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct
universe u v

namespace Module.Koszul.ProjectiveContraction

variable (S : Type u) [CommRing S]
variable (P : Type v) [AddCommGroup P] [Module S P]
variable [Module.Finite S P] [Module.Projective S P]

/-- The number of coordinates in a chosen finite free retraction of `P`.
This number is not asserted to be an intrinsic rank. -/
def coordinateCount : ℕ :=
  Classical.choose (Module.Finite.exists_comp_eq_id_of_projective S P)

/-- The retraction from the chosen finite coordinate module to `P`. -/
def retraction : CanonicalFreeContraction.Carrier S (coordinateCount S P) →ₗ[S] P :=
  Classical.choose
    (Classical.choose_spec (Module.Finite.exists_comp_eq_id_of_projective S P))

/-- The inclusion of `P` into the chosen finite coordinate module. -/
def inclusion : P →ₗ[S] CanonicalFreeContraction.Carrier S (coordinateCount S P) :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec (Module.Finite.exists_comp_eq_id_of_projective S P)))

/-- The chosen retraction is surjective. -/
theorem retraction_surjective : Function.Surjective (retraction S P) :=
  (Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec
        (Module.Finite.exists_comp_eq_id_of_projective S P)))).1

/-- The chosen inclusion is injective. -/
theorem inclusion_injective : Function.Injective (inclusion S P) :=
  (Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec
        (Module.Finite.exists_comp_eq_id_of_projective S P)))).2.1

/-- The chosen maps exhibit `P` as a retract of the finite coordinate module. -/
theorem retraction_comp_inclusion :
    (retraction S P).comp (inclusion S P) = (LinearMap.id : P →ₗ[S] P) :=
  (Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec
        (Module.Finite.exists_comp_eq_id_of_projective S P)))).2.2

/-- The Koszul contraction obtained by inclusion into a finite coordinate module,
its finite free contraction, and retraction to `P`. Its source symmetric degree
is positive. See Weibel, *The K-book* (2013). -/
def kappa (i d : ℕ) :
    Term S P i (d + 1) →ₗ[S] Term S P (i + 1) d :=
  (TensorProduct.map (exteriorPower.map (i + 1) (retraction S P))
      (SymmetricPower.map (ι := SymmetricIndex.{u} d) (retraction S P))).comp
    ((CanonicalFreeContraction.kappa S (coordinateCount S P) i d).comp
      (TensorProduct.map (exteriorPower.map i (inclusion S P))
        (SymmetricPower.map (ι := SymmetricIndex.{u} (d + 1)) (inclusion S P))))

/-- The defining composite of the projective contraction. -/
theorem kappa_eq_comp (i d : ℕ) :
    kappa S P i d =
      (TensorProduct.map (exteriorPower.map (i + 1) (retraction S P))
          (SymmetricPower.map (ι := SymmetricIndex.{u} d) (retraction S P))).comp
        ((CanonicalFreeContraction.kappa S (coordinateCount S P) i d).comp
          (TensorProduct.map (exteriorPower.map i (inclusion S P))
            (SymmetricPower.map (ι := SymmetricIndex.{u} (d + 1)) (inclusion S P)))) :=
  rfl

/-- Evaluation of the contraction using the inclusion, finite free contraction,
and retraction. -/
theorem kappa_apply (i d : ℕ) (x : Term S P i (d + 1)) :
    kappa S P i d x =
      TensorProduct.map (exteriorPower.map (i + 1) (retraction S P))
        (SymmetricPower.map (ι := SymmetricIndex.{u} d) (retraction S P))
        (CanonicalFreeContraction.kappa S (coordinateCount S P) i d
          (TensorProduct.map (exteriorPower.map i (inclusion S P))
            (SymmetricPower.map (ι := SymmetricIndex.{u} (d + 1)) (inclusion S P)) x)) :=
  rfl

private theorem tensor_retraction_comp_inclusion (i d : ℕ) :
    (TensorProduct.map (exteriorPower.map i (retraction S P))
        (SymmetricPower.map (ι := SymmetricIndex.{u} d) (retraction S P))).comp
      (TensorProduct.map (exteriorPower.map i (inclusion S P))
        (SymmetricPower.map (ι := SymmetricIndex.{u} d) (inclusion S P))) =
      (LinearMap.id : Term S P i d →ₗ[S] Term S P i d) := by
  rw [← TensorProduct.map_comp, ← exteriorPower.map_comp, ← SymmetricPower.map_comp]
  simp only [retraction_comp_inclusion, exteriorPower.map_id,
    SymmetricPower.map_id, TensorProduct.map_id]

/-- The two differential-contraction composites sum to the identity in positive
exterior and symmetric degrees. See Weibel, *The K-book* (2013). -/
theorem delta_comp_kappa_add_kappa_comp_delta (i d : ℕ) :
    (Module.Koszul.delta S P (i + 1) d).comp (kappa S P (i + 1) d) +
      (kappa S P i (d + 1)).comp (Module.Koszul.delta S P i (d + 1)) =
      (LinearMap.id : Term S P (i + 1) (d + 1) →ₗ[S]
        Term S P (i + 1) (d + 1)) := by
  calc
    _ =
        (TensorProduct.map (exteriorPower.map (i + 1) (retraction S P))
          (SymmetricPower.map (ι := SymmetricIndex.{u} (d + 1)) (retraction S P))).comp
          (((Module.Koszul.delta S
                (CanonicalFreeContraction.Carrier S (coordinateCount S P)) (i + 1) d).comp
              (CanonicalFreeContraction.kappa S (coordinateCount S P) (i + 1) d) +
            (CanonicalFreeContraction.kappa S (coordinateCount S P) i (d + 1)).comp
              (Module.Koszul.delta S
                (CanonicalFreeContraction.Carrier S (coordinateCount S P)) i (d + 1))).comp
            (TensorProduct.map (exteriorPower.map (i + 1) (inclusion S P))
              (SymmetricPower.map (ι := SymmetricIndex.{u} (d + 1)) (inclusion S P)))) := by
      simp only [kappa_eq_comp]
      simp only [← LinearMap.comp_assoc]
      rw [← Module.Koszul.delta_natural (retraction S P) (i + 1) d]
      simp only [LinearMap.comp_assoc]
      rw [Module.Koszul.delta_natural (inclusion S P) i (d + 1)]
      simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_assoc]
    _ = _ := by
      rw [CanonicalFreeContraction.delta_comp_kappa_add_kappa_comp_delta,
        LinearMap.id_comp]
      exact tensor_retraction_comp_inclusion S P (i + 1) (d + 1)

/-- In exterior degree zero and positive symmetric degree, differential after
contraction is the identity. See Weibel, *The K-book* (2013). -/
theorem delta_comp_kappa_exterior_zero (d : ℕ) :
    (Module.Koszul.delta S P 0 d).comp (kappa S P 0 d) =
      (LinearMap.id : Term S P 0 (d + 1) →ₗ[S] Term S P 0 (d + 1)) := by
  calc
    _ =
        (TensorProduct.map (exteriorPower.map 0 (retraction S P))
          (SymmetricPower.map (ι := SymmetricIndex.{u} (d + 1)) (retraction S P))).comp
          (((Module.Koszul.delta S
                (CanonicalFreeContraction.Carrier S (coordinateCount S P)) 0 d).comp
              (CanonicalFreeContraction.kappa S (coordinateCount S P) 0 d)).comp
            (TensorProduct.map (exteriorPower.map 0 (inclusion S P))
              (SymmetricPower.map (ι := SymmetricIndex.{u} (d + 1)) (inclusion S P)))) := by
      simp only [kappa_eq_comp, ← LinearMap.comp_assoc]
      rw [← Module.Koszul.delta_natural (retraction S P) 0 d]
    _ = _ := by
      rw [CanonicalFreeContraction.delta_comp_kappa_exterior_zero, LinearMap.id_comp]
      exact tensor_retraction_comp_inclusion S P 0 (d + 1)

/-- In symmetric degree zero and positive exterior degree, contraction after
differential is the identity. See Weibel, *The K-book* (2013). -/
theorem kappa_comp_delta_symmetric_zero (i : ℕ) :
    (kappa S P i 0).comp (Module.Koszul.delta S P i 0) =
      (LinearMap.id : Term S P (i + 1) 0 →ₗ[S] Term S P (i + 1) 0) := by
  calc
    _ =
        (TensorProduct.map (exteriorPower.map (i + 1) (retraction S P))
          (SymmetricPower.map (ι := SymmetricIndex.{u} 0) (retraction S P))).comp
          (((CanonicalFreeContraction.kappa S (coordinateCount S P) i 0).comp
              (Module.Koszul.delta S
                (CanonicalFreeContraction.Carrier S (coordinateCount S P)) i 0)).comp
            (TensorProduct.map (exteriorPower.map (i + 1) (inclusion S P))
              (SymmetricPower.map (ι := SymmetricIndex.{u} 0) (inclusion S P)))) := by
      simp only [kappa_eq_comp, LinearMap.comp_assoc]
      rw [Module.Koszul.delta_natural (inclusion S P) i 0]
    _ = _ := by
      rw [CanonicalFreeContraction.kappa_comp_delta_symmetric_zero, LinearMap.id_comp]
      exact tensor_retraction_comp_inclusion S P (i + 1) 0

end Module.Koszul.ProjectiveContraction
