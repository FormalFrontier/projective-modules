/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.ScalarExtension
public import ProjectiveModules.Module.DirectLimit
public import Mathlib.Algebra.Colimit.Module
public import AlgebraicDirectLimits.Algebra.Colimit.Module
public import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
public import AlgebraicDirectLimits.DirectedGroupCompletion

import ProjectiveModules.Module.RightExtensionMatrixRange

/-!
# Projective classes and K₀ over directed ring limits

Canonical scalar extension to a nonempty directed limit of unital rings detects
equality of finite-projective right-module classes at a common upper stage.
Every class over the limit comes from some stage. The maps are the additive
homomorphisms `KTheory.ProjectiveClass.map` along `DirectLimit.Ring.of`.

The rings need not be commutative, and transition maps need not be injective.
The index and coefficient universes are independent. The stage witnessing
equality may depend on the two classes; descent is not asserted from a prescribed
stage. The finite-projective class statements concern isomorphism classes before
group completion. The corresponding K₀ comparison identifies the additive direct
limit of the K₀ groups with the K₀ of the ring limit, characterized by its
canonical stage maps.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  the finite-idempotent description of projective modules and directed-limit argument.
* Projective Modules' right scalar extension, finite-projective class maps,
  idempotent-range classification and common-stage range-equivalence criterion.
-/

@[expose] public section

universe uι uR

namespace KTheory.ProjectiveClass

/-- Equality of two stage classes after canonical scalar extension to the
limit is detected at a common upper stage. -/
theorem map_eq_iff_exists_common_stage
    {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (R : ι → Type uR) [∀ i, Ring (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]
    (i j : ι) (x : KTheory.ProjectiveClass (R i))
    (y : KTheory.ProjectiveClass (R j)) :
    KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i) x =
        KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f j) y ↔
      ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
        KTheory.ProjectiveClass.map (f i k hik) x =
          KTheory.ProjectiveClass.map (f j k hjk) y := by
  classical
  constructor
  · intro h
    obtain ⟨X, rfl⟩ := of_surjective (R i) x
    obtain ⟨Y, rfl⟩ := of_surjective (R j) y
    rw [map_of, map_of] at h
    obtain ⟨e⟩ := (of_eq_iff _ _ _).mp h
    obtain ⟨n, A, hA, ⟨eA⟩⟩ :=
      Module.Projective.exists_equiv_range_idempotent_matrix (R := R i) (P := X)
    obtain ⟨m, B, hB, ⟨eB⟩⟩ :=
      Module.Projective.exists_equiv_range_idempotent_matrix (R := R j) (P := Y)
    obtain ⟨k, hik, hjk, ⟨eK⟩⟩ :=
      (DirectLimit.nonempty_rightExtension_rangeEquiv_iff_exists_common_stage
        R f i j A B hA hB).mp
          ⟨(ModuleCat.RightExtension.mapLinearEquiv (DirectLimit.Ring.of R f i) eA).symm.trans
            (e.trans
              (ModuleCat.RightExtension.mapLinearEquiv (DirectLimit.Ring.of R f j) eB))⟩
    refine ⟨k, hik, hjk, ?_⟩
    rw [map_of, map_of]
    -- The common-stage criterion returns mapped ranges, not scalar extensions.
    let eAk := (ModuleCat.RightExtension.mapLinearEquiv (f i k hik) eA).trans
      (ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv (f i k hik) A hA)
    let eBk := (ModuleCat.RightExtension.mapLinearEquiv (f j k hjk) eB).trans
      (ModuleCat.RightExtension.idempotentMatrixRangeLinearEquiv (f j k hjk) B hB)
    exact of_eq_of_equiv (R k) _ (eAk.trans (eK.trans eBk.symm))
  · rintro ⟨k, hik, hjk, h⟩
    have hi : (DirectLimit.Ring.of R f k).comp (f i k hik) =
        DirectLimit.Ring.of R f i := by
      ext a
      exact DirectLimit.Ring.of_f (G := R) (f := f) hik a
    have hj : (DirectLimit.Ring.of R f k).comp (f j k hjk) =
        DirectLimit.Ring.of R f j := by
      ext a
      exact DirectLimit.Ring.of_f (G := R) (f := f) hjk a
    calc
      map (DirectLimit.Ring.of R f i) x =
          map (DirectLimit.Ring.of R f k) (map (f i k hik) x) := by
        rw [← hi, map_comp, AddMonoidHom.comp_apply]
      _ = map (DirectLimit.Ring.of R f k) (map (f j k hjk) y) :=
        congrArg (map (DirectLimit.Ring.of R f k)) h
      _ = map (DirectLimit.Ring.of R f j) y := by
        rw [← hj, map_comp, AddMonoidHom.comp_apply]

/-- Every finite-projective right-module class over a nonempty directed
ring limit comes by canonical scalar extension from some stage. -/
theorem exists_map_eq
    {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (R : ι → Type uR) [∀ i, Ring (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]
    (y : KTheory.ProjectiveClass (DirectLimit R f)) :
    ∃ (i : ι) (x : KTheory.ProjectiveClass (R i)),
      KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i) x = y := by
  classical
  obtain ⟨M, rfl⟩ := of_surjective (DirectLimit R f) y
  obtain ⟨i, n, A, hA, ⟨e⟩⟩ :=
    DirectLimit.exists_rightExtension_range_idempotent_matrix_equiv R f M
  let Q := LinearMap.range (Matrix.mulVecBilin (R i) (R i)ᵐᵒᵖ A)
  have hQ : Module.Finite (R i)ᵐᵒᵖ Q ∧ Module.Projective (R i)ᵐᵒᵖ Q :=
    (Module.finite_projective_iff_exists_equiv_range_idempotent_matrix
      (R := R i) (P := Q)).2 ⟨n, A, hA.eq, ⟨LinearEquiv.refl (R i)ᵐᵒᵖ Q⟩⟩
  let : Module.Finite (R i)ᵐᵒᵖ Q := hQ.1
  let : Module.Projective (R i)ᵐᵒᵖ Q := hQ.2
  refine ⟨i, of (R i) Q, ?_⟩
  rw [map_of]
  exact of_eq_of_equiv (DirectLimit R f) _ e

end KTheory.ProjectiveClass

/-!
## Additive comparison and universal property

The comparison uses Mathlib's additive direct limit of commutative monoids,
with its canonical ℕ-module structure; it does not group-complete the classes.
-/

universe uA

namespace KTheory.ProjectiveClass

variable {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable (R : ι → Type uR) [∀ i, Ring (R i)]
variable (f : ∀ i j, i ≤ j → R i →+* R j)
variable [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]

/-- The canonical scalar-extension maps form an additive cocone over the ring diagram. -/
theorem map_directLimit_of_comp (i j : ι) (hij : i ≤ j) :
    (KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f j)).comp
        (KTheory.ProjectiveClass.map (f i j hij)) =
      KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i) := by
  rw [← KTheory.ProjectiveClass.map_comp]
  congr 1
  ext x
  exact DirectLimit.Ring.of_f (G := R) (f := f) hij x

open scoped Classical in
/-- The additive direct limit of the finite-projective class monoids is additively
equivalent to the finite-projective class monoid of the ring limit.
See Weibel, *The K-book*, for the finite-idempotent directed-limit argument. -/
noncomputable def directLimitEquiv :
    AddCommGroup.DirectLimit (fun i ↦ KTheory.ProjectiveClass (R i))
        (fun i j h ↦ KTheory.ProjectiveClass.map (f i j h)) ≃+
      KTheory.ProjectiveClass (DirectLimit R f) := by
  refine AddEquiv.ofBijective
    (AddCommGroup.DirectLimit.lift
      (fun i ↦ KTheory.ProjectiveClass (R i))
      (fun i j h ↦ KTheory.ProjectiveClass.map (f i j h))
      (KTheory.ProjectiveClass (DirectLimit R f))
      (fun i ↦ KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i))
      (fun i j h x ↦ DFunLike.congr_fun (map_directLimit_of_comp R f i j h) x)) ?_
  -- Capture the original ring-system laws before installing the derived system.
  have hf_id (i : ι) : f i i le_rfl = RingHom.id (R i) := by
    ext a
    exact DirectedSystem.map_self' f a
  have hf_comp (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) :
      (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk) := by
    ext a
    exact DirectedSystem.map_map' f hij hjk a
  -- The canonical ℕ-linear family in the original additive direct limit.
  let fN : ∀ i j : ι, i ≤ j →
      KTheory.ProjectiveClass (R i) →ₗ[ℕ] KTheory.ProjectiveClass (R j) :=
    fun i j h ↦ (KTheory.ProjectiveClass.map (f i j h)).toNatLinearMap
  let : DirectedSystem (fun i ↦ KTheory.ProjectiveClass (R i)) (fN · · ·) := {
    map_self := fun {i} x ↦ by
      change KTheory.ProjectiveClass.map (f i i le_rfl) x = x
      simp only [hf_id i, KTheory.ProjectiveClass.map_id, AddMonoidHom.id_apply]
    map_map := fun {k j i} hij hjk x ↦ by
      change KTheory.ProjectiveClass.map (f j k hjk)
          (KTheory.ProjectiveClass.map (f i j hij) x) =
        KTheory.ProjectiveClass.map (f i k (hij.trans hjk)) x
      calc
        _ = KTheory.ProjectiveClass.map ((f j k hjk).comp (f i j hij)) x :=
          (DFunLike.congr_fun
            (KTheory.ProjectiveClass.map_comp (f i j hij) (f j k hjk)) x).symm
        _ = _ := congrArg
          (fun g : R i →+* R k ↦ KTheory.ProjectiveClass.map g x)
          (hf_comp i j k hij hjk)
  }
  have hJS : ∀ z : KTheory.ProjectiveClass (DirectLimit R f),
      ∃ (i : ι) (x : KTheory.ProjectiveClass (R i)),
        KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i) x = z := by
    intro z
    exact KTheory.ProjectiveClass.exists_map_eq R f z
  have hEQ (i j : ι) (x : KTheory.ProjectiveClass (R i))
      (y : KTheory.ProjectiveClass (R j)) :
      KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i) x =
          KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f j) y ↔
        ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
          KTheory.ProjectiveClass.map (f i k hik) x =
            KTheory.ProjectiveClass.map (f j k hjk) y := by
    exact KTheory.ProjectiveClass.map_eq_iff_exists_common_stage R f i j x y
  -- The original target and canonical maps, with independent universes.
  let C : CategoryTheory.Functor.CoconeTypes.{max uι uR}
      (DirectedSystem.typesFunctor fN) := {
    pt := KTheory.ProjectiveClass (DirectLimit R f)
    ι := fun i ↦ KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i)
    ι_naturality := by
      intro i j h
      funext x
      exact DFunLike.congr_fun
        (map_directLimit_of_comp R f i j (CategoryTheory.leOfHom h)) x
  }
  have hC : C.IsColimit := by
    refine ⟨⟨?_, ?_⟩⟩
    · apply (C.descColimitType_injective_iff_of_isFiltered).2
      intro i j x y hxy
      obtain ⟨k, hik, hjk, hk⟩ := (hEQ i j x y).mp hxy
      refine ⟨k, CategoryTheory.homOfLE hik, CategoryTheory.homOfLE hjk, ?_⟩
      exact (DirectedSystem.typesFunctor_map_homOfLE
          (G := fun i ↦ KTheory.ProjectiveClass (R i)) fN hik x).trans
        (hk.trans (DirectedSystem.typesFunctor_map_homOfLE
          (G := fun i ↦ KTheory.ProjectiveClass (R i)) fN hjk y).symm)
    · apply (C.descColimitType_surjective_iff).2
      intro z
      exact hJS z
  -- The target legs agree with the original lift on the canonical source legs.
  have hstage (i : ι) (x : KTheory.ProjectiveClass (R i)) :
      C.ι i x =
        (AddCommGroup.DirectLimit.lift
          (fun i ↦ KTheory.ProjectiveClass (R i))
          (fun i j h ↦ KTheory.ProjectiveClass.map (f i j h))
          (KTheory.ProjectiveClass (DirectLimit R f))
          (fun i ↦ KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i))
          (fun i j h x ↦ DFunLike.congr_fun (map_directLimit_of_comp R f i j h) x))
        ((Module.DirectLimit.coconeTypes
          (fun i ↦ KTheory.ProjectiveClass (R i)) fN).ι i x) := by
    change KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i) x =
      (AddCommGroup.DirectLimit.lift
        (fun i ↦ KTheory.ProjectiveClass (R i))
        (fun i j h ↦ KTheory.ProjectiveClass.map (f i j h))
        (KTheory.ProjectiveClass (DirectLimit R f))
        (fun i ↦ KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i))
        (fun i j h x ↦ DFunLike.congr_fun (map_directLimit_of_comp R f i j h) x))
      (AddCommGroup.DirectLimit.of
        (fun i ↦ KTheory.ProjectiveClass (R i))
        (fun i j h ↦ KTheory.ProjectiveClass.map (f i j h)) i x)
    exact (AddCommGroup.DirectLimit.lift_of
        (G := fun i ↦ KTheory.ProjectiveClass (R i))
        (f := fun i j h ↦ KTheory.ProjectiveClass.map (f i j h))
        (KTheory.ProjectiveClass (DirectLimit R f))
        (fun i ↦ KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i))
        (fun i j h x ↦ DFunLike.congr_fun (map_directLimit_of_comp R f i j h) x)
        i x).symm
  exact ((Module.DirectLimit.coconeTypesIsColimit
    (fun i ↦ KTheory.ProjectiveClass (R i)) fN).iff_bijective (c' := C)
      (AddCommGroup.DirectLimit.lift
        (fun i ↦ KTheory.ProjectiveClass (R i))
        (fun i j h ↦ KTheory.ProjectiveClass.map (f i j h))
        (KTheory.ProjectiveClass (DirectLimit R f))
        (fun i ↦ KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i))
        (fun i j h x ↦ DFunLike.congr_fun (map_directLimit_of_comp R f i j h) x))
      hstage).mp hC

open scoped Classical in
/-- The forward homomorphism of the comparison equivalence is the additive direct-limit
lift of the canonical scalar-extension maps. -/
theorem directLimitEquiv_toAddMonoidHom :
    (directLimitEquiv R f).toAddMonoidHom =
      AddCommGroup.DirectLimit.lift
        (fun i ↦ KTheory.ProjectiveClass (R i))
        (fun i j h ↦ KTheory.ProjectiveClass.map (f i j h))
        (KTheory.ProjectiveClass (DirectLimit R f))
        (fun i ↦ KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i))
        (fun i j h x ↦
          DFunLike.congr_fun (map_directLimit_of_comp R f i j h) x) := by
  rfl

open scoped Classical in
/-- The comparison equivalence evaluates on a stage class as canonical scalar extension. -/
theorem directLimitEquiv_apply_of (i : ι)
    (x : KTheory.ProjectiveClass (R i)) :
    directLimitEquiv R f
        (AddCommGroup.DirectLimit.of
          (fun i ↦ KTheory.ProjectiveClass (R i))
          (fun i j h ↦ KTheory.ProjectiveClass.map (f i j h)) i x) =
      KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i) x := by
  simpa only [AddEquiv.coe_toAddMonoidHom, AddCommGroup.DirectLimit.lift_of] using
    DFunLike.congr_fun (directLimitEquiv_toAddMonoidHom R f)
      (AddCommGroup.DirectLimit.of
        (fun i ↦ KTheory.ProjectiveClass (R i))
        (fun i j h ↦ KTheory.ProjectiveClass.map (f i j h)) i x)

open scoped Classical in
/-- The inverse comparison sends a canonical scalar-extension image to its additive
direct-limit stage image. -/
theorem directLimitEquiv_symm_map (i : ι)
    (x : KTheory.ProjectiveClass (R i)) :
    (directLimitEquiv R f).symm
        (KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i) x) =
      AddCommGroup.DirectLimit.of
        (fun i ↦ KTheory.ProjectiveClass (R i))
        (fun i j h ↦ KTheory.ProjectiveClass.map (f i j h)) i x := by
  apply (directLimitEquiv R f).injective
  rw [AddEquiv.apply_symm_apply, directLimitEquiv_apply_of]

/-- Additive maps out of the class monoid of the ring limit are determined by their
composites with all canonical scalar-extension maps. -/
theorem directLimit_hom_ext {A : Type uA} [AddCommMonoid A]
    {a b : KTheory.ProjectiveClass (DirectLimit R f) →+ A}
    (h : ∀ i : ι,
      a.comp (KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i)) =
        b.comp (KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i))) :
    a = b := by
  apply AddMonoidHom.ext
  intro y
  obtain ⟨i, x, rfl⟩ := exists_map_eq R f y
  exact DFunLike.congr_fun (h i) x

open scoped Classical in
/-- A compatible family of additive maps extends through the inverse comparison, and
the resulting map restricts to the original family at every stage. -/
theorem directLimitEquiv_lift_comp_map {A : Type uA} [AddCommMonoid A]
    (a : ∀ i : ι, KTheory.ProjectiveClass (R i) →+ A)
    (ha : ∀ (i j : ι) (h : i ≤ j),
      (a j).comp (KTheory.ProjectiveClass.map (f i j h)) = a i)
    (i : ι) :
    ((AddCommGroup.DirectLimit.lift
          (fun i ↦ KTheory.ProjectiveClass (R i))
          (fun i j h ↦ KTheory.ProjectiveClass.map (f i j h)) A a
          (fun i j h x ↦ DFunLike.congr_fun (ha i j h) x)).comp
        (directLimitEquiv R f).symm.toAddMonoidHom).comp
      (KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i)) = a i := by
  apply AddMonoidHom.ext
  intro x
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    directLimitEquiv_symm_map, AddCommGroup.DirectLimit.lift_of]

end KTheory.ProjectiveClass

/-!
## Canonical K₀ comparison

The source of the comparison is Mathlib's `AddCommGroup.DirectLimit` with the
original `KTheory.K0.map` transition homomorphisms. The scoped classical choice
fixes the stock carrier's computational `DecidableEq` parameter, without adding
a mathematical hypothesis or choosing a different carrier. No directed-system
instance on K₀ is assumed publicly in addition to the given ring system.
-/

namespace KTheory.K0

open CategoryTheory

universe uG

variable {ι : Type uι} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable (R : ι → Type uR) [∀ i, Ring (R i)]
variable (f : ∀ i j, i ≤ j → R i →+* R j)
variable [DirectedSystem R (fun i j h ↦ (f i j h : R i → R j))]

/-- The original K₀ maps to the ring limit form a coherent cocone. -/
theorem map_directLimit_of_comp (i j : ι) (hij : i ≤ j) :
    (KTheory.K0.map (DirectLimit.Ring.of R f j)).comp (KTheory.K0.map (f i j hij)) =
      KTheory.K0.map (DirectLimit.Ring.of R f i) := by
  rw [← KTheory.K0.map_comp]
  congr 1
  ext x
  exact DirectLimit.Ring.of_f (G := R) (f := f) hij x

open scoped Classical in
/-- The additive comparison from the stock direct limit of the original K₀
system to the original K₀ of the directed ring limit.

See Weibel, *The K-book*, for the finite-idempotent directed-limit argument. -/
noncomputable def directLimitEquiv :
    AddCommGroup.DirectLimit (fun i ↦ KTheory.K0 (R i))
        (fun i j h ↦ KTheory.K0.map (f i j h)) ≃+
      KTheory.K0 (DirectLimit R f) := by
  refine AddEquiv.ofBijective
    (AddCommGroup.DirectLimit.lift (fun i ↦ KTheory.K0 (R i))
      (fun i j h ↦ KTheory.K0.map (f i j h)) (KTheory.K0 (DirectLimit R f))
      (fun i ↦ KTheory.K0.map (DirectLimit.Ring.of R f i))
      (fun i j h x ↦ DFunLike.congr_fun (map_directLimit_of_comp R f i j h) x)) ?_
  -- Capture the ring-system laws before installing derived class systems.
  have hf_id (i : ι) : f i i le_rfl = RingHom.id (R i) := by
    ext a
    exact DirectedSystem.map_self' f a
  have hf_comp (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) :
      (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk) := by
    ext a
    exact DirectedSystem.map_map' f hij hjk a
  -- The ORIGINAL projective-class system and cocone, before group completion.
  let t : ∀ i j : ι, i ≤ j →
      KTheory.ProjectiveClass (R i) →+ KTheory.ProjectiveClass (R j) :=
    fun i j h ↦ KTheory.ProjectiveClass.map (f i j h)
  let c : ∀ i : ι, KTheory.ProjectiveClass (R i) →+
      KTheory.ProjectiveClass (DirectLimit R f) :=
    fun i ↦ KTheory.ProjectiveClass.map (DirectLimit.Ring.of R f i)
  let : DirectedSystem (fun i ↦ KTheory.ProjectiveClass (R i))
      (fun ⦃i j⦄ (h : i ≤ j) ↦
        (t i j h : KTheory.ProjectiveClass (R i) → KTheory.ProjectiveClass (R j))) := {
    map_self := fun {i} x ↦ by
      change KTheory.ProjectiveClass.map (f i i le_rfl) x = x
      simp only [hf_id i, KTheory.ProjectiveClass.map_id, AddMonoidHom.id_apply]
    map_map := fun {k j i} hij hjk x ↦ by
      change KTheory.ProjectiveClass.map (f j k hjk)
          (KTheory.ProjectiveClass.map (f i j hij) x) =
        KTheory.ProjectiveClass.map (f i k (hij.trans hjk)) x
      calc
        _ = KTheory.ProjectiveClass.map ((f j k hjk).comp (f i j hij)) x :=
          (DFunLike.congr_fun
            (KTheory.ProjectiveClass.map_comp (f i j hij) (f j k hjk)) x).symm
        _ = _ := congrArg
          (fun g : R i →+* R k ↦ KTheory.ProjectiveClass.map g x)
          (hf_comp i j k hij hjk)
  }
  have hc (i j : ι) (hij : i ≤ j) : (c j).comp (t i j hij) = c i := by
    simpa only [c, t] using
      (KTheory.ProjectiveClass.map_directLimit_of_comp R f i j hij)
  have hs : ∀ b : KTheory.ProjectiveClass (DirectLimit R f),
      ∃ (i : ι) (a : KTheory.ProjectiveClass (R i)), c i a = b := by
    intro b
    exact KTheory.ProjectiveClass.exists_map_eq R f b
  have he : ∀ (i j : ι) (a : KTheory.ProjectiveClass (R i))
      (b : KTheory.ProjectiveClass (R j)), c i a = c j b →
      ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), t i k hik a = t j k hjk b := by
    intro i j a b hab
    exact (KTheory.ProjectiveClass.map_eq_iff_exists_common_stage
      R f i j a b).mp hab
  -- Transfer joint surjectivity and common-stage equality to group completions.
  -- The public whole-map equation identifies these with the original K₀ maps.
  have hJS : ∀ z : KTheory.K0 (DirectLimit R f),
      ∃ (i : ι) (xi : KTheory.K0 (R i)),
        KTheory.K0.map (DirectLimit.Ring.of R f i) xi = z := by
    intro z
    obtain ⟨i, xi, hxi⟩ :=
      Algebra.GrothendieckAddGroup.jointly_surjective_lift_of_jointly_surjective
        t c hc hs z
    refine ⟨i, xi, ?_⟩
    rw [KTheory.K0.map_eq_grothendieckLift]
    exact hxi
  have hEQ : ∀ (i j : ι) (xi : KTheory.K0 (R i)) (xj : KTheory.K0 (R j)),
      KTheory.K0.map (DirectLimit.Ring.of R f i) xi =
          KTheory.K0.map (DirectLimit.Ring.of R f j) xj ↔
        ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
          KTheory.K0.map (f i k hik) xi = KTheory.K0.map (f j k hjk) xj := by
    intro i j xi xj
    simpa only [KTheory.K0.map_eq_grothendieckLift, KTheory.K0.ofClass, c, t] using
      (Algebra.GrothendieckAddGroup.lift_eq_lift_iff_exists
        t c hc hs he i j xi xj)
  -- This is exactly the coefficient family used INSIDE AddCommGroup.DirectLimit:
  -- canonical ℕ-modules, original additive maps reinterpreted by toNatLinearMap.
  -- No alternative ℕ-module dictionaries or DecidableEq are introduced.
  let fN : ∀ i j : ι, i ≤ j → KTheory.K0 (R i) →ₗ[ℕ] KTheory.K0 (R j) :=
    fun i j h ↦ (KTheory.K0.map (f i j h)).toNatLinearMap
  let : DirectedSystem (fun i ↦ KTheory.K0 (R i)) (fN · · ·) := {
    map_self := fun {i} x ↦ by
      change KTheory.K0.map (f i i le_rfl) x = x
      simp only [hf_id i, KTheory.K0.map_id, AddMonoidHom.id_apply]
    map_map := fun {k j i} hij hjk x ↦ by
      change KTheory.K0.map (f j k hjk) (KTheory.K0.map (f i j hij) x) =
        KTheory.K0.map (f i k (hij.trans hjk)) x
      calc
        _ = KTheory.K0.map ((f j k hjk).comp (f i j hij)) x :=
          (DFunLike.congr_fun (KTheory.K0.map_comp (f i j hij) (f j k hjk)) x).symm
        _ = _ := congrArg (fun g : R i →+* R k ↦ KTheory.K0.map g x)
          (hf_comp i j k hij hjk)
  }
  -- This packages the ORIGINAL target and canonical maps, not a new colimit model.
  -- The unlifted source functor has stage universe uR; its point has max uι uR.
  let C : Functor.CoconeTypes.{max uι uR} (DirectedSystem.typesFunctor fN) := {
    pt := KTheory.K0 (DirectLimit R f)
    ι := fun i ↦ KTheory.K0.map (DirectLimit.Ring.of R f i)
    ι_naturality := by
      intro i j h
      funext x
      exact DFunLike.congr_fun
        (map_directLimit_of_comp R f i j (leOfHom h)) x
  }
  have hC : C.IsColimit := by
    refine ⟨⟨?_, ?_⟩⟩
    · apply (C.descColimitType_injective_iff_of_isFiltered).2
      intro i j x y hxy
      obtain ⟨k, hik, hjk, hk⟩ := (hEQ i j x y).mp hxy
      refine ⟨k, homOfLE hik, homOfLE hjk, ?_⟩
      exact (DirectedSystem.typesFunctor_map_homOfLE
        (G := fun i ↦ KTheory.K0 (R i)) fN hik x).trans
        (hk.trans (DirectedSystem.typesFunctor_map_homOfLE
          (G := fun i ↦ KTheory.K0 (R i)) fN hjk y).symm)
    · apply (C.descColimitType_surjective_iff).2
      intro z
      exact hJS z
  -- The only stage square is the symmetric STOCK lift_of equation.
  -- No stage-bridge premise, module/additive comparison equivalence, induction,
  -- individual-leg injectivity, or second eventual-equality proof is needed.
  have hstage (i : ι) (x : KTheory.K0 (R i)) :
      C.ι i x =
        (AddCommGroup.DirectLimit.lift (fun i ↦ KTheory.K0 (R i))
          (fun i j h ↦ KTheory.K0.map (f i j h)) (KTheory.K0 (DirectLimit R f))
          (fun i ↦ KTheory.K0.map (DirectLimit.Ring.of R f i))
          (fun i j h x ↦ DFunLike.congr_fun (map_directLimit_of_comp R f i j h) x))
        ((Module.DirectLimit.coconeTypes (fun i ↦ KTheory.K0 (R i)) fN).ι i x) := by
    change KTheory.K0.map (DirectLimit.Ring.of R f i) x =
      (AddCommGroup.DirectLimit.lift (fun i ↦ KTheory.K0 (R i))
        (fun i j h ↦ KTheory.K0.map (f i j h)) (KTheory.K0 (DirectLimit R f))
        (fun i ↦ KTheory.K0.map (DirectLimit.Ring.of R f i))
        (fun i j h x ↦ DFunLike.congr_fun (map_directLimit_of_comp R f i j h) x))
      (AddCommGroup.DirectLimit.of (fun i ↦ KTheory.K0 (R i))
        (fun i j h ↦ KTheory.K0.map (f i j h)) i x)
    exact (AddCommGroup.DirectLimit.lift_of
        (G := fun i ↦ KTheory.K0 (R i))
        (f := fun i j h ↦ KTheory.K0.map (f i j h))
        (KTheory.K0 (DirectLimit R f))
        (fun i ↦ KTheory.K0.map (DirectLimit.Ring.of R f i))
        (fun i j h x ↦ DFunLike.congr_fun (map_directLimit_of_comp R f i j h) x)
        i x).symm
  exact ((Module.DirectLimit.coconeTypesIsColimit
    (fun i ↦ KTheory.K0 (R i)) fN).iff_bijective (c' := C)
      (AddCommGroup.DirectLimit.lift (fun i ↦ KTheory.K0 (R i))
        (fun i j h ↦ KTheory.K0.map (f i j h)) (KTheory.K0 (DirectLimit R f))
        (fun i ↦ KTheory.K0.map (DirectLimit.Ring.of R f i))
        (fun i j h x ↦ DFunLike.congr_fun (map_directLimit_of_comp R f i j h) x))
      hstage).mp hC

open scoped Classical in
/-- The forward homomorphism of the comparison is the stock lift of the
original scalar-extension cocone. -/
theorem directLimitEquiv_toAddMonoidHom :
    (directLimitEquiv R f).toAddMonoidHom =
      AddCommGroup.DirectLimit.lift (fun i ↦ KTheory.K0 (R i))
        (fun i j h ↦ KTheory.K0.map (f i j h)) (KTheory.K0 (DirectLimit R f))
        (fun i ↦ KTheory.K0.map (DirectLimit.Ring.of R f i))
        (fun i j h x ↦ DFunLike.congr_fun (map_directLimit_of_comp R f i j h) x) := by
  rfl

open scoped Classical in
/-- On every canonical direct-limit stage image, the comparison is the original K₀ map
along the canonical ring-limit homomorphism. -/
theorem directLimitEquiv_apply_of (i : ι) (x : KTheory.K0 (R i)) :
    directLimitEquiv R f
        (AddCommGroup.DirectLimit.of (fun i ↦ KTheory.K0 (R i))
          (fun i j h ↦ KTheory.K0.map (f i j h)) i x) =
      KTheory.K0.map (DirectLimit.Ring.of R f i) x := by
  simpa only [AddEquiv.coe_toAddMonoidHom, AddCommGroup.DirectLimit.lift_of] using
    DFunLike.congr_fun (directLimitEquiv_toAddMonoidHom R f)
      (AddCommGroup.DirectLimit.of (fun i ↦ KTheory.K0 (R i))
        (fun i j h ↦ KTheory.K0.map (f i j h)) i x)

open scoped Classical in
/-- The inverse comparison sends an original canonical stage-map image to
its canonical direct-limit image. -/
theorem directLimitEquiv_symm_map (i : ι) (x : KTheory.K0 (R i)) :
    (directLimitEquiv R f).symm (KTheory.K0.map (DirectLimit.Ring.of R f i) x) =
      AddCommGroup.DirectLimit.of (fun i ↦ KTheory.K0 (R i))
        (fun i j h ↦ KTheory.K0.map (f i j h)) i x := by
  apply (directLimitEquiv R f).injective
  rw [AddEquiv.apply_symm_apply, directLimitEquiv_apply_of]

/-- Additive maps out of the original K₀ of the ring limit are determined by
their composites with the original canonical stage maps. -/
theorem directLimit_hom_ext {G : Type uG} [AddCommGroup G]
    {a b : KTheory.K0 (DirectLimit R f) →+ G}
    (h : ∀ i : ι,
      a.comp (KTheory.K0.map (DirectLimit.Ring.of R f i)) =
        b.comp (KTheory.K0.map (DirectLimit.Ring.of R f i))) :
    a = b := by
  classical
  have hab : a.comp (directLimitEquiv R f).toAddMonoidHom =
      b.comp (directLimitEquiv R f).toAddMonoidHom := by
    apply AddCommGroup.DirectLimit.hom_ext
    intro i
    apply AddMonoidHom.ext
    intro x
    simpa only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      directLimitEquiv_apply_of] using DFunLike.congr_fun (h i) x
  apply AddMonoidHom.ext
  intro y
  obtain ⟨x, rfl⟩ := (directLimitEquiv R f).surjective y
  exact DFunLike.congr_fun hab x

open scoped Classical in
/-- A compatible family extends to the original K₀ of the ring limit by the
stock lift composed with the inverse comparison; its restriction is the given
family. Together with `directLimit_hom_ext`, this gives existence and uniqueness. -/
theorem directLimitEquiv_lift_comp_map {G : Type uG} [AddCommGroup G]
    (a : ∀ i : ι, KTheory.K0 (R i) →+ G)
    (ha : ∀ (i j : ι) (h : i ≤ j),
      (a j).comp (KTheory.K0.map (f i j h)) = a i)
    (i : ι) :
    ((AddCommGroup.DirectLimit.lift (fun i ↦ KTheory.K0 (R i))
          (fun i j h ↦ KTheory.K0.map (f i j h)) G a
          (fun i j h x ↦ DFunLike.congr_fun (ha i j h) x)).comp
        (directLimitEquiv R f).symm.toAddMonoidHom).comp
      (KTheory.K0.map (DirectLimit.Ring.of R f i)) = a i := by
  apply AddMonoidHom.ext
  intro x
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    directLimitEquiv_symm_map, AddCommGroup.DirectLimit.lift_of]

end KTheory.K0
