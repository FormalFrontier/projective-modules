/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Iris; see docs/CREDITS.md
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.PicardGroup
public import ProjectiveModules.Module.RankFiberDecomposition
public import ProjectiveModules.ExteriorPower.Invertible
import ProjectiveModules.Module.Product
import ProjectiveModules.Invertible.OfRankOne

/-!
# Determinant lines of finite projective modules

The determinant line is the product, over the nonempty stalk-rank fibers, of
that fiber's top exterior power. Scalars act through the quotient ring of each
fiber. In particular, an attained rank-zero fiber contributes an exterior power
of degree zero, rather than being omitted. The construction also allows an
empty prime spectrum and an empty product.

Isomorphic modules have isomorphic determinant lines, and scalar extension to a
rank-fiber ring recovers the corresponding top exterior power. The zero module
has determinant line isomorphic to the regular module; the determinant line of
an invertible module is isomorphic to the module itself.

Each component is an invertible top exterior power. A componentwise evaluation
pairing assembles these into an invertible module over the original ring.

## References

For the mathematical determinant construction, see C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*.

The construction uses the rank-fiber decomposition and Mathlib's exterior-power,
tensor-product and invertible-module interfaces. In particular, the final step
uses `Module.Invertible.right`, from the invertible-module formalization by
Junyan Xu. The rank-fiber decomposition and the exterior-algebra base-change
formalization are credited in `docs/CREDITS.md`. The degree-zero and degree-one
comparisons use Mathlib's exterior-power equivalences by Sophie Morel and
Joël Riou.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped TensorProduct

namespace Module

variable (R : Type u) [CommRing R]
variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

/-- The top exterior power on one stalk-rank fiber. -/
abbrev DeterminantLineComponent (i : rankFiberIndex R P) :=
  ⋀[rankFiberRing R P i]^(rankFiberRank R P i) (rankFiberModule R P i)

/-- The determinant-line carrier, assembled over all nonempty rank fibers. -/
def DeterminantLine : Type (max u v) :=
  ∀ i : rankFiberIndex R P, DeterminantLineComponent R P i

namespace DeterminantLine

instance instAddCommGroup : AddCommGroup (DeterminantLine R P) :=
  inferInstanceAs (AddCommGroup (∀ i : rankFiberIndex R P, DeterminantLineComponent R P i))

/-- Scalars act componentwise through the rank-fiber quotient maps. -/
instance instModule : Module R (DeterminantLine R P) := by
  letI : Module (∀ i : rankFiberIndex R P, rankFiberRing R P i) (DeterminantLine R P) :=
    inferInstanceAs (Module (∀ i : rankFiberIndex R P, rankFiberRing R P i)
      (∀ i : rankFiberIndex R P, DeterminantLineComponent R P i))
  exact Module.compHom (DeterminantLine R P) (rankFiberRingEquiv R P).toAlgHom.toRingHom

/-- Assemble a determinant-line element from its component exterior powers. -/
def ofComponents (x : ∀ i : rankFiberIndex R P, DeterminantLineComponent R P i) :
    DeterminantLine R P := x

/-- The component of a determinant-line element on a rank fiber. -/
def component (i : rankFiberIndex R P) (x : DeterminantLine R P) :
    DeterminantLineComponent R P i := x i

@[simp]
theorem component_ofComponents
    (x : ∀ i : rankFiberIndex R P, DeterminantLineComponent R P i)
    (i : rankFiberIndex R P) :
    component R P i (ofComponents R P x) = x i :=
  rfl

@[simp]
theorem ofComponents_component (x : DeterminantLine R P) :
    ofComponents R P (fun i ↦ component R P i x) = x :=
  rfl

@[ext]
theorem ext {x y : DeterminantLine R P}
    (h : ∀ i : rankFiberIndex R P, component R P i x = component R P i y) : x = y :=
  funext h

@[simp]
theorem component_zero (i : rankFiberIndex R P) :
    component R P i (0 : DeterminantLine R P) = 0 :=
  rfl

@[simp]
theorem component_add (i : rankFiberIndex R P) (x y : DeterminantLine R P) :
    component R P i (x + y) = component R P i x + component R P i y :=
  rfl

@[simp]
theorem component_smul (i : rankFiberIndex R P) (r : R) (x : DeterminantLine R P) :
    component R P i (r • x) = (rankFiberRingEquiv R P r i) • component R P i x :=
  rfl

-- Transport the coefficient-product action along the rank-fiber ring equivalence.
private def coefficientEquiv :
    let e := (rankFiberRingEquiv R P).toRingEquiv
    letI : RingHomInvPair e.symm.toRingHom e.toRingHom :=
      RingHomInvPair.of_ringEquiv_symm e
    letI : RingHomInvPair e.toRingHom e.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv e
    LinearEquiv e.symm.toRingHom (σ' := e.toRingHom)
      (∀ i : rankFiberIndex R P, DeterminantLineComponent R P i) (DeterminantLine R P) := by
  let e := (rankFiberRingEquiv R P).toRingEquiv
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm e
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e
  exact
    { toFun := ofComponents R P
      invFun := fun x i ↦ component R P i x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ by
        apply ext
        intro i
        change a i • x i = rankFiberRingEquiv R P (e.symm a) i • x i
        rw [show rankFiberRingEquiv R P (e.symm a) = a from e.apply_symm_apply a] }

instance instFinite : Module.Finite R (DeterminantLine R P) := by
  letI : Module.Finite (∀ i : rankFiberIndex R P, rankFiberRing R P i)
      (∀ i : rankFiberIndex R P, DeterminantLineComponent R P i) :=
    Module.finite_pi (rankFiberRing R P) (fun i ↦ ↥(DeterminantLineComponent R P i))
  let e := (rankFiberRingEquiv R P).toRingEquiv
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm e
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e
  exact Module.Finite.of_surjective (coefficientEquiv R P).toLinearMap
    (coefficientEquiv R P).surjective

instance instProjective : Module.Projective R (DeterminantLine R P) := by
  letI : Module.Projective (∀ i : rankFiberIndex R P, rankFiberRing R P i)
      (∀ i : rankFiberIndex R P, DeterminantLineComponent R P i) :=
    Module.projective_pi (rankFiberRing R P) (fun i ↦ ↥(DeterminantLineComponent R P i))
  let e := (rankFiberRingEquiv R P).toRingEquiv
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm e
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e
  exact Module.Projective.of_equiv (coefficientEquiv R P)

end DeterminantLine

private theorem determinantLineInvertible_component_algebraMap
    (r : R) (i : rankFiberIndex R P) :
    rankFiberRingEquiv R P r i = algebraMap R (rankFiberRing R P i) r := by
  simpa only [Algebra.algebraMap_self_apply, Pi.algebraMap_apply] using
    congrFun ((rankFiberRingEquiv R P).commutes r) i

-- The restricted component actions agree with the pulled-back product action.
private def determinantLineInvertibleComponentsLinearEquiv :
    (∀ i : rankFiberIndex R P, DeterminantLineComponent R P i) ≃ₗ[R]
      DeterminantLine R P where
  toFun := DeterminantLine.ofComponents R P
  invFun := fun x i ↦ DeterminantLine.component R P i x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    apply DeterminantLine.ext
    intro i
    change r • x i = rankFiberRingEquiv R P r i • x i
    rw [determinantLineInvertible_component_algebraMap R P r i]
    exact (IsScalarTower.algebraMap_smul (rankFiberRing R P i) r (x i)).symm

-- The inverse image of a coordinate idempotent acts as that coordinate's
-- projection on any product of modules on the rank-fiber rings.
private theorem determinantLineInvertible_projector_smul
    [DecidableEq (rankFiberIndex R P)]
    (N : rankFiberIndex R P → Type w)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, Module (rankFiberRing R P i) (N i)]
    [∀ i, IsScalarTower R (rankFiberRing R P i) (N i)]
    (i : rankFiberIndex R P) (x : ∀ j, N j) :
    (rankFiberRingEquiv R P).symm (Pi.single i 1) • x = Pi.single i (x i) := by
  classical
  funext j
  change (rankFiberRingEquiv R P).symm (Pi.single i 1) • x j = _
  rw [← IsScalarTower.algebraMap_smul (rankFiberRing R P j)]
  rw [← determinantLineInvertible_component_algebraMap R P
    ((rankFiberRingEquiv R P).symm (Pi.single i 1)) j]
  rw [(rankFiberRingEquiv R P).apply_symm_apply]
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.single_apply, h, Ne.symm h]

/-- A determinant line is an invertible module. -/
theorem determinantLine_invertible : Module.Invertible R (DeterminantLine R P) := by
  classical
  let A := rankFiberRing R P
  let C : rankFiberIndex R P → Type (max u v) :=
    fun i ↦ ↥(DeterminantLineComponent R P i)
  let D := ∀ i : rankFiberIndex R P, Module.Dual (A i) (C i)
  let e := rankFiberRingEquiv R P
  letI : ∀ i, Module.Invertible (A i) (C i) := fun i ↦
    exteriorPower.invertible_of_rankAtStalk_eq (rankFiberRank R P i)
      (funext (rankAtStalk_rankFiberModule R P i))
  -- Surjective quotient maps identify the two balancing relations.
  letI : ∀ i, TensorProduct.CompatibleSMul R (A i)
      (Module.Dual (A i) (C i)) (C i) := fun i ↦ ⟨by
    intro a f m
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective a
    change algebraMap R (A i) r = a at hr
    rw [← hr]
    simpa only [IsScalarTower.algebraMap_smul (A i)] using
      (TensorProduct.smul_tmul r f m)⟩
  let insert (i : rankFiberIndex R P) :
      (Module.Dual (A i) (C i) ⊗[A i] C i) →ₗ[R] (D ⊗[R] (∀ j, C j)) :=
    (TensorProduct.map (LinearMap.single R (fun j ↦ Module.Dual (A j) (C j)) i)
      (LinearMap.single R C i)).comp
      (TensorProduct.equivOfCompatibleSMul R (A i) R
        (Module.Dual (A i) (C i)) (C i)).toLinearMap
  let project (i : rankFiberIndex R P) :
      (D ⊗[R] (∀ j, C j)) →ₗ[R] (Module.Dual (A i) (C i) ⊗[A i] C i) :=
    (TensorProduct.equivOfCompatibleSMul R (A i) R
      (Module.Dual (A i) (C i)) (C i)).symm.toLinearMap.comp
      (TensorProduct.map (LinearMap.proj i) (LinearMap.proj i))
  have hinsert (i : rankFiberIndex R P) (f : Module.Dual (A i) (C i)) (m : C i) :
      insert i (f ⊗ₜ[A i] m) = Pi.single i f ⊗ₜ[R] Pi.single i m := by
    simp [insert, TensorProduct.equivOfCompatibleSMul]
  have hproject (i : rankFiberIndex R P) (d : D) (m : ∀ j, C j) :
      project i (d ⊗ₜ[R] m) = d i ⊗ₜ[A i] m i := by
    simp only [project, LinearMap.comp_apply, TensorProduct.map_tmul]
    change
      ((LinearMap.proj i : D →ₗ[R] Module.Dual (A i) (C i)) d) ⊗ₜ[A i]
        ((LinearMap.proj i : (∀ j, C j) →ₗ[R] C i) m) = d i ⊗ₜ[A i] m i
    exact congrArg₂ (TensorProduct.tmul (A i))
      (LinearMap.proj_apply (R := R) i d) (LinearMap.proj_apply (R := R) i m)
  let b : D →ₗ[R] (∀ i, C i) →ₗ[R] (∀ i, A i) :=
    { toFun := fun d ↦
        { toFun := fun m i ↦ d i (m i)
          map_add' := fun x y ↦ by
            funext i
            exact (d i).map_add (x i) (y i)
          map_smul' := fun r m ↦ by
            funext i
            exact ((d i).restrictScalars R).map_smul r (m i) }
      map_add' := fun d d' ↦ by
        ext m i
        rfl
      map_smul' := fun r d ↦ by
        ext m i
        rfl }
  let q : (D ⊗[R] (∀ i, C i)) →ₗ[R] R :=
    e.symm.toLinearEquiv.toLinearMap.comp (TensorProduct.lift b)
  have hq (d : D) (m : ∀ i, C i) :
      q (d ⊗ₜ[R] m) = e.symm (fun i ↦ d i (m i)) := rfl
  have hqinsert (i : rankFiberIndex R P)
      (z : Module.Dual (A i) (C i) ⊗[A i] C i) :
      q (insert i z) = e.symm (Pi.single i (contractLeft (A i) (C i) z)) := by
    refine TensorProduct.inductionOn
      (motive := fun z ↦
        q (insert i z) = e.symm (Pi.single i (contractLeft (A i) (C i) z))) z ?_ ?_
    · intro f m
      rw [hinsert, hq, contractLeft_apply]
      congr 1
      funext j
      by_cases h : j = i
      · subst j
        simp
      · simp [Pi.single_apply, h, Ne.symm h]
    · intro x y hx hy
      simp only [map_add, Pi.single_add, hx, hy]
  have hcontractproject (i : rankFiberIndex R P) (z : D ⊗[R] (∀ j, C j)) :
      contractLeft (A i) (C i) (project i z) = e (q z) i := by
    refine TensorProduct.inductionOn
      (motive := fun z ↦ contractLeft (A i) (C i) (project i z) = e (q z) i) z ?_ ?_
    · intro d m
      rw [hproject, contractLeft_apply, hq, e.apply_symm_apply]
    · intro x y hx hy
      simp only [map_add, Pi.add_apply, hx, hy]
  have hdiagonal (i : rankFiberIndex R P) (d : D) (m : ∀ j, C j) :
      (Pi.single i (d i) : D) ⊗ₜ[R] Pi.single i (m i) =
        (Pi.single i (d i) : D) ⊗ₜ[R] m := by
    let r := e.symm (Pi.single i 1)
    have hd : r • (Pi.single i (d i) : D) = Pi.single i (d i) := by
      simpa using determinantLineInvertible_projector_smul R P
        (fun j ↦ Module.Dual (A j) (C j)) i (Pi.single i (d i))
    have hm : r • m = Pi.single i (m i) :=
      determinantLineInvertible_projector_smul R P C i m
    rw [← hm, ← TensorProduct.smul_tmul, hd]
  have hdecompose (z : D ⊗[R] (∀ i, C i)) :
      ∑ i, insert i (project i z) = z := by
    refine TensorProduct.inductionOn
      (motive := fun z ↦ ∑ i, insert i (project i z) = z) z ?_ ?_
    · intro d m
      simp_rw [hproject, hinsert, hdiagonal]
      rw [← TensorProduct.sum_tmul, LinearMap.sum_single_apply]
    · intro x y hx hy
      simp only [map_add, Finset.sum_add_distrib, hx, hy]
  have hinjective : Function.Injective q := by
    intro x y h
    have hp : ∀ i, project i x = project i y := by
      intro i
      exact (Module.Invertible.bijective (R := A i) (M := C i)).1
        ((hcontractproject i x).trans
          ((congrArg (fun r : R ↦ e r i) h).trans (hcontractproject i y).symm))
    rw [← hdecompose x, ← hdecompose y]
    simp_rw [hp]
  have hsurjective : Function.Surjective q := by
    intro r
    have hz : ∀ i, ∃ z : Module.Dual (A i) (C i) ⊗[A i] C i,
        contractLeft (A i) (C i) z = e r i := fun i ↦
      (Module.Invertible.bijective (R := A i) (M := C i)).2 (e r i)
    choose z hz using hz
    refine ⟨∑ i, insert i (z i), ?_⟩
    rw [map_sum]
    simp_rw [hqinsert, hz]
    rw [← map_sum, LinearMap.sum_single_apply, e.symm_apply_apply]
  letI : Module.Invertible R (∀ i, C i) :=
    Module.Invertible.right (LinearEquiv.ofBijective q ⟨hinjective, hsurjective⟩)
  exact Module.Invertible.congr (determinantLineInvertibleComponentsLinearEquiv R P)

private def exteriorPowerCongr {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (n : ℕ) (e : M ≃ₗ[A] N) : (⋀[A]^n M) ≃ₗ[A] (⋀[A]^n N) :=
  LinearEquiv.ofLinearMap (exteriorPower.map n e.toLinearMap)
    (exteriorPower.map n e.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp, e.comp_symm, exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp, e.symm_comp, exteriorPower.map_id])

-- The transport model records all data that affect the carrier or scalar action.
-- Its instances depend only on that data, not on a particular module's rank API.
private abbrev determinantLineCongrData :=
  Σ k : LocallyConstant (PrimeSpectrum R) ℕ,
    (Function.Fiber k → R) × (Function.Fiber k → ℕ)

private theorem determinantLineCongrData_ext
    {k l : LocallyConstant (PrimeSpectrum R) ℕ}
    {a : Function.Fiber k → R} {b : Function.Fiber l → R}
    {n : Function.Fiber k → ℕ} {m : Function.Fiber l → ℕ}
    (h : k = l)
    (ha : ∀ i j, i.1 = j.1 → a i = b j)
    (hn : ∀ i j, i.1 = j.1 → n i = m j) :
    (⟨k, a, n⟩ : determinantLineCongrData R) = ⟨l, b, m⟩ := by
  cases h
  have hab : a = b := funext fun i ↦ ha i i rfl
  have hnm : n = m := funext fun i ↦ hn i i rfl
  cases hab
  cases hnm
  rfl

private abbrev determinantLineCongrRing (d : determinantLineCongrData R)
    (i : Function.Fiber d.1) :=
  R ⧸ Ideal.span {1 - d.2.1 i}

private abbrev determinantLineCongrComponent (d : determinantLineCongrData R)
    (M : Type v) [AddCommGroup M] [Module R M] (i : Function.Fiber d.1) :=
  ⋀[determinantLineCongrRing R d i]^(d.2.2 i)
    (determinantLineCongrRing R d i ⊗[R] M)

private def determinantLineCongrModel (d : determinantLineCongrData R)
    (M : Type v) [AddCommGroup M] [Module R M] : Type (max u v) :=
  ∀ i : Function.Fiber d.1, determinantLineCongrComponent R d M i

private instance determinantLineCongrModelAddCommGroup (d : determinantLineCongrData R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    AddCommGroup (determinantLineCongrModel R d M) :=
  inferInstanceAs (AddCommGroup
    (∀ i : Function.Fiber d.1, determinantLineCongrComponent R d M i))

private instance determinantLineCongrModelModule (d : determinantLineCongrData R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    Module R (determinantLineCongrModel R d M) := by
  letI : Module (∀ i : Function.Fiber d.1, determinantLineCongrRing R d i)
      (determinantLineCongrModel R d M) :=
    inferInstanceAs (Module (∀ i : Function.Fiber d.1, determinantLineCongrRing R d i)
      (∀ i : Function.Fiber d.1, determinantLineCongrComponent R d M i))
  exact Module.compHom (determinantLineCongrModel R d M)
    (AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ R (Ideal.span {1 - d.2.1 i})).toRingHom

private def determinantLineCongrModelEquiv :
    DeterminantLine R P ≃ₗ[R]
      determinantLineCongrModel R
        ⟨rankLocallyConstant R P, rankFiberIdempotent R P, rankFiberRank R P⟩ P where
  toFun x := fun i ↦ DeterminantLine.component R P i x
  invFun x := DeterminantLine.ofComponents R P x
  left_inv := DeterminantLine.ofComponents_component R P
  right_inv := fun _ ↦ rfl
  map_add' := fun x y ↦ funext fun i ↦ DeterminantLine.component_add R P i x y
  map_smul' := by
    intro r x
    funext i
    change DeterminantLine.component R P i (r • x) =
      (Ideal.Quotient.mk (Ideal.span {1 - rankFiberIdempotent R P i}) r) •
        DeterminantLine.component R P i x
    rw [DeterminantLine.component_smul]
    exact congrArg (fun a : rankFiberRing R P i ↦ a • DeterminantLine.component R P i x)
      (congrFun ((rankFiberRingEquiv R P).commutes r) i)

private def determinantLineCongrModelMap (d : determinantLineCongrData R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] (f : M ≃ₗ[R] N) :
    determinantLineCongrModel R d M ≃ₗ[R] determinantLineCongrModel R d N := by
  let e (i : Function.Fiber d.1) :
      determinantLineCongrComponent R d M i ≃ₗ[determinantLineCongrRing R d i]
        determinantLineCongrComponent R d N i :=
    exteriorPowerCongr (d.2.2 i) (f.baseChange R (determinantLineCongrRing R d i))
  exact {
    toFun := fun x i ↦ e i (x i)
    invFun := fun x i ↦ (e i).symm (x i)
    left_inv := fun x ↦ funext fun i ↦ (e i).symm_apply_apply (x i)
    right_inv := fun x ↦ funext fun i ↦ (e i).apply_symm_apply (x i)
    map_add' := fun x y ↦ funext fun i ↦ (e i).map_add (x i) (y i)
    map_smul' := fun r x ↦ funext fun i ↦
      (e i).map_smul (Ideal.Quotient.mk (Ideal.span {1 - d.2.1 i}) r) (x i) }

-- Equality elimination here transports the indices, rings, degrees, additive
-- groups and quotient-map scalar actions together, before returning to DLine.
private def determinantLineCongrModelTransport
    {d e : determinantLineCongrData R} (h : d = e)
    (M : Type v) [AddCommGroup M] [Module R M] :
    determinantLineCongrModel R d M ≃ₗ[R] determinantLineCongrModel R e M := by
  cases h
  exact LinearEquiv.refl R _

/-- Isomorphic finite projective modules have isomorphic determinant lines. -/
theorem determinantLine_congr (Q : Type w) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q] (f : P ≃ₗ[R] Q) :
    Nonempty (DeterminantLine R P ≃ₗ[R] DeterminantLine R Q) := by
  have hrank : rankLocallyConstant R P = rankLocallyConstant R Q := by
    ext p
    exact congrFun (rankAtStalk_eq_of_equiv f) p
  have hdata :
      (⟨rankLocallyConstant R P, rankFiberIdempotent R P, rankFiberRank R P⟩ :
        determinantLineCongrData R) =
      ⟨rankLocallyConstant R Q, rankFiberIdempotent R Q, rankFiberRank R Q⟩ := by
    refine determinantLineCongrData_ext R hrank ?_ ?_
    · intro i j hij
      have he :
          (⟨rankFiberIdempotent R P i, rankFiberIdempotent_isIdempotent R P i⟩ :
            {a : R // IsIdempotentElem a}) =
          ⟨rankFiberIdempotent R Q j, rankFiberIdempotent_isIdempotent R Q j⟩ := by
        apply (PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).injective
        apply SetLike.coe_injective
        rw [PrimeSpectrum.coe_isIdempotentElemEquivClopens_apply,
          PrimeSpectrum.coe_isIdempotentElemEquivClopens_apply]
        ext p
        change rankFiberIdempotent R P i ∉ p.asIdeal ↔
          rankFiberIdempotent R Q j ∉ p.asIdeal
        rw [rankFiberIdempotent_notMem_iff, rankFiberIdempotent_notMem_iff, hij]
      exact congrArg Subtype.val he
    · intro i j hij
      obtain ⟨p, hp⟩ := Function.Fiber.fiber_nonempty (rankLocallyConstant R P) i
      have hq : p ∈ j.1 := by
        rw [← hij]
        exact hp
      exact (rankAtStalk_eq_rankFiberRank_of_mem R P i p hp).symm.trans
        ((congrFun (rankAtStalk_eq_of_equiv f) p).trans
          (rankAtStalk_eq_rankFiberRank_of_mem R Q j p hq))
  exact ⟨(determinantLineCongrModelEquiv R P).trans
    ((determinantLineCongrModelMap R _ f).trans
      ((determinantLineCongrModelTransport R hdata Q).trans
        (determinantLineCongrModelEquiv R Q).symm))⟩

/-- Base change to a rank-fiber ring recovers that fiber's top exterior power. -/
theorem determinantLine_component (i : rankFiberIndex R P) :
    Nonempty ((rankFiberRing R P i) ⊗[R] DeterminantLine R P ≃ₗ[rankFiberRing R P i]
      DeterminantLineComponent R P i) := by
  classical
  have hscalar (r : R) :
      rankFiberRingEquiv R P r i = algebraMap R (rankFiberRing R P i) r :=
    congrFun ((rankFiberRingEquiv R P).commutes r) i
  have hsmul (r : R) (y : DeterminantLineComponent R P i) :
      rankFiberRingEquiv R P r i • y = r • y := by
    rw [hscalar]
    exact IsScalarTower.algebraMap_smul (rankFiberRing R P i) r y
  let q : DeterminantLine R P →ₗ[R] DeterminantLineComponent R P i :=
    { toFun := DeterminantLine.component R P i
      map_add' := DeterminantLine.component_add R P i
      map_smul' := fun r x ↦ by
        rw [DeterminantLine.component_smul]
        exact hsmul r (DeterminantLine.component R P i x) }
  let s : DeterminantLineComponent R P i →ₗ[R] DeterminantLine R P :=
    { toFun := fun y ↦ DeterminantLine.ofComponents R P (Pi.single i y)
      map_add' := by
        intro y z
        apply DeterminantLine.ext
        intro j
        by_cases h : j = i
        · subst j
          simp
        · simp [Pi.single_apply, h, Ne.symm h]
      map_smul' := by
        intro r y
        apply DeterminantLine.ext
        intro j
        by_cases h : j = i
        · subst j
          simpa only [DeterminantLine.component_ofComponents, RingHom.id_apply,
            DeterminantLine.component_smul, Pi.single_eq_same] using (hsmul r y).symm
        · simp [Pi.single_apply, h, Ne.symm h] }
  let f : (rankFiberRing R P i) ⊗[R] DeterminantLine R P →ₗ[rankFiberRing R P i]
      DeterminantLineComponent R P i :=
    TensorProduct.AlgebraTensorModule.lift
      ((LinearMap.id : rankFiberRing R P i →ₗ[rankFiberRing R P i]
        rankFiberRing R P i).smulRight q)
  have hf (a : rankFiberRing R P i) (x : DeterminantLine R P) :
      f (a ⊗ₜ[R] x) = a • q x :=
    TensorProduct.AlgebraTensorModule.lift_tmul _ a x
  let g : DeterminantLineComponent R P i →ₗ[R]
      (rankFiberRing R P i) ⊗[R] DeterminantLine R P :=
    (TensorProduct.mk R (rankFiberRing R P i) (DeterminantLine R P) 1).comp s
  have hg (y : DeterminantLineComponent R P i) :
      g y = (1 : rankFiberRing R P i) ⊗ₜ[R] s y := by
    simp only [g, LinearMap.comp_apply, TensorProduct.mk_apply]
  -- A scalar supported at this coordinate removes all the other components.
  have hsupport (a : rankFiberRing R P i) (x : DeterminantLine R P) :
      (rankFiberRingEquiv R P).symm (Pi.single i a) • x = s (a • q x) := by
    apply DeterminantLine.ext
    intro j
    rw [DeterminantLine.component_smul, (rankFiberRingEquiv R P).apply_symm_apply]
    by_cases h : j = i
    · subst j
      simp [s, q]
    · simp [s, Pi.single_apply, h, Ne.symm h]
  have hleft : Function.LeftInverse g f := by
    intro z
    refine TensorProduct.inductionOn (motive := fun z ↦ g (f z) = z) z ?_ ?_
    · intro a x
      rw [hf, hg, ← hsupport a x, ← TensorProduct.smul_tmul]
      have hone : (rankFiberRingEquiv R P).symm (Pi.single i a) •
          (1 : rankFiberRing R P i) = a := by
        rw [Algebra.smul_def, ← hscalar, (rankFiberRingEquiv R P).apply_symm_apply]
        simp
      rw [hone]
    · intro z w hz hw
      rw [f.map_add, g.map_add, hz, hw]
  have hright : Function.RightInverse g f := by
    intro y
    rw [hg, hf]
    simp [s, q]
  exact ⟨LinearEquiv.ofBijective f ⟨hleft.injective, hright.surjective⟩⟩

private theorem rankFiberRank_eq_of_forall_rankAtStalk_eq (n : ℕ)
    (h : ∀ p : PrimeSpectrum R, rankAtStalk (R := R) P p = n)
    (i : rankFiberIndex R P) : rankFiberRank R P i = n := by
  obtain ⟨p, hp⟩ := Function.Fiber.fiber_nonempty (rankLocallyConstant R P) i
  exact (rankAtStalk_eq_rankFiberRank_of_mem R P i p hp).symm.trans (h p)

-- The quotient-ring action in each component agrees with restriction of scalars.
private def determinantLinePiEquiv (N : rankFiberIndex R P → Type w)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, Module (rankFiberRing R P i) (N i)]
    [∀ i, IsScalarTower R (rankFiberRing R P i) (N i)]
    (e : ∀ i, DeterminantLineComponent R P i ≃ₗ[rankFiberRing R P i] N i) :
    DeterminantLine R P ≃ₗ[R] ∀ i, N i where
  __ := Equiv.piCongrRight fun i ↦ (e i).toEquiv
  map_add' x y := by
    funext i
    exact (e i).map_add _ _
  map_smul' r x := by
    funext i
    change e i (DeterminantLine.component R P i (r • x)) =
      r • e i (DeterminantLine.component R P i x)
    rw [DeterminantLine.component_smul, (e i).map_smul]
    have hscalar : rankFiberRingEquiv R P r i =
        algebraMap R (rankFiberRing R P i) r :=
      congrFun ((rankFiberRingEquiv R P).commutes r) i
    rw [hscalar]
    exact IsScalarTower.algebraMap_smul (rankFiberRing R P i) r
      (e i (DeterminantLine.component R P i x))

/-- The zero module has determinant line isomorphic to the regular module. -/
theorem determinantLine_zero :
    Nonempty (DeterminantLine R (Fin 0 → R) ≃ₗ[R] R) := by
  have hrank : ∀ i : rankFiberIndex R (Fin 0 → R),
      rankFiberRank R (Fin 0 → R) i = 0 :=
    rankFiberRank_eq_of_forall_rankAtStalk_eq R (Fin 0 → R) 0
      (fun p ↦ congrFun (rankAtStalk_eq_zero_of_subsingleton
        (R := R) (M := Fin 0 → R)) p)
  let e (i : rankFiberIndex R (Fin 0 → R)) :
      DeterminantLineComponent R (Fin 0 → R) i ≃ₗ[rankFiberRing R (Fin 0 → R) i]
        rankFiberRing R (Fin 0 → R) i := by
    exact Eq.mpr
      (congrArg (fun n : ℕ ↦
        (⋀[rankFiberRing R (Fin 0 → R) i]^n (rankFiberModule R (Fin 0 → R) i)) ≃ₗ[
          rankFiberRing R (Fin 0 → R) i] rankFiberRing R (Fin 0 → R) i) (hrank i))
      (exteriorPower.zeroEquiv (rankFiberRing R (Fin 0 → R) i)
        (rankFiberModule R (Fin 0 → R) i))
  exact ⟨(determinantLinePiEquiv R (Fin 0 → R)
    (fun i ↦ rankFiberRing R (Fin 0 → R) i) e).trans
      (rankFiberRingEquiv R (Fin 0 → R)).toLinearEquiv.symm⟩

/-- The determinant line of an invertible module is isomorphic to that module. -/
theorem determinantLine_invertibleModule (L : Type v) [AddCommGroup L] [Module R L]
    [Module.Invertible R L] : Nonempty (DeterminantLine R L ≃ₗ[R] L) := by
  have hL : rankAtStalk (R := R) L = 1 :=
    ((invertible_iff_finite_projective_rankAtStalk_eq_one
      (R := R) (M := L)).mp inferInstance).2.2
  have hrank : ∀ i : rankFiberIndex R L, rankFiberRank R L i = 1 :=
    rankFiberRank_eq_of_forall_rankAtStalk_eq R L 1 (fun p ↦ congrFun hL p)
  let e (i : rankFiberIndex R L) :
      DeterminantLineComponent R L i ≃ₗ[rankFiberRing R L i] rankFiberModule R L i := by
    exact Eq.mpr
      (congrArg (fun n : ℕ ↦
        (⋀[rankFiberRing R L i]^n (rankFiberModule R L i)) ≃ₗ[rankFiberRing R L i]
          rankFiberModule R L i) (hrank i))
      (exteriorPower.oneEquiv (rankFiberRing R L i) (rankFiberModule R L i))
  exact ⟨(determinantLinePiEquiv R L (fun i ↦ rankFiberModule R L i) e).trans
    (rankFiberLinearEquiv R L).symm⟩


end Module
