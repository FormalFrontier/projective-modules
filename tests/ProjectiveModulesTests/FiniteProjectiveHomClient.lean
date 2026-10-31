/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.FiniteProjectiveHom
public import ProjectiveModules.TensorProduct.Hom
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Ring.PUnit
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import ProjectiveModules.Module.PID
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.Tactic.NormNum

/-!
# Separate target conditions for linear maps from finite projective modules

Evaluation at `1` identifies linear maps from a regular module with their
values. Over `ℤ`, this gives two complementary examples:

* the target `ℕ →₀ ℤ` and its linear-map module are projective but not finite;
* the target `ZMod 5` and its linear-map module are finite but not projective.

The first example uses the single-coordinate basis. In the second, a hypothetical
projective module is free over the PID `ℤ`, hence torsion-free, contradicting
`5 • 1 = 0` with both factors nonzero. Specified maps in both examples are nonzero
and move under the canonical pointwise coefficient action.

The same modules also exhibit finite-source tensor-Hom surjectivity with a
nonprojective source and an infinite projective tensor factor. The map sending
a residue modulo `5` to its tensor with the first integer coordinate vector
has a tensor preimage and a nonzero value at `1`.

The natural-number self-module supplies a nonzero example without additive
inverses. Empty source, zero target, and the one-element scalar ring are separate
boundary examples. Private specializations also exercise finite generation for
free-source Hom and finite-free splittings for the ordinary commutative dual,
without changing either carrier or action.

## References

The basis, evaluation equivalence, finite-generation, torsion-free and splitting
arguments use Mathlib, particularly `Finsupp.basisSingleOne`,
`LinearMap.ringLmapEquivSelf`, `Module.Finite.linearMap`,
`Module.dual_projective`, and `Module.dual_finite`. The implication from projectivity
to freeness over `ℤ` uses the public Projective Modules theorem
`Module.Projective.free_of_pid`. The tensor preimage uses Projective Modules'
finite-source tensor-Hom surjectivity theorem, and its nonzero value is detected
by Mathlib's `TensorProduct.finsuppScalarRight`. These examples follow the
elementary model ideas of the Projective Modules finite-projective developments.
This module was written with AI assistance.
-/

@[expose] public section

universe uA uS uM uN uR

namespace ProjectiveModulesTests.FiniteProjectiveHomClient

noncomputable section

private def integerCoordinateBasis : Module.Basis ℕ ℤ (ℕ →₀ ℤ) :=
  Finsupp.basisSingleOne

/-- Countably many integer coordinates form a projective module which is not
finitely generated, by Mathlib's single-coordinate basis and infinite-basis
criterion. -/
theorem integer_finsupp_projective_not_finite :
    Module.Projective ℤ (ℕ →₀ ℤ) ∧ ¬ Module.Finite ℤ (ℕ →₀ ℤ) :=
  ⟨Module.Projective.of_basis integerCoordinateBasis,
    Module.not_finite_of_infinite_basis integerCoordinateBasis⟩

/-- The regular-source map corresponding under evaluation at `1` to the first
integer coordinate vector. -/
def integerCoordinateMap : ℤ →ₗ[ℤ] (ℕ →₀ ℤ) :=
  (LinearMap.ringLmapEquivSelf ℤ ℤ (ℕ →₀ ℤ)).symm (Finsupp.single 0 1)

/-- The coordinate map sends an integer to its scalar multiple of the first
coordinate vector. -/
@[simp] theorem integerCoordinateMap_apply (z : ℤ) :
    integerCoordinateMap z = z • Finsupp.single 0 (1 : ℤ) :=
  rfl

/-- The coordinate map is nonzero, as seen at input `1` and coordinate `0`. -/
theorem integerCoordinateMap_ne_zero : integerCoordinateMap ≠ 0 := by
  intro h
  have hcoord := congrArg (fun f : ℤ →ₗ[ℤ] (ℕ →₀ ℤ) ↦ f 1 0) h
  simp at hcoord

/-- Multiplication by `2` moves the coordinate map under the pointwise action. -/
theorem integerCoordinateMap_moved : (2 : ℤ) • integerCoordinateMap ≠ integerCoordinateMap := by
  intro h
  have hcoord := congrArg (fun f : ℤ →ₗ[ℤ] (ℕ →₀ ℤ) ↦ f 1 0) h
  norm_num [LinearMap.smul_apply, Finsupp.smul_apply, zsmul_eq_mul] at hcoord

/-- The projectivity headline applies with a target which is not finite.
Evaluation at `1` also transfers nonfiniteness to this nonzero Hom module. -/
theorem integer_finsupp_hom_projective_not_finite :
    Module.Projective ℤ (ℤ →ₗ[ℤ] (ℕ →₀ ℤ)) ∧
      ¬ Module.Finite ℤ (ℤ →ₗ[ℤ] (ℕ →₀ ℤ)) ∧
      Nontrivial (ℤ →ₗ[ℤ] (ℕ →₀ ℤ)) := by
  let : Module.Projective ℤ (ℕ →₀ ℤ) := integer_finsupp_projective_not_finite.1
  refine ⟨Module.Projective.linearMap ℤ ℤ ℤ (ℕ →₀ ℤ), ?_,
    nontrivial_of_ne integerCoordinateMap 0 integerCoordinateMap_ne_zero⟩
  intro hfinite
  let : Module.Finite ℤ (ℤ →ₗ[ℤ] (ℕ →₀ ℤ)) := hfinite
  exact integer_finsupp_projective_not_finite.2
    (Module.Finite.equiv (LinearMap.ringLmapEquivSelf ℤ ℤ (ℕ →₀ ℤ)))

/-- The integer `5` annihilates `1` modulo `5`, although neither is zero in its
respective scalar or target type. -/
theorem zmod_five_annihilator :
    (5 : ℤ) ≠ 0 ∧ (1 : ZMod 5) ≠ 0 ∧ (5 : ℤ) • (1 : ZMod 5) = 0 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [ne_eq, ZMod.one_eq_zero_iff]
    norm_num
  · simpa [Int.smul_one_eq_cast] using ZMod.natCast_self 5

/-- The finite integer module `ZMod 5` is not projective: PID-freeness would make
it torsion-free, contradicting its specified nonzero annihilated element.
Finiteness uses Mathlib's finite-carrier criterion. -/
theorem zmod_five_finite_not_projective :
    Module.Finite ℤ (ZMod 5) ∧ ¬ Module.Projective ℤ (ZMod 5) := by
  refine ⟨Module.Finite.of_finite, ?_⟩
  intro hprojective
  let : Module.Projective ℤ (ZMod 5) := hprojective
  let : Module.Free ℤ (ZMod 5) := Module.Projective.free_of_pid ℤ (ZMod 5)
  let : Module.IsTorsionFree ℤ (ZMod 5) := Module.Free.instIsTorsionFree ℤ (ZMod 5)
  have hzero := (Module.isTorsionFree_iff_smul_eq_zero (R := ℤ) (M := ZMod 5)).mp
    (inferInstance : Module.IsTorsionFree ℤ (ZMod 5)) 5 1 zmod_five_annihilator.2.2
  exact hzero.elim zmod_five_annihilator.1 zmod_five_annihilator.2.1

open scoped TensorProduct

/-- The map sending a residue modulo `5` to its tensor with the first integer
coordinate vector has a tensor preimage and a nonzero value at `1`. The finite
source is not projective, and the projective right tensor factor is not finite. -/
theorem zmod_five_tensorHom_preimage :
    ¬ Module.Projective ℤ (ZMod 5) ∧
      ¬ Module.Finite ℤ (ℕ →₀ ℤ) ∧
      ∃ t : (ZMod 5 →ₗ[ℤ] ZMod 5) ⊗[ℤ] (ℕ →₀ ℤ),
        TensorProduct.rTensorHomToHomRTensor (RingHom.id ℤ)
            (ZMod 5) (ZMod 5) (ℕ →₀ ℤ) t =
          (TensorProduct.mk ℤ (ZMod 5) (ℕ →₀ ℤ)).flip (Finsupp.single 0 1) ∧
        TensorProduct.rTensorHomToHomRTensor (RingHom.id ℤ)
            (ZMod 5) (ZMod 5) (ℕ →₀ ℤ) t 1 ≠ 0 := by
  let : Module.Finite ℤ (ZMod 5) := zmod_five_finite_not_projective.1
  let : Module.Projective ℤ (ℕ →₀ ℤ) := integer_finsupp_projective_not_finite.1
  refine ⟨zmod_five_finite_not_projective.2, integer_finsupp_projective_not_finite.2, ?_⟩
  let f := (TensorProduct.mk ℤ (ZMod 5) (ℕ →₀ ℤ)).flip (Finsupp.single 0 1)
  obtain ⟨t, ht⟩ :=
    (TensorProduct.rTensorHomToHomRTensor_surjective_of_finite_left_projective_right
      (L := ZMod 5) (M := ZMod 5) (N := ℕ →₀ ℤ) (RingHom.id ℤ)) f
  refine ⟨t, ht, ?_⟩
  rw [ht]
  intro hzero
  apply zmod_five_annihilator.2.1
  have hcoord := congrArg
    (fun x : ZMod 5 ⊗[ℤ] (ℕ →₀ ℤ) =>
      TensorProduct.finsuppScalarRight ℤ ℤ (ZMod 5) ℕ x 0) hzero
  simpa only [f, LinearMap.flip_apply, TensorProduct.mk_apply,
    TensorProduct.finsuppScalarRight_apply_tmul_apply, Finsupp.single_eq_same,
    one_smul, map_zero, Finsupp.zero_apply] using hcoord

/-- The regular-source map corresponding to `1` modulo `5` under evaluation
at `1`. -/
def zmodFiveMap : ℤ →ₗ[ℤ] ZMod 5 :=
  (LinearMap.ringLmapEquivSelf ℤ ℤ (ZMod 5)).symm 1

/-- The residue map sends an integer to its scalar multiple of `1`. -/
@[simp] theorem zmodFiveMap_apply (z : ℤ) : zmodFiveMap z = z • (1 : ZMod 5) :=
  rfl

/-- The residue map is nonzero because its value at `1` is nonzero. -/
theorem zmodFiveMap_ne_zero : zmodFiveMap ≠ 0 := by
  intro h
  apply zmod_five_annihilator.2.1
  simpa using congrArg (fun f : ℤ →ₗ[ℤ] ZMod 5 ↦ f 1) h

/-- The canonical outer integer action annihilates the nonzero residue map. -/
theorem zmodFiveMap_smul_five : (5 : ℤ) • zmodFiveMap = 0 := by
  let E := LinearMap.ringLmapEquivSelf ℤ ℤ (ZMod 5)
  apply E.injective
  rw [map_smul, map_zero]
  change (5 : ℤ) • E (E.symm 1) = 0
  rw [LinearEquiv.apply_symm_apply]
  exact zmod_five_annihilator.2.2

/-- Multiplication by `5` moves the residue map, rather than fixing it. -/
theorem zmodFiveMap_moved : (5 : ℤ) • zmodFiveMap ≠ zmodFiveMap := by
  rw [zmodFiveMap_smul_five]
  exact zmodFiveMap_ne_zero.symm

/-- The finiteness headline applies with a nonprojective target. Evaluation at
`1` transfers nonprojectivity to the nonzero Hom module with its same action. -/
theorem zmod_five_hom_finite_not_projective :
    Module.Finite ℤ (ℤ →ₗ[ℤ] ZMod 5) ∧
      ¬ Module.Projective ℤ (ℤ →ₗ[ℤ] ZMod 5) ∧
      Nontrivial (ℤ →ₗ[ℤ] ZMod 5) := by
  let : Module.Finite ℤ (ZMod 5) := zmod_five_finite_not_projective.1
  refine ⟨Module.Finite.linearMap_of_projective ℤ ℤ ℤ (ZMod 5), ?_,
    nontrivial_of_ne zmodFiveMap 0 zmodFiveMap_ne_zero⟩
  intro hprojective
  let : Module.Projective ℤ (ℤ →ₗ[ℤ] ZMod 5) := hprojective
  exact zmod_five_finite_not_projective.2
    (Module.Projective.of_equiv' (LinearMap.ringLmapEquivSelf ℤ ℤ (ZMod 5)))

/-- The natural-number regular map corresponding to `1` under evaluation
at `1`. Its source and target are semimodules without additive inverses. -/
def natRegularMap : ℕ →ₗ[ℕ] ℕ :=
  (LinearMap.ringLmapEquivSelf ℕ ℕ ℕ).symm 1

/-- The natural-number regular map fixes every natural number. -/
@[simp] theorem natRegularMap_apply (n : ℕ) : natRegularMap n = n := by
  change n • (1 : ℕ) = n
  exact Nat.smul_one_eq_cast n

/-- The natural-number regular map is nonzero. -/
theorem natRegularMap_ne_zero : natRegularMap ≠ 0 := by
  intro h
  have hone := congrArg (fun f : ℕ →ₗ[ℕ] ℕ ↦ f 1) h
  simp at hone

/-- The pointwise natural-number action moves the regular map. -/
theorem natRegularMap_moved : (2 : ℕ) • natRegularMap ≠ natRegularMap := by
  intro h
  have hone := congrArg (fun f : ℕ →ₗ[ℕ] ℕ ↦ f 1) h
  norm_num [LinearMap.smul_apply, nsmul_eq_mul] at hone

/-- Both headlines apply to the natural-number self-module, and its Hom module
is nontrivial. No additive-group structure is needed. -/
theorem nat_hom_finite_projective_nontrivial :
    Module.Projective ℕ (ℕ →ₗ[ℕ] ℕ) ∧ Module.Finite ℕ (ℕ →ₗ[ℕ] ℕ) ∧
      Nontrivial (ℕ →ₗ[ℕ] ℕ) :=
  ⟨Module.Projective.linearMap ℕ ℕ ℕ ℕ,
    Module.Finite.linearMap_of_projective ℕ ℕ ℕ ℕ,
    nontrivial_of_ne natRegularMap 0 natRegularMap_ne_zero⟩

/-- The additive operation in the natural-number example has no inverse for
`1`, so this is a genuinely nongroup example. -/
theorem nat_one_has_no_additive_inverse : ¬ ∃ n : ℕ, n + 1 = 0 := by
  simp

private theorem emptyIntegerModule_projective : Module.Projective ℤ (Fin 0 → ℤ) :=
  Module.Projective.of_basis (Pi.basisFun ℤ (Fin 0))

/-- An empty finite-free source yields a subsingleton Hom module, while still
satisfying both headline conclusions. -/
theorem empty_source_hom_controls :
    Module.Projective ℤ ((Fin 0 → ℤ) →ₗ[ℤ] ℤ) ∧
      Module.Finite ℤ ((Fin 0 → ℤ) →ₗ[ℤ] ℤ) ∧
      Subsingleton ((Fin 0 → ℤ) →ₗ[ℤ] ℤ) := by
  let : Module.Projective ℤ (Fin 0 → ℤ) := emptyIntegerModule_projective
  exact ⟨Module.Projective.linearMap ℤ ℤ (Fin 0 → ℤ) ℤ,
    Module.Finite.linearMap_of_projective ℤ ℤ (Fin 0 → ℤ) ℤ, inferInstance⟩

/-- A zero target, here the module of functions on `Fin 0`, also yields a
subsingleton Hom module and both headline conclusions. -/
theorem zero_target_hom_controls :
    Module.Projective ℤ (ℤ →ₗ[ℤ] (Fin 0 → ℤ)) ∧
      Module.Finite ℤ (ℤ →ₗ[ℤ] (Fin 0 → ℤ)) ∧
      Subsingleton (ℤ →ₗ[ℤ] (Fin 0 → ℤ)) := by
  let : Module.Projective ℤ (Fin 0 → ℤ) := emptyIntegerModule_projective
  exact ⟨Module.Projective.linearMap ℤ ℤ ℤ (Fin 0 → ℤ),
    Module.Finite.linearMap_of_projective ℤ ℤ ℤ (Fin 0 → ℤ), inferInstance⟩

/-- Both headlines include the one-element scalar ring, where `1 = 0`.
This degenerate example is separate from the nonzero regular maps. -/
theorem trivial_ring_hom_controls :
    Module.Projective PUnit.{1} (PUnit.{1} →ₗ[PUnit.{1}] PUnit.{1}) ∧
      Module.Finite PUnit.{1} (PUnit.{1} →ₗ[PUnit.{1}] PUnit.{1}) ∧
      Subsingleton (PUnit.{1} →ₗ[PUnit.{1}] PUnit.{1}) ∧ (1 : PUnit.{1}) = 0 :=
  ⟨Module.Projective.linearMap PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1},
    Module.Finite.linearMap_of_projective PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1},
    inferInstance, Subsingleton.elim _ _⟩

-- The free-source specialization retains exactly the hypotheses of
-- Mathlib's finite-linear-map instance, including no target projectivity.
private theorem linearMap_finite_of_free
    (A : Type uA) (S : Type uS) (M : Type uM) (N : Type uN)
    [Ring A] [Ring S] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module.Free A M] [Module.Finite A M]
    [Module A N] [Module S N] [SMulCommClass A S N] [Module.Finite S N] :
    Module.Finite S (M →ₗ[A] N) ∧ (⊤ : Submodule S (M →ₗ[A] N)).FG := by
  have h : Module.Finite S (M →ₗ[A] N) :=
    Module.Finite.linearMap_of_projective A S M N
  exact ⟨h, h.fg_top⟩

private theorem free_source_hom_generators
    (A : Type uA) (S : Type uS) (M : Type uM) (N : Type uN)
    [Ring A] [Ring S] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module.Free A M] [Module.Finite A M]
    [Module A N] [Module S N] [SMulCommClass A S N] [Module.Finite S N] :
    ∃ (n : ℕ) (v : Fin n → M →ₗ[A] N),
      Submodule.span S (Set.range v) = ⊤ :=
  Submodule.fg_iff_exists_fin_generating_family.mp
    (linearMap_finite_of_free A S M N).2

private theorem free_source_hom_fg_old
    (A : Type uA) (S : Type uS) (M : Type uM) (N : Type uN)
    [Ring A] [Ring S] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module.Free A M] [Module.Finite A M]
    [Module A N] [Module S N] [SMulCommClass A S N] [Module.Finite S N] :
    (⊤ : Submodule S (M →ₗ[A] N)).FG :=
  (Module.Finite.linearMap A S M N).fg_top

-- Module.Dual is the existing linear-map carrier with the existing pointwise
-- action. Only the two Prop-valued class witnesses are installed locally.
private theorem dual_split_and_fg
    (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    (∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] Module.Dual R M)
      (g : Module.Dual R M →ₗ[R] (Fin n → R)),
      Function.Surjective f ∧ Function.Injective g ∧ f ∘ₗ g = LinearMap.id) ∧
      (⊤ : Submodule R (Module.Dual R M)).FG := by
  have hP : Module.Projective R (Module.Dual R M) :=
    Module.Projective.linearMap R R M R
  have hF : Module.Finite R (Module.Dual R M) :=
    Module.Finite.linearMap_of_projective R R M R
  let : Module.Projective R (Module.Dual R M) := hP
  let : Module.Finite R (Module.Dual R M) := hF
  exact ⟨Module.Finite.exists_comp_eq_id_of_projective R (Module.Dual R M), hF.fg_top⟩

private theorem dual_split_old
    (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] Module.Dual R M)
      (g : Module.Dual R M →ₗ[R] (Fin n → R)),
      Function.Surjective f ∧ Function.Injective g ∧ f ∘ₗ g = LinearMap.id := by
  let : Module.Projective R (Module.Dual R M) := Module.dual_projective
  let : Module.Finite R (Module.Dual R M) := Module.dual_finite
  exact Module.Finite.exists_comp_eq_id_of_projective R (Module.Dual R M)

end

end ProjectiveModulesTests.FiniteProjectiveHomClient
