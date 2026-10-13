/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.RightExtensionComparison
public import ProjectiveModules.Module.RightExtensionIdeal
public import ProjectiveModules.Module.RightExtensionFree
public import Mathlib.Algebra.Ring.Fin
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.Algebra.Ring.Action.Group
public import Mathlib.Algebra.Group.Semiconj.Units
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Ring.PUnit
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Diagonal coefficient maps and right-extension tensor controls

The two diagonal embeddings of `ℤ × ℤ` into two-by-two integer matrices
are interchanged by the permutation unit associated to the transposition.
Evaluation of the principal ideal of one detects a surviving source tensor,
a nonzero displaced target tensor, and both failures of the prescription
that multiplies its coefficient on the right by the permutation matrix.
The prescription is not defined as a map on the balanced tensor quotient.

Identity, empty-coordinate and zero-ring examples use unital coefficient
maps. Equality of coefficient maps alone does not force an identity
comparison: a nonidentity central unit can move a surviving one-generator.
Three independent scalar and carrier lifts preserve the observations;
the lifted module is a lift of the low opposite carrier, with its action
pulled back along the source-down homomorphism.

## References

The examples use Mathlib's diagonal ring homomorphism, permutation matrices,
group-to-units homomorphism, conjugation action, opposite modules and transport
APIs. Tensor evaluation uses the principal-ideal and balanced right-extension
formalization of Projective Modules, including the approach contributed by
Prism and Lens. No additional tensor or regular-extension constructor is used.
-/

@[expose] public section

noncomputable section

namespace ProjectiveModulesTests.RightExtensionConjugacy

open ModuleCat.RightExtension MulOpposite

universe uR uS uM a b c

section Identity

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable (f : R →+* S) (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- The unit one supplies the identity coefficient relation. -/
theorem unit_one_semiconj (r : R) : SemiconjBy (1 : S) (f r) (f r) := by
  change 1 * f r = f r * 1
  rw [one_mul, mul_one]

/-- The unit-one coefficient prescription determines the identity linear map. -/
theorem unit_one_prescription (F : Obj f M →ₗ[Sᵐᵒᵖ] Obj f M)
    (h : ∀ m s, F (tmul f m s) = tmul f m ((1 : S) * s)) :
    F = LinearMap.id := by
  apply linearMap_ext f
  intro m s
  simpa only [one_mul, LinearMap.id_apply] using h m s

/-- The same prescription determines the identity linear equivalence. -/
theorem unit_one_equivalence (E : Obj f M ≃ₗ[Sᵐᵒᵖ] Obj f M)
    (h : ∀ m s, E (tmul f m s) = tmul f m ((1 : S) * s)) :
    E = LinearEquiv.refl Sᵐᵒᵖ (Obj f M) := by
  apply LinearEquiv.toLinearMap_injective
  exact unit_one_prescription f M E.toLinearMap h

end Identity

/-- The coefficient source for the two diagonal embeddings. -/
abbrev R0 := ℤ × ℤ

/-- The noncommutative integer-matrix target. -/
abbrev S0 := Matrix (Fin 2) (Fin 2) ℤ

/-- The product-to-coordinates equivalence followed by the diagonal homomorphism. -/
def φ0 : R0 →+* S0 :=
  (Matrix.diagonalRingHom (Fin 2) ℤ).comp
    (RingEquiv.piFinTwo (fun _ : Fin 2 => ℤ)).symm.toRingHom

/-- The canonical unit of matrices associated to the transposition. -/
def u0 : S0ˣ :=
  (Matrix.permMatrixHom (n := Fin 2) (R := ℤ)).toHomUnits (Equiv.swap 0 1)

/-- The conjugate coefficient map, using the canonical conjugation action. -/
def ψ0 : R0 →+* S0 :=
  (MulSemiringAction.toRingEquiv (ConjAct S0ˣ) S0
    (ConjAct.toConjAct u0)).toRingHom.comp φ0

/-- The underlying permutation matrix. -/
abbrev U : S0 := (u0 : S0)

/-- The first coordinate idempotent of the source. -/
def r0 : R0 := (1, 0)

/-- The diagonal coefficient map has the two prescribed diagonal entries. -/
theorem φ0_apply (x y : ℤ) : φ0 (x, y) = Matrix.diagonal ![x, y] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The matrix of the canonical unit has zero diagonal and off-diagonal ones. -/
theorem U_apply (i j : Fin 2) : U i j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [U, u0, Matrix.permMatrixHom, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.Perm.inv_def]

/-- The transposition unit is its own inverse. -/
theorem u0_inv : u0⁻¹ = u0 := by
  rw [u0, ← map_inv, Equiv.Perm.inv_def, Equiv.symm_swap]

/-- The permutation matrix squares to the identity. -/
theorem U_mul_U : U * U = 1 := by
  simpa only [u0_inv] using u0.mul_inv

/-- The conjugation action gives the coefficient formula without a new actor. -/
theorem ψ0_conjugation (r : R0) : ψ0 r = U * φ0 r * U := by
  change ConjAct.toConjAct u0 • φ0 r = U * φ0 r * U
  rw [ConjAct.units_smul_def]
  simp only [ConjAct.ofConjAct_toConjAct, u0_inv]

/-- The conjugate embedding reverses the diagonal entries. -/
theorem ψ0_apply (x y : ℤ) : ψ0 (x, y) = Matrix.diagonal ![y, x] := by
  rw [ψ0_conjugation, φ0_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, U_apply, Matrix.diagonal_apply]

/-- The canonical unit gives the coefficient semiconjugacy relation. -/
theorem coefficient_semiconj (r : R0) : SemiconjBy U (φ0 r) (ψ0 r) := by
  simpa only [ψ0_conjugation, u0_inv] using u0.mk_semiconjBy (φ0 r)

private theorem φ0_r0 : φ0 r0 = Matrix.single 0 0 1 := by
  rw [r0, φ0_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem ψ0_r0 : ψ0 r0 = Matrix.single 1 1 1 := by
  rw [r0, ψ0_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The coefficient homomorphisms differ at the first source idempotent. -/
theorem coefficient_maps_ne : φ0 ≠ ψ0 := by
  intro h
  have he := congrArg (fun f : R0 →+* S0 => f r0 0 0) h
  rw [φ0_r0, ψ0_r0] at he
  norm_num at he

/-- The target identity is not zero, as detected by its first diagonal entry. -/
theorem target_one_ne_zero : (1 : S0) ≠ 0 := by
  intro h
  have he := congrArg (fun A : S0 => A 0 0) h
  norm_num at he

/-- The permutation matrix is nonzero. -/
theorem U_ne_zero : U ≠ 0 := by
  intro h
  have he := congrArg (fun A : S0 => A 0 1) h
  norm_num [U_apply] at he

/-- An off-diagonal entry separates the permutation matrix from the identity. -/
theorem U_ne_one : U ≠ 1 := by
  intro h
  have he := congrArg (fun A : S0 => A 0 1) h
  norm_num [U_apply] at he

/-- The canonical permutation unit is not the identity unit. -/
theorem u0_ne_one : u0 ≠ 1 := by
  intro h
  exact U_ne_one (congrArg (fun u : S0ˣ => (u : S0)) h)

private theorem U_e00 : U * Matrix.single 0 0 1 = Matrix.single 1 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, U_apply]

private theorem e00_U : Matrix.single 0 0 1 * U = Matrix.single 0 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, U_apply]

private theorem e11_U : Matrix.single 1 1 1 * U = Matrix.single 1 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, U_apply]

private theorem e10_ne_e01 : (Matrix.single 1 0 1 : S0) ≠ Matrix.single 0 1 1 := by
  intro h
  have he := congrArg (fun A : S0 => A 1 0) h
  norm_num at he

/-- Left and right multiplication by the permutation unit give distinct matrix units. -/
theorem permutation_order :
    U * Matrix.single 0 0 1 = Matrix.single 1 0 1 ∧
      Matrix.single 0 0 1 * U = Matrix.single 0 1 1 ∧
      U * Matrix.single 0 0 1 ≠ Matrix.single 0 0 1 * U := by
  exact ⟨U_e00, e00_U, by rw [U_e00, e00_U]; exact e10_ne_e01⟩

/-- The permutation matrix is not central. -/
theorem U_not_central : ¬ ∀ A : S0, Commute U A := by
  intro h
  exact permutation_order.2.2 (h (Matrix.single 0 0 1)).eq

/-- The product source has two nonzero factors with zero product. -/
theorem source_zero_divisors :
    (r0 : R0) ≠ 0 ∧ ((0, 1) : R0) ≠ 0 ∧ r0 * (0, 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have he := congrArg Prod.fst h
    norm_num [r0] at he
  · intro h
    have he := congrArg Prod.snd h
    norm_num at he
  · ext <;> simp [r0]

/-- The target also has nonzero zero divisors, so the matrix example is not
a division-ring example. -/
theorem target_zero_divisors :
    (Matrix.single 0 0 1 : S0) ≠ 0 ∧ (Matrix.single 1 1 1 : S0) ≠ 0 ∧
      (Matrix.single 0 0 1 : S0) * Matrix.single 1 1 1 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have he := congrArg (fun A : S0 => A 0 0) h
    norm_num at he
  · intro h
    have he := congrArg (fun A : S0 => A 1 1) h
    norm_num at he
  · simp

/-- The principal right ideal of one. -/
abbrev P := Ideal.span {op (1 : R0)}

/-- Its canonical principal generator. -/
abbrev q : P := spanGenerator (1 : R0)

/-- The ideal of one is produced as a finite-projective module by idempotent span. -/
def principalOne : ModuleCat.FiniteProjective R0ᵐᵒᵖ :=
  (show IsIdempotentElem (1 : R0) from one_mul 1).rightSpanFiniteProjective

/-- Bundling retains the principal-ideal carrier. -/
theorem principalOne_carrier : (principalOne : Type) = P := rfl

/-- The principal ideal inherits the producer's proved finiteness and projectivity. -/
theorem principalOne_properties : Module.Finite R0ᵐᵒᵖ P ∧ Module.Projective R0ᵐᵒᵖ P := by
  change Module.Finite R0ᵐᵒᵖ principalOne ∧ Module.Projective R0ᵐᵒᵖ principalOne
  exact ⟨inferInstance, inferInstance⟩

/-- The identity comparison on the principal ideal evaluates its one-generator. -/
theorem principal_identity :
    idLinearEquiv R0 P (tmul (RingHom.id R0) q 1) = q ∧
      (idLinearEquiv R0 P).symm q = tmul (RingHom.id R0) q 1 := by
  constructor
  · rw [idLinearEquiv_tmul, op_one, one_smul]
  · exact idLinearEquiv_symm_apply q

/-- Evaluation is the existing principal-ideal equivalence. -/
def observe (f : R0 →+* S0) : Obj f P ≃ₗ[S0ᵐᵒᵖ] S0ᵐᵒᵖ :=
  spanLinearEquivOfMapEqOne f 1 f.map_one

/-- Evaluation on all pure tensors retains the multiplication order. -/
theorem observe_tmul (f : R0 →+* S0) (m : P) (s : S0) :
    observe f (tmul f m s) = op (f (unop m.val) * s) :=
  spanLinearEquivOfMapEqOne_tmul f 1 f.map_one m s

/-- Evaluation of a one-generator tensor is its target coefficient. -/
theorem observe_q (f : R0 →+* S0) (s : S0) : observe f (tmul f q s) = op s := by
  rw [observe_tmul]
  simp only [q, spanGenerator_coe, unop_op, f.map_one, one_mul]

/-- The inverse observer inserts the canonical ideal generator. -/
theorem observe_inverse (f : R0 →+* S0) (s : S0ᵐᵒᵖ) :
    (observe f).symm s = tmul f q (unop s) :=
  spanLinearEquivOfMapEqOne_symm_apply f 1 f.map_one s

/-- The source one-generator survives, and the intended target tensor is
nonzero and displaced from the target's own one-generator. -/
theorem surviving_movement :
    tmul φ0 q (1 : S0) ≠ 0 ∧ tmul ψ0 q U ≠ 0 ∧
      tmul ψ0 q U ≠ tmul ψ0 q (1 : S0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have he := congrArg (observe φ0) h
    rw [observe_q, _root_.map_zero] at he
    exact target_one_ne_zero (congrArg unop he)
  · intro h
    have he := congrArg (observe ψ0) h
    rw [observe_q, _root_.map_zero] at he
    exact U_ne_zero (congrArg unop he)
  · intro h
    have he := congrArg (observe ψ0) h
    rw [observe_q, observe_q] at he
    exact U_ne_one (congrArg unop he)

private theorem observe_smul_q (r : R0) (s : S0) :
    observe ψ0 (tmul ψ0 (op r • q) s) = op (ψ0 r * s) := by
  rw [smul_tmul, observe_q]

/-- Balancing identifies the two source representatives used in the wrong-order test. -/
theorem source_balancing :
    tmul φ0 (op r0 • q) (1 : S0) = tmul φ0 q (φ0 r0) := by
  rw [smul_tmul, mul_one]

/-- The wrongly ordered outputs of those representatives are separated by
entry `(1,0)` under principal-ideal evaluation. -/
theorem wrong_order_balancing_observed :
    observe ψ0 (tmul ψ0 (op r0 • q) ((1 : S0) * U)) = op (Matrix.single 1 0 1) ∧
      observe ψ0 (tmul ψ0 q (φ0 r0 * U)) = op (Matrix.single 0 1 1) := by
  constructor
  · rw [one_mul, observe_smul_q, ψ0_r0, e11_U]
  · rw [observe_q, φ0_r0, e00_U]

/-- No function on the quotient can satisfy the right-multiplication
prescription on every pure tensor. This does not define that prescription. -/
theorem no_wrong_order_function :
    ¬ ∃ F : Obj φ0 P → Obj ψ0 P,
      ∀ m s, F (tmul φ0 m s) = tmul ψ0 m (s * U) := by
  rintro ⟨F, hF⟩
  have h := congrArg F source_balancing
  rw [hF, hF] at h
  have he := congrArg (observe ψ0) h
  rw [wrong_order_balancing_observed.1, wrong_order_balancing_observed.2] at he
  exact e10_ne_e01 (congrArg unop he)

/-- The independent right-scalar test separates the two candidate outputs,
without treating the bad prescription as a quotient map. -/
theorem wrong_order_right_action_observed :
    observe ψ0 (tmul ψ0 q (Matrix.single 0 0 1 * U)) = op (Matrix.single 0 1 1) ∧
      observe ψ0 (op (Matrix.single 0 0 1 : S0) • tmul ψ0 q U) =
        op (Matrix.single 1 0 1) := by
  constructor
  · rw [observe_q, e00_U]
  · rw [ModuleCat.RightExtension.tmul_smul, op_smul_eq_mul, observe_q, U_e00]

/-- Even the two prescriptions at the one-generator and its right scalar
multiple are incompatible with fixed-target linearity. -/
theorem no_wrong_order_linear_map :
    ¬ ∃ F : Obj φ0 P →ₗ[S0ᵐᵒᵖ] Obj ψ0 P,
      F (tmul φ0 q 1) = tmul ψ0 q U ∧
      F (tmul φ0 q (Matrix.single 0 0 1)) =
        tmul ψ0 q (Matrix.single 0 0 1 * U) := by
  rintro ⟨F, h1, he00⟩
  have h := F.map_smul (op (Matrix.single 0 0 1 : S0)) (tmul φ0 q 1)
  rw [ModuleCat.RightExtension.tmul_smul, op_smul_eq_mul, one_mul, he00, h1] at h
  have he := congrArg (observe ψ0) h
  rw [wrong_order_right_action_observed.1, wrong_order_right_action_observed.2] at he
  exact e10_ne_e01 (congrArg unop he.symm)

section ZeroBoundaries

/-- Empty coordinates on the low right source module. -/
abbrev EmptyCoordinates := Fin 0 → R0

private theorem empty_finite : Module.Finite R0ᵐᵒᵖ EmptyCoordinates :=
  Module.Finite.equiv (Module.rightFreeCoordEquiv R0 (Fin 0))

private theorem empty_free : Module.Free R0ᵐᵒᵖ EmptyCoordinates :=
  Module.Free.of_equiv (Module.rightFreeCoordEquiv R0 (Fin 0))

attribute [local instance] empty_finite empty_free

private theorem empty_projective : Module.Projective R0ᵐᵒᵖ EmptyCoordinates :=
  Module.Projective.of_free

attribute [local instance] empty_projective

/-- The finite-projective producer of the empty-coordinate module. -/
def emptyObject : ModuleCat.FiniteProjective R0ᵐᵒᵖ :=
  ModuleCat.FiniteProjective.of R0ᵐᵒᵖ EmptyCoordinates

/-- The empty-coordinate bundle retains its singleton carrier. -/
theorem emptyObject_carrier : (emptyObject : Type) = EmptyCoordinates := rfl

/-- Empty coordinates form a finite-projective zero module,
with a singleton, not empty, underlying carrier. -/
theorem empty_coordinates_finite_projective :
    Module.Finite R0ᵐᵒᵖ EmptyCoordinates ∧ Module.Free R0ᵐᵒᵖ EmptyCoordinates ∧
      Module.Projective R0ᵐᵒᵖ EmptyCoordinates ∧
      Nonempty EmptyCoordinates ∧ Subsingleton EmptyCoordinates :=
  ⟨empty_finite, empty_free, empty_projective, ⟨0⟩, inferInstance⟩

/-- The existing finite-free equivalence detects every empty-coordinate
extension as zero, for either coefficient embedding. -/
theorem empty_extension_zero (f : R0 →+* S0) (x : Obj f EmptyCoordinates) : x = 0 := by
  apply (rightFreeLinearEquiv f (Fin 0)).injective
  rw [_root_.map_zero]
  exact Subsingleton.elim _ _

example (x : Obj φ0 EmptyCoordinates) : x = 0 := empty_extension_zero φ0 x

example (x : Obj ψ0 EmptyCoordinates) : x = 0 := empty_extension_zero ψ0 x

/-- A unital coefficient homomorphism from the product source to the zero ring. -/
def zeroTarget : R0 →+* PUnit.{1} :=
  (Int.castRingHom PUnit.{1}).comp (RingHom.fst ℤ ℤ)

/-- One and zero coincide in the zero target. -/
theorem zero_target_one_eq_zero : (1 : PUnit.{1}) = 0 := Subsingleton.elim _ _

/-- The zero target has one unit and its value is both one and zero. -/
theorem zero_target_unit (u : PUnit.{1}ˣ) : u = 1 ∧ (u : PUnit.{1}) = 0 :=
  ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Every extension into the zero ring vanishes, without a target
nontriviality assumption. -/
theorem zero_target_extension (M : Type uM) [AddCommGroup M] [Module R0ᵐᵒᵖ M]
    (x : Obj zeroTarget M) : x = 0 := by
  let _ : Subsingleton (Obj zeroTarget M) := Module.subsingleton PUnit.{1}ᵐᵒᵖ _
  exact Subsingleton.elim _ _

/-- Identity extension with zero source and zero target is valid. -/
theorem all_zero_extension (M : Type uM) [AddCommGroup M] [Module PUnit.{1}ᵐᵒᵖ M]
    (x : Obj (RingHom.id PUnit.{1}) M) : x = 0 := by
  let _ : Subsingleton (Obj (RingHom.id PUnit.{1}) M) :=
    Module.subsingleton PUnit.{1}ᵐᵒᵖ _
  exact Subsingleton.elim _ _

/-- A zero source cannot map unitally into the nonzero matrix target. -/
theorem no_zero_source_map : ¬ Nonempty (PUnit.{1} →+* S0) := by
  rintro ⟨f⟩
  let _ : Subsingleton S0 := f.codomain_trivial
  exact target_one_ne_zero (Subsingleton.elim _ _)

end ZeroBoundaries

namespace Lift

/-- The independently lifted source ring. -/
abbrev Rhat := ULift.{a} R0

/-- The independently lifted target ring. -/
abbrev Shat := ULift.{b} S0

/-- The carrier lift is of the low opposite ring, not of the lifted source ring. -/
abbrev Mhat := ULift.{c} R0ᵐᵒᵖ

/-- Source-down ring equivalence. -/
def dR : Rhat.{a} ≃+* R0 := ULift.ringEquiv

/-- Target-down ring equivalence. -/
def dS : Shat.{b} ≃+* S0 := ULift.ringEquiv

/-- The opposite ring-equivalence homomorphism is the selected action pullback. -/
theorem op_down_hom :
    (RingEquiv.op dR.{a}).toRingHom = RingHom.op dR.{a}.toRingHom := by
  apply RingHom.ext
  intro x
  rfl

-- These named activations are local to the fixture and use existing module producers.
local instance lowModule : Module Rhat.{a}ᵐᵒᵖ R0ᵐᵒᵖ :=
  Module.compHom R0ᵐᵒᵖ (RingHom.op dR.{a}.toRingHom)

local instance carrierModule : Module Rhat.{a}ᵐᵒᵖ Mhat.{c} :=
  @ULift.module' Rhat.{a}ᵐᵒᵖ R0ᵐᵒᵖ _ _ lowModule.{a}

/-- The pullback action is right multiplication by the source-down coefficient. -/
theorem low_action (r : Rhat.{a}) (m : R0ᵐᵒᵖ) :
    op r • m = op (unop m * dR.{a} r) := rfl

/-- The lifted carrier action retains multiplication in the low source ring. -/
theorem carrier_action (r t : R0) :
    op (dR.{a}.symm r) • (ULift.up (op t) : Mhat.{c}) = ULift.up (op (t * r)) := by
  change (ULift.up (op (t * dR.{a} (dR.{a}.symm r))) : Mhat.{c}) = _
  rw [dR.{a}.apply_symm_apply]

/-- The existing pullback equivalence has the selected, proved-matching action. -/
private def downLinearEquiv : Rhat.{a}ᵐᵒᵖ ≃ₗ[Rhat.{a}ᵐᵒᵖ] R0ᵐᵒᵖ :=
  -- Retain the pullback's additive maps; linearity uses the selected opposite homomorphism.
  (Module.compHom.toLinearEquiv (RingEquiv.op dR.{a})).toAddEquiv.toLinearEquiv
    (fun r m => by
      change (RingEquiv.op dR.{a}) (r * m) =
        (RingHom.op dR.{a}.toRingHom r) * (RingEquiv.op dR.{a}) m
      rw [← op_down_hom.{a}]
      exact (RingEquiv.op dR.{a}).map_mul r m)

/-- Canonical carrier-down followed by the inverse pullback equivalence. -/
private def carrierToRegular : Mhat.{c} ≃ₗ[Rhat.{a}ᵐᵒᵖ] Rhat.{a}ᵐᵒᵖ :=
  (ULift.moduleEquiv : Mhat.{c} ≃ₗ[Rhat.{a}ᵐᵒᵖ] R0ᵐᵒᵖ).trans
    downLinearEquiv.{a}.symm

private theorem carrierToRegular_apply (m : Mhat.{c}) :
    carrierToRegular.{a,c} m = op (dR.{a}.symm (unop m.down)) := by
  change downLinearEquiv.{a}.symm m.down = _
  rfl

private theorem carrier_finite : Module.Finite Rhat.{a}ᵐᵒᵖ Mhat.{c} :=
  Module.Finite.equiv carrierToRegular.{a,c}.symm

private theorem carrier_free : Module.Free Rhat.{a}ᵐᵒᵖ Mhat.{c} :=
  Module.Free.of_equiv carrierToRegular.{a,c}.symm

private theorem carrier_projective : Module.Projective Rhat.{a}ᵐᵒᵖ Mhat.{c} :=
  Module.Projective.of_equiv' carrierToRegular.{a,c}.symm

attribute [local instance] carrier_finite carrier_free carrier_projective

/-- The three-universe carrier has proved finite generation, freeness and projectivity. -/
theorem carrier_properties :
    Module.Finite Rhat.{a}ᵐᵒᵖ Mhat.{c} ∧ Module.Free Rhat.{a}ᵐᵒᵖ Mhat.{c} ∧
      Module.Projective Rhat.{a}ᵐᵒᵖ Mhat.{c} :=
  ⟨carrier_finite.{a,c}, carrier_free.{a,c}, carrier_projective.{a,c}⟩

/-- The finite-projective bundle for the independently lifted carrier. -/
def carrierObject : ModuleCat.FiniteProjective.{a,c} Rhat.{a}ᵐᵒᵖ := by
  letI : Module.Finite Rhat.{a}ᵐᵒᵖ Mhat.{c} := (carrier_properties.{a,c}).1
  letI : Module.Projective Rhat.{a}ᵐᵒᵖ Mhat.{c} := (carrier_properties.{a,c}).2.2
  exact ModuleCat.FiniteProjective.of Rhat.{a}ᵐᵒᵖ Mhat.{c}

/-- The bundle has exactly the independent carrier lift. -/
theorem carrierObject_carrier : (carrierObject.{a,c} : Type c) = Mhat.{c} := rfl

/-- Source-down, then the low coefficient map, then target-up. -/
def coefficient (f : R0 →+* S0) : Rhat.{a} →+* Shat.{b} :=
  dS.{b}.symm.toRingHom.comp (f.comp dR.{a}.toRingHom)

/-- The first lifted diagonal embedding. -/
abbrev φhat : Rhat.{a} →+* Shat.{b} := coefficient.{a,b} φ0

/-- The second lifted diagonal embedding. -/
abbrev ψhat : Rhat.{a} →+* Shat.{b} := coefficient.{a,b} ψ0

/-- The existing unit-map producer lifts the same permutation unit. -/
def uhat : Shat.{b}ˣ := Units.map dS.{b}.symm.toRingHom.toMonoidHom u0

/-- Coefficient evaluation commutes with source-down and target-down. -/
theorem coefficient_down (f : R0 →+* S0) (r : Rhat.{a}) :
    dS.{b} (coefficient.{a,b} f r) = f (dR.{a} r) := by
  exact dS.{b}.apply_symm_apply _

/-- The transported unit retains the low permutation matrix. -/
theorem unit_down : dS.{b} (uhat.{b} : Shat.{b}) = U := by
  exact dS.{b}.apply_symm_apply _

/-- The lifted coefficient maps have the same semiconjugacy orientation. -/
theorem coefficient_semiconj (r : Rhat.{a}) :
    SemiconjBy (uhat.{b} : Shat.{b}) (φhat.{a,b} r) (ψhat.{a,b} r) := by
  apply dS.{b}.injective
  simp only [map_mul, unit_down.{b}, coefficient_down.{a,b}]
  exact (RightExtensionConjugacy.coefficient_semiconj (dR.{a} r)).eq

/-- Distinctness of the coefficient maps survives the independent lifts. -/
theorem coefficient_maps_ne : φhat.{a,b} ≠ ψhat.{a,b} := by
  intro h
  apply RightExtensionConjugacy.coefficient_maps_ne
  apply RingHom.ext
  intro r
  have he := congrArg
    (fun f : Rhat.{a} →+* Shat.{b} => dS.{b} (f (dR.{a}.symm r))) h
  simpa only [coefficient_down.{a,b}, dR.{a}.apply_symm_apply] using he

private abbrev Phat := Ideal.span {op (1 : Rhat.{a})}

private def regularToIdeal : Rhat.{a}ᵐᵒᵖ ≃ₗ[Rhat.{a}ᵐᵒᵖ] Phat.{a} :=
  (Submodule.topEquiv : (⊤ : Submodule Rhat.{a}ᵐᵒᵖ Rhat.{a}ᵐᵒᵖ)
    ≃ₗ[Rhat.{a}ᵐᵒᵖ] Rhat.{a}ᵐᵒᵖ).symm.trans
      (LinearEquiv.ofEq (⊤ : Submodule Rhat.{a}ᵐᵒᵖ Rhat.{a}ᵐᵒᵖ) Phat.{a}
        (by
          change (⊤ : Ideal Rhat.{a}ᵐᵒᵖ) = Ideal.span {op (1 : Rhat.{a})}
          rw [op_one, Ideal.span_singleton_one]))

private theorem regularToIdeal_val (r : Rhat.{a}ᵐᵒᵖ) :
    (regularToIdeal.{a} r).val = r := by
  simp [regularToIdeal]

private def carrierToIdeal : Mhat.{c} ≃ₗ[Rhat.{a}ᵐᵒᵖ] Phat.{a} :=
  carrierToRegular.{a,c}.trans regularToIdeal.{a}

private theorem carrierToIdeal_val (m : Mhat.{c}) :
    (carrierToIdeal.{a,c} m).val = op (dR.{a}.symm (unop m.down)) := by
  rw [carrierToIdeal, LinearEquiv.trans_apply, regularToIdeal_val.{a},
    carrierToRegular_apply.{a,c}]

/-- Observe the lifted extension through module transport to the principal
ideal of one and the existing ideal-one evaluation. -/
def observe (f : R0 →+* S0) :
    Obj (coefficient.{a,b} f) Mhat.{c} ≃ₗ[Shat.{b}ᵐᵒᵖ] Shat.{b}ᵐᵒᵖ where
  __ := private (mapLinearEquiv (coefficient.{a,b} f) carrierToIdeal.{a,c}).trans
    (spanLinearEquivOfMapEqOne (coefficient.{a,b} f) 1 (coefficient.{a,b} f).map_one)

/-- Pure-tensor evaluation after the canonical module transports. -/
theorem observe_tmul (f : R0 →+* S0) (m : Mhat.{c}) (s : Shat.{b}) :
    observe.{a,b,c} f (tmul (M := Mhat.{c}) (coefficient.{a,b} f) m s) =
      op (dS.{b}.symm (f (unop m.down)) * s) := by
  change (spanLinearEquivOfMapEqOne (coefficient.{a,b} f) 1
    (coefficient.{a,b} f).map_one)
      (mapLinearEquiv (coefficient.{a,b} f) carrierToIdeal.{a,c}
        (tmul (M := Mhat.{c}) (coefficient.{a,b} f) m s)) = _
  rw [mapLinearEquiv_tmul (coefficient.{a,b} f) carrierToIdeal.{a,c} m s,
    spanLinearEquivOfMapEqOne_tmul, carrierToIdeal_val.{a,c}, unop_op]
  change op (dS.{b}.symm (f (dR.{a} (dR.{a}.symm (unop m.down)))) * s) = _
  exact congrArg (fun r : R0 => op (dS.{b}.symm (f r) * s))
    (dR.{a}.apply_symm_apply (unop m.down))

/-- The independently lifted one-generator. -/
def qhat : Mhat.{c} := ULift.up (op (1 : R0))

/-- One-generator evaluation still detects its target coefficient. -/
theorem observe_q (f : R0 →+* S0) (s : Shat.{b}) :
    observe.{a,b,c} f
      (tmul (M := Mhat.{c}) (coefficient.{a,b} f) qhat.{c} s) = op s := by
  rw [observe_tmul.{a,b,c}]
  change op (dS.{b}.symm (f 1) * s) = op s
  rw [f.map_one, map_one, one_mul]

/-- Taking target-down after evaluation yields the low pure-tensor formula. -/
theorem observe_down (f : R0 →+* S0) (m : Mhat.{c}) (s : Shat.{b}) :
    dS.{b} (unop (observe.{a,b,c} f
      (tmul (M := Mhat.{c}) (coefficient.{a,b} f) m s))) =
        f (unop m.down) * dS.{b} s := by
  rw [observe_tmul.{a,b,c}, unop_op, map_mul, dS.{b}.apply_symm_apply]

private theorem observe_action_q (r : R0) (s : Shat.{b}) :
    dS.{b} (unop (observe.{a,b,c} ψ0
      (tmul (M := Mhat.{c}) ψhat.{a,b} (op (dR.{a}.symm r) • qhat.{c}) s))) =
        ψ0 r * dS.{b} s := by
  rw [smul_tmul (M := Mhat.{c}) ψhat.{a,b} (dR.{a}.symm r) qhat.{c} s,
    observe_q.{a,b,c}, unop_op, map_mul, coefficient_down.{a,b},
    dR.{a}.apply_symm_apply]

/-- The two extensions have exactly the universe `max c b`, independent of
how high the source ring was lifted. -/
abbrev SourceObj : Type (max c b) := Obj φhat.{a,b} Mhat.{c}

/-- The target extension has the same independently computed carrier universe. -/
abbrev TargetObj : Type (max c b) := Obj ψhat.{a,b} Mhat.{c}

/-- Source and target nonzero observations and target movement survive all
three independent lifts. -/
theorem surviving_movement :
    tmul (M := Mhat.{c}) φhat.{a,b} qhat.{c} (1 : Shat.{b}) ≠ 0 ∧
      tmul (M := Mhat.{c}) ψhat.{a,b} qhat.{c} (uhat.{b} : Shat.{b}) ≠ 0 ∧
      tmul (M := Mhat.{c}) ψhat.{a,b} qhat.{c} (uhat.{b} : Shat.{b}) ≠
        tmul (M := Mhat.{c}) ψhat.{a,b} qhat.{c} (1 : Shat.{b}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have he := congrArg
      (fun x : SourceObj.{a,b,c} => dS.{b} (unop (observe.{a,b,c} φ0 x))) h
    rw [observe_q.{a,b,c}, _root_.map_zero, unop_op, unop_zero,
      map_one, _root_.map_zero] at he
    exact target_one_ne_zero he
  · intro h
    have he := congrArg
      (fun x : TargetObj.{a,b,c} => dS.{b} (unop (observe.{a,b,c} ψ0 x))) h
    rw [observe_q.{a,b,c}, _root_.map_zero, unop_op, unop_zero,
      unit_down.{b}, _root_.map_zero] at he
    exact U_ne_zero he
  · intro h
    have he := congrArg
      (fun x : TargetObj.{a,b,c} => dS.{b} (unop (observe.{a,b,c} ψ0 x))) h
    rw [observe_q.{a,b,c}, observe_q.{a,b,c}, unop_op, unop_op,
      unit_down.{b}, map_one] at he
    exact U_ne_one he

/-- Lifted balancing still identifies the source representatives. -/
theorem source_balancing :
    tmul (M := Mhat.{c}) φhat.{a,b}
      (op (dR.{a}.symm r0) • qhat.{c}) (1 : Shat.{b}) =
        tmul (M := Mhat.{c}) φhat.{a,b} qhat.{c} (φhat.{a,b} (dR.{a}.symm r0)) := by
  rw [smul_tmul (M := Mhat.{c}) φhat.{a,b} (dR.{a}.symm r0) qhat.{c} (1 : Shat.{b}),
    mul_one]

/-- The same low matrix entries distinguish the prescribed outputs after
lifted balancing, without constructing the prescription on the quotient. -/
theorem wrong_order_balancing_observed :
    dS.{b} (unop (observe.{a,b,c} ψ0
      (tmul (M := Mhat.{c}) ψhat.{a,b} (op (dR.{a}.symm r0) • qhat.{c})
        ((1 : Shat.{b}) * (uhat.{b} : Shat.{b}))))) = Matrix.single 1 0 1 ∧
      dS.{b} (unop (observe.{a,b,c} ψ0
        (tmul (M := Mhat.{c}) ψhat.{a,b} qhat.{c}
          (φhat.{a,b} (dR.{a}.symm r0) * (uhat.{b} : Shat.{b}))))) =
            Matrix.single 0 1 1 := by
  constructor
  · rw [one_mul, observe_action_q.{a,b,c}, unit_down.{b}, ψ0_r0, e11_U]
  · rw [observe_q.{a,b,c}, unop_op, map_mul, coefficient_down.{a,b},
      dR.{a}.apply_symm_apply, unit_down.{b}, φ0_r0, e00_U]

/-- No function on either lifted quotient satisfies the bad all-tensor formula. -/
theorem no_wrong_order_function :
    ¬ ∃ F : SourceObj.{a,b,c} → TargetObj.{a,b,c},
      ∀ (m : Mhat.{c}) (s : Shat.{b}),
        F (tmul (M := Mhat.{c}) φhat.{a,b} m s) =
          tmul (M := Mhat.{c}) ψhat.{a,b} m (s * (uhat.{b} : Shat.{b})) := by
  rintro ⟨F, hF⟩
  have h := congrArg F source_balancing.{a,b,c}
  rw [hF, hF] at h
  have he := congrArg
    (fun x : TargetObj.{a,b,c} => dS.{b} (unop (observe.{a,b,c} ψ0 x))) h
  rw [(wrong_order_balancing_observed.{a,b,c}).1,
    (wrong_order_balancing_observed.{a,b,c}).2] at he
  exact e10_ne_e01 he

/-- Both sides of the lifted right-scalar obstruction retain the low entries. -/
theorem wrong_order_right_action_observed :
    dS.{b} (unop (observe.{a,b,c} ψ0
      (tmul (M := Mhat.{c}) ψhat.{a,b} qhat.{c}
        (dS.{b}.symm (Matrix.single 0 0 1 : S0) * (uhat.{b} : Shat.{b}))))) =
          Matrix.single 0 1 1 ∧
      dS.{b} (unop (observe.{a,b,c} ψ0
        (op (dS.{b}.symm (Matrix.single 0 0 1 : S0)) •
          tmul (M := Mhat.{c}) ψhat.{a,b} qhat.{c} (uhat.{b} : Shat.{b})))) =
            Matrix.single 1 0 1 := by
  constructor
  · rw [observe_q.{a,b,c}, unop_op, map_mul, dS.{b}.apply_symm_apply,
      unit_down.{b}, e00_U]
  · rw [tmul_smul (M := Mhat.{c}) ψhat.{a,b},
      MulOpposite.smul_eq_mul_unop, unop_op, observe_q.{a,b,c}, unop_op,
      map_mul, unit_down.{b}, dS.{b}.apply_symm_apply, U_e00]

/-- The independently lifted pair of prescribed values is incompatible with
fixed-right-target linearity even without the balancing obstruction. -/
theorem no_wrong_order_linear_map :
    ¬ ∃ F : SourceObj.{a,b,c} →ₗ[Shat.{b}ᵐᵒᵖ] TargetObj.{a,b,c},
      F (tmul (M := Mhat.{c}) φhat.{a,b} qhat.{c} (1 : Shat.{b})) =
        tmul (M := Mhat.{c}) ψhat.{a,b} qhat.{c} (uhat.{b} : Shat.{b}) ∧
      F (tmul (M := Mhat.{c}) φhat.{a,b} qhat.{c}
        (dS.{b}.symm (Matrix.single 0 0 1 : S0))) =
          tmul (M := Mhat.{c}) ψhat.{a,b} qhat.{c}
            (dS.{b}.symm (Matrix.single 0 0 1 : S0) * (uhat.{b} : Shat.{b})) := by
  rintro ⟨F, h1, he00⟩
  have h := F.map_smul (op (dS.{b}.symm (Matrix.single 0 0 1 : S0)))
    (tmul (M := Mhat.{c}) φhat.{a,b} qhat.{c} (1 : Shat.{b}))
  rw [tmul_smul (M := Mhat.{c}) φhat.{a,b}, MulOpposite.smul_eq_mul_unop,
    unop_op, one_mul, he00, h1] at h
  have he := congrArg
    (fun x : TargetObj.{a,b,c} => dS.{b} (unop (observe.{a,b,c} ψ0 x))) h
  rw [(wrong_order_right_action_observed.{a,b,c}).1,
    (wrong_order_right_action_observed.{a,b,c}).2] at he
  exact e10_ne_e01 he.symm

-- Each closed use separates one scalar or carrier universe from the other two.
example : tmul φhat.{1,0} qhat.{0} (1 : Shat.{0}) ≠ 0 :=
  (surviving_movement.{1,0,0}).1

example : tmul ψhat.{0,1} qhat.{0} (uhat.{1} : Shat.{1}) ≠
    tmul ψhat.{0,1} qhat.{0} (1 : Shat.{1}) :=
  (surviving_movement.{0,1,0}).2.2

example : ¬ ∃ F : SourceObj.{0,0,1} → TargetObj.{0,0,1},
    ∀ (m : Mhat.{1}) (s : Shat.{0}),
      F (tmul (M := Mhat.{1}) φhat.{0,0} m s) =
        tmul (M := Mhat.{1}) ψhat.{0,0} m (s * (uhat.{0} : Shat.{0})) :=
  no_wrong_order_function.{0,0,1}

example : ¬ ∃ F : SourceObj.{1,0,0} →ₗ[Shat.{0}ᵐᵒᵖ] TargetObj.{1,0,0},
    F (tmul (M := Mhat.{0}) φhat.{1,0} qhat.{0} (1 : Shat.{0})) =
      tmul (M := Mhat.{0}) ψhat.{1,0} qhat.{0} (uhat.{0} : Shat.{0}) ∧
    F (tmul (M := Mhat.{0}) φhat.{1,0} qhat.{0}
      (dS.{0}.symm (Matrix.single 0 0 1 : S0))) =
        tmul (M := Mhat.{0}) ψhat.{1,0} qhat.{0}
          (dS.{0}.symm (Matrix.single 0 0 1 : S0) * (uhat.{0} : Shat.{0})) :=
  no_wrong_order_linear_map.{1,0,0}

end Lift

end ProjectiveModulesTests.RightExtensionConjugacy
