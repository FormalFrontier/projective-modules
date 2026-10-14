/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Lens
module

public import ProjectiveModules.Free.LinearMap
import ProjectiveModules.Module.RightRegular
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Algebra.Module.PUnit
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Finite free sources and two target scalar actions

These clients use the finite-source linear-map instances with ordinary Mathlib
module actions. The outer scalar acts on the **target**, not on the source.
In particular, right regular sources over an opposite matrix semiring have
left multiplication as the outer action on their linear maps.

The constructions and calculations reuse Mathlib's bases, matrix units,
opposite modules, finitely supported functions and universe-lift equivalences.
The nonzero examples are separate from the empty and scalar-trivial cases.
The infinite free target and the finite torsion target exercise the two
conclusions separately. The final quotient-source data concern a finite
source whose specified action is unfaithful, so it is not free. No
finite-free-source instance is applied to it.
-/

@[expose] public section

open MulOpposite
open Module

namespace ProjectiveModulesTests.LinearMapClient

private abbrev NatTwo := Fin 2 → ℕ
private abbrev NatThree := Fin 3 → ℕ

/-- Evaluate a two-coordinate basis construction on a characteristic vector. -/
private theorem natTwo_constr_single (S : Type*) [Semiring S]
    {N : Type*} [AddCommMonoid N] [Module S N] (v : Fin 2 → N) (i : Fin 2) :
    (Pi.basisFun ℕ (Fin 2)).constr S v (Pi.single i 1) = v i := by
  rw [← Pi.basisFun_apply ℕ (Fin 2) i]
  exact (Pi.basisFun ℕ (Fin 2)).constr_basis S v i

/-- A non-Ring source with a genuinely three-coordinate output. -/
private def duplicate : NatTwo →ₗ[ℕ] NatThree :=
  LinearMap.pi fun j => LinearMap.proj (if j = 0 then 0 else 1)

example (x : NatTwo) : duplicate x 0 = x 0 := rfl
example (x : NatTwo) : duplicate x 1 = x 1 := rfl
example (x : NatTwo) : duplicate x 2 = x 1 := rfl

example : Module.Free ℕ (NatTwo →ₗ[ℕ] NatThree) := inferInstance
example : Module.Finite ℕ (NatTwo →ₗ[ℕ] NatThree) := inferInstance

example : duplicate (Pi.single 0 1) ≠ 0 := by
  intro h
  have := congrArg (fun v : NatThree => v 0) h
  simp [duplicate] at this

example : (2 • duplicate) (Pi.single 0 1) ≠ duplicate (Pi.single 0 1) := by
  intro h
  have := congrArg (fun v : NatThree => v 0) h
  norm_num [duplicate] at this

/-! ## Noncommutative left action, with the right regular source -/

private abbrev MatTwo (K : Type*) := Matrix (Fin 2) (Fin 2) K
private def p (K : Type*) [Zero K] [One K] : MatTwo K := Matrix.single 0 0 1
private def q (K : Type*) [Zero K] [One K] : MatTwo K := Matrix.single 0 1 1

private theorem pq (K : Type*) [Semiring K] : p K * q K = q K := by
  simp [p, q, Matrix.single_mul_single_same]

private theorem qp (K : Type*) [Semiring K] : q K * p K = 0 := by
  simp [p, q, Matrix.single_mul_single_of_ne]

private theorem q_ne_zero (K : Type*) [Semiring K] [Nontrivial K] : q K ≠ 0 := by
  intro h
  have := congrArg (fun x : MatTwo K => x 0 1) h
  simp [q] at this

private theorem p_ne_one (K : Type*) [Semiring K] [Nontrivial K] : p K ≠ 1 := by
  intro h
  have := congrArg (fun x : MatTwo K => x 1 1) h
  simp [p] at this

private def rightId (K : Type*) [Semiring K] :
    MatTwo K →ₗ[(MatTwo K)ᵐᵒᵖ] MatTwo K := LinearMap.id

example : Module.Free (MatTwo ℕ) (MatTwo ℕ →ₗ[(MatTwo ℕ)ᵐᵒᵖ] MatTwo ℕ) :=
  inferInstance
example : Module.Finite (MatTwo ℕ) (MatTwo ℕ →ₗ[(MatTwo ℕ)ᵐᵒᵖ] MatTwo ℕ) :=
  inferInstance

private theorem rightId_one (K : Type*) [Semiring K] [Nontrivial K] :
    rightId K 1 ≠ 0 := one_ne_zero

private theorem left_moves (K : Type*) [Semiring K] [Nontrivial K] :
    (p K • rightId K) 1 ≠ rightId K 1 := by
  simpa [rightId, smul_eq_mul] using p_ne_one K

private theorem left_at_q (K : Type*) [Semiring K] :
    (p K • rightId K) (q K) = q K := by
  simpa [rightId, smul_eq_mul] using pq K

private theorem left_order (K : Type*) [Semiring K] :
    (p K • (q K • rightId K)) 1 = q K := by
  simpa [rightId, smul_eq_mul] using pq K

private theorem reverse_order (K : Type*) [Semiring K] :
    (q K • (p K • rightId K)) 1 = 0 := by
  simpa [rightId, smul_eq_mul] using qp K

/-- Multiplying the output on the right is not an opposite-linear map. -/
private theorem wrong_right (K : Type*) [Semiring K] [Nontrivial K] :
    ¬ ((op (q K) • (1 : MatTwo K)) * p K =
      op (q K) • ((1 : MatTwo K) * p K)) := by
  simpa [op_smul_eq_mul, qp, pq] using (q_ne_zero K).symm

example : rightId ℕ 1 ≠ 0 := rightId_one ℕ
example : (p ℕ • rightId ℕ) 1 ≠ rightId ℕ 1 := left_moves ℕ
example : (p ℕ • rightId ℕ) (q ℕ) = q ℕ := left_at_q ℕ
example : (p ℕ • (q ℕ • rightId ℕ)) 1 = q ℕ := left_order ℕ
example : (q ℕ • (p ℕ • rightId ℕ)) 1 = 0 := reverse_order ℕ
example : q ℕ * p ℕ = 0 := qp ℕ
example : q ℕ ≠ 0 := q_ne_zero ℕ
example : ¬ ((op (q ℕ) • (1 : MatTwo ℕ)) * p ℕ =
    op (q ℕ) • ((1 : MatTwo ℕ) * p ℕ)) := wrong_right ℕ

/-! The same ordinary actions retain the old two-Ring clients. -/

example : Module.Free (MatTwo ℤ) (MatTwo ℤ →ₗ[(MatTwo ℤ)ᵐᵒᵖ] MatTwo ℤ) :=
  inferInstance
example : Module.Finite (MatTwo ℤ) (MatTwo ℤ →ₗ[(MatTwo ℤ)ᵐᵒᵖ] MatTwo ℤ) :=
  inferInstance
example : rightId ℤ 1 ≠ 0 := rightId_one ℤ
example : (p ℤ • rightId ℤ) 1 ≠ rightId ℤ 1 := left_moves ℤ
example : (p ℤ • rightId ℤ) (q ℤ) = q ℤ := left_at_q ℤ
example : (p ℤ • (q ℤ • rightId ℤ)) 1 = q ℤ := left_order ℤ
example : (q ℤ • (p ℤ • rightId ℤ)) 1 = 0 := reverse_order ℤ
example : ¬ ((op (q ℤ) • (1 : MatTwo ℤ)) * p ℤ =
    op (q ℤ) • ((1 : MatTwo ℤ) * p ℤ)) := wrong_right ℤ

/-- The old public factor coordinates of the identity are its basis values. -/
example (i : Module.Free.ChooseBasisIndex (MatTwo ℤ)ᵐᵒᵖ (MatTwo ℤ)) :
    (((Module.Free.chooseBasis (MatTwo ℤ)ᵐᵒᵖ (MatTwo ℤ)).repr.congrLeft
        (MatTwo ℤ) (MatTwo ℤ) ≪≫ₗ (Finsupp.lsum (MatTwo ℤ)).symm ≪≫ₗ
      LinearEquiv.piCongrRight fun _ =>
        LinearMap.ringLmapEquivSelf (MatTwo ℤ)ᵐᵒᵖ (MatTwo ℤ) (MatTwo ℤ))
      (rightId ℤ)) i = Module.Free.chooseBasis (MatTwo ℤ)ᵐᵒᵖ (MatTwo ℤ) i := by
  rw [← Module.Free.constr_symm_eq_repr_congrLeft_lsum
    (MatTwo ℤ)ᵐᵒᵖ (MatTwo ℤ) (MatTwo ℤ) (MatTwo ℤ)]
  rfl

/-! ## Distinct source and outer scalars -/

/-- Evaluation at a row, using the existing right-row matrix module. -/
private noncomputable def rowMap : MatTwo ℕ →ₗ[(MatTwo ℕ)ᵐᵒᵖ] NatTwo :=
  ((LinearMap.ringLmapEquivSelf (MatTwo ℕ)ᵐᵒᵖ ℕ NatTwo).symm (Pi.single 0 1)).comp
    (MulOpposite.opLinearEquiv (MatTwo ℕ)ᵐᵒᵖ (M := MatTwo ℕ)).toLinearMap

example : Module.Free ℕ (MatTwo ℕ →ₗ[(MatTwo ℕ)ᵐᵒᵖ] NatTwo) := inferInstance
example : Module.Finite ℕ (MatTwo ℕ →ₗ[(MatTwo ℕ)ᵐᵒᵖ] NatTwo) := inferInstance

example (x : MatTwo ℕ) : rowMap x = Matrix.vecMul (Pi.single 0 1) x := rfl

private theorem row_at_one : rowMap 1 = Pi.single 0 1 := by
  change Matrix.vecMul (Pi.single 0 1) (1 : MatTwo ℕ) = _
  simp

private theorem row_at_q : rowMap (q ℕ) = Pi.single 1 1 := by
  change Matrix.vecMul (Pi.single 0 1) (q ℕ) = Pi.single 1 1
  ext j
  fin_cases j <;> norm_num [q, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  exact (Pi.single_eq_same (M := fun _ : Fin 2 ↦ ℕ) (1 : Fin 2) (1 : ℕ)).symm

example : rowMap 1 ≠ 0 := by
  rw [row_at_one]
  intro h
  have := congrArg (fun v : NatTwo => v 0) h
  simp at this

example : rowMap (q ℕ) ≠ 0 := by
  rw [row_at_q]
  intro h
  have := congrArg (fun v : NatTwo => v 1) h
  simp at this

example : (2 • rowMap) 1 ≠ rowMap 1 := by
  intro h
  have := congrArg (fun v : NatTwo => v 0) h
  norm_num [LinearMap.smul_apply, row_at_one] at this

example (n : ℕ) : op (q ℕ) • (Pi.single 0 1 : NatTwo) ≠ n • Pi.single 0 1 := by
  intro h
  have hrow : op (q ℕ) • (Pi.single 0 1 : NatTwo) = Pi.single 1 1 := row_at_q
  rw [hrow] at h
  have := congrArg (fun v : NatTwo => v 1) h
  simp at this

example : Module.Free ℕ (MatTwo ℕ →ₗ[(MatTwo ℕ)ᵐᵒᵖ] MatTwo ℕ) := inferInstance
example : Module.Finite ℕ (MatTwo ℕ →ₗ[(MatTwo ℕ)ᵐᵒᵖ] MatTwo ℕ) := inferInstance
example : rightId ℕ 1 ≠ 0 := rightId_one ℕ

example : (2 • rightId ℕ) 1 ≠ rightId ℕ 1 := by
  intro h
  have := congrArg (fun x : MatTwo ℕ => x 0 0) h
  norm_num [rightId] at this

example (n : ℕ) : op (q ℕ) • (1 : MatTwo ℕ) ≠ n • (1 : MatTwo ℕ) := by
  intro h
  have := congrArg (fun x : MatTwo ℕ => x 0 1) h
  simp [q] at this

/-! ## A free infinite target and a finite torsion target -/

private noncomputable def finsuppMap (K : Type*) [Semiring K] :
    NatTwo →ₗ[ℕ] (ℕ →₀ K) :=
  (Pi.basisFun ℕ (Fin 2)).constr K fun i => Finsupp.single (i : ℕ) 1

private theorem finsupp_at_single (K : Type*) [Semiring K] (i : Fin 2) :
    finsuppMap K (Pi.single i 1) = Finsupp.single (i : ℕ) 1 :=
  natTwo_constr_single K (fun j => Finsupp.single (j : ℕ) 1) i

example (K : Type*) [Semiring K] :
    Module.Free K (NatTwo →ₗ[ℕ] (ℕ →₀ K)) := inferInstance
example : Module.Free ℕ (NatTwo →ₗ[ℕ] (ℕ →₀ ℕ)) := inferInstance

example (K : Type*) [Semiring K] :
    finsuppMap K (Pi.single 0 1) = Finsupp.single 0 1 :=
  finsupp_at_single K 0

private theorem finsupp_ne_zero (K : Type*) [Semiring K] [Nontrivial K] :
    finsuppMap K (Pi.single 0 1) ≠ 0 := by
  intro h
  have hb : finsuppMap K (Pi.single 0 1) = Finsupp.single 0 1 :=
    finsupp_at_single K 0
  rw [hb] at h
  have := congrArg (fun v : ℕ →₀ K => v 0) h
  simp at this

example : finsuppMap ℕ (Pi.single 0 1) ≠ 0 := finsupp_ne_zero ℕ

example (K : Type*) [Semiring K] :
    finsuppMap K (Pi.single 1 1) = Finsupp.single 1 1 :=
  finsupp_at_single K 1

example (K : Type*) [Semiring K] [Nontrivial K] :
    finsuppMap K (Pi.single 1 1) ≠ 0 := by
  intro h
  have hb : finsuppMap K (Pi.single 1 1) = Finsupp.single 1 1 :=
    finsupp_at_single K 1
  rw [hb] at h
  have := congrArg (fun v : ℕ →₀ K => v 1) h
  simp at this

private noncomputable def torsionMap : NatTwo →ₗ[ℕ] ZMod 2 :=
  (Pi.basisFun ℕ (Fin 2)).constr ℤ fun i => if i = 0 then 1 else 0

example : Module.Finite ℤ (ZMod 2) := Module.Finite.of_finite
example : Module.Finite ℤ (NatTwo →ₗ[ℕ] ZMod 2) := inferInstance

private theorem torsion_at_zero : torsionMap (Pi.single 0 1) = 1 :=
  natTwo_constr_single ℤ (fun i => if i = 0 then 1 else 0) 0

example : torsionMap (Pi.single 1 1) = 0 :=
  natTwo_constr_single ℤ (fun i => if i = 0 then 1 else 0) 1

example : torsionMap (Pi.single 0 1) ≠ 0 := by
  rw [torsion_at_zero]
  decide

example : ((2 : ℤ) • torsionMap) (Pi.single 0 1) = 0 := by
  simpa only [LinearMap.smul_apply, torsion_at_zero, zsmul_eq_mul, Int.cast_ofNat] using
    (show (2 : ZMod 2) * 1 = 0 by decide)

example : ((2 : ℤ) • torsionMap) (Pi.single 0 1) ≠ torsionMap (Pi.single 0 1) := by
  simpa only [LinearMap.smul_apply, torsion_at_zero, zsmul_eq_mul, Int.cast_ofNat] using
    (show (2 : ZMod 2) * 1 ≠ 1 by decide)

/-! ## Empty, zero and scalar-trivial modules -/

example : Module.Free ℕ ((Fin 0 → ℕ) →ₗ[ℕ] NatThree) := inferInstance
example : Module.Finite ℕ ((Fin 0 → ℕ) →ₗ[ℕ] NatThree) := inferInstance

example (f : (Fin 0 → ℕ) →ₗ[ℕ] NatThree) : f = 0 :=
  LinearMap.ext fun x =>
    (congrArg f (Subsingleton.elim x 0)).trans f.map_zero

example : Module.Free ℕ (NatTwo →ₗ[ℕ] PUnit) := inferInstance
example : Module.Finite ℕ (NatTwo →ₗ[ℕ] PUnit) := inferInstance
example (f : NatTwo →ₗ[ℕ] PUnit) : f = 0 := Subsingleton.elim _ _

private noncomputable def emptyMap : PUnit →ₗ[ℕ] NatThree :=
  (Basis.empty PUnit : Basis PEmpty.{1} ℕ PUnit).constr ℕ fun i => PEmpty.elim i

example : Module.Free ℕ (PUnit →ₗ[ℕ] NatThree) := inferInstance
example : Module.Finite ℕ (PUnit →ₗ[ℕ] NatThree) := inferInstance
example : (emptyMap : PUnit.{1} →ₗ[ℕ] NatThree) = 0 := by
  let f : PUnit.{1} →ₗ[ℕ] NatThree := emptyMap
  exact LinearMap.ext fun x =>
    (congrArg f (Subsingleton.elim x 0)).trans f.map_zero

-- Trivial inner scalars force both modules to be trivial. The chosen basis
-- index is finite; no finiteness claim about arbitrary bases is needed.
example : Module.Free ℕ (PUnit →ₗ[PUnit] PUnit) := inferInstance
example : Module.Finite ℕ (PUnit →ₗ[PUnit] PUnit) := inferInstance
example : Finite (Module.Free.ChooseBasisIndex PUnit PUnit) := inferInstance
example : Subsingleton (PUnit →ₗ[PUnit] PUnit) := inferInstance

-- Trivial outer scalars force only the target to be trivial, not NatTwo.
example : Module.Free PUnit (NatTwo →ₗ[ℕ] PUnit) := inferInstance
example : Module.Finite PUnit (NatTwo →ₗ[ℕ] PUnit) := inferInstance
example : (Pi.single 0 1 : NatTwo) ≠ 0 := by
  intro h
  have := congrArg (fun v : NatTwo => v 0) h
  simp at this
example : Subsingleton (NatTwo →ₗ[ℕ] PUnit) := inferInstance

/-! ## Arbitrary semiring coefficients, without a source coefficient action -/

private noncomputable def coefficientMap (K : Type*) [Semiring K] :
    NatTwo →ₗ[ℕ] (Fin 3 → K) :=
  (Pi.basisFun ℕ (Fin 2)).constr K fun i =>
    if i = 0 then Pi.single 0 1 else Pi.single 1 1 + Pi.single 2 1

example (K : Type*) [Semiring K] : Module.Free K (NatTwo →ₗ[ℕ] (Fin 3 → K)) :=
  inferInstance
example (K : Type*) [Semiring K] : Module.Finite K (NatTwo →ₗ[ℕ] (Fin 3 → K)) :=
  inferInstance

private theorem coefficient_at_zero (K : Type*) [Semiring K] :
    coefficientMap K (Pi.single 0 1) = Pi.single 0 1 :=
  natTwo_constr_single K
    (fun i => if i = 0 then Pi.single 0 1 else Pi.single 1 1 + Pi.single 2 1) 0

example (K : Type*) [Semiring K] [Nontrivial K] :
    coefficientMap K (Pi.single 0 1) ≠ 0 := by
  rw [coefficient_at_zero]
  intro h
  have := congrArg (fun v : Fin 3 → K => v 0) h
  simp at this

example (K : Type*) [Semiring K] [Nontrivial K] :
    ((0 : K) • coefficientMap K) (Pi.single 0 1) ≠ coefficientMap K (Pi.single 0 1) := by
  simp only [zero_smul, LinearMap.zero_apply, coefficient_at_zero]
  intro h
  have := congrArg (fun v : Fin 3 → K => v 0) h
  simp at this

example (K : Type*) [Semiring K] [Subsingleton K] : coefficientMap K = 0 :=
  Subsingleton.elim _ _

example (K : Type*) [CommSemiring K] :
    Module.Free K ((Fin 2 → K) →ₗ[K] (Fin 3 → K)) := inferInstance
example (K : Type*) [CommSemiring K] :
    Module.Finite K ((Fin 2 → K) →ₗ[K] (Fin 3 → K)) := inferInstance

/-! ## Independent scalar and carrier universes -/

universe uA uS uM uN uK

section CoefficientLifts

variable (K : Type uK) [Semiring K]

-- These local transports use the existing down action, not a new module action.
local instance : Module.Free (ULift.{uA} ℕ) ℕ :=
  Module.Free.of_equiv
    (Module.compHom.toLinearEquiv (ULift.ringEquiv : ULift.{uA} ℕ ≃+* ℕ))
local instance : Module.Finite (ULift.{uA} ℕ) ℕ :=
  Module.Finite.equiv
    (Module.compHom.toLinearEquiv (ULift.ringEquiv : ULift.{uA} ℕ ≃+* ℕ))
local instance : Module.Free (ULift.{uS} K) K :=
  Module.Free.of_equiv
    (Module.compHom.toLinearEquiv (ULift.ringEquiv : ULift.{uS} K ≃+* K))
local instance : Module.Finite (ULift.{uS} K) K :=
  Module.Finite.equiv
    (Module.compHom.toLinearEquiv (ULift.ringEquiv : ULift.{uS} K ≃+* K))

local instance : SMulCommClass (ULift.{uA} ℕ) K (Fin 3 → K) where
  smul_comm a s v := show a.down • (s • v) = s • (a.down • v) from
    smul_comm a.down s v

local instance : SMulCommClass ℕ K (ULift.{uN} (Fin 3 → K)) where
  smul_comm a s v := by
    change ULift.up (a • (s • v.down)) = ULift.up (s • (a • v.down))
    exact congrArg ULift.up (smul_comm a s v.down)

local instance : SMulCommClass (ULift.{uA} ℕ) (ULift.{uS} K)
    (ULift.{uN} (Fin 3 → K)) where
  smul_comm a s v := by
    change ULift.up (a.down • (s.down • v.down)) =
      ULift.up (s.down • (a.down • v.down))
    exact congrArg ULift.up (smul_comm a.down s.down v.down)

-- One knob at a time, with the other carriers and scalars unchanged.
example : Module.Free K (NatTwo →ₗ[ULift.{uA} ℕ] (Fin 3 → K)) := inferInstance
example : Module.Finite K (NatTwo →ₗ[ULift.{uA} ℕ] (Fin 3 → K)) := inferInstance
example : Module.Free (ULift.{uS} K) (NatTwo →ₗ[ℕ] (Fin 3 → K)) := inferInstance
example : Module.Finite (ULift.{uS} K) (NatTwo →ₗ[ℕ] (Fin 3 → K)) := inferInstance
example : Module.Free K (ULift.{uM} NatTwo →ₗ[ℕ] (Fin 3 → K)) := inferInstance
example : Module.Finite K (ULift.{uM} NatTwo →ₗ[ℕ] (Fin 3 → K)) := inferInstance
example : Module.Free K (NatTwo →ₗ[ℕ] ULift.{uN} (Fin 3 → K)) := inferInstance
example : Module.Finite K (NatTwo →ₗ[ℕ] ULift.{uN} (Fin 3 → K)) := inferInstance

-- All four lift levels and the coefficient universe are unrelated.
example : Module.Free (ULift.{uS} K)
    (ULift.{uM} NatTwo →ₗ[ULift.{uA} ℕ] ULift.{uN} (Fin 3 → K)) := inferInstance
example : Module.Finite (ULift.{uS} K)
    (ULift.{uM} NatTwo →ₗ[ULift.{uA} ℕ] ULift.{uN} (Fin 3 → K)) := inferInstance

private noncomputable def liftedCoefficientMap :
    ULift.{uM} NatTwo →ₗ[ULift.{uA} ℕ] ULift.{uN} (Fin 3 → K) :=
  (ULift.moduleEquiv (R := ULift.{uA} ℕ) (M := Fin 3 → K)).symm.toLinearMap.comp
    (((coefficientMap K).restrictScalars (ULift.{uA} ℕ)).comp
      (ULift.moduleEquiv (R := ULift.{uA} ℕ) (M := NatTwo)).toLinearMap)

example (a : ULift.{uA} ℕ) (x : ULift.{uM} NatTwo) :
    a • x = ULift.up (a.down • x.down) := rfl
example (a : ULift.{uA} ℕ) (v : ULift.{uN} (Fin 3 → K)) :
    a • v = ULift.up (a.down • v.down) := rfl
example (s : ULift.{uS} K) (v : ULift.{uN} (Fin 3 → K)) :
    s • v = ULift.up (s.down • v.down) := rfl

example :
    (liftedCoefficientMap K :
      ULift.{uM} NatTwo →ₗ[ULift.{uA} ℕ] ULift.{uN} (Fin 3 → K))
      (ULift.up (Pi.single 0 1)) =
    (ULift.up (Pi.single 0 1) : ULift.{uN} (Fin 3 → K)) := by
  change ULift.up (coefficientMap K (Pi.single 0 1)) = _
  rw [coefficient_at_zero]

example [Nontrivial K] :
    (liftedCoefficientMap K :
      ULift.{uM} NatTwo →ₗ[ULift.{uA} ℕ] ULift.{uN} (Fin 3 → K))
      (ULift.up (Pi.single 0 1)) ≠ 0 := by
  intro h
  have := congrArg (fun v : ULift.{uN} (Fin 3 → K) => v.down 0) h
  change coefficientMap K (Pi.single 0 1) 0 = 0 at this
  simp [coefficient_at_zero] at this

example [Nontrivial K] :
    ((ULift.up (0 : K) : ULift.{uS} K) •
        (liftedCoefficientMap K :
          ULift.{uM} NatTwo →ₗ[ULift.{uA} ℕ] ULift.{uN} (Fin 3 → K)))
      (ULift.up (Pi.single 0 1)) ≠
    (liftedCoefficientMap K :
      ULift.{uM} NatTwo →ₗ[ULift.{uA} ℕ] ULift.{uN} (Fin 3 → K))
      (ULift.up (Pi.single 0 1)) := by
  intro h
  have := congrArg (fun v : ULift.{uN} (Fin 3 → K) => v.down 0) h
  change (0 : K) • coefficientMap K (Pi.single 0 1) 0 =
    coefficientMap K (Pi.single 0 1) 0 at this
  simp [coefficient_at_zero] at this

example [Subsingleton K] :
    (liftedCoefficientMap K :
      ULift.{uM} NatTwo →ₗ[ULift.{uA} ℕ] ULift.{uN} (Fin 3 → K)) = 0 :=
  Subsingleton.elim _ _

end CoefficientLifts

/-! The lifted matrix probes use the same opposite and left-regular actors. -/

section MatrixLifts

variable (K : Type uK) [Semiring K]

private noncomputable def scalarRightEquiv :
    ULift.{uA} ((MatTwo K)ᵐᵒᵖ) ≃ₗ[ULift.{uA} ((MatTwo K)ᵐᵒᵖ)] MatTwo K :=
  (Module.compHom.toLinearEquiv
    (ULift.ringEquiv : ULift.{uA} ((MatTwo K)ᵐᵒᵖ) ≃+* (MatTwo K)ᵐᵒᵖ)).trans
      (MulOpposite.opLinearEquiv (ULift.{uA} ((MatTwo K)ᵐᵒᵖ))
        (M := MatTwo K)).symm

-- The model abbreviations are private, so their local transports must be private too.
private local instance : Module.Free (ULift.{uA} ((MatTwo K)ᵐᵒᵖ)) (MatTwo K) :=
  Module.Free.of_equiv (scalarRightEquiv K)
private local instance : Module.Finite (ULift.{uA} ((MatTwo K)ᵐᵒᵖ)) (MatTwo K) :=
  Module.Finite.equiv (scalarRightEquiv K)
private local instance : Module.Free (ULift.{uS} (MatTwo K)) (MatTwo K) :=
  Module.Free.of_equiv
    (Module.compHom.toLinearEquiv
      (ULift.ringEquiv : ULift.{uS} (MatTwo K) ≃+* MatTwo K))
private local instance : Module.Finite (ULift.{uS} (MatTwo K)) (MatTwo K) :=
  Module.Finite.equiv
    (Module.compHom.toLinearEquiv
      (ULift.ringEquiv : ULift.{uS} (MatTwo K) ≃+* MatTwo K))

private local instance : SMulCommClass (ULift.{uA} ((MatTwo K)ᵐᵒᵖ))
    (MatTwo K) (MatTwo K) where
  smul_comm a s x := show a.down • (s • x) = s • (a.down • x) from
    smul_comm a.down s x

private local instance : SMulCommClass (MatTwo K)ᵐᵒᵖ (ULift.{uS} (MatTwo K))
    (MatTwo K) where
  smul_comm a s x := show a • (s.down • x) = s.down • (a • x) from
    smul_comm a s.down x

private local instance : SMulCommClass (MatTwo K)ᵐᵒᵖ (MatTwo K)
    (ULift.{uN} (MatTwo K)) where
  smul_comm a s x := by
    change ULift.up (a • (s • x.down)) = ULift.up (s • (a • x.down))
    exact congrArg ULift.up (smul_comm a s x.down)

private local instance : SMulCommClass (ULift.{uA} ((MatTwo K)ᵐᵒᵖ))
    (ULift.{uS} (MatTwo K)) (ULift.{uN} (MatTwo K)) where
  smul_comm a s x := by
    change ULift.up (a.down • (s.down • x.down)) =
      ULift.up (s.down • (a.down • x.down))
    exact congrArg ULift.up (smul_comm a.down s.down x.down)

example : Module.Free (MatTwo K)
    (MatTwo K →ₗ[ULift.{uA} ((MatTwo K)ᵐᵒᵖ)] MatTwo K) := inferInstance
example : Module.Finite (MatTwo K)
    (MatTwo K →ₗ[ULift.{uA} ((MatTwo K)ᵐᵒᵖ)] MatTwo K) := inferInstance
example : Module.Free (ULift.{uS} (MatTwo K))
    (MatTwo K →ₗ[(MatTwo K)ᵐᵒᵖ] MatTwo K) := inferInstance
example : Module.Finite (ULift.{uS} (MatTwo K))
    (MatTwo K →ₗ[(MatTwo K)ᵐᵒᵖ] MatTwo K) := inferInstance
example : Module.Free (MatTwo K)
    (ULift.{uM} (MatTwo K) →ₗ[(MatTwo K)ᵐᵒᵖ] MatTwo K) := inferInstance
example : Module.Finite (MatTwo K)
    (ULift.{uM} (MatTwo K) →ₗ[(MatTwo K)ᵐᵒᵖ] MatTwo K) := inferInstance
example : Module.Free (MatTwo K)
    (MatTwo K →ₗ[(MatTwo K)ᵐᵒᵖ] ULift.{uN} (MatTwo K)) := inferInstance
example : Module.Finite (MatTwo K)
    (MatTwo K →ₗ[(MatTwo K)ᵐᵒᵖ] ULift.{uN} (MatTwo K)) := inferInstance

example : Module.Free (ULift.{uS} (MatTwo K))
    (ULift.{uM} (MatTwo K) →ₗ[ULift.{uA} ((MatTwo K)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo K)) := inferInstance
example : Module.Finite (ULift.{uS} (MatTwo K))
    (ULift.{uM} (MatTwo K) →ₗ[ULift.{uA} ((MatTwo K)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo K)) := inferInstance

private def liftedRightId (K : Type uK) [Semiring K] :
    ULift.{uM} (MatTwo K) →ₗ[ULift.{uA} ((MatTwo K)ᵐᵒᵖ)] ULift.{uN} (MatTwo K) :=
  (ULift.moduleEquiv (R := ULift.{uA} ((MatTwo K)ᵐᵒᵖ)) (M := MatTwo K) :
    ULift.{uN} (MatTwo K) ≃ₗ[ULift.{uA} ((MatTwo K)ᵐᵒᵖ)] MatTwo K).symm.toLinearMap.comp
      (ULift.moduleEquiv (R := ULift.{uA} ((MatTwo K)ᵐᵒᵖ)) (M := MatTwo K) :
        ULift.{uM} (MatTwo K) ≃ₗ[ULift.{uA} ((MatTwo K)ᵐᵒᵖ)] MatTwo K).toLinearMap

example (x : MatTwo K) :
    let f : ULift.{uM} (MatTwo K) →ₗ[ULift.{uA} ((MatTwo K)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo K) := liftedRightId K
    f (ULift.up x) = ULift.up x := rfl
example (a : ULift.{uA} ((MatTwo K)ᵐᵒᵖ)) (x : ULift.{uM} (MatTwo K)) :
    a • x = ULift.up (x.down * a.down.unop) := rfl
example (a : ULift.{uA} ((MatTwo K)ᵐᵒᵖ)) (x : ULift.{uN} (MatTwo K)) :
    a • x = ULift.up (x.down * a.down.unop) := rfl
example (s : ULift.{uS} (MatTwo K)) (x : ULift.{uN} (MatTwo K)) :
    s • x = ULift.up (s.down * x.down) := rfl

-- A full hom type fixes the scalar, source and target levels independently.
private theorem lifted_left_at_q (K : Type uK) [Semiring K] :
    let f : ULift.{uM} (MatTwo K) →ₗ[ULift.{uA} ((MatTwo K)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo K) := liftedRightId K
    ((ULift.up (p K) : ULift.{uS} (MatTwo K)) • f)
      (ULift.up (q K)) = ULift.up (q K) := by
  change ULift.up (p K * q K) = _
  rw [pq]

private theorem lifted_left_order (K : Type uK) [Semiring K] :
    let f : ULift.{uM} (MatTwo K) →ₗ[ULift.{uA} ((MatTwo K)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo K) := liftedRightId K
    ((ULift.up (p K) : ULift.{uS} (MatTwo K)) •
      ((ULift.up (q K) : ULift.{uS} (MatTwo K)) • f))
        (ULift.up 1) = ULift.up (q K) := by
  change ULift.up (p K * (q K * 1)) = _
  rw [mul_one, pq]

private theorem lifted_reverse_order (K : Type uK) [Semiring K] :
    let f : ULift.{uM} (MatTwo K) →ₗ[ULift.{uA} ((MatTwo K)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo K) := liftedRightId K
    ((ULift.up (q K) : ULift.{uS} (MatTwo K)) •
      ((ULift.up (p K) : ULift.{uS} (MatTwo K)) • f))
        (ULift.up 1) = 0 := by
  change ULift.up (q K * (p K * 1)) = ULift.up 0
  rw [mul_one, qp]

/-- The deliberately wrong right-output function, not a bundled linear map. -/
private def liftedWrongRight (K : Type uK) [Semiring K]
    (x : ULift.{uM} (MatTwo K)) : ULift.{uN} (MatTwo K) :=
  ULift.up (x.down * p K)

private theorem lifted_wrong_right (K : Type uK) [Semiring K] [Nontrivial K] :
    let w : ULift.{uM} (MatTwo K) → ULift.{uN} (MatTwo K) := liftedWrongRight K
    w ((ULift.up (op (q K)) : ULift.{uA} ((MatTwo K)ᵐᵒᵖ)) • ULift.up 1) ≠
      (ULift.up (op (q K)) : ULift.{uA} ((MatTwo K)ᵐᵒᵖ)) • w (ULift.up 1) := by
  dsimp only
  intro h
  have hd := congrArg ULift.down h
  change (1 * q K) * p K = (1 * p K) * q K at hd
  simp only [one_mul, qp, pq] at hd
  exact (q_ne_zero K) hd.symm

private theorem lifted_one_ne_zero (K : Type uK) [Semiring K] [Nontrivial K] :
    let f : ULift.{uM} (MatTwo K) →ₗ[ULift.{uA} ((MatTwo K)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo K) := liftedRightId K
    f (ULift.up 1) ≠ 0 := by
  dsimp only
  intro h
  have hd := congrArg ULift.down h
  exact one_ne_zero hd

private theorem lifted_q_ne_zero (K : Type uK) [Semiring K] [Nontrivial K] :
    (ULift.up (q K) : ULift.{uN} (MatTwo K)) ≠ 0 := by
  intro h
  exact q_ne_zero K (congrArg ULift.down h)

private theorem lifted_moves (K : Type uK) [Semiring K] [Nontrivial K] :
    let f : ULift.{uM} (MatTwo K) →ₗ[ULift.{uA} ((MatTwo K)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo K) := liftedRightId K
    ((ULift.up (p K) : ULift.{uS} (MatTwo K)) • f) (ULift.up 1) ≠
      f (ULift.up 1) := by
  dsimp only
  intro h
  have hd := congrArg ULift.down h
  change p K * 1 = (1 : MatTwo K) at hd
  exact p_ne_one K (by simpa using hd)

private theorem lifted_wrong_at_q (K : Type uK) [Semiring K] :
    let w : ULift.{uM} (MatTwo K) → ULift.{uN} (MatTwo K) := liftedWrongRight K
    w (ULift.up (q K)) = 0 := by
  change ULift.up (q K * p K) = ULift.up 0
  rw [qp]

-- Both the genuinely non-Ring and old Ring coefficient choices retain four knobs.
private def natLiftedId : ULift.{uM} (MatTwo ℕ) →ₗ[ULift.{uA} ((MatTwo ℕ)ᵐᵒᵖ)]
    ULift.{uN} (MatTwo ℕ) := liftedRightId ℕ
private def intLiftedId : ULift.{uM} (MatTwo ℤ) →ₗ[ULift.{uA} ((MatTwo ℤ)ᵐᵒᵖ)]
    ULift.{uN} (MatTwo ℤ) := liftedRightId ℤ
private def natLiftedWrong : ULift.{uM} (MatTwo ℕ) → ULift.{uN} (MatTwo ℕ) :=
  liftedWrongRight ℕ
private def intLiftedWrong : ULift.{uM} (MatTwo ℤ) → ULift.{uN} (MatTwo ℤ) :=
  liftedWrongRight ℤ

example :
    let f : ULift.{uM} (MatTwo ℕ) →ₗ[ULift.{uA} ((MatTwo ℕ)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo ℕ) := natLiftedId
    f (ULift.up 1) ≠ 0 := lifted_one_ne_zero.{uA, uM, uN, 0} ℕ
example :
    let f : ULift.{uM} (MatTwo ℕ) →ₗ[ULift.{uA} ((MatTwo ℕ)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo ℕ) := natLiftedId
    ((ULift.up (p ℕ) : ULift.{uS} (MatTwo ℕ)) • f)
      (ULift.up (q ℕ)) = ULift.up (q ℕ) := lifted_left_at_q.{uA, uS, uM, uN, 0} ℕ
example : (ULift.up (q ℕ) : ULift.{uN} (MatTwo ℕ)) ≠ 0 := lifted_q_ne_zero ℕ
example :
    let f : ULift.{uM} (MatTwo ℕ) →ₗ[ULift.{uA} ((MatTwo ℕ)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo ℕ) := natLiftedId
    ((ULift.up (p ℕ) : ULift.{uS} (MatTwo ℕ)) •
      ((ULift.up (q ℕ) : ULift.{uS} (MatTwo ℕ)) • f))
        (ULift.up 1) = ULift.up (q ℕ) := lifted_left_order.{uA, uS, uM, uN, 0} ℕ
example :
    let f : ULift.{uM} (MatTwo ℕ) →ₗ[ULift.{uA} ((MatTwo ℕ)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo ℕ) := natLiftedId
    ((ULift.up (q ℕ) : ULift.{uS} (MatTwo ℕ)) •
      ((ULift.up (p ℕ) : ULift.{uS} (MatTwo ℕ)) • f))
        (ULift.up 1) = 0 := lifted_reverse_order.{uA, uS, uM, uN, 0} ℕ
example :
    let w : ULift.{uM} (MatTwo ℕ) → ULift.{uN} (MatTwo ℕ) := natLiftedWrong
    w ((ULift.up (op (q ℕ)) : ULift.{uA} ((MatTwo ℕ)ᵐᵒᵖ)) • ULift.up 1) ≠
      (ULift.up (op (q ℕ)) : ULift.{uA} ((MatTwo ℕ)ᵐᵒᵖ)) • w (ULift.up 1) :=
  lifted_wrong_right.{uA, uM, uN, 0} ℕ

example :
    let f : ULift.{uM} (MatTwo ℤ) →ₗ[ULift.{uA} ((MatTwo ℤ)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo ℤ) := intLiftedId
    f (ULift.up 1) ≠ 0 := lifted_one_ne_zero.{uA, uM, uN, 0} ℤ
example :
    let f : ULift.{uM} (MatTwo ℤ) →ₗ[ULift.{uA} ((MatTwo ℤ)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo ℤ) := intLiftedId
    ((ULift.up (p ℤ) : ULift.{uS} (MatTwo ℤ)) • f)
      (ULift.up (q ℤ)) = ULift.up (q ℤ) := lifted_left_at_q.{uA, uS, uM, uN, 0} ℤ
example : (ULift.up (q ℤ) : ULift.{uN} (MatTwo ℤ)) ≠ 0 := lifted_q_ne_zero ℤ
example :
    let f : ULift.{uM} (MatTwo ℤ) →ₗ[ULift.{uA} ((MatTwo ℤ)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo ℤ) := intLiftedId
    ((ULift.up (p ℤ) : ULift.{uS} (MatTwo ℤ)) •
      ((ULift.up (q ℤ) : ULift.{uS} (MatTwo ℤ)) • f))
        (ULift.up 1) = ULift.up (q ℤ) := lifted_left_order.{uA, uS, uM, uN, 0} ℤ
example :
    let f : ULift.{uM} (MatTwo ℤ) →ₗ[ULift.{uA} ((MatTwo ℤ)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo ℤ) := intLiftedId
    ((ULift.up (q ℤ) : ULift.{uS} (MatTwo ℤ)) •
      ((ULift.up (p ℤ) : ULift.{uS} (MatTwo ℤ)) • f))
        (ULift.up 1) = 0 := lifted_reverse_order.{uA, uS, uM, uN, 0} ℤ
example :
    let w : ULift.{uM} (MatTwo ℤ) → ULift.{uN} (MatTwo ℤ) := intLiftedWrong
    w ((ULift.up (op (q ℤ)) : ULift.{uA} ((MatTwo ℤ)ᵐᵒᵖ)) • ULift.up 1) ≠
      (ULift.up (op (q ℤ)) : ULift.{uA} ((MatTwo ℤ)ᵐᵒᵖ)) • w (ULift.up 1) :=
  lifted_wrong_right.{uA, uM, uN, 0} ℤ

example :
    let f : ULift.{uM} (MatTwo ℕ) →ₗ[ULift.{uA} ((MatTwo ℕ)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo ℕ) := natLiftedId
    ((ULift.up (p ℕ) : ULift.{uS} (MatTwo ℕ)) • f) (ULift.up 1) ≠
      f (ULift.up 1) := lifted_moves.{uA, uS, uM, uN, 0} ℕ
example :
    let w : ULift.{uM} (MatTwo ℕ) → ULift.{uN} (MatTwo ℕ) := natLiftedWrong
    w (ULift.up (q ℕ)) = 0 := lifted_wrong_at_q ℕ
example :
    let f : ULift.{uM} (MatTwo ℤ) →ₗ[ULift.{uA} ((MatTwo ℤ)ᵐᵒᵖ)]
      ULift.{uN} (MatTwo ℤ) := intLiftedId
    ((ULift.up (p ℤ) : ULift.{uS} (MatTwo ℤ)) • f) (ULift.up 1) ≠
      f (ULift.up 1) := lifted_moves.{uA, uS, uM, uN, 0} ℤ
example :
    let w : ULift.{uM} (MatTwo ℤ) → ULift.{uN} (MatTwo ℤ) := intLiftedWrong
    w (ULift.up (q ℤ)) = 0 := lifted_wrong_at_q ℤ

end MatrixLifts

/-! ## Quotient-source boundary model

Here the specified source action factors through `ZMod 4 → ZMod 2`.
The freeness instance above requires a finite *free* source; the canonical
finiteness instance requires only a finite *projective* source. This source
is not free because its specified action is unfaithful: nonzero `2` acts as
zero on every source element. This nonfreeness argument does not establish
nonprojectivity. In contrast, the target `ZMod 4` with its regular action is
free and finite.

The function `x ↦ 2 * x.val` descends to a linear map for this same source
action, with nonzero value `2` at `1`. Every such linear map is annihilated by
`2`, since the source is annihilated by `2`. Thus the linear-map module is
nontrivial but not free over `ZMod 4`. Both nonfreeness arguments use Mathlib's
faithful-action instance for nontrivial free modules in
`Mathlib.LinearAlgebra.FreeModule.Basic`; no freeness of the source is assumed.
-/

private def quotientScalars : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)

section QuotientSource

private local instance : Module (ZMod 4) (ZMod 2) := Module.compHom (ZMod 2) quotientScalars

private lemma quotient_smul_eq (r : ZMod 4) (x : ZMod 2) :
    r • x = quotientScalars r * x := by
  rfl

example : Module.Finite (ZMod 4) (ZMod 2) := Module.Finite.of_finite
example (r : ZMod 4) (x : ZMod 2) : r • x = quotientScalars r * x := quotient_smul_eq r x
example : quotientScalars 2 = 0 := by decide
example : (2 : ZMod 4) • (1 : ZMod 2) = 0 := by
  rw [quotient_smul_eq]
  decide
example : (2 : ZMod 4) ≠ 0 := by decide
example : (2 : ZMod 4) * 2 = 0 := by decide

private lemma quotient_two_smul_eq_zero (x : ZMod 2) : (2 : ZMod 4) • x = 0 := by
  rw [quotient_smul_eq, show quotientScalars 2 = 0 by decide, zero_mul]

private lemma quotient_source_not_faithful : ¬ FaithfulSMul (ZMod 4) (ZMod 2) := by
  intro h
  let : FaithfulSMul (ZMod 4) (ZMod 2) := h
  have hzero : (2 : ZMod 4) = 0 :=
    eq_of_smul_eq_smul fun x : ZMod 2 => by
      rw [quotient_two_smul_eq_zero, zero_smul]
  exact (show (2 : ZMod 4) ≠ 0 by decide) hzero

example : ¬ Module.Free (ZMod 4) (ZMod 2) := by
  intro h
  let : Module.Free (ZMod 4) (ZMod 2) := h
  exact quotient_source_not_faithful inferInstance

example : Module.Free (ZMod 4) (ZMod 4) := inferInstance
example : Module.Finite (ZMod 4) (ZMod 4) := inferInstance

private def quotientDescended : ZMod 2 →ₗ[ZMod 4] ZMod 4 where
  toFun x := (2 : ZMod 4) * (x.val : ZMod 4)
  map_add' := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide
  map_smul' := by
    intro r x
    rw [quotient_smul_eq]
    fin_cases r <;> fin_cases x <;> decide

private lemma quotientDescended_one : quotientDescended 1 = (2 : ZMod 4) := by
  decide

private lemma quotientDescended_ne_zero : quotientDescended ≠ 0 := by
  intro h
  have htwo : (2 : ZMod 4) = 0 := by
    simpa only [quotientDescended_one, LinearMap.zero_apply] using
      congrArg (fun f : ZMod 2 →ₗ[ZMod 4] ZMod 4 => f 1) h
  exact (show (2 : ZMod 4) ≠ 0 by decide) htwo

example : ∃ f : ZMod 2 →ₗ[ZMod 4] ZMod 4, f 1 = 2 ∧ f ≠ 0 :=
  ⟨quotientDescended, quotientDescended_one, quotientDescended_ne_zero⟩

private lemma quotient_hom_two_smul_eq_zero (f : ZMod 2 →ₗ[ZMod 4] ZMod 4) :
    (2 : ZMod 4) • f = 0 := by
  ext x
  rw [LinearMap.smul_apply, LinearMap.zero_apply, ← f.map_smul,
    quotient_two_smul_eq_zero, f.map_zero]

example (f : ZMod 2 →ₗ[ZMod 4] ZMod 4) : (2 : ZMod 4) • f = 0 :=
  quotient_hom_two_smul_eq_zero f

private lemma quotient_hom_not_faithful :
    ¬ FaithfulSMul (ZMod 4) (ZMod 2 →ₗ[ZMod 4] ZMod 4) := by
  intro h
  let : FaithfulSMul (ZMod 4) (ZMod 2 →ₗ[ZMod 4] ZMod 4) := h
  have hzero : (2 : ZMod 4) = 0 :=
    eq_of_smul_eq_smul fun f : ZMod 2 →ₗ[ZMod 4] ZMod 4 => by
      rw [quotient_hom_two_smul_eq_zero, zero_smul]
  exact (show (2 : ZMod 4) ≠ 0 by decide) hzero

example : ¬ Module.Free (ZMod 4) (ZMod 2 →ₗ[ZMod 4] ZMod 4) := by
  intro h
  let : Module.Free (ZMod 4) (ZMod 2 →ₗ[ZMod 4] ZMod 4) := h
  let : Nontrivial (ZMod 2 →ₗ[ZMod 4] ZMod 4) :=
    ⟨⟨quotientDescended, 0, quotientDescended_ne_zero⟩⟩
  exact quotient_hom_not_faithful inferInstance

end QuotientSource

end ProjectiveModulesTests.LinearMapClient
