/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Residue rank and base change

The dimension of a maximal fibre after scalar extension agrees with the dimension over the
residue field at the contracted prime. This holds for arbitrary modules and arbitrary algebra
maps: the two fibres differ by extension of their coefficient fields.
-/

@[expose] public section

universe uR uS v

open scoped TensorProduct

namespace Module

/-- Cardinal dimension of a maximal fibre is preserved by base change, after lifting the
cardinals to a common universe. The coefficient field on the right is the residue field at the
contraction of the maximal ideal; the contraction need not itself be maximal. -/
theorem lift_rank_quotient_baseChange
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
    {P : Type v} [AddCommMonoid P] [Module R P]
    (m : Ideal S) [m.IsMaximal] :
    Cardinal.lift.{uR}
        (Module.rank (S ⧸ m) ((S ⧸ m) ⊗[S] (S ⊗[R] P))) =
      Cardinal.lift.{uS}
        (Module.rank (m.under R).ResidueField
          ((m.under R).ResidueField ⊗[R] P)) := by
  let K := S ⧸ m
  let k := (m.under R).ResidueField
  let : Field K := Ideal.Quotient.field m
  let f : R →ₐ[R] K := Algebra.ofId R K
  have hf (r : R) : f r = 0 ↔ r ∈ m.under R := by
    rw [Ideal.mem_under]
    change algebraMap R K r = 0 ↔ algebraMap R S r ∈ m
    rw [← Ideal.Quotient.mk_comp_algebraMap (R₁ := R) m]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hf₁ : m.under R ≤ RingHom.ker f := by
    intro r hr
    change f r = 0
    exact (hf r).mpr hr
  have hf₂ : (m.under R).primeCompl ≤ (IsUnit.submonoid K).comap f := by
    intro r hr
    change IsUnit (f r)
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact hr ((hf r).mp hz)
  -- The canonical residue-field map supplies the intermediate scalar action and tower.
  let β : k →ₐ[R] K := Ideal.ResidueField.liftₐ (m.under R) f hf₁ hf₂
  let : Algebra k K := RingHom.toAlgebra β.toRingHom
  let : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R K r = β (algebraMap R k r)
    exact (congrArg (fun g : R →+* K => g r) β.comp_algebraMap).symm
  have hS :
      Module.rank K (K ⊗[S] (S ⊗[R] P)) = Module.rank K (K ⊗[R] P) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S K K P).rank_eq
  have hk :
      Module.rank K (K ⊗[k] (k ⊗[R] P)) =
        Cardinal.lift.{uR} (Module.rank K (K ⊗[R] P)) := by
    calc
      Module.rank K (K ⊗[k] (k ⊗[R] P)) =
          Cardinal.lift.{max uS v} (Module.rank K (K ⊗[k] (k ⊗[R] P))) :=
        (Cardinal.lift_id'.{max uS v, uR} _).symm
      _ = Cardinal.lift.{max (max uR uS) v} (Module.rank K (K ⊗[R] P)) :=
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R k K K P).lift_rank_eq
      _ = Cardinal.lift.{uR} (Module.rank K (K ⊗[R] P)) :=
        congrFun (Cardinal.lift_umax.{max uS v, uR}) _
  let : AddCommGroup (k ⊗[R] P) := TensorProduct.addCommGroup
  let : Module.Free k (k ⊗[R] P) := Module.Free.of_divisionRing k (k ⊗[R] P)
  calc
    Cardinal.lift.{uR} (Module.rank K (K ⊗[S] (S ⊗[R] P))) =
        Cardinal.lift.{uR} (Module.rank K (K ⊗[R] P)) := congrArg Cardinal.lift hS
    _ = Module.rank K (K ⊗[k] (k ⊗[R] P)) := hk.symm
    _ = Cardinal.lift.{uS} (Module.rank k (k ⊗[R] P)) :=
      Module.rank_baseChange

end Module
