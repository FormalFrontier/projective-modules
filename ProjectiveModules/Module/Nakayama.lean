/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import Mathlib.RingTheory.Nakayama

/-!
# Submodules with finitely generated quotients

Nakayama's lemma applies to the inherited quotient by a submodule. Consequently,
a submodule is the whole module if that quotient is finitely generated and the
submodule, together with the action of an ideal in the Jacobson radical, generates
the module. The ideal need only be a left ideal; the module need not be finite.
-/

@[expose] public section

universe uA uN
open scoped Pointwise

/-- A submodule with finitely generated quotient is the whole module if it and the
action of a left ideal contained in the Jacobson radical generate the module. -/
theorem Submodule.eq_top_of_finite_quotient_of_sup_smul_eq_top
    {A : Type uA} [Ring A]
    {N : Type uN} [AddCommGroup N] [Module A N]
    (P : Submodule A N) [Module.Finite A (N ⧸ P)]
    (J : Ideal A) (hJ : J ≤ Ideal.jacobson (⊥ : Ideal A))
    (hgen : P ⊔ J • (⊤ : Submodule A N) = ⊤) :
    P = ⊤ := by
  let π : N →ₗ[A] N ⧸ P := P.mkQ
  let T : Submodule A (N ⧸ P) := ⊤
  have hT : T.FG := Module.Finite.fg_top
  have hsup : P ⊔ J • (⊤ : Submodule A N) ≤
      ((Ideal.jacobson (⊥ : Ideal A)) • T).comap π := by
    refine sup_le ?_ ?_
    · intro x hx
      change π x ∈ (Ideal.jacobson (⊥ : Ideal A)) • T
      have hxzero : π x = 0 := by
        change (Submodule.Quotient.mk x : N ⧸ P) = 0
        simpa only [Submodule.Quotient.mk_eq_zero] using hx
      rw [hxzero]
      exact ((Ideal.jacobson (⊥ : Ideal A)) • T).zero_mem
    · apply Submodule.smul_le.mpr
      intro r hr x hx
      change π (r • x) ∈ (Ideal.jacobson (⊥ : Ideal A)) • T
      rw [π.map_smul]
      exact Submodule.smul_mem_smul (hJ hr) (show π x ∈ T from trivial)
  have hTgen : T ≤ (Ideal.jacobson (⊥ : Ideal A)) • T := by
    intro y _
    induction y using Submodule.Quotient.induction_on with
    | _ x =>
        have hx : x ∈ P ⊔ J • (⊤ : Submodule A N) := by
          rw [hgen]
          trivial
        exact hsup hx
  have hTzero : T = ⊥ := by
    apply hT.eq_bot_of_le_jacobson_smul
    simpa only [Ideal.jacobson_bot] using hTgen
  apply top_unique
  intro x _
  have hxT : π x ∈ T := by trivial
  have hxzero : π x = 0 := by
    simpa only [hTzero, Submodule.mem_bot] using hxT
  change (Submodule.Quotient.mk x : N ⧸ P) = 0 at hxzero
  simpa only [Submodule.Quotient.mk_eq_zero] using hxzero
