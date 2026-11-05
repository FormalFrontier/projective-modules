/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Dual.Annihilator

/-!
# Annihilator closure over fields

The projective-quotient theorem recovers
`Subspace.dualAnnihilator_dualCoannihilator_eq` with independent coefficient and
vector-space universes, without a finiteness assumption.
-/

@[expose] public section

universe u v

example (K : Type u) [Field K] (V : Type v) [AddCommGroup V] [Module K V]
    (p : Submodule K V) : p.dualAnnihilator.dualCoannihilator = p := by
  exact Submodule.dualAnnihilator_dualCoannihilator_eq_of_projective_quotient p

/-- The packaged correspondence recovers reversed inclusion for vector-space
subobjects, with the quotient-projectivity witnesses supplied automatically. -/
example (K : Type u) [Field K] (V : Type v) [AddCommGroup V] [Module K V]
    [Module.Finite K V] (p q : Submodule K V) :
    q.dualAnnihilator ≤ p.dualAnnihilator ↔ p ≤ q := by
  let p' : {p : Submodule K V // Module.Projective K (V ⧸ p)} :=
    ⟨p, inferInstance⟩
  let q' : {q : Submodule K V // Module.Projective K (V ⧸ q)} :=
    ⟨q, inferInstance⟩
  have h := (Submodule.dualAnnihilatorOrderIso K V).le_iff_le (x := p') (y := q')
  change (Submodule.dualAnnihilatorOrderIso K V q').1 ≤
    (Submodule.dualAnnihilatorOrderIso K V p').1 ↔ p ≤ q at h
  simpa only [Submodule.dualAnnihilatorOrderIso_apply] using h
