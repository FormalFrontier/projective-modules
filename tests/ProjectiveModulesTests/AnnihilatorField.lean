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
