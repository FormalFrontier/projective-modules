/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective
public import ProjectiveModules.Module.KernelComparison

/-!
# Kernel comparison for projective presentations

Two surjective linear maps from projective modules to the same semimodule have
stably isomorphic kernels: the kernel of either map, multiplied by the source of
the other, is linearly equivalent to the corresponding product in the opposite
order. This is Schanuel's lemma.

The source modules have additive inverses, while the common target needs only an
additive commutative monoid. Projectivity supplies lifts in both directions, and
`LinearMap.kerProdEquivOfLifts` compares the two kernels. The conclusion is stated
as `Nonempty`, without selecting lifts or a distinguished equivalence.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory* (2013),
  Schanuel's lemma.
* Mathlib, `Mathlib.Algebra.Module.Projective` (the projective lifting property).
-/

@[expose] public section

universe uR uP uQ uM

namespace LinearMap

variable {R : Type uR} [Semiring R]
variable {P : Type uP} [AddCommGroup P] [Module R P]
variable {Q : Type uQ} [AddCommGroup Q] [Module R Q]
variable {M : Type uM} [AddCommMonoid M] [Module R M]

/-- Schanuel's lemma: two surjections from projective modules to a common
semimodule have linearly equivalent products of their kernels with the other
source module. Projectivity of `Q` lifts `q` through `p`, and projectivity of `P`
lifts `p` through `q`; the target requires no additive inverses.

See Weibel, *The K-book* (2013), Schanuel's lemma. -/
theorem nonempty_kerProdEquiv_of_surjective [Module.Projective R P] [Module.Projective R Q]
    (p : P →ₗ[R] M) (q : Q →ₗ[R] M)
    (hp : Function.Surjective p) (hq : Function.Surjective q) :
    Nonempty ((p.ker × Q) ≃ₗ[R] (q.ker × P)) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p q hp
  obtain ⟨t, ht⟩ := Module.projective_lifting_property q p hq
  exact ⟨kerProdEquivOfLifts p q s t hs ht⟩

end LinearMap
