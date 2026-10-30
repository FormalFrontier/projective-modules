/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import ProjectiveModules.Module.KernelComparison
public import ProjectiveModules.Module.KernelCoprod

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
* Mathlib, `Mathlib.RingTheory.Finiteness.Basic` and
  `Mathlib.RingTheory.Finiteness.Prod` (finite generation and products).
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

/-- For two surjections from projective modules to the same semimodule, the second
kernel is finitely generated whenever the first kernel and the second source
are finitely generated. -/
theorem finite_ker_of_surjective_of_finite_ker
    [Module.Projective R P] [Module.Projective R Q]
    (p : P →ₗ[R] M) (q : Q →ₗ[R] M)
    [Module.Finite R p.ker] [Module.Finite R Q]
    (hp : Function.Surjective p) (hq : Function.Surjective q) :
    Module.Finite R q.ker := by
  obtain ⟨e⟩ := nonempty_kerProdEquiv_of_surjective p q hp hq
  let : Module.Finite R (q.ker × P) := Module.Finite.equiv e
  exact Module.Finite.of_surjective (fst R q.ker P) fst_surjective

/-- For two surjections from projective modules to the same semimodule, the second
kernel is projective whenever the first kernel is projective. -/
theorem projective_ker_of_surjective_of_projective_ker
    [Module.Projective R P] [Module.Projective R Q]
    (p : P →ₗ[R] M) (q : Q →ₗ[R] M)
    [Module.Projective R p.ker]
    (hp : Function.Surjective p) (hq : Function.Surjective q) :
    Module.Projective R q.ker := by
  obtain ⟨e⟩ := nonempty_kerProdEquiv_of_surjective p q hp hq
  let : Module.Projective R (q.ker × P) := Module.Projective.of_equiv' e
  exact Module.Projective.of_split (inl R q.ker P) (fst R q.ker P)
    (fst_comp_inl R q.ker P)

end LinearMap
