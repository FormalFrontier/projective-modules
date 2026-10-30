/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.NatInt

/-!
# Finite presentation criteria for ring modules

The finite-generation and quotient criteria for finitely presented modules apply
when the underlying additive structures are commutative monoids. Over a ring,
these structures already determine additive inverses.

## Main results

* `Module.FinitePresentation.finite_ker`: a surjection from a finite module to a
  finitely presented module has finite kernel.
* `LinearMap.finitePresentation_of_surjective`: a quotient of a finitely presented
  module by a finitely generated kernel is finitely presented.

## Implementation notes

The additive group structures are introduced only inside the proofs, on the same
carriers and with the original addition and scalar multiplication. The criteria
then follow from Mathlib's additive-group versions.

## References

* Mathlib, `Mathlib.Algebra.Module.FinitePresentation` (finite presentation criteria).
* Mathlib, `Mathlib.Algebra.Module.NatInt` (the additive group structure of a module
  over a ring).
-/

@[expose] public section

universe u w v

section AddCommMonoid

variable {S : Type u} [Ring S]
variable {P : Type w} [AddCommMonoid P] [Module S P]
variable {M : Type v} [AddCommMonoid M] [Module S M]

/-- A surjection from a finite module to a finitely presented module over a ring
has finite kernel. This extends `Module.FinitePresentation.fg_ker` to modules
whose additive structures are stated as commutative monoids. -/
theorem Module.FinitePresentation.finite_ker
    [Module.Finite S P] [Module.FinitePresentation S M]
    (p : P →ₗ[S] M) (hp : Function.Surjective p) : Module.Finite S p.ker := by
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup S
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup S
  exact Module.Finite.of_fg (Module.FinitePresentation.fg_ker p hp)

/-- A surjective image of a finitely presented module over a ring is finitely
presented if its kernel is finitely generated. This extends
`Module.finitePresentation_of_surjective` to modules whose additive structures
are stated as commutative monoids. -/
theorem LinearMap.finitePresentation_of_surjective
    [Module.FinitePresentation S P]
    (p : P →ₗ[S] M) (hp : Function.Surjective p) (hker : p.ker.FG) :
    Module.FinitePresentation S M := by
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup S
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup S
  exact Module.finitePresentation_of_surjective p hp hker

end AddCommMonoid

section AddCommGroup

variable {S : Type u} [Ring S]
variable {P : Type w} [AddCommGroup P] [Module S P]
variable {M : Type v} [AddCommGroup M] [Module S M]

-- Under additive-group hypotheses, the certificates agree with Mathlib's.
private theorem finite_ker_eq_of_fg
    [Module.Finite S P] [Module.FinitePresentation S M]
    (p : P →ₗ[S] M) (hp : Function.Surjective p) :
    Module.FinitePresentation.finite_ker p hp =
      Module.Finite.of_fg (Module.FinitePresentation.fg_ker p hp) :=
  Subsingleton.elim _ _

private theorem finitePresentation_of_surjective_eq
    [Module.FinitePresentation S P]
    (p : P →ₗ[S] M) (hp : Function.Surjective p) (hker : p.ker.FG) :
    LinearMap.finitePresentation_of_surjective p hp hker =
      Module.finitePresentation_of_surjective p hp hker :=
  Subsingleton.elim _ _

end AddCommGroup
