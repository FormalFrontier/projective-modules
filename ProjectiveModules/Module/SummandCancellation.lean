/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.Group.Monoid

/-!
# Cancellation of a direct summand from a Dedekind-finite endomorphism monoid

If the endomorphism monoid of a semimodule is Dedekind-finite, a product
equivalence from that semimodule to itself times another semimodule forces the
other factor to be trivial. The two factors and the scalars can inhabit
independent universes.

## References

* C. A. Weibel, *The K-book*, Exercises I.1.2–I.1.4 (motivation for the
  finite-free specialization).
* Mathlib, `Mathlib.Algebra.Group.Monoid` (Dedekind-finite monoids) and
  `Mathlib.LinearAlgebra.Prod` (linear product maps).
-/

@[expose] public section

universe uR uM uP

namespace Module.End

/-- A semimodule with a Dedekind-finite endomorphism monoid cannot be
equivalent to itself times a nontrivial semimodule. -/
theorem subsingleton_of_linearEquiv_prod
    (R : Type uR) [Semiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    [IsDedekindFiniteMonoid (Module.End R M)]
    {P : Type uP} [AddCommMonoid P] [Module R P]
    (e : M ≃ₗ[R] (M × P)) : Subsingleton P := by
  let projection : Module.End R M := (LinearMap.fst R M P).comp e.toLinearMap
  let inclusion : Module.End R M := e.symm.toLinearMap.comp (LinearMap.inl R M P)
  have hleft : projection * inclusion = 1 := by
    ext x
    simp [projection, inclusion, Module.End.mul_apply]
  have hright : inclusion * projection = 1 := mul_eq_one_symm hleft
  have hinjective : Function.Injective projection := by
    intro x y hxy
    calc
      x = (inclusion * projection) x := by rw [hright]; rfl
      _ = (inclusion * projection) y := by simp only [Module.End.mul_apply, hxy]
      _ = y := by rw [hright]; rfl
  have hzero (p : P) : p = 0 := by
    let x : M := e.symm (0, p)
    have hx : x = 0 := hinjective (by simp [projection, x])
    have hp : ((0 : M), p) = ((0 : M), (0 : P)) := by
      calc
        (0, p) = e x := by simp [x]
        _ = e (0 : M) := congrArg e hx
        _ = (0, 0) := e.map_zero
    exact congrArg Prod.snd hp
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

end Module.End
