/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# The right regular module on the ordinary carrier

For a semiring `R`, Mathlib gives the ordinary carrier `R` its canonical right
regular action as an `Rᵐᵒᵖ`-module: `op a • x = x * a`. This module is free
and finitely generated, including when `R` is the zero semiring. Projectivity
then follows from Mathlib's existing instance for free modules.

The instances transport the corresponding facts for the left regular module
`Rᵐᵒᵖ` through Mathlib's same-scalar `MulOpposite.opLinearEquiv`. They introduce
neither a new equivalence nor a change of scalar convention. The matrix-kernel
proof in `ProjectiveModules.Free.StableKernel` uses these instances.

## References

* Mathlib's opposite-module equivalence, free-module transfer and finiteness
  transfer APIs.
-/

@[expose] public section

universe u

namespace Module

variable (R : Type u) [Semiring R]

/-- The ordinary carrier of a semiring is free under its canonical right
regular action by the opposite semiring. -/
instance Free.right_regular : Module.Free Rᵐᵒᵖ R :=
  Module.Free.of_equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm

/-- The ordinary carrier of a semiring is finitely generated under its
canonical right regular action by the opposite semiring. -/
instance Finite.right_regular : Module.Finite Rᵐᵒᵖ R :=
  Module.Finite.equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm

end Module
