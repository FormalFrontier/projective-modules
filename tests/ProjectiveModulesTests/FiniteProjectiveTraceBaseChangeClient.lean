/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.Trace.BaseChange
import ProjectiveModules.Module.Trace.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.NormNum

/-!
# Reduction of an integer diagonal endomorphism

The integer module `ℤ × ℤ` carries the diagonal endomorphism with entries 2 and 3,
whose contraction trace is 5. Reducing coefficients modulo 2 gives its canonical
scalar extension on `(ZMod 2) ⊗[ℤ] (ℤ × ℤ)`. The finite-projective scalar-extension
trace law computes the target trace as 1, retaining the original module and
tensor-product carriers. The source calculation uses the product and rank-one
trace formulas; the zero-map boundary uses only trace linearity.

## References

The tensor product and scalar extension are from Mathlib. The rank-one and
product trace formulas are from `ProjectiveModules.Module.Trace.Basic` and
`ProjectiveModules.Module.Trace.Prod`; scalar-extension naturality is from
`ProjectiveModules.Module.Trace.BaseChange`.
-/

noncomputable section

open scoped TensorProduct

namespace ProjectiveModulesTests

private def integerDiagonal : (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ) :=
  LinearMap.prodMap
    ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).smulRight 2)
    ((LinearMap.id : ℤ →ₗ[ℤ] ℤ).smulRight 3)

private def reducedDiagonal :
    ((ZMod 2) ⊗[ℤ] (ℤ × ℤ)) →ₗ[ZMod 2] ((ZMod 2) ⊗[ℤ] (ℤ × ℤ)) :=
  integerDiagonal.baseChange (ZMod 2)

private theorem integerDiagonal_trace :
    LinearMap.traceOfFiniteProjective ℤ (ℤ × ℤ) integerDiagonal = 5 := by
  norm_num [integerDiagonal, LinearMap.traceOfFiniteProjective_prodMap,
    LinearMap.traceOfFiniteProjective_smulRight, LinearMap.id_apply]

example : LinearMap.traceOfFiniteProjective (ZMod 2) ((ZMod 2) ⊗[ℤ] (ℤ × ℤ))
    reducedDiagonal = 1 := by
  calc
    LinearMap.traceOfFiniteProjective (ZMod 2) ((ZMod 2) ⊗[ℤ] (ℤ × ℤ)) reducedDiagonal =
        algebraMap ℤ (ZMod 2) (LinearMap.traceOfFiniteProjective ℤ (ℤ × ℤ) integerDiagonal) :=
      LinearMap.traceOfFiniteProjective_baseChange ℤ (ZMod 2) (ℤ × ℤ) integerDiagonal
    _ = 1 := by
      simpa [integerDiagonal_trace] using
        (ZMod.intCast_eq_intCast_iff' 5 1 2).2 (by norm_num)

example : LinearMap.traceOfFiniteProjective (ZMod 2) ((ZMod 2) ⊗[ℤ] (ℤ × ℤ))
    (0 : ((ZMod 2) ⊗[ℤ] (ℤ × ℤ)) →ₗ[ZMod 2] ((ZMod 2) ⊗[ℤ] (ℤ × ℤ))) = 0 :=
  map_zero (LinearMap.traceOfFiniteProjective (ZMod 2) ((ZMod 2) ⊗[ℤ] (ℤ × ℤ)))

end ProjectiveModulesTests
