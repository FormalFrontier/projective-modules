/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.LocallyConstantRank

/-!
# Complementary idempotent span coordinates

The generic application and projection rules simplify the four coordinate
formulas for complementary idempotent left ideals over an arbitrary ring.
-/

universe u

variable {R : Type u} [Ring R] {e : R}

example (he : IsIdempotentElem e) (x : Ideal.span {e}) :
    he.spanProdEquiv (x, 0) = (x : R) := by simp

example (he : IsIdempotentElem e) (x : Ideal.span {1 - e}) :
    he.spanProdEquiv (0, x) = (x : R) := by simp

example (he : IsIdempotentElem e) (r : R) :
    ((he.spanProdEquiv.symm r).1 : R) = r * e := by simp

example (he : IsIdempotentElem e) (r : R) :
    ((he.spanProdEquiv.symm r).2 : R) = r * (1 - e) := by simp
