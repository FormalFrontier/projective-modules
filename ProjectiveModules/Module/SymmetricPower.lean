/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

This file uses Mathlib's TensorPower/Symmetric.lean:
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ProjectiveModules.Module.SymmetricPower.Basic
public import ProjectiveModules.Module.SymmetricPower.Basis
public import ProjectiveModules.Module.SymmetricPower.Quadratic
public import ProjectiveModules.Module.PiTensorProduct

/-!
# Finite generation of symmetric tensor powers

Symmetric tensor powers of finite semimodules are finite, without
projectivity, additive inverses, or an invertibility condition on factorials.
-/

@[expose] public section

open TensorProduct

universe u v

namespace SymmetricPower

variable {R ι : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

instance instModuleFinite [Finite ι] [Module.Finite R M] :
    Module.Finite R (SymmetricPower R ι M) := by
  have : Module.Finite R (⨂[R] (_ : ι), M) := Module.Finite.piTensorProduct
  exact Module.Finite.of_surjective (mk R ι M) AddCon.mk'_surjective

end SymmetricPower
