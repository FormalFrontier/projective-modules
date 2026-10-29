/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

The stock symmetric-algebra API reused here is from Mathlib's
LinearAlgebra/SymmetricAlgebra/Basic.lean and Basis.lean:
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Authors: Raphael Douglas Giles, Zhixuan Dai, Zhenyan Fu, Yiming Fu,
Jingting Wang, Eric Wieser.
The stock projectivity API is from Mathlib's Algebra/Module/Projective.lean:
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Authors: Kevin Buzzard, Antoine Labelle.
These Mathlib files are released under Apache 2.0 as described in their LICENSE.
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-!
# Projectivity of symmetric algebras

The symmetric algebra preserves linear split retractions and hence projective modules.
-/

@[expose] public section

universe u v w z

namespace SymmetricAlgebra

variable {S : Type u} [CommSemiring S]
variable {M : Type v} [AddCommMonoid M] [Module S M]
variable {N : Type w} [AddCommMonoid N] [Module S N]
variable {A : Type z} [CommSemiring A] [Algebra S A]

/-- Lifting a linear composite agrees with composing its algebra lifts. -/
@[simp]
theorem lift_comp_lift (f : M →ₗ[S] N) (g : N →ₗ[S] A) :
    (lift g).comp (lift ((ι S N).comp f)) = lift (g.comp f) := by
  apply algHom_ext
  ext x
  simp

/-- The symmetric algebra preserves a linear split retraction. -/
theorem lift_comp_lift_eq_id (i : M →ₗ[S] N) (r : N →ₗ[S] M)
    (h : r.comp i = LinearMap.id) :
    (lift ((ι S M).comp r)).comp (lift ((ι S N).comp i)) =
      AlgHom.id S (SymmetricAlgebra S M) := by
  rw [lift_comp_lift]
  change lift ((ι S M).comp (r.comp i)) = _
  rw [h]
  change lift (ι S M) = _
  exact lift_ι

/-- Forgetting algebra structure gives a split retraction of the original modules. -/
theorem lift_toLinearMap_comp_eq_id (i : M →ₗ[S] N) (r : N →ₗ[S] M)
    (h : r.comp i = LinearMap.id) :
    (lift ((ι S M).comp r)).toLinearMap.comp
        (lift ((ι S N).comp i)).toLinearMap = LinearMap.id :=
  congrArg AlgHom.toLinearMap (lift_comp_lift_eq_id i r h)

/-- The whole symmetric algebra of a projective module is projective. -/
instance instModuleProjective [Module.Projective S M] :
    Module.Projective S (SymmetricAlgebra S M) := by
  obtain ⟨F, hF, mF, freeF, i, r, h⟩ :=
    (Module.Projective.iff_split (R := S) (P := M)).mp
      (inferInstance : Module.Projective S M)
  let : AddCommMonoid F := hF
  let : Module S F := mF
  have : Module.Free S F := freeF
  exact Module.Projective.of_split
    (lift ((ι S F).comp i)).toLinearMap
    (lift ((ι S M).comp r)).toLinearMap
    (lift_toLinearMap_comp_eq_id i r h)

end SymmetricAlgebra
