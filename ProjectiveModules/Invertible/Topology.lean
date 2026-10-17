/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The module topology of an invertible topological vector space

A Hausdorff invertible topological vector space over a nontrivially normed field has
its module topology. The result concerns the given topology and module structure;
it requires neither completeness of the field nor a norm on the vector space.

An algebraic linear coordinate has zero kernel. Hausdorffness makes this kernel
closed, so Mathlib's closed-kernel continuity theorem applies even over an
incomplete field. The inverse coordinate is continuous by the scalar field's
module topology, and the resulting continuous linear equivalence transports that
property to the original space.

## References

* Mathlib, `RingTheory.PicardGroup`, for invertible modules and their algebraic
  coordinate equivalences.
* Mathlib, `Topology.Algebra.Module.FiniteDimension` and
  `Topology.Algebra.Module.ModuleTopology`, for closed-kernel continuity and
  transport of module topologies.
* Formal Frontier Agents, formalization of the Hausdorff line argument.
-/

@[expose] public section

universe uκ uE

noncomputable section

namespace Module.Invertible

/-- A Hausdorff invertible topological module over a nontrivially normed field carries
the module topology on its given topological space. -/
theorem isModuleTopology (κ : Type uκ) [NontriviallyNormedField κ]
    (E : Type uE) [AddCommGroup E] [Module κ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul κ E] [T2Space E] [Module.Invertible κ E] :
    IsModuleTopology κ E := by
  let e : E ≃ₗ[κ] κ :=
    ((Module.Invertible.free_iff_linearEquiv (R := κ) (M := E)).mp inferInstance).some
  have hker : LinearMap.ker e.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr e.injective
  have he : Continuous e := e.toLinearMap.continuous_of_isClosed_ker (by
    simpa only [hker, Submodule.bot_coe] using
      (isClosed_singleton : IsClosed ({(0 : E)} : Set E)))
  let eL : E ≃L[κ] κ :=
    { toLinearEquiv := e
      continuous_toFun := he
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  exact IsModuleTopology.iso eL.symm

end Module.Invertible
