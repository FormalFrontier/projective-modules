/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Injective
public import ProjectiveModules.Module.ProjectiveComplement

/-!
# Injectivity of finite projective modules

A finite projective module over a left self-injective ring is injective. The
proof realizes the module as a retract of a finite standard free module,
extends maps into each scalar coordinate, and composes with the retraction.

The scalar and carrier universes are independent. Coordinate maps take values
in `R`, so their extension uses smallness of `R` in its own universe, not a
smallness assumption on `R` in the carrier universe.

## References

* Mathlib's injective-module formalization by Jujian Zhang, for injectivity of
  products and the extension property across independent carrier universes.
* `ProjectiveModules.Module.ProjectiveComplement`, for the kernel-product
  equivalence associated with a surjection onto a projective module.
-/

@[expose] public section

universe uR uP

namespace Module

/-- Every finite projective module over a left self-injective ring is injective. -/
theorem injective_of_finite_projective
    (R : Type uR) [Ring R] (P : Type uP) [AddCommGroup P] [Module R P]
    [Module.Injective R R] [Module.Finite R P] [Module.Projective R P] :
    Module.Injective R P := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  let s : P →ₗ[R] (Fin n → R) :=
    (Module.Projective.prodKerEquivOfSurjective f hf).toLinearMap.comp
      (LinearMap.inl R P (LinearMap.ker f))
  have hs (p : P) : f (s p) = p :=
    Module.Projective.prodKerEquivOfSurjective_apply_fst f hf p 0
  refine ⟨?_⟩
  intro X Y _ _ _ _ i hi g
  -- The finite free target has universe uR, where R is automatically small.
  -- Mathlib's product instance therefore supplies its injectivity.
  obtain ⟨l, hl⟩ :=
    Module.Injective.extension_property R (Fin n → R) X Y i hi (s.comp g)
  refine ⟨f.comp l, fun x ↦ ?_⟩
  exact (congrArg f (DFunLike.congr_fun hl x)).trans (hs (g x))

end Module
