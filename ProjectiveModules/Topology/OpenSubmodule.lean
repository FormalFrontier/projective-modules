/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.HomContinuity
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Continuous extension from open submodules

A linear map on a module with separately continuous addition is continuous if its restriction
to an open submodule is continuous. Consequently, a continuous linear map from an open submodule
to a module satisfying Baer's criterion extends to the ambient module.

`ContinuousLinearMap.extendOfBaer` keeps the linear map selected by
`Module.Baer.extension_property` and supplies its continuity certificate. Its restriction is the
given map, but the selection is noncanonical: no uniqueness or linearity of the selection is
asserted. Restriction is surjective as a function, without a module structure on spaces of
continuous linear maps.

The ring and the two modules have independent universes. All actions and topologies are the
given ones, and submodules carry their induced topologies. No topology on the scalar ring or
continuity of scalar multiplication is required.

## References

The algebraic extension uses Mathlib's formalization of Baer's criterion by Jujian Zhang.
The continuity argument uses the additive homomorphism criterion in
`GroupTheory.Topology.HomContinuity`, together with Mathlib's linear-map, submodule and
continuous-linear-map interfaces.
-/

@[expose] public section

universe uR uM uN

namespace LinearMap

section Semiring

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M]
variable {N : Type uN} [AddCommMonoid N] [Module R N] [TopologicalSpace N]
variable [SeparatelyContinuousAdd M] [SeparatelyContinuousAdd N]

/-- A linear map is continuous if and only if its restriction to an open submodule is continuous.
The submodule need not be closed under negation. -/
theorem continuous_iff_continuous_domRestrict_of_isOpen (g : M →ₗ[R] N)
    (S : Submodule R M) (hS : IsOpen (S : Set M)) :
    Continuous g ↔ Continuous (g.domRestrict S) := by
  exact continuous_iff_continuous_domRestrict_of_isOpen_of_zero_mem g hS S.zero_mem

end Semiring

end LinearMap

namespace ContinuousLinearMap

section Ring

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M]
variable {N : Type uN} [AddCommGroup N] [Module R N] [TopologicalSpace N]
variable [SeparatelyContinuousAdd M] [SeparatelyContinuousAdd N]

/-- Extend a continuous linear map from an open submodule to a target satisfying Baer's criterion.
The underlying linear map is exactly the choice from `Module.Baer.extension_property`; only its
continuity certificate is added. -/
noncomputable def extendOfBaer (hN : Module.Baer R N) (S : Submodule R M)
    (hS : IsOpen (S : Set M)) (f : S →L[R] N) : M →L[R] N where
  toLinearMap := Classical.choose
    (Module.Baer.extension_property hN S.subtype S.subtype_injective f.toLinearMap)
  cont := by
    apply (LinearMap.continuous_iff_continuous_domRestrict_of_isOpen
      (Classical.choose
        (Module.Baer.extension_property hN S.subtype S.subtype_injective f.toLinearMap)) S hS).2
    have hg : LinearMap.domRestrict
        (Classical.choose
          (Module.Baer.extension_property hN S.subtype S.subtype_injective f.toLinearMap)) S =
        f.toLinearMap :=
      Classical.choose_spec
        (Module.Baer.extension_property hN S.subtype S.subtype_injective f.toLinearMap)
    rw [hg]
    exact f.continuous_toLinearMap

/-- The extension retains the exact linear map selected by Baer's extension property. -/
theorem toLinearMap_extendOfBaer (hN : Module.Baer R N) (S : Submodule R M)
    (hS : IsOpen (S : Set M)) (f : S →L[R] N) :
    (extendOfBaer hN S hS f).toLinearMap = Classical.choose
      (Module.Baer.extension_property hN S.subtype S.subtype_injective f.toLinearMap) :=
  rfl

/-- The value at every ambient point is the value of that same selected linear map. -/
theorem extendOfBaer_apply (hN : Module.Baer R N) (S : Submodule R M)
    (hS : IsOpen (S : Set M)) (f : S →L[R] N) (x : M) :
    extendOfBaer hN S hS f x = (Classical.choose
      (Module.Baer.extension_property hN S.subtype S.subtype_injective f.toLinearMap)) x :=
  rfl

/-- Algebraic restriction of the extension recovers the original linear map. -/
@[simp]
theorem domRestrict_toLinearMap_extendOfBaer (hN : Module.Baer R N) (S : Submodule R M)
    (hS : IsOpen (S : Set M)) (f : S →L[R] N) :
    (extendOfBaer hN S hS f).toLinearMap.domRestrict S = f.toLinearMap := by
  rw [toLinearMap_extendOfBaer]
  exact Classical.choose_spec
    (Module.Baer.extension_property hN S.subtype S.subtype_injective f.toLinearMap)

/-- The extension agrees with the original map at every point of the submodule. -/
@[simp]
theorem extendOfBaer_apply_coe (hN : Module.Baer R N) (S : Submodule R M)
    (hS : IsOpen (S : Set M)) (f : S →L[R] N) (s : S) :
    extendOfBaer hN S hS f (s : M) = f s :=
  DFunLike.congr_fun (domRestrict_toLinearMap_extendOfBaer hN S hS f) s

/-- A membership proof gives the pointwise restriction law without unfolding the extension. -/
theorem extendOfBaer_apply_of_mem (hN : Module.Baer R N) (S : Submodule R M)
    (hS : IsOpen (S : Set M)) (f : S →L[R] N) (x : M) (hx : x ∈ S) :
    extendOfBaer hN S hS f x = f ⟨x, hx⟩ :=
  extendOfBaer_apply_coe hN S hS f ⟨x, hx⟩

/-- Restricting the continuous extension along the original inclusion recovers the given map. -/
@[simp]
theorem extendOfBaer_comp_subtypeL (hN : Module.Baer R N) (S : Submodule R M)
    (hS : IsOpen (S : Set M)) (f : S →L[R] N) :
    (extendOfBaer hN S hS f).comp S.subtypeL = f := by
  apply ContinuousLinearMap.coe_injective
  exact domRestrict_toLinearMap_extendOfBaer hN S hS f

/-- A continuous linear map from an open submodule to a Baer module has a continuous linear
extension to the ambient module, using the given actions and topologies. -/
theorem exists_extension_of_baer (hN : Module.Baer R N) (S : Submodule R M)
    (hS : IsOpen (S : Set M)) (f : S →L[R] N) :
    ∃ g : M →L[R] N, g.comp S.subtypeL = f :=
  ⟨extendOfBaer hN S hS f, extendOfBaer_comp_subtypeL hN S hS f⟩

/-- Canonical restriction to an open submodule is surjective when the target satisfies Baer's
criterion. This is surjectivity of a function, not of a bundled linear map between Hom spaces. -/
theorem comp_subtypeL_surjective_of_baer (hN : Module.Baer R N) (S : Submodule R M)
    (hS : IsOpen (S : Set M)) :
    Function.Surjective (fun g : M →L[R] N => g.comp S.subtypeL) := by
  intro f
  exact exists_extension_of_baer hN S hS f

end Ring

end ContinuousLinearMap
