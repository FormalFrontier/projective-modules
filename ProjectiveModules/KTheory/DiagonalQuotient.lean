/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.ShortExact
public import ProjectiveModules.Module.DiagonalQuotientSplitting

/-!
# Diagonal-quotient additivity in K₀

For right-linear maps `f : X →ₗ[Rᵐᵒᵖ] M` and `g : X →ₗ[Rᵐᵒᵖ] N`,
`KTheory.K0.of_diagonalQuotient` identifies the diagonal quotient's class with the
sum of the classes of `X ⧸ (ker f ⊔ ker g)`, `M ⧸ range f`, and `N ⧸ range g`,
in that order. Only these three right modules need be finitely generated and
projective. The diagonal quotient's corresponding properties follow from the
splitting criteria; they are not additional hypotheses.

The proof applies short-exact additivity to the canonical projection onto the
product of cokernels, using the canonical kernel equivalence for its injection.
A second application to the product's left inclusion and second projection
separates the two cokernel classes.

The ring may be noncommutative or zero. Its universe and the universes of the three
input modules are independent, and all quotients retain their given right actions.

## References

* The canonical projection and kernel identification in
  `ProjectiveModules.Module.DiagonalQuotient`.
* The normalized splitting and finiteness and projectivity criteria in
  `ProjectiveModules.Module.DiagonalQuotientSplitting`.
* Right-module short-exact additivity in `ProjectiveModules.KTheory.ShortExact`.
* Mathlib's canonical submodule inclusions, product coordinates, and linear-equivalence
  characteristics.
-/

@[expose] public section

universe uR uX uM uN

namespace KTheory.K0

variable (R : Type uR) [Ring R]
variable {X : Type uX} {M : Type uM} {N : Type uN}
variable [AddCommGroup X] [AddCommGroup M] [AddCommGroup N]
variable [Module Rᵐᵒᵖ X] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ N]

/-- The diagonal quotient's K₀ class equals the sum of the source kernel-sum quotient's
class and the two cokernel classes. Only these three right-hand modules need be finitely
generated and projective. -/
theorem of_diagonalQuotient (f : X →ₗ[Rᵐᵒᵖ] M) (g : X →ₗ[Rᵐᵒᵖ] N)
    [Module.Finite Rᵐᵒᵖ (X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g))]
    [Module.Projective Rᵐᵒᵖ (X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g))]
    [Module.Finite Rᵐᵒᵖ (M ⧸ LinearMap.range f)]
    [Module.Projective Rᵐᵒᵖ (M ⧸ LinearMap.range f)]
    [Module.Finite Rᵐᵒᵖ (N ⧸ LinearMap.range g)]
    [Module.Projective Rᵐᵒᵖ (N ⧸ LinearMap.range g)] :
    @of R _ ((M × N) ⧸ LinearMap.range (f.prod g)) _ _
      ((LinearMap.DiagonalQuotient.finite_iff f g).mpr ⟨inferInstance, inferInstance⟩)
      ((LinearMap.DiagonalQuotient.projective_iff f g).mpr inferInstance) =
    (of R (X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g)) +
      of R (M ⧸ LinearMap.range f)) + of R (N ⧸ LinearMap.range g) := by
  let K := X ⧸ (LinearMap.ker f ⊔ LinearMap.ker g)
  let A := M ⧸ LinearMap.range f
  let B := N ⧸ LinearMap.range g
  let D := (M × N) ⧸ LinearMap.range (f.prod g)
  let : Module.Finite Rᵐᵒᵖ D :=
    (LinearMap.DiagonalQuotient.finite_iff f g).mpr ⟨inferInstance, inferInstance⟩
  let : Module.Projective Rᵐᵒᵖ D :=
    (LinearMap.DiagonalQuotient.projective_iff f g).mpr inferInstance
  let π : D →ₗ[Rᵐᵒᵖ] A × B := LinearMap.DiagonalQuotient.projection f g
  let θ : K ≃ₗ[Rᵐᵒᵖ] LinearMap.ker π :=
    LinearMap.DiagonalQuotient.quotientKerEquiv f g
  let i : K →ₗ[Rᵐᵒᵖ] D := (LinearMap.ker π).subtype.comp (θ : K →ₗ[Rᵐᵒᵖ] LinearMap.ker π)
  have hi : Function.Injective i := by
    intro x y h
    have hθ : θ x = θ y := (LinearMap.ker π).subtype_injective (by
      simpa only [i, LinearMap.comp_apply, LinearEquiv.coe_coe] using h)
    simpa only [LinearEquiv.symm_apply_apply] using congrArg θ.symm hθ
  have hrange : LinearMap.range i = LinearMap.ker π := by
    apply le_antisymm
    · intro z hz
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hz
      simpa only [i, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
        using (θ x).property
    · intro z hz
      refine LinearMap.mem_range.mpr ⟨θ.symm ⟨z, hz⟩, ?_⟩
      have hθ := congrArg (fun w : LinearMap.ker π => (w : D))
        (θ.apply_symm_apply ⟨z, hz⟩)
      simpa only [i, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
        using hθ
  have hD : of R D = of R K + of R (A × B) :=
    of_eq_add_of_exact R K D (A × B) i π hi
      (LinearMap.DiagonalQuotient.projection_surjective f g) hrange
  have hinl : Function.Injective (LinearMap.inl Rᵐᵒᵖ A B) := by
    intro a a' h
    simpa only [LinearMap.inl_apply] using congrArg Prod.fst h
  have hsnd : Function.Surjective (LinearMap.snd Rᵐᵒᵖ A B) :=
    fun b => ⟨(0, b), by simp only [LinearMap.snd_apply]⟩
  have hprod : LinearMap.range (LinearMap.inl Rᵐᵒᵖ A B) =
      LinearMap.ker (LinearMap.snd Rᵐᵒᵖ A B) := by
    apply le_antisymm
    · intro z hz
      obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hz
      exact LinearMap.mem_ker.mpr (by simp only [LinearMap.inl_apply, LinearMap.snd_apply])
    · rintro ⟨a, b⟩ hz
      have hb : b = 0 := by
        simpa only [LinearMap.snd_apply] using LinearMap.mem_ker.mp hz
      subst b
      exact LinearMap.mem_range.mpr ⟨a, by simp only [LinearMap.inl_apply]⟩
  have hAB : of R (A × B) = of R A + of R B :=
    of_eq_add_of_exact R A (A × B) B (LinearMap.inl Rᵐᵒᵖ A B)
      (LinearMap.snd Rᵐᵒᵖ A B) hinl hsnd hprod
  calc
    _ = of R K + of R (A × B) := hD
    _ = of R K + (of R A + of R B) := congrArg (fun c => of R K + c) hAB
    _ = _ := (add_assoc _ _ _).symm

end KTheory.K0
