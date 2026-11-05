module

public import ProjectiveModules.Dual.TensorProduct
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Dual annihilators of submodules

A projective quotient splits the inclusion of a submodule. For a finite projective
ambient module, this makes the quotient of its dual by the annihilator projective.
Projectivity of the original quotient alone also implies double annihilator closure.

## References

The double-annihilator theorem generalizes
`Subspace.dualAnnihilator_dualCoannihilator_eq` from
`Mathlib.LinearAlgebra.Dual.Lemmas`: a projective quotient replaces the field
hypothesis. The argument uses `Module.forall_dual_apply_eq_zero_iff`, the
projective-module separation theorem from the same module.
-/

@[expose] public section

universe u v

namespace Submodule

section Ring

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

private theorem exists_retraction_of_projective_quotient (p : Submodule R M)
    [Module.Projective R (M ⧸ p)] :
    ∃ r : M →ₗ[R] p, r.comp p.subtype = LinearMap.id := by
  have hq : Function.Surjective p.mkQ := p.mkQ_surjective
  obtain ⟨s, hs⟩ :=
    Module.projective_lifting_property p.mkQ LinearMap.id hq
  have hright : Function.RightInverse s p.mkQ := by
    intro x
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun hs x
  have hker : LinearMap.ker p.mkQ = p := Submodule.ker_mkQ p
  let t : M →ₗ[R] M := LinearMap.id - s.comp p.mkQ
  have hmem : ∀ x : M, t x ∈ p := by
    intro x
    have hk : t x ∈ LinearMap.ker p.mkQ := by
      change p.mkQ (x - s (p.mkQ x)) = 0
      rw [map_sub, hright, sub_self]
    simpa only [hker] using hk
  let r : M →ₗ[R] p := t.codRestrict p hmem
  refine ⟨r, ?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (x : M) - s (p.mkQ (x : M)) = (x : M)
  have hx : p.mkQ (x : M) = 0 := by
    change (x : M) ∈ LinearMap.ker p.mkQ
    rw [hker]
    exact x.property
  simp only [hx, map_zero, sub_zero]

end Ring

section CommRing

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- If a submodule has projective quotient in a finite projective module, then
quotienting the dual by its annihilator again gives a projective module. -/
theorem projective_quotient_dualAnnihilator (p : Submodule R M)
    [Module.Finite R M] [Module.Projective R M]
    [Module.Projective R (M ⧸ p)] :
    Module.Projective R ((Module.Dual R M) ⧸ p.dualAnnihilator) := by
  obtain ⟨r, hr⟩ := exists_retraction_of_projective_quotient p
  let : Module.Projective R p := Module.Projective.of_split p.subtype r hr
  have hsurj : Function.Surjective r := by
    intro x
    refine ⟨p.subtype x, ?_⟩
    exact LinearMap.congr_fun hr x
  let : Module.Finite R p := Module.Finite.of_surjective r hsurj
  let f : Module.Dual R M →ₗ[R] Module.Dual R p := p.dualRestrict
  have hf : Function.Surjective f := by
    intro g
    refine ⟨g.comp r, ?_⟩
    apply LinearMap.ext
    intro x
    change g (r (p.subtype x)) = g x
    exact congrArg g (LinearMap.congr_fun hr x)
  have hker : LinearMap.ker f = p.dualAnnihilator :=
    Submodule.dualRestrict_ker_eq_dualAnnihilator p
  let e : ((Module.Dual R M) ⧸ p.dualAnnihilator) ≃ₗ[R] Module.Dual R p := by
    rw [← hker]
    exact f.quotKerEquivOfSurjective hf
  exact Module.Projective.of_equiv e.symm

/-- A submodule with projective quotient is equal to its double annihilator. -/
theorem dualAnnihilator_dualCoannihilator_eq_of_projective_quotient
    (p : Submodule R M) [Module.Projective R (M ⧸ p)] :
    p.dualAnnihilator.dualCoannihilator = p := by
  apply le_antisymm
  · intro x hx
    have hx0 : p.mkQ x = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff R (p.mkQ x)).mp
      intro f
      have hf : f.comp p.mkQ ∈ p.dualAnnihilator := by
        rw [Submodule.mem_dualAnnihilator]
        intro y hy
        have hy0 : p.mkQ y = 0 := by
          change y ∈ LinearMap.ker p.mkQ
          rwa [p.ker_mkQ]
        change f (p.mkQ y) = 0
        rw [hy0, map_zero]
      exact ((Submodule.mem_dualCoannihilator x).mp hx) (f.comp p.mkQ) hf
    have hxker : x ∈ LinearMap.ker p.mkQ := hx0
    rwa [p.ker_mkQ] at hxker
  · intro x hx
    rw [Submodule.mem_dualCoannihilator]
    intro f hf
    exact ((Submodule.mem_dualAnnihilator f).mp hf) x hx

end CommRing

end Submodule
