/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearMap.Units
public import ProjectiveModules.Module.FiniteFactorization
public import ProjectiveModules.Module.Nakayama

/-!
# Units from finitely generated radical images on projective modules

Over an arbitrary ring, an endomorphism of a projective module whose image is
finitely generated and contained in the Jacobson radical times the module has
unit complement. The ambient module need not be finitely generated.

The proof factors the endomorphism through a finite free module and uses the
rectangular unit equivalence. On the finite free module, Nakayama first gives
surjectivity of the complement. A section makes its kernel a finitely generated
retract, so a second application of Nakayama gives injectivity. In particular,
we do not infer injectivity from surjectivity of a finite projective endomorphism.

## References

The proof uses `Module.Projective.exists_finite_free_factorization_on`,
`Submodule.eq_top_of_finite_quotient_of_sup_smul_eq_top`, and
`LinearMap.isUnit_one_sub_comp_iff`, together with Mathlib's module and ideal APIs.
-/

@[expose] public section

universe u v w

open scoped Pointwise

namespace LinearMap

variable {R : Type u} [Ring R]

/-- Linear maps preserve the submodule obtained by multiplying by an ideal. -/
private theorem map_mem_ideal_smul_top
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (I : Ideal R) {x : M}
    (hx : x ∈ I • (⊤ : Submodule R M)) :
    f x ∈ I • (⊤ : Submodule R N) := by
  have hle : I • (⊤ : Submodule R M) ≤
      (I • (⊤ : Submodule R N)).comap f := by
    refine Submodule.smul_le.mpr ?_
    intro r hr m _
    change f (r • m) ∈ I • (⊤ : Submodule R N)
    rw [map_smul]
    exact Submodule.smul_mem_smul hr (Submodule.mem_top)
  exact hle hx

/-- The finite free step uses Nakayama on both the cokernel and the split kernel. -/
private theorem isUnit_one_sub_of_finite_free_radical_range
    (n : ℕ) (c : Module.End R (Fin n → R))
    (hc : range c ≤ (⊥ : Ideal R).jacobson • (⊤ : Submodule R (Fin n → R))) :
    IsUnit ((1 : Module.End R (Fin n → R)) - c) := by
  let F := Fin n → R
  let J : Ideal R := (⊥ : Ideal R).jacobson
  let u : Module.End R F := 1 - c
  have hgen : range u ⊔ J • (⊤ : Submodule R F) = ⊤ := by
    apply top_unique
    intro x _
    have hx : u x + c x = x := by simp [u]
    rw [← hx]
    exact Submodule.add_mem _
      ((le_sup_left : range u ≤ range u ⊔ J • (⊤ : Submodule R F))
        (mem_range_self u x))
      ((le_sup_right : J • (⊤ : Submodule R F) ≤ range u ⊔ J • (⊤ : Submodule R F))
        (hc (mem_range_self c x)))
  have hu : range u = ⊤ :=
    Submodule.eq_top_of_finite_quotient_of_sup_smul_eq_top
      (range u) J le_rfl hgen
  have hsurj : Function.Surjective u := range_eq_top.mp hu
  -- The section, rather than a Noetherian hypothesis, makes the kernel finite.
  obtain ⟨s, hs⟩ := Module.projective_lifting_property u (LinearMap.id : F →ₗ[R] F) hsurj
  have hs_apply (x : F) : u (s x) = x := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      congrArg (fun f : F →ₗ[R] F => f x) hs
  let p : F →ₗ[R] ker u :=
    (1 - s.comp u).codRestrict (ker u) (by
      intro x
      change u (x - s (u x)) = 0
      rw [map_sub, hs_apply, sub_self])
  have hp (k : ker u) : p (k : F) = k := by
    apply Subtype.ext
    change (k : F) - s (u k) = k
    rw [k.property, map_zero, sub_zero]
  have : Module.Finite R (ker u) :=
    Module.Finite.of_surjective p (fun k => ⟨(k : F), hp k⟩)
  have hkJ (k : ker u) : (k : F) ∈ J • (⊤ : Submodule R F) := by
    have hk : (k : F) - c k = 0 := k.property
    rw [sub_eq_zero] at hk
    rw [hk]
    exact hc (mem_range_self c k)
  have hJK : J • (⊤ : Submodule R (ker u)) = ⊤ := by
    apply top_unique
    intro k _
    simpa only [hp] using map_mem_ideal_smul_top p J (hkJ k)
  have hK : (⊥ : Submodule R (ker u)) = ⊤ :=
    Submodule.eq_top_of_finite_quotient_of_sup_smul_eq_top
      ⊥ J le_rfl (by simpa only [bot_sup_eq] using hJK)
  have hkzero (k : ker u) : k = 0 := by
    have hk : k ∈ (⊥ : Submodule R (ker u)) := by rw [hK]; exact Submodule.mem_top
    exact hk
  have hker : ker u = ⊥ := by
    apply bot_unique
    intro x hx
    have hz := congrArg (fun k : ker u => (k : F)) (hkzero ⟨x, hx⟩)
    exact hz
  have hinj : Function.Injective u := ker_eq_bot.mp hker
  let e : F ≃ₗ[R] F := LinearEquiv.ofBijective u ⟨hinj, hsurj⟩
  refine ⟨⟨u, e.symm.toLinearMap, ?_, ?_⟩, rfl⟩
  · exact LinearMap.ext fun x => e.apply_symm_apply x
  · exact LinearMap.ext fun x => e.symm_apply_apply x

/-- If an endomorphism of a projective module has finitely generated image in
`J(R)M`, then its complement is a unit. The ring may be noncommutative, and the
ambient module need not be finitely generated. -/
theorem isUnit_one_sub_of_projective_of_fg_range
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Projective R M]
    (T : Module.End R M) (hfg : (range T).FG)
    (hJ : range T ≤ (⊥ : Ideal R).jacobson • (⊤ : Submodule R M)) :
    IsUnit ((1 : Module.End R M) - T) := by
  classical
  obtain ⟨S, hS, hspan⟩ := Submodule.fg_def.mp hfg
  let : Fintype S := hS.fintype
  obtain ⟨n, A, B, hAB⟩ :=
    Module.Projective.exists_finite_free_factorization_on (R := R) (fun x : S => (x : M))
  have hfix : range T ≤ ker (A.comp B - (LinearMap.id : M →ₗ[R] M)) := by
    rw [← hspan]
    refine Submodule.span_le.mpr ?_
    intro x hx
    change A (B x) - x = 0
    exact sub_eq_zero.mpr (hAB ⟨x, hx⟩)
  let b : M →ₗ[R] (Fin n → R) := B.comp T
  have hab : A.comp b = T := by
    ext x
    have hx := hfix (mem_range_self T x)
    change A (B (T x)) - T x = 0 at hx
    exact sub_eq_zero.mp hx
  -- A need not have radical-contained image: b = B ∘ T does.
  have hba : range (b.comp A) ≤
      (⊥ : Ideal R).jacobson • (⊤ : Submodule R (Fin n → R)) := by
    rintro _ ⟨x, rfl⟩
    exact map_mem_ideal_smul_top B _ (hJ (mem_range_self T (A x)))
  have hunit := isUnit_one_sub_of_finite_free_radical_range n (b.comp A) hba
  simpa only [hab] using (isUnit_one_sub_comp_iff A b).mpr hunit

end LinearMap
