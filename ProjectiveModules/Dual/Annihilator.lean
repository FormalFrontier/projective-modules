/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Dual.TensorProduct
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Annihilators and coannihilators with projective quotients

A projective quotient splits the inclusion of a submodule. If the ambient dual
is projective, its quotient by the annihilator is projective.
Projectivity of the original quotient alone also implies double annihilator closure.

For a submodule of the dual with projective quotient, reflexivity identifies it
with the annihilator of its coannihilator. If the reflexive ambient module is
projective, the quotient by this coannihilator is projective as well.

For a reflexive projective module with projective dual, these operations give an
order anti-isomorphism between its submodules with projective quotient and the
submodules of its dual with projective quotient. This includes finite projective
modules. The correspondence uses the original annihilator and
coannihilator, and concerns the induced orders on these two collections.

## References

The identity `Submodule.dualAnnihilator_dualCoannihilator_eq_of_projective_quotient`
generalizes `Subspace.dualAnnihilator_dualCoannihilator_eq` from
`Mathlib.LinearAlgebra.Dual.Lemmas`: a projective quotient replaces the field
hypothesis. The argument uses `Module.forall_dual_apply_eq_zero_iff`, the
projective-module separation theorem from the same module. The coannihilator
statements use the canonical evaluation equivalence `Module.evalEquiv`.
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

/-- If a submodule has projective quotient and the ambient dual is projective,
then quotienting the dual by the annihilator gives a projective module. -/
theorem projective_quotient_dualAnnihilator (p : Submodule R M)
    [Module.Projective R (Module.Dual R M)] [Module.Projective R (M ⧸ p)] :
    Module.Projective R ((Module.Dual R M) ⧸ p.dualAnnihilator) := by
  obtain ⟨r, hr⟩ := exists_retraction_of_projective_quotient p
  let f : Module.Dual R M →ₗ[R] Module.Dual R p := p.dualRestrict
  let i : Module.Dual R p →ₗ[R] Module.Dual R M := r.dualMap
  have hi : f.comp i = LinearMap.id := by
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro x
    change g (r (p.subtype x)) = g x
    exact congrArg g (LinearMap.congr_fun hr x)
  let : Module.Projective R (Module.Dual R p) := Module.Projective.of_split i f hi
  have hf : Function.Surjective f := by
    intro g
    exact ⟨i g, LinearMap.congr_fun hi g⟩
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

/-- A submodule of the dual of a reflexive module is the annihilator of its
coannihilator if the quotient of the dual by the submodule is projective. -/
theorem dualCoannihilator_dualAnnihilator_eq_of_projective_quotient
    [Module.IsReflexive R M] (q : Submodule R (Module.Dual R M))
    [Module.Projective R ((Module.Dual R M) ⧸ q)] :
    q.dualCoannihilator.dualAnnihilator = q := by
  apply le_antisymm
  · intro f hf
    rw [Submodule.mem_dualAnnihilator] at hf
    have hzero : q.mkQ f = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff R (q.mkQ f)).mp
      intro ψ
      let g : Module.Dual R (Module.Dual R M) := ψ.comp q.mkQ
      let x : M := (Module.evalEquiv R M).symm g
      have hx_eval : (Module.evalEquiv R M) x = g :=
        (Module.evalEquiv R M).apply_symm_apply g
      have hx : x ∈ q.dualCoannihilator := by
        rw [Submodule.mem_dualCoannihilator]
        intro h hh
        have hqh : q.mkQ h = 0 := by
          change h ∈ LinearMap.ker q.mkQ
          rw [Submodule.ker_mkQ]
          exact hh
        calc
          h x = (Module.evalEquiv R M) x h := rfl
          _ = g h :=
            congrArg (fun k : Module.Dual R (Module.Dual R M) => k h) hx_eval
          _ = ψ (q.mkQ h) := rfl
          _ = 0 := by rw [hqh, map_zero]
      calc
        ψ (q.mkQ f) = g f := rfl
        _ = (Module.evalEquiv R M) x f :=
          (congrArg (fun k : Module.Dual R (Module.Dual R M) => k f) hx_eval).symm
        _ = f x := rfl
        _ = 0 := hf x hx
    have hker : f ∈ LinearMap.ker q.mkQ := hzero
    rwa [Submodule.ker_mkQ] at hker
  · intro f hf
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    exact hx f hf

/-- A projective quotient of the dual of a reflexive projective module gives a
projective quotient of the original module by the coannihilator. -/
theorem projective_quotient_dualCoannihilator (q : Submodule R (Module.Dual R M))
    [Module.Projective R M] [Module.IsReflexive R M]
    [Module.Projective R ((Module.Dual R M) ⧸ q)] :
    Module.Projective R (M ⧸ q.dualCoannihilator) := by
  let e : M ≃ₗ[R] Module.Dual R (Module.Dual R M) := Module.evalEquiv R M
  let : Module.Projective R (Module.Dual R (Module.Dual R M)) :=
    Module.Projective.of_equiv e
  let : Module.Projective R
      ((Module.Dual R (Module.Dual R M)) ⧸ q.dualAnnihilator) :=
    Submodule.projective_quotient_dualAnnihilator q
  have hmap : q.dualCoannihilator.map e.toLinearMap = q.dualAnnihilator := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Submodule.mem_dualAnnihilator]
      intro f hf
      change f x = 0
      exact ((Submodule.mem_dualCoannihilator x).mp hx) f hf
    · intro hy
      obtain ⟨x, rfl⟩ := e.surjective y
      refine ⟨x, ?_, rfl⟩
      refine (Submodule.mem_dualCoannihilator x).mpr ?_
      intro f hf
      have hzero := ((Submodule.mem_dualAnnihilator (e x)).mp hy) f hf
      change f x = 0 at hzero
      exact hzero
  let equot : (M ⧸ q.dualCoannihilator) ≃ₗ[R]
      ((Module.Dual R (Module.Dual R M)) ⧸ q.dualAnnihilator) :=
    Submodule.Quotient.equiv q.dualCoannihilator q.dualAnnihilator e hmap
  exact Module.Projective.of_equiv equot.symm

/-- The annihilator order anti-isomorphism between submodules with projective
quotient in a reflexive projective module with projective dual and submodules
with projective quotient in its dual. Its inverse is the coannihilator, using
canonical evaluation to identify the module with its double dual. -/
def dualAnnihilatorOrderIso (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Projective R M] [Module.Projective R (Module.Dual R M)]
    [Module.IsReflexive R M] :
    {p : Submodule R M // Module.Projective R (M ⧸ p)} ≃o
      OrderDual {q : Submodule R (Module.Dual R M) //
        Module.Projective R ((Module.Dual R M) ⧸ q)} where
  toFun p := by
    let : Module.Projective R (M ⧸ p.1) := p.2
    exact ⟨p.1.dualAnnihilator, projective_quotient_dualAnnihilator p.1⟩
  invFun q := by
    let : Module.Projective R ((Module.Dual R M) ⧸ q.1) := q.2
    exact ⟨q.1.dualCoannihilator, projective_quotient_dualCoannihilator q.1⟩
  left_inv p := by
    let : Module.Projective R (M ⧸ p.1) := p.2
    apply Subtype.ext
    exact dualAnnihilator_dualCoannihilator_eq_of_projective_quotient p.1
  right_inv q := by
    let : Module.Projective R ((Module.Dual R M) ⧸ q.1) := q.2
    apply Subtype.ext
    exact dualCoannihilator_dualAnnihilator_eq_of_projective_quotient q.1
  map_rel_iff' := by
    intro p₁ p₂
    change p₂.1.dualAnnihilator ≤ p₁.1.dualAnnihilator ↔ p₁.1 ≤ p₂.1
    constructor
    · intro h
      let : Module.Projective R (M ⧸ p₂.1) := p₂.2
      rw [← dualAnnihilator_dualCoannihilator_eq_of_projective_quotient p₂.1]
      intro x hx
      refine (Submodule.mem_dualCoannihilator x).mpr ?_
      intro f hf
      exact ((Submodule.mem_dualAnnihilator f).mp (h hf)) x hx
    · intro h f hf
      refine (Submodule.mem_dualAnnihilator f).mpr ?_
      intro x hx
      exact ((Submodule.mem_dualAnnihilator f).mp hf) x (h hx)

variable [Module.Projective R M] [Module.Projective R (Module.Dual R M)]
variable [Module.IsReflexive R M]

/-- The forward correspondence has the original annihilator as its underlying
submodule. -/
@[simp]
theorem dualAnnihilatorOrderIso_apply
    (p : {p : Submodule R M // Module.Projective R (M ⧸ p)}) :
    (dualAnnihilatorOrderIso R M p).1 = p.1.dualAnnihilator := rfl

/-- The inverse correspondence has the original coannihilator as its underlying
submodule. -/
@[simp]
theorem dualAnnihilatorOrderIso_symm_apply
    (q : {q : Submodule R (Module.Dual R M) //
      Module.Projective R ((Module.Dual R M) ⧸ q)}) :
    ((dualAnnihilatorOrderIso R M).symm q).1 = q.1.dualCoannihilator := rfl

/-- Membership in the forward correspondence means vanishing on the original
submodule. -/
theorem mem_dualAnnihilatorOrderIso_apply
    (p : {p : Submodule R M // Module.Projective R (M ⧸ p)})
    (f : Module.Dual R M) :
    f ∈ (dualAnnihilatorOrderIso R M p).1 ↔ ∀ x ∈ p.1, f x = 0 := by
  rw [dualAnnihilatorOrderIso_apply]
  exact Submodule.mem_dualAnnihilator f

/-- Membership in the inverse correspondence means that every functional in the
original submodule vanishes at the given vector. -/
theorem mem_dualAnnihilatorOrderIso_symm_apply
    (q : {q : Submodule R (Module.Dual R M) //
      Module.Projective R ((Module.Dual R M) ⧸ q)}) (x : M) :
    x ∈ ((dualAnnihilatorOrderIso R M).symm q).1 ↔ ∀ f ∈ q.1, f x = 0 := by
  rw [dualAnnihilatorOrderIso_symm_apply]
  exact Submodule.mem_dualCoannihilator x

end CommRing

end Submodule
