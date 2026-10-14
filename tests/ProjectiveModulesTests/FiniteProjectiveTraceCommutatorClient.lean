/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.LocallyConstantRank
public import ProjectiveModules.Module.Trace.Prod
public import ProjectiveModules.Module.Trace.Cyclicity

/-!
# A nonfree finite-projective additive group over a semiring

For the canonical commutative semiring `R = ℕ × ℤ`, let `I` be the submodule
spanned by `(0, 1)` and let `M = I × I`. The integer coordinate supplies
additive inverses in `I`, while its addition, zero and natural-number scalar
multiplication remain those of the canonical submodule. The existing module
structures on `I` and its product are unchanged. In contrast, the scalar unit
has no additive inverse under the canonical addition on `R`.

Both `I` and `M` are nonzero finite projective modules, and neither is free.
The nonfreeness of `M` is proved directly: the nonzero scalar `(1, 0)` kills
every vector, contradicting the faithful action on a nontrivial free module.
The identity trace on `I` is computed using the rank-one trace formula and the
idempotent's action on its span. The two off-diagonal inclusion–projection
maps on `M` have distinct nonzero composites and a nonzero additive commutator.
Their composite traces are independently computed as the nonzero idempotent
before applying the commutator trace corollary.

## References

The idempotent-span projection and projectivity API is from
`ProjectiveModules.Module.LocallyConstantRank`. The faithful scalar action on
a nontrivial free module is from Mathlib's free-module formalization. Product
finiteness and projectivity use the formalizations by Johan Commelin, Kevin
Buzzard and Antoine Labelle in `Mathlib.RingTheory.Finiteness.Prod` and
`Mathlib.Algebra.Module.Projective`. The rank-one trace formula uses the
contraction formalization by Oliver Nash and Antoine Labelle in
`Mathlib.LinearAlgebra.Contraction`. The product-map application formulas are
from the formalization by Johannes Hölzl, Mario Carneiro, Kevin Buzzard,
Yury Kudryashov and Eric Wieser in `Mathlib.LinearAlgebra.Prod`.
-/

noncomputable section

namespace ProjectiveModulesTests.FiniteProjectiveTraceCommutatorClient

private abbrev R := ℕ × ℤ

private def e : R := (0, 1)

private abbrev I := Submodule.span R {e}

private abbrev M := I × I

private def v : I := ⟨e, Submodule.mem_span_singleton_self e⟩

private theorem e_isIdempotent : IsIdempotentElem e := by
  change (0, 1) * (0, 1) = ((0, 1) : R)
  exact Prod.ext (by simp) (by simp)

private theorem e_ne_zero : e ≠ 0 :=
  fun h ↦ one_ne_zero (congrArg Prod.snd h)

private theorem e_ne_one : e ≠ 1 :=
  fun h ↦ zero_ne_one (congrArg Prod.fst h)

private theorem v_coe : (v : R) = e := rfl

private theorem v_ne_zero : v ≠ 0 :=
  fun h ↦ e_ne_zero (congrArg Subtype.val h)

-- Capture the submodule and product structures before adding inverses.
private abbrev canonicalIAddCommMonoid : AddCommMonoid I := inferInstance
private abbrev canonicalMAddCommMonoid : AddCommMonoid M := inferInstance
private abbrev canonicalIModule : Module R I := inferInstance
private abbrev canonicalMModule : Module R M := inferInstance

private theorem I_fst_zero (x : I) : (x : R).1 = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.property
  simpa [e, smul_eq_mul] using (congrArg Prod.fst ha).symm

private def I_neg (x : I) : I :=
  ⟨(0, -(x : R).2), Submodule.mem_span_singleton.mpr
    ⟨(0, -(x : R).2), by ext <;> simp [e, smul_eq_mul]⟩⟩

private theorem I_neg_add_cancel (x : I) : I_neg x + x = 0 := by
  apply Subtype.ext
  apply Prod.ext
  · change 0 + (x : R).1 = 0
    simpa only [zero_add] using I_fst_zero x
  · change -(x : R).2 + (x : R).2 = 0
    exact neg_add_cancel _

-- Extending this very monoid retains its operations and its `nsmul`, rather
-- than transporting an unrelated group structure onto the same carrier.
private instance I_addCommGroup : AddCommGroup I :=
  { canonicalIAddCommMonoid with
    neg := I_neg
    neg_add_cancel := I_neg_add_cancel
    zsmul := @zsmulRec I _ _ ⟨I_neg⟩ canonicalIAddCommMonoid.nsmul
    zsmul_zero' := canonicalIAddCommMonoid.nsmul_zero
    zsmul_succ' := canonicalIAddCommMonoid.nsmul_succ
    zsmul_neg' _ _ := rfl }

private theorem I_addCommMonoid_compatible :
    I_addCommGroup.toAddCommMonoid = canonicalIAddCommMonoid := rfl

private theorem M_addCommMonoid_compatible :
    (inferInstance : AddCommGroup M).toAddCommMonoid = canonicalMAddCommMonoid := rfl

private theorem I_module_compatible :
    (inferInstance : Module R I) = canonicalIModule := rfl

private theorem M_module_compatible :
    (inferInstance : Module R M) = canonicalMModule := rfl

private theorem I_neg_coe (x : I) : ((-x : I) : R) = (0, -(x : R).2) := rfl

private instance I_finite : Module.Finite R I := Module.Finite.span_singleton R e

private instance I_projective : Module.Projective R I := e_isIdempotent.projective_span

private theorem I_not_free : ¬ Module.Free R I :=
  e_isIdempotent.not_free_span e_ne_zero e_ne_one

private instance I_nontrivial : Nontrivial I :=
  Submodule.nontrivial_span_singleton e_ne_zero

private instance M_finite : Module.Finite R M := inferInstance

private instance M_projective : Module.Projective R M := inferInstance

private theorem M_witness_ne_zero : ((v, 0) : M) ≠ 0 :=
  fun h ↦ v_ne_zero (congrArg Prod.fst h)

private instance M_nontrivial : Nontrivial M := ⟨⟨(v, 0), 0, M_witness_ne_zero⟩⟩

private def annihilator : R := (1, 0)

private theorem annihilator_ne_zero : annihilator ≠ 0 :=
  fun h ↦ one_ne_zero (congrArg Prod.fst h)

private theorem annihilator_smul_I (x : I) : annihilator • x = 0 := by
  apply Subtype.ext
  change annihilator * (x : R) = 0
  exact Prod.ext (by simp [annihilator, I_fst_zero x]) (by simp [annihilator])

private theorem annihilator_smul_M (x : M) : annihilator • x = 0 :=
  Prod.ext (annihilator_smul_I x.1) (annihilator_smul_I x.2)

private theorem M_not_free : ¬ Module.Free R M := by
  intro hfree
  have : Module.Free R M := hfree
  have hzero : annihilator = (0 : R) := eq_of_smul_eq_smul fun x : M ↦ by
    rw [annihilator_smul_M, zero_smul]
  exact annihilator_ne_zero hzero

private theorem scalar_one_no_additive_inverse : ¬ ∃ r : R, (1 : R) + r = 0 := by
  rintro ⟨r, hr⟩
  have hfirst : 1 + r.1 = (0 : ℕ) := congrArg Prod.fst hr
  simp at hfirst

private theorem subtype_smulRight_v :
    I.subtype.smulRight v = (LinearMap.id : I →ₗ[R] I) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (x : R) * e = (x : R)
  rw [mul_comm]
  exact congrArg Subtype.val (e_isIdempotent.smul_span x)

private theorem trace_I_id :
    LinearMap.traceOfFiniteProjective R I LinearMap.id = e := by
  rw [← subtype_smulRight_v, LinearMap.traceOfFiniteProjective_smulRight]
  rfl

private theorem upper_apply (x y : I) :
    ((LinearMap.inl R I I).comp (LinearMap.snd R I I)) (x, y) = (y, 0) := by
  simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.snd_apply]

private theorem lower_apply (x y : I) :
    ((LinearMap.inr R I I).comp (LinearMap.fst R I I)) (x, y) = (0, x) := by
  simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.fst_apply]

private theorem upper_comp_lower :
    ((LinearMap.inl R I I).comp (LinearMap.snd R I I)).comp
        ((LinearMap.inr R I I).comp (LinearMap.fst R I I)) =
      (LinearMap.inl R I I).comp
        ((LinearMap.id : I →ₗ[R] I).comp (LinearMap.fst R I I)) := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.id_apply]

private theorem lower_comp_upper :
    ((LinearMap.inr R I I).comp (LinearMap.fst R I I)).comp
        ((LinearMap.inl R I I).comp (LinearMap.snd R I I)) =
      (LinearMap.inr R I I).comp
        ((LinearMap.id : I →ₗ[R] I).comp (LinearMap.snd R I I)) := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.id_apply]

private theorem upper_ne_zero :
    (LinearMap.inl R I I).comp (LinearMap.snd R I I) ≠ 0 := by
  intro h
  apply v_ne_zero
  simpa only [upper_apply, LinearMap.zero_apply, Prod.fst_zero] using
    congrArg (fun f : (I × I) →ₗ[R] (I × I) => (f (0, v)).1) h

private theorem lower_ne_zero :
    (LinearMap.inr R I I).comp (LinearMap.fst R I I) ≠ 0 := by
  intro h
  apply v_ne_zero
  simpa only [lower_apply, LinearMap.zero_apply, Prod.snd_zero] using
    congrArg (fun f : (I × I) →ₗ[R] (I × I) => (f (v, 0)).2) h

private theorem upper_comp_lower_ne_zero :
    ((LinearMap.inl R I I).comp (LinearMap.snd R I I)).comp
      ((LinearMap.inr R I I).comp (LinearMap.fst R I I)) ≠ 0 := by
  intro h
  rw [upper_comp_lower] at h
  apply v_ne_zero
  simpa only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.fst_apply,
    LinearMap.id_apply, LinearMap.zero_apply, Prod.fst_zero] using
    congrArg (fun f : (I × I) →ₗ[R] (I × I) => (f (v, 0)).1) h

private theorem lower_comp_upper_ne_zero :
    ((LinearMap.inr R I I).comp (LinearMap.fst R I I)).comp
      ((LinearMap.inl R I I).comp (LinearMap.snd R I I)) ≠ 0 := by
  intro h
  rw [lower_comp_upper] at h
  apply v_ne_zero
  simpa only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.snd_apply,
    LinearMap.id_apply, LinearMap.zero_apply, Prod.snd_zero] using
    congrArg (fun f : (I × I) →ₗ[R] (I × I) => (f (0, v)).2) h

private theorem composites_ne :
    ((LinearMap.inl R I I).comp (LinearMap.snd R I I)).comp
        ((LinearMap.inr R I I).comp (LinearMap.fst R I I)) ≠
      ((LinearMap.inr R I I).comp (LinearMap.fst R I I)).comp
        ((LinearMap.inl R I I).comp (LinearMap.snd R I I)) := by
  intro h
  rw [upper_comp_lower, lower_comp_upper] at h
  apply v_ne_zero
  simpa only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.id_apply] using
    congrArg (fun f : (I × I) →ₗ[R] (I × I) => (f (v, 0)).1) h

private theorem commutator_apply (x y : I) :
    (((LinearMap.inl R I I).comp (LinearMap.snd R I I)).comp
        ((LinearMap.inr R I I).comp (LinearMap.fst R I I)) -
      ((LinearMap.inr R I I).comp (LinearMap.fst R I I)).comp
        ((LinearMap.inl R I I).comp (LinearMap.snd R I I))) (x, y) = (x, -y) := by
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.inl_apply,
    LinearMap.inr_apply, LinearMap.fst_apply, LinearMap.snd_apply]
  apply Prod.ext <;> simp

private theorem commutator_apply_witness :
    (((LinearMap.inl R I I).comp (LinearMap.snd R I I)).comp
        ((LinearMap.inr R I I).comp (LinearMap.fst R I I)) -
      ((LinearMap.inr R I I).comp (LinearMap.fst R I I)).comp
        ((LinearMap.inl R I I).comp (LinearMap.snd R I I))) (v, 0) = (v, 0) := by
  simpa only [neg_zero] using commutator_apply v 0

private theorem commutator_ne_zero :
    ((LinearMap.inl R I I).comp (LinearMap.snd R I I)).comp
        ((LinearMap.inr R I I).comp (LinearMap.fst R I I)) -
      ((LinearMap.inr R I I).comp (LinearMap.fst R I I)).comp
        ((LinearMap.inl R I I).comp (LinearMap.snd R I I)) ≠ 0 := by
  intro h
  apply v_ne_zero
  simpa only [commutator_apply_witness, LinearMap.zero_apply, Prod.fst_zero] using
    congrArg (fun f : (I × I) →ₗ[R] (I × I) => (f (v, 0)).1) h

private theorem trace_upper_comp_lower :
    LinearMap.traceOfFiniteProjective R (I × I)
        (((LinearMap.inl R I I).comp (LinearMap.snd R I I)).comp
          ((LinearMap.inr R I I).comp (LinearMap.fst R I I))) =
      LinearMap.traceOfFiniteProjective R I LinearMap.id := by
  rw [upper_comp_lower, LinearMap.traceOfFiniteProjective_inl_fst]

private theorem trace_lower_comp_upper :
    LinearMap.traceOfFiniteProjective R (I × I)
        (((LinearMap.inr R I I).comp (LinearMap.fst R I I)).comp
          ((LinearMap.inl R I I).comp (LinearMap.snd R I I))) =
      LinearMap.traceOfFiniteProjective R I LinearMap.id := by
  rw [lower_comp_upper, LinearMap.traceOfFiniteProjective_inr_snd]

private theorem trace_upper_comp_lower_value :
    LinearMap.traceOfFiniteProjective R M
        (((LinearMap.inl R I I).comp (LinearMap.snd R I I)).comp
          ((LinearMap.inr R I I).comp (LinearMap.fst R I I))) = e := by
  rw [trace_upper_comp_lower, trace_I_id]

private theorem trace_lower_comp_upper_value :
    LinearMap.traceOfFiniteProjective R M
        (((LinearMap.inr R I I).comp (LinearMap.fst R I I)).comp
          ((LinearMap.inl R I I).comp (LinearMap.snd R I I))) = e := by
  rw [trace_lower_comp_upper, trace_I_id]

private theorem trace_upper_comp_lower_ne_zero :
    LinearMap.traceOfFiniteProjective R M
        (((LinearMap.inl R I I).comp (LinearMap.snd R I I)).comp
          ((LinearMap.inr R I I).comp (LinearMap.fst R I I))) ≠ 0 := by
  rw [trace_upper_comp_lower_value]
  exact e_ne_zero

private theorem trace_lower_comp_upper_ne_zero :
    LinearMap.traceOfFiniteProjective R M
        (((LinearMap.inr R I I).comp (LinearMap.fst R I I)).comp
          ((LinearMap.inl R I I).comp (LinearMap.snd R I I))) ≠ 0 := by
  rw [trace_lower_comp_upper_value]
  exact e_ne_zero

private theorem trace_commutator_eq_zero :
    LinearMap.traceOfFiniteProjective R M
        (((LinearMap.inl R I I).comp (LinearMap.snd R I I)).comp
            ((LinearMap.inr R I I).comp (LinearMap.fst R I I)) -
          ((LinearMap.inr R I I).comp (LinearMap.fst R I I)).comp
            ((LinearMap.inl R I I).comp (LinearMap.snd R I I))) = 0 :=
  LinearMap.traceOfFiniteProjective_commutator R M
    ((LinearMap.inl R I I).comp (LinearMap.snd R I I))
    ((LinearMap.inr R I I).comp (LinearMap.fst R I I))

end ProjectiveModulesTests.FiniteProjectiveTraceCommutatorClient
