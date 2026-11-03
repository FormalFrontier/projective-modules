/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Reduction

/-!
# Nilpotence of the kernel of endomorphism reduction

Endomorphisms reduce by a ring homomorphism for the composition multiplication.
For any module over a ring, reduction modulo a nilpotent two-sided ideal has a
whole nilpotent kernel on endomorphism rings, with the same nilpotence exponent.
No finite-generation or projectivity hypothesis is needed.
-/

@[expose] public section

universe u v

namespace Module

variable {R : Type u} [Ring R] (I : Ideal R) [I.IsTwoSided]

/-- Reduction of endomorphisms as a ring homomorphism, with multiplication given by
composition in both endomorphism rings. -/
def reductionEnd (M : Type v) [AddCommGroup M] [Module R M] :
    Module.End R M →+* Module.End (R ⧸ I) (Reduction I M) where
  toFun := reductionMap I
  map_one' := reductionMap_id I
  map_mul' f g := reductionMap_comp I g f
  map_zero' := reductionMap_zero I
  map_add' f g := reductionMap_add I f g

/-- Endomorphism reduction is the reduction of the underlying linear map. -/
@[simp] theorem reductionEnd_apply (M : Type v) [AddCommGroup M] [Module R M]
    (f : Module.End R M) : reductionEnd I M f = reductionMap I f := by
  rfl

/-- A reduced endomorphism sends the class of a vector to the class of its image. -/
theorem reductionEnd_mk (M : Type v) [AddCommGroup M] [Module R M]
    (f : Module.End R M) (m : M) :
    reductionEnd I M f (reductionMk I M m) = reductionMk I M (f m) := by
  exact reductionMap_mk I f m

/-- Representative values uniquely characterize the reduction of an endomorphism. -/
theorem reductionEnd_unique (M : Type v) [AddCommGroup M] [Module R M]
    (f : Module.End R M) (g : Module.End (R ⧸ I) (Reduction I M))
    (hg : ∀ m, g (reductionMk I M m) = reductionMk I M (f m)) :
    g = reductionEnd I M f := by
  apply reduction_hom_ext I
  intro m
  rw [reductionEnd_mk]
  exact hg m

/-- An endomorphism reduces to zero exactly when all its values lie in the ideal action. -/
theorem reductionEnd_mem_ker_iff (M : Type v) [AddCommGroup M] [Module R M]
    (f : Module.End R M) :
    f ∈ RingHom.ker (reductionEnd I M) ↔
      ∀ m, f m ∈ I • (⊤ : Submodule R M) := by
  rw [RingHom.mem_ker, reductionEnd_apply]
  exact reductionMap_eq_zero_iff I f

/-- The kernel of endomorphism reduction consists of maps with range in the ideal action. -/
theorem reductionEnd_mem_ker_iff_range_le (M : Type v) [AddCommGroup M] [Module R M]
    (f : Module.End R M) :
    f ∈ RingHom.ker (reductionEnd I M) ↔
      LinearMap.range f ≤ I • (⊤ : Submodule R M) := by
  rw [reductionEnd_mem_ker_iff]
  constructor
  · intro hf
    rintro _ ⟨m, rfl⟩
    exact hf m
  · intro hf m
    exact hf ⟨m, rfl⟩

/-- Endomorphisms whose values lie in the action of a scalar ideal form a left ideal. -/
private def endRangeIdeal (M : Type v) [AddCommGroup M] [Module R M]
    (A : Ideal R) : Ideal (Module.End R M) where
  carrier := {f | ∀ x, f x ∈ A • (⊤ : Submodule R M)}
  zero_mem' := by
    intro x
    change (0 : M) ∈ A • (⊤ : Submodule R M)
    exact Submodule.zero_mem _
  add_mem' := by
    intro f g hf hg x
    change f x + g x ∈ A • (⊤ : Submodule R M)
    exact Submodule.add_mem _ (hf x) (hg x)
  smul_mem' := by
    intro h f hf x
    change h (f x) ∈ A • (⊤ : Submodule R M)
    refine Submodule.smul_induction_on (hf x) ?_ ?_
    · intro a ha y _
      rw [map_smul]
      exact Submodule.smul_mem_smul ha
        (Submodule.mem_top : h y ∈ (⊤ : Submodule R M))
    · intro y z hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz

private theorem endRangeIdeal_mul_mem (M : Type v) [AddCommGroup M]
    [Module R M] (A B : Ideal R) {f g : Module.End R M}
    (hf : f ∈ endRangeIdeal M A) (hg : g ∈ endRangeIdeal M B) :
    f * g ∈ endRangeIdeal M (B * A) := by
  intro x
  change f (g x) ∈ (B * A) • (⊤ : Submodule R M)
  refine Submodule.smul_induction_on (hg x) ?_ ?_
  · intro b hb y _
    rw [map_smul]
    refine Submodule.smul_induction_on (hf y) ?_ ?_
    · intro a ha z hz
      rw [smul_smul]
      -- The scalar contributed by the right-hand factor g is on the left.
      have hba : b * a ∈ B * A := Ideal.mul_mem_mul hb ha
      exact Submodule.smul_mem_smul hba hz
    · intro y z hy hz
      rw [smul_add]
      exact Submodule.add_mem _ hy hz
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

private theorem end_ideal_pow_eq_zero_of_range_le_ideal_smul_top
    (M : Type v) [AddCommGroup M] [Module R M]
    (J : Ideal (Module.End R M))
    (hJ : ∀ f ∈ J, LinearMap.range f ≤ I • (⊤ : Submodule R M))
    (n : ℕ) (hI : I ^ n = 0) : J ^ n = 0 := by
  -- Work entirely with the original R-action, without quotients by powers of I.
  have hk : ∀ k : ℕ, J ^ k ≤ endRangeIdeal M (I ^ k) := by
    intro k
    induction k with
    | zero =>
        intro f _ x
        have hunit : (1 : R) ∈ (I ^ (0 : ℕ) : Ideal R) := by
          rw [Submodule.pow_zero, Ideal.one_eq_top]
          exact Submodule.mem_top
        have hx : (1 : R) • f x ∈ (I ^ (0 : ℕ)) • (⊤ : Submodule R M) :=
          Submodule.smul_mem_smul hunit
            (Submodule.mem_top : f x ∈ (⊤ : Submodule R M))
        simpa using hx
    | succ k ih =>
        have hpow : J ^ (k + 1) = J ^ k * J := by
          exact Submodule.pow_succ J
        have hscalar : I ^ (k + 1) = I * I ^ k := by
          exact Ideal.IsTwoSided.pow_succ (I := I) k
        rw [hpow]
        apply Ideal.mul_le.2
        intro f hf g hg
        rw [hscalar]
        apply endRangeIdeal_mul_mem M (I ^ k) I (ih hf)
        intro x
        exact hJ g hg ⟨x, rfl⟩
  refine le_antisymm ?_ bot_le
  intro f hf
  change f = 0
  apply LinearMap.ext
  intro x
  change f x = 0
  have hx : f x ∈ I ^ n • (⊤ : Submodule R M) := (hk n hf) x
  rw [hI] at hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    have ha0 : a = 0 := by simpa using ha
    rw [ha0, zero_smul]
  · intro y z hy hz
    rw [hy, hz, zero_add]

/-- A vanishing power of the scalar ideal annihilates the same power of the whole
kernel of endomorphism reduction, for an arbitrary module. -/
theorem reductionEnd_ker_pow_eq_zero (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (hI : I ^ n = 0) :
    (RingHom.ker (reductionEnd I M)) ^ n = 0 := by
  apply end_ideal_pow_eq_zero_of_range_le_ideal_smul_top I M
    (RingHom.ker (reductionEnd I M)) ?_ n hI
  intro f hf
  exact (reductionEnd_mem_ker_iff_range_le I M f).1 hf

/-- Reduction modulo a whole nilpotent two-sided ideal has a whole nilpotent kernel
on endomorphism rings, without finite-generation or projectivity assumptions. -/
theorem reductionEnd_ker_isNilpotent (M : Type v) [AddCommGroup M] [Module R M]
    (hI : IsNilpotent I) : IsNilpotent (RingHom.ker (reductionEnd I M)) := by
  obtain ⟨n, hn⟩ := hI
  exact ⟨n, reductionEnd_ker_pow_eq_zero I M n hn⟩

end Module
