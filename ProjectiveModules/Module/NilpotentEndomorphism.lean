/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.IdealAction
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Nilpotence from finite generation of an image

Pointwise eventual vanishing is uniform on a finitely generated submodule. Consequently,
an endomorphism with a finitely generated image of some power is nilpotent exactly when
it is pointwise nilpotent. The submodule need not be invariant under the endomorphism.

Over a commutative semiring, an ideal bound on the image gives the corresponding
ideal-power bound on every iterate. A finitely generated image contained in the
nilradical action therefore forces nilpotence. On an additive-group module, the usual
nilpotent-element unit criteria then apply to the identity plus or minus the endomorphism.

## References

The proofs use Mathlib's finite-generation induction and ideal-action APIs. The criterion
for finitely generated nil ideals is from
`Mathlib.RingTheory.Noetherian.Nilpotent`; the unit criteria for nilpotent elements are
from `Mathlib.RingTheory.Nilpotent.Basic`.
-/

@[expose] public section

universe u v

namespace Submodule.FG

section

variable {A : Type u} {M : Type v}
  [Semiring A] [AddCommMonoid M] [Module A M]

/-- Powers that annihilate elements pointwise have a common annihilating exponent on a
finitely generated submodule. No invariance of the submodule is assumed. -/
theorem exists_le_ker_pow {U : Submodule A M}
    (hU : U.FG) (δ : Module.End A M)
    (hδ : ∀ m ∈ U, ∃ n : ℕ, (δ ^ n) m = 0) :
    ∃ n : ℕ, U ≤ LinearMap.ker (δ ^ n) := by
  refine Submodule.fg_induction
    (motive := fun V _ =>
      (∀ m ∈ V, ∃ n : ℕ, (δ ^ n) m = 0) →
        ∃ n : ℕ, V ≤ LinearMap.ker (δ ^ n))
    ?_ ?_ U hU hδ
  · intro x hx
    obtain ⟨n, hn⟩ := hx x (Submodule.subset_span (by rfl))
    refine ⟨n, Submodule.span_le.mpr ?_⟩
    rintro y rfl
    exact hn
  · intro V W _ _ ihV ihW hx
    obtain ⟨n, hn⟩ := ihV (fun m hm => hx m ((le_sup_left : V ≤ V ⊔ W) hm))
    obtain ⟨k, hk⟩ := ihW (fun m hm => hx m ((le_sup_right : W ≤ V ⊔ W) hm))
    refine ⟨n + k, sup_le ?_ ?_⟩
    · intro m hm
      have hm0 : (δ ^ n) m = 0 := hn hm
      change (δ ^ (n + k)) m = 0
      rw [Nat.add_comm n k, pow_add, Module.End.mul_apply, hm0, map_zero]
    · intro m hm
      have hm0 : (δ ^ k) m = 0 := hk hm
      change (δ ^ (n + k)) m = 0
      rw [pow_add, Module.End.mul_apply, hm0, map_zero]

end

end Submodule.FG

namespace Module.End

section Semiring

variable {A : Type u} {M : Type v}
  [Semiring A] [AddCommMonoid M] [Module A M]

/-- Finite generation of the image of any power, including the zeroth power, makes
pointwise nilpotence equivalent to nilpotence. -/
theorem isNilpotent_iff_of_fg_range_pow
    (δ : Module.End A M) (k : ℕ)
    (hfg : (LinearMap.range (δ ^ k)).FG) :
    IsNilpotent δ ↔ ∀ m : M, ∃ n : ℕ, (δ ^ n) m = 0 := by
  constructor
  · rintro ⟨n, hn⟩ m
    refine ⟨n, ?_⟩
    rw [hn]
    rfl
  · intro hδ
    obtain ⟨n, hn⟩ := hfg.exists_le_ker_pow δ (fun m _ => hδ m)
    refine ⟨n + k, ?_⟩
    ext m
    change (δ ^ (n + k)) m = 0
    rw [pow_add, Module.End.mul_apply]
    exact hn (show (δ ^ k) m ∈ LinearMap.range (δ ^ k) from ⟨m, rfl⟩)

/-- An endomorphism with finitely generated image is nilpotent if and only if it is
pointwise nilpotent. -/
theorem isNilpotent_iff_of_fg_range
    (δ : Module.End A M) (hfg : (LinearMap.range δ).FG) :
    IsNilpotent δ ↔ ∀ m : M, ∃ n : ℕ, (δ ^ n) m = 0 := by
  exact isNilpotent_iff_of_fg_range_pow δ 1 (by simpa only [pow_one] using hfg)

example [Module.Finite A M] (δ : Module.End A M) :
    IsNilpotent δ ↔ ∀ m : M, ∃ n : ℕ, (δ ^ n) m = 0 := by
  exact isNilpotent_iff_of_fg_range δ
    (Submodule.FG.of_finite (N := LinearMap.range δ))

end Semiring

section Semimodule

variable {A : Type u} {M : Type v}
  [CommSemiring A] [AddCommMonoid M] [Module A M]

/-- An ideal bound on the image of an endomorphism gives the corresponding ideal-power
bound on the image of each iterate. -/
theorem range_pow_le_smul_pow (δ : Module.End A M) (J : Ideal A)
    (hδ : LinearMap.range δ ≤ J • (⊤ : Submodule A M)) (n : ℕ) :
    LinearMap.range (δ ^ n) ≤ (J ^ n) • (⊤ : Submodule A M) := by
  induction n with
  | zero =>
    simpa only [pow_zero, Submodule.one_smul] using
      (le_top : LinearMap.range (1 : Module.End A M) ≤ (⊤ : Submodule A M))
  | succ n ih =>
    rintro y ⟨x, rfl⟩
    rw [pow_succ' δ n, Module.End.mul_apply, pow_succ J n, Submodule.mul_smul]
    have hx : (δ ^ n) x ∈ (J ^ n) • (⊤ : Submodule A M) := ih ⟨x, rfl⟩
    refine Submodule.smul_induction_on
      (p := fun m => δ m ∈ (J ^ n) • (J • (⊤ : Submodule A M))) hx ?_ ?_
    · intro a ha m _
      rw [map_smul]
      exact Submodule.smul_mem_smul ha (hδ ⟨m, rfl⟩)
    · intro m₁ m₂ hm₁ hm₂
      rw [map_add]
      exact add_mem hm₁ hm₂

/-- A finitely generated image contained in the nilradical action forces nilpotence.
This uses Mathlib's criterion for nilpotence of a finitely generated ideal. -/
theorem isNilpotent_of_fg_range_le_nilradical_smul
    (δ : Module.End A M) (hfg : (LinearMap.range δ).FG)
    (hδ : LinearMap.range δ ≤ nilradical A • (⊤ : Submodule A M)) :
    IsNilpotent δ := by
  obtain ⟨J, hJfg, hJnil, hδJ⟩ :=
    hfg.exists_fg_ideal_le_smul (nilradical A) (⊤ : Submodule A M) hδ
  obtain ⟨n, hn⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical hJfg).mpr hJnil
  have hrange := range_pow_le_smul_pow δ J hδJ n
  have hzero : LinearMap.range (δ ^ n) ≤ (⊥ : Submodule A M) := by
    simpa only [hn, show (0 : Ideal A) = ⊥ from rfl, Submodule.bot_smul] using hrange
  refine ⟨n, ?_⟩
  ext m
  change (δ ^ n) m = 0
  exact hzero (show (δ ^ n) m ∈ LinearMap.range (δ ^ n) from ⟨m, rfl⟩)

/-- A finitely generated image controlled by an ideal in the nilradical forces
nilpotence. -/
theorem isNilpotent_of_fg_range_le_ideal_smul
    (δ : Module.End A M) (I : Ideal A) (hfg : (LinearMap.range δ).FG)
    (hδ : LinearMap.range δ ≤ I • (⊤ : Submodule A M))
    (hI : I ≤ nilradical A) : IsNilpotent δ := by
  exact isNilpotent_of_fg_range_le_nilradical_smul δ hfg
    (hδ.trans (Submodule.smul_mono_left hI))

/-- On a finite module, an image bound by an ideal in the nilradical implies
nilpotence. -/
theorem isNilpotent_of_range_le_ideal_smul [Module.Finite A M] (δ : Module.End A M) (I : Ideal A)
    (hδ : LinearMap.range δ ≤ I • (⊤ : Submodule A M))
    (hI : I ≤ nilradical A) : IsNilpotent δ := by
  exact isNilpotent_of_fg_range_le_ideal_smul δ I
    (Submodule.FG.of_finite (N := LinearMap.range δ)) hδ hI

end Semimodule

section AddCommGroup

variable {A : Type u} {M : Type v}
  [CommSemiring A] [AddCommGroup M] [Module A M]

/-- The identity minus an endomorphism with finitely generated image controlled by a
nilradical ideal is a unit, by Mathlib's nilpotent-element unit criterion. -/
theorem isUnit_one_sub_of_fg_range_le_ideal_smul
    (δ : Module.End A M) (I : Ideal A) (hfg : (LinearMap.range δ).FG)
    (hδ : LinearMap.range δ ≤ I • (⊤ : Submodule A M))
    (hI : I ≤ nilradical A) : IsUnit (1 - δ) := by
  exact (isNilpotent_of_fg_range_le_ideal_smul δ I hfg hδ hI).isUnit_one_sub

/-- The identity plus an endomorphism with finitely generated image controlled by a
nilradical ideal is a unit, by Mathlib's nilpotent-element unit criterion. -/
theorem isUnit_one_add_of_fg_range_le_ideal_smul
    (δ : Module.End A M) (I : Ideal A) (hfg : (LinearMap.range δ).FG)
    (hδ : LinearMap.range δ ≤ I • (⊤ : Submodule A M))
    (hI : I ≤ nilradical A) : IsUnit (1 + δ) := by
  exact (isNilpotent_of_fg_range_le_ideal_smul δ I hfg hδ hI).isUnit_one_add

end AddCommGroup

end Module.End
