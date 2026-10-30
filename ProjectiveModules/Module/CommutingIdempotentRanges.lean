/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.ProjectiveKernel

/-!
# Ranges of commuting idempotents

The intersection of the ranges of two commuting idempotents is the range of their
product. Over an additive commutative group, their sum is the range of `p + q - p * q`.
Consequently these submodules are projective whenever the ambient module is projective,
and the intersection is finite whenever the ambient module is finite.

The proofs use the fixed-point characterization of the range of an idempotent from
Mathlib's projection API and the projectivity of an idempotent's range from
`ProjectiveModules.Module.ProjectiveKernel`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe uR uM

namespace LinearMap

section AddCommMonoid

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]

/-- The product of two commuting idempotents projects onto the intersection of their ranges. -/
theorem range_mul_of_commute (p q : Module.End R M)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : Commute p q) :
    (p * q).range = p.range ⊓ q.range := by
  have hpq_apply (x : M) : p (q x) = q (p x) :=
    congrArg (fun a : Module.End R M => a x) hpq.eq
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    constructor
    · exact ⟨q y, rfl⟩
    · exact ⟨p y, hpq_apply y |>.symm⟩
  · intro x hx
    refine ⟨x, ?_⟩
    change p (q x) = x
    rw [(LinearMap.IsIdempotentElem.mem_range_iff hq).mp hx.2,
      (LinearMap.IsIdempotentElem.mem_range_iff hp).mp hx.1]

end AddCommMonoid

section AddCommGroup

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

private theorem add_sub_mul_fixes_ranges (p q : Module.End R M)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : Commute p q) :
    (∀ x, (p + q - p * q) (p x) = p x) ∧
      (∀ x, (p + q - p * q) (q x) = q x) := by
  have hp_apply (x : M) : p (p x) = p x :=
    congrArg (fun a : Module.End R M => a x) hp
  have hq_apply (x : M) : q (q x) = q x :=
    congrArg (fun a : Module.End R M => a x) hq
  have hpq_apply (x : M) : p (q x) = q (p x) :=
    congrArg (fun a : Module.End R M => a x) hpq.eq
  constructor
  · intro x
    change p (p x) + q (p x) - p (q (p x)) = p x
    simp only [hp_apply, ← hpq_apply, add_sub_cancel_right]
  · intro x
    change p (q x) + q (q x) - p (q (q x)) = q x
    simp only [hq_apply, add_sub_cancel_left]

/-- The sum of the ranges of commuting idempotents is the range of `p + q - p * q`. -/
theorem range_add_sub_mul_of_commute (p q : Module.End R M)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : Commute p q) :
    (p + q - p * q).range = p.range ⊔ q.range := by
  obtain ⟨hleft, hright⟩ := add_sub_mul_fixes_ranges p q hp hq hpq
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    change p y + q y - p (q y) ∈ p.range ⊔ q.range
    have hpq_apply : p (q y) = q (p y) :=
      congrArg (fun a : Module.End R M => a y) hpq.eq
    have hy : p y + q (y - p y) ∈ p.range ⊔ q.range :=
      Submodule.add_mem_sup
        (show p y ∈ p.range from ⟨y, rfl⟩)
        (show q (y - p y) ∈ q.range from ⟨y - p y, rfl⟩)
    simpa only [q.map_sub, ← hpq_apply, add_sub_assoc] using hy
  · apply sup_le
    · rintro x ⟨y, rfl⟩
      exact ⟨p y, hleft y⟩
    · rintro x ⟨y, rfl⟩
      exact ⟨q y, hright y⟩

end AddCommGroup

end LinearMap

namespace Module.Finite

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]

/-- In a finite module, the intersection of the ranges of commuting idempotents is finite. -/
theorem inf_range_of_commute [Module.Finite R M] (p q : Module.End R M)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : Commute p q) :
    Module.Finite R ↥(p.range ⊓ q.range) := by
  rw [← LinearMap.range_mul_of_commute p q hp hq hpq]
  infer_instance

end Module.Finite

namespace Module.Projective

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]

/-- In a projective module, the intersection of commuting idempotents' ranges is projective. -/
theorem inf_range_of_commute [Module.Projective R M] (p q : Module.End R M)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : Commute p q) :
    Module.Projective R ↥(p.range ⊓ q.range) := by
  rw [← LinearMap.range_mul_of_commute p q hp hq hpq]
  exact range_of_isIdempotentElem (p * q) (IsIdempotentElem.mul_of_commute hpq hp hq)

/-- In a projective module, the sum of the ranges of commuting idempotents is projective. -/
theorem sup_range_of_commute
    {N : Type uM} [AddCommGroup N] [Module R N] [Module.Projective R N]
    (p q : Module.End R N)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : Commute p q) :
    Module.Projective R ↥(p.range ⊔ q.range) := by
  rw [← LinearMap.range_add_sub_mul_of_commute p q hp hq hpq]
  exact range_of_isIdempotentElem (p + q - p * q)
    (IsIdempotentElem.add_sub_mul_of_commute hpq hp hq)

end Module.Projective
