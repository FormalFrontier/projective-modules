/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Johan Commelin, Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Finiteness.Finsupp
public import ProjectiveModules.LinearMap.ChangeOfScalars

/-!
# Finitely supported families of semilinear maps

`LinearMap.finsuppLinearMapₛₗ` sends a finitely supported family of semilinear
maps to a semilinear map with finitely supported values, by evaluation in each
coordinate. It is linear for any auxiliary scalar action commuting with the
action on the target. The comparison is always injective, and is bijective
when the source module is finitely generated.

For the identity scalar homomorphism, this comparison agrees with Mathlib's
`LinearMap.finsuppLinearMap`, with its original commuting-scalar hypotheses.
The scalar, module and index universes are independent.

## References

This construction generalizes Johan Commelin's formalization of
`LinearMap.finsuppLinearMap` in `Mathlib.RingTheory.Finiteness.Finsupp`.
It uses Mathlib's semilinear `LinearMap.flip` and `Finsupp.mapRange.linearMap`.
The finite-source result reuses `LinearMap.finsuppLinearMap_bijective_of_moduleFinite`
after restricting the target scalar action along the scalar homomorphism.
-/

@[expose] public section

universe uR uS uT uL uM uι

namespace LinearMap

section Semilinear

variable {R : Type uR} {S : Type uS} (T : Type uT)
variable [Semiring R] [Semiring S] [Semiring T]
variable {L : Type uL} {M : Type uM} {ι : Type uι}
variable [AddCommMonoid L] [AddCommMonoid M]
variable [Module R L] [Module S M] [Module T M] [SMulCommClass S T M]
variable (σ : R →+* S)

/-- The comparison from finitely supported families of `σ`-semilinear maps to
`σ`-semilinear maps with finitely supported values. Evaluation is coordinatewise,
and the comparison is linear for any commuting auxiliary scalar action. -/
noncomputable def finsuppLinearMapₛₗ :
    (ι →₀ (L →ₛₗ[σ] M)) →ₗ[T] (L →ₛₗ[σ] (ι →₀ M)) :=
  letI : SMulCommClass T S M := SMulCommClass.symm S T M
  flip
    { toFun := fun l => Finsupp.mapRange.linearMap
        (flip (LinearMap.id : (L →ₛₗ[σ] M) →ₗ[T] (L →ₛₗ[σ] M)) l)
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun _ _ => by ext; simp }

/-- The semilinear finitely supported comparison evaluates coordinatewise. -/
@[simp]
theorem finsuppLinearMapₛₗ_apply (f : ι →₀ (L →ₛₗ[σ] M)) (l : L) (i : ι) :
    finsuppLinearMapₛₗ T σ f l i = f i l := rfl

/-- A finitely supported family of semilinear maps is determined by its
coordinatewise evaluation map. No finiteness assumption on the source or the
index type is needed. -/
theorem finsuppLinearMapₛₗ_injective :
    Function.Injective (finsuppLinearMapₛₗ (L := L) (M := M) (ι := ι) T σ) := by
  intro f g h
  ext i l
  simpa only [finsuppLinearMapₛₗ_apply] using
    congrArg (fun F : L →ₛₗ[σ] (ι →₀ M) => F l i) h

/-- The semilinear finitely supported comparison is bijective when its source
module is finitely generated. The index type is unrestricted. This reuses
`finsuppLinearMap_bijective_of_moduleFinite` after restriction of the target
scalar action along `σ`. -/
theorem finsuppLinearMapₛₗ_bijective_of_moduleFinite [Module.Finite R L] :
    Function.Bijective (finsuppLinearMapₛₗ (L := L) (M := M) (ι := ι) T σ) := by
  refine ⟨finsuppLinearMapₛₗ_injective T σ, ?_⟩
  intro f
  let : Module R M := Module.compHom M σ
  let e : (L →ₛₗ[σ] M) ≃+ (L →ₗ[R] M) :=
    (semilinearCompHomEquiv ℕ σ).toAddEquiv
  -- Use the pointwise restricted action on the finitely supported target.
  let f' : L →ₗ[R] (ι →₀ M) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r l => by
        ext i
        change f (r • l) i = σ r • f l i
        simpa only [Finsupp.smul_apply] using
          congrArg (fun v : ι →₀ M => v i) (f.map_smulₛₗ r l) }
  -- Natural-number scalars commute with every module action.
  obtain ⟨g, hg⟩ :=
    (finsuppLinearMap_bijective_of_moduleFinite (R := R) (M := L) (N := M)
      (ι := ι) (S := ℕ)).2 f'
  have hcoord (i : ι) (l : L) :
      (Finsupp.mapRange.addEquiv e.symm g) i l = g i l :=
    semilinearCompHomEquiv_symm_apply ℕ σ (g i) l
  refine ⟨Finsupp.mapRange.addEquiv e.symm g, ?_⟩
  ext l i
  simpa only [finsuppLinearMapₛₗ_apply, hcoord] using
    (show g i l = f l i from
      congrArg (fun F : L →ₗ[R] (ι →₀ M) => F l i) hg)

end Semilinear

section Linear

variable {R : Type uR} (T : Type uT) [Semiring R] [Semiring T]
variable {L : Type uL} {M : Type uM} {ι : Type uι}
variable [AddCommMonoid L] [AddCommMonoid M]
variable [Module R L] [Module R M] [Module T M] [SMulCommClass R T M]

/-- For the identity scalar homomorphism, the semilinear comparison is Mathlib's
`finsuppLinearMap`, under its original commuting auxiliary-scalar hypotheses. -/
@[simp]
theorem finsuppLinearMapₛₗ_id :
    finsuppLinearMapₛₗ (L := L) (M := M) (ι := ι) T (RingHom.id R) =
      finsuppLinearMap (M := L) (N := M) (ι := ι) T := by
  ext f l i
  rfl

end Linear

end LinearMap
