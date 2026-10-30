/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Presentation.Finite
public import ProjectiveModules.KTheory.K0
public import ProjectiveModules.Module.FinitePresentation
public import ProjectiveModules.Module.ProjectiveKernelComparison

/-!
# Intrinsic Euler classes of modules with projective presentation kernels

For two surjections from finite projective right modules to the same semimodule,
the difference between the source class and the kernel class is independent of
the presentation. Only the first kernel is assumed finite projective: the
kernel-property comparison supplies these properties for the second kernel.
No projectivity or additive-group structure is assumed on the common target.

`KTheory.K0.eulerClass R M hM` assigns this difference to the original finitely
presented right module `M`, given a proof `hM` that some finite-free cover has
projective kernel. The cover is chosen internally. Every surjection from a
finite projective module has finite projective kernel and computes the same
class. Finite projective modules recover their existing `KTheory.K0.of` class;
zero modules have class zero, and same-scalar linear equivalences preserve the
Euler class. Stock presentations by finitely many generators and relations
supply the construction when their kernel is projective, without requiring
independent relations.

The ring may be noncommutative or zero, and scalar and carrier universes are
independent. No target projectivity or free-kernel hypothesis is imposed.
Naturality under arbitrary underived scalar extension is not asserted.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory* (2013),
  Schanuel's lemma and Euler classes of finite projective resolutions.
* Mathlib's finite-presentation, finite-free-cover and generators-and-relations
  presentation APIs.
-/

@[expose] public section

universe uR uP uQ uM uN uG uRel

namespace KTheory.K0

variable (R : Type uR) [Ring R]

section Comparison

variable {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P]
  [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]
variable {Q : Type uQ} [AddCommGroup Q] [Module Rᵐᵒᵖ Q]
  [Module.Finite Rᵐᵒᵖ Q] [Module.Projective Rᵐᵒᵖ Q]
variable {M : Type uM} [AddCommMonoid M] [Module Rᵐᵒᵖ M]

/-- The source-minus-kernel class is independent of a finite projective
presentation. Finite generation and projectivity of the second kernel are
derived from those of the first; the target is only a semimodule.

This is a consequence of Schanuel's lemma; see Weibel, *The K-book* (2013). -/
theorem sub_ker_eq_sub_ker_of_surjective
    (p : P →ₗ[Rᵐᵒᵖ] M) (q : Q →ₗ[Rᵐᵒᵖ] M)
    [Module.Finite Rᵐᵒᵖ p.ker] [Module.Projective Rᵐᵒᵖ p.ker]
    (hp : Function.Surjective p) (hq : Function.Surjective q) :
    of R P - of R p.ker = of R Q -
      @of R _ q.ker _ _
        (LinearMap.finite_ker_of_surjective_of_finite_ker p q hp hq)
        (LinearMap.projective_ker_of_surjective_of_projective_ker p q hp hq) := by
  have : Module.Finite Rᵐᵒᵖ q.ker :=
    LinearMap.finite_ker_of_surjective_of_finite_ker p q hp hq
  have : Module.Projective Rᵐᵒᵖ q.ker :=
    LinearMap.projective_ker_of_surjective_of_projective_ker p q hp hq
  obtain ⟨e⟩ := LinearMap.nonempty_kerProdEquiv_of_surjective p q hp hq
  have h := of_eq_of_equiv R (p.ker × Q) e
  rw [of_prod, of_prod] at h
  apply sub_eq_sub_iff_add_eq_add.mpr
  calc
    of R P + of R q.ker = of R q.ker + of R P := add_comm _ _
    _ = of R p.ker + of R Q := h.symm
    _ = of R Q + of R p.ker := add_comm _ _

end Comparison

section Constructors

variable {M : Type uM} [AddCommMonoid M] [Module Rᵐᵒᵖ M]
variable {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P]
  [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P]

/-- A surjection from a finite projective module with projective kernel gives a
finite-free cover of the original target with projective kernel.

This uses the kernel-property form of Schanuel's lemma; see Weibel,
*The K-book* (2013). -/
theorem exists_projective_ker_free_cover_of_surjective
    (p : P →ₗ[Rᵐᵒᵖ] M) [Module.Projective Rᵐᵒᵖ p.ker]
    (hp : Function.Surjective p) :
    ∃ (n : ℕ) (π : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M),
      Function.Surjective π ∧ Module.Projective Rᵐᵒᵖ π.ker := by
  let : Module.Finite Rᵐᵒᵖ M := Module.Finite.of_surjective p hp
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' Rᵐᵒᵖ M
  exact ⟨n, π, hπ,
    LinearMap.projective_ker_of_surjective_of_projective_ker p π hp hπ⟩

/-- A finite projective presentation with finite projective kernel gives both
finite presentation of the original target and eligibility for its Euler class.
The target need not be projective. -/
theorem finitePresentation_and_exists_projective_ker_free_cover
    (p : P →ₗ[Rᵐᵒᵖ] M)
    [Module.Finite Rᵐᵒᵖ p.ker] [Module.Projective Rᵐᵒᵖ p.ker]
    (hp : Function.Surjective p) :
    Module.FinitePresentation Rᵐᵒᵖ M ∧
      ∃ (n : ℕ) (π : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M),
        Function.Surjective π ∧ Module.Projective Rᵐᵒᵖ π.ker := by
  let : Module.FinitePresentation Rᵐᵒᵖ P :=
    Module.finitePresentation_of_projective Rᵐᵒᵖ P
  exact ⟨LinearMap.finitePresentation_of_surjective p hp
      (Module.Finite.iff_fg.mp inferInstance),
    exists_projective_ker_free_cover_of_surjective R p hp⟩

end Constructors

section EulerClass

variable (M : Type uM) [AddCommMonoid M] [Module Rᵐᵒᵖ M]

/-- The Euler class of a finitely presented right module admitting a finite-free
cover with projective kernel. It is the source class minus the kernel class of
an internally chosen cover, in the existing group `KTheory.K0 R`.

The kernel is finitely generated by finite presentation of `M`; neither the
target nor the kernel is required to be free. Independence of the cover follows
from Schanuel's lemma; see Weibel, *The K-book* (2013). -/
noncomputable def eulerClass [Module.FinitePresentation Rᵐᵒᵖ M]
    (hM : ∃ (n : ℕ) (π : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M),
      Function.Surjective π ∧ Module.Projective Rᵐᵒᵖ π.ker) : K0 R := by
  classical
  let π := hM.choose_spec.choose
  letI : Module.Finite Rᵐᵒᵖ π.ker :=
    Module.FinitePresentation.finite_ker π hM.choose_spec.choose_spec.1
  letI : Module.Projective Rᵐᵒᵖ π.ker := hM.choose_spec.choose_spec.2
  exact of R (Fin hM.choose → Rᵐᵒᵖ) - of R π.ker

variable {M}
variable {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P]
  [Module.Projective Rᵐᵒᵖ P]

/-- Euler-class eligibility implies that every surjection from a projective
module has projective kernel. No certificate for this kernel is an input. -/
theorem eulerClass_projective_ker
    (hM : ∃ (n : ℕ) (π : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M),
      Function.Surjective π ∧ Module.Projective Rᵐᵒᵖ π.ker)
    (p : P →ₗ[Rᵐᵒᵖ] M) (hp : Function.Surjective p) :
    Module.Projective Rᵐᵒᵖ p.ker := by
  obtain ⟨n, π, hπ, hker⟩ := hM
  let : Module.Projective Rᵐᵒᵖ π.ker := hker
  exact LinearMap.projective_ker_of_surjective_of_projective_ker π p hπ hp

variable (M) [Module.FinitePresentation Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ P]

/-- Every surjection from an original finite projective module computes the
intrinsic Euler class. Both finiteness and projectivity of its kernel are
derived, rather than assumed.

The value comparison is Schanuel's lemma in K₀; see Weibel, *The K-book* (2013). -/
theorem eulerClass_eq_sub_ker_of_surjective
    (hM : ∃ (n : ℕ) (π : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M),
      Function.Surjective π ∧ Module.Projective Rᵐᵒᵖ π.ker)
    (p : P →ₗ[Rᵐᵒᵖ] M) (hp : Function.Surjective p) :
    eulerClass R M hM = of R P -
      @of R _ p.ker _ _ (Module.FinitePresentation.finite_ker p hp)
        (eulerClass_projective_ker R hM p hp) := by
  classical
  let π := hM.choose_spec.choose
  let : Module.Finite Rᵐᵒᵖ π.ker :=
    Module.FinitePresentation.finite_ker π hM.choose_spec.choose_spec.1
  let : Module.Projective Rᵐᵒᵖ π.ker := hM.choose_spec.choose_spec.2
  exact sub_ker_eq_sub_ker_of_surjective R π p hM.choose_spec.choose_spec.1 hp

end EulerClass

section Projective

variable (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]

/-- Every finite projective module is eligible for its Euler class, using the
identity presentation. No stable-freeness hypothesis is required. -/
theorem exists_projective_ker_free_cover_of_projective :
    ∃ (n : ℕ) (π : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M),
      Function.Surjective π ∧ Module.Projective Rᵐᵒᵖ π.ker := by
  let : Module.Projective Rᵐᵒᵖ (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M).ker := by
    rw [LinearMap.ker_id]
    infer_instance
  exact exists_projective_ker_free_cover_of_surjective R
    (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) Function.surjective_id

/-- For every finite projective module, its intrinsic Euler class is its
existing K₀ class, for every proof of eligibility. This includes projective
modules that are not stably free. -/
@[simp]
theorem eulerClass_eq_of_projective
    (hM : ∃ (n : ℕ) (π : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M),
      Function.Surjective π ∧ Module.Projective Rᵐᵒᵖ π.ker) :
    @eulerClass R _ M _ _ (Module.finitePresentation_of_projective Rᵐᵒᵖ M) hM =
      of R M := by
  let : Module.FinitePresentation Rᵐᵒᵖ M :=
    Module.finitePresentation_of_projective Rᵐᵒᵖ M
  simpa only [LinearMap.ker_id, of_zero, sub_zero] using
    eulerClass_eq_sub_ker_of_surjective R M hM
      (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) Function.surjective_id

end Projective

section Presentation

variable {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- A stock presentation with finitely many generators and projective kernel
supplies Euler-class eligibility. Finite presentation of the target follows
from `pres.finitePresentation` when the relation index is finite. -/
theorem exists_projective_ker_free_cover_of_presentation
    (pres : Module.Presentation.{uG, uRel} Rᵐᵒᵖ M) [Finite pres.G]
    [Module.Projective Rᵐᵒᵖ pres.π.ker] :
    ∃ (n : ℕ) (π : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M),
      Function.Surjective π ∧ Module.Projective Rᵐᵒᵖ π.ker :=
  exists_projective_ker_free_cover_of_surjective R pres.π pres.surjective_π

variable (pres : Module.Presentation.{uG, uRel} Rᵐᵒᵖ M) [Finite pres.G]
  [Module.Projective Rᵐᵒᵖ pres.π.ker]

/-- A presentation by finitely many generators and relations computes the
intrinsic Euler class as its source class minus its projective kernel class.
Relations need not be independent, and the kernel need not be free. -/
theorem eulerClass_eq_sub_ker_of_presentation [Finite pres.R]
    (hM : ∃ (n : ℕ) (π : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M),
      Function.Surjective π ∧ Module.Projective Rᵐᵒᵖ π.ker) :
    @eulerClass R _ M _ _ pres.finitePresentation hM =
      of R (pres.G →₀ Rᵐᵒᵖ) -
        @of R _ pres.π.ker _ _
          (Module.Finite.of_fg (by
            rw [pres.ker_π]
            exact Submodule.fg_span (Set.finite_range _))) inferInstance := by
  let : Module.FinitePresentation Rᵐᵒᵖ M := pres.finitePresentation
  exact eulerClass_eq_sub_ker_of_surjective R M hM pres.π pres.surjective_π

end Presentation

section Zero

variable (M : Type uM) [AddCommMonoid M] [Module Rᵐᵒᵖ M] [Subsingleton M]

/-- Every zero right module admits a finite-free cover with projective kernel,
including over the zero ring. -/
theorem exists_projective_ker_free_cover_of_subsingleton :
    ∃ (n : ℕ) (π : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M),
      Function.Surjective π ∧ Module.Projective Rᵐᵒᵖ π.ker := by
  refine ⟨0, 0, fun m ↦ ⟨0, Subsingleton.elim _ _⟩, ?_⟩
  infer_instance

/-- A zero right module has zero intrinsic Euler class. Its finite-presentation
certificate is derived on the original additive-monoid carrier. -/
@[simp]
theorem eulerClass_zero
    (hM : ∃ (n : ℕ) (π : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M),
      Function.Surjective π ∧ Module.Projective Rᵐᵒᵖ π.ker) :
    @eulerClass R _ M _ _
      (finitePresentation_and_exists_projective_ker_free_cover R
        (0 : (Fin 0 → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M)
        (fun _ ↦ ⟨0, Subsingleton.elim _ _⟩)).1 hM = 0 := by
  have hπ : Function.Surjective (0 : (Fin 0 → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M) :=
    fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
  let : Module.FinitePresentation Rᵐᵒᵖ M :=
    (finitePresentation_and_exists_projective_ker_free_cover R
      (0 : (Fin 0 → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M) hπ).1
  simpa only [of_zero, sub_self] using
    eulerClass_eq_sub_ker_of_surjective R M hM
      (0 : (Fin 0 → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M) hπ

end Zero

section Equivalence

variable {M : Type uM} [AddCommMonoid M] [Module Rᵐᵒᵖ M]
  [Module.FinitePresentation Rᵐᵒᵖ M]
variable {N : Type uN} [AddCommMonoid N] [Module Rᵐᵒᵖ N]

/-- Same-scalar linear equivalence preserves the intrinsic Euler class, with
independent carrier universes. Finite presentation of the second module is
derived from the equivalence; no target projectivity is assumed. -/
theorem eulerClass_eq_of_equiv
    (hM : ∃ (n : ℕ) (π : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] M),
      Function.Surjective π ∧ Module.Projective Rᵐᵒᵖ π.ker)
    (hN : ∃ (n : ℕ) (π : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] N),
      Function.Surjective π ∧ Module.Projective Rᵐᵒᵖ π.ker)
    (e : M ≃ₗ[Rᵐᵒᵖ] N) :
    eulerClass R M hM = @eulerClass R _ N _ _
      (LinearMap.finitePresentation_of_surjective e.toLinearMap e.surjective (by
        rw [e.ker]
        exact Submodule.fg_bot)) hN := by
  let : Module.FinitePresentation Rᵐᵒᵖ N :=
    LinearMap.finitePresentation_of_surjective e.toLinearMap e.surjective (by
      rw [e.ker]
      exact Submodule.fg_bot)
  have hcover := hM
  obtain ⟨n, π, hπ, hker⟩ := hcover
  let : Module.Finite Rᵐᵒᵖ π.ker := Module.FinitePresentation.finite_ker π hπ
  let : Module.Projective Rᵐᵒᵖ π.ker := hker
  let q : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] N := e.toLinearMap.comp π
  have hq : Function.Surjective q := e.surjective.comp hπ
  let k : π.ker ≃ₗ[Rᵐᵒᵖ] q.ker := LinearEquiv.ofEq _ _ (e.ker_comp π).symm
  let : Module.Finite Rᵐᵒᵖ q.ker := Module.Finite.equiv k
  let : Module.Projective Rᵐᵒᵖ q.ker := Module.Projective.of_equiv' k
  calc
    eulerClass R M hM = of R (Fin n → Rᵐᵒᵖ) - of R π.ker :=
      eulerClass_eq_sub_ker_of_surjective R M hM π hπ
    _ = of R (Fin n → Rᵐᵒᵖ) - of R q.ker :=
      congrArg (fun a ↦ of R (Fin n → Rᵐᵒᵖ) - a) (of_eq_of_equiv R π.ker k)
    _ = eulerClass R N hN :=
      (eulerClass_eq_sub_ker_of_surjective R N hN q hq).symm

end Equivalence

end KTheory.K0
