/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
public import ProjectiveModules.Module.ProjectiveKernelComparison

/-!
# K₀ classes of projective presentations

For two surjections from finite projective right modules to the same semimodule,
the difference between the source class and the kernel class is independent of
the presentation. Only the first kernel is assumed finite projective: the
kernel-property comparison supplies these properties for the second kernel.
No projectivity or additive-group structure is assumed on the common target.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory* (2013),
  Schanuel's lemma.
-/

@[expose] public section

universe uR uP uQ uM

namespace KTheory.K0

variable (R : Type uR) [Ring R]
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

end KTheory.K0
