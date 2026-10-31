/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.LocalRing
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Local bases with prescribed fiber rank

A projective module localized at a maximal ideal has a basis indexed by `Fin r` if its
residue fiber has cardinal rank `r`. No finite-generation hypothesis on the original
module is needed: projectivity gives freeness over the local ring, and scalar extension
to the residue field determines the cardinality of that local basis.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Module.Projective

/-- If the residue fiber of a projective module at a maximal ideal has cardinal rank
`r`, its localization at that ideal admits a basis indexed by `Fin r`.

The original module need not be finitely generated, and `r = 0` is allowed. -/
theorem nonempty_basis_atPrime_of_residue_rank_eq
    {R : Type u} [CommRing R]
    {P : Type v} [AddCommMonoid P] [Module R P] [Module.Projective R P]
    (m : Ideal R) [m.IsMaximal] (r : ℕ)
    (h : Module.rank (R ⧸ m) ((R ⧸ m) ⊗[R] P) = (r : Cardinal)) :
    Nonempty (Module.Basis (Fin r) (Localization.AtPrime m)
      ((Localization.AtPrime m) ⊗[R] P)) := by
  classical
  let A := Localization.AtPrime m
  let K := R ⧸ m
  let N := A ⊗[R] P
  let : Field K := Ideal.Quotient.field m
  let : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A m
  -- Enrich only the local module, retaining its additive monoid and scalar action.
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup A
  let : Module.Projective A N :=
    Module.Projective.tensorProduct (R := A) (R₀ := R) (M := A) (N := P)
  let : Module.Free A N := Module.Projective.free_of_isLocalRing
  let b := Module.Free.chooseBasis A N
  -- The quotient map extends across localization without changing the R-algebra on K.
  have hunit : ∀ s : m.primeCompl, IsUnit (Ideal.Quotient.mk m (s : R)) := by
    intro s
    apply isUnit_iff_ne_zero.mpr
    intro hs
    exact (Ideal.mem_primeCompl_iff.mp s.property) (Ideal.Quotient.eq_zero_iff_mem.mp hs)
  let q : A →+* K := IsLocalization.lift (S := A) hunit
  let : Algebra A K := q.toAlgebra
  let : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq fun x => by
    change Ideal.Quotient.mk m x = q (algebraMap R A x)
    exact (IsLocalization.lift_eq (S := A) hunit x).symm
  -- The fiber basis has exactly the same index as the local basis.
  let c := (b.baseChange K).map
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A K K P)
  have hindex : Cardinal.mk (Module.Free.ChooseBasisIndex A N) = (r : Cardinal) := by
    apply Cardinal.lift_inj.{_, max u v}.mp
    have hc := c.mk_eq_rank
    change Cardinal.lift (Cardinal.mk (Module.Free.ChooseBasisIndex A N)) =
      Cardinal.lift (Module.rank (R ⧸ m) ((R ⧸ m) ⊗[R] P)) at hc
    simpa only [h, Cardinal.lift_natCast] using hc
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hindex
  exact ⟨b.reindex e⟩

end Module.Projective
