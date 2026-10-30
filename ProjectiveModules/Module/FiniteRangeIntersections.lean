/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.CommutingProducts
public import ProjectiveModules.Module.ProjectiveKernel
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Fintype.EquivFin

/-!
# Intersections of ranges of commuting idempotents

The range of a finite product of pairwise commuting idempotent endomorphisms is the
intersection of their ranges. Consequently, a finite intersection of such ranges is
finitely generated if the ambient module is finitely generated, and projective if the
ambient module is projective. Neither conclusion requires the other ambient hypothesis.

The scalar semiring, additive commutative monoid, module action and original index type
are retained throughout. The empty intersection is the whole ambient module.

## References

* Mathlib's fixed-point characterization of idempotent ranges in
  `Mathlib.LinearAlgebra.Projection` and image finiteness in
  `Mathlib.RingTheory.Finiteness.Basic`.
* Charles A. Weibel, *The K-book*, Chapter I, §2, for projective modules and split summands.
-/

@[expose] public section

universe uR uM uI

namespace Module.End

variable {R : Type uR} {M : Type uM} {I : Type uI}
variable [Semiring R] [AddCommMonoid M] [Module R M]

private theorem noncommProd_apply_eq_self_of_forall
    (s : Finset I) (f : I → Module.End R M)
    (comm : (s : Set I).Pairwise (fun i j => Commute (f i) (f j)))
    (x : M) (hx : ∀ i ∈ s, f i x = x) :
    (s.noncommProd f comm) x = x := by
  refine Finset.noncommProd_induction s f comm
    (p := fun g : Module.End R M => g x = x) ?_ ?_ hx
  · intro g h hg hh
    rw [Module.End.mul_apply, hh, hg]
  · exact Module.End.one_apply x

end Module.End

namespace LinearMap

variable {R : Type uR} {M : Type uM} {I : Type uI}
variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- The range of a finite product of pairwise commuting idempotent endomorphisms is the
intersection of their ranges. The empty product has range `⊤`. The proof uses Mathlib's
fixed-point characterization of idempotent ranges. -/
theorem range_noncommProd (s : Finset I) (f : I → Module.End R M)
    (comm : (s : Set I).Pairwise (fun i j => Commute (f i) (f j)))
    (hf : ∀ i ∈ s, IsIdempotentElem (f i)) :
    (s.noncommProd f comm).range = ⨅ i ∈ s, (f i).range := by
  have hprod : IsIdempotentElem (s.noncommProd f comm) :=
    IsIdempotentElem.noncommProd s f comm hf
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    have hfix := (LinearMap.IsIdempotentElem.mem_range_iff hprod).mp hx
    apply (Submodule.mem_iInf _).mpr
    intro i
    apply (Submodule.mem_iInf _).mpr
    intro hi
    apply (LinearMap.IsIdempotentElem.mem_range_iff (hf i hi)).mpr
    have habs := congrArg (fun q : Module.End R M => q x)
      (IsIdempotentElem.mul_noncommProd s f comm hi (hf i hi))
    have heval :=
      (Module.End.mul_apply (f i) (s.noncommProd f comm) x).symm.trans habs
    exact (congrArg (fun y : M => f i y) hfix.symm).trans (heval.trans hfix)
  · intro hx
    apply (LinearMap.IsIdempotentElem.mem_range_iff hprod).mpr
    apply Module.End.noncommProd_apply_eq_self_of_forall s f comm x
    intro i hi
    exact (LinearMap.IsIdempotentElem.mem_range_iff (hf i hi)).mp
      ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hx i) hi)

private theorem range_noncommProd_univ [Fintype I] (p : I → Module.End R M)
    (hp : ∀ i, IsIdempotentElem (p i))
    (hcomm : Pairwise (fun i j => Commute (p i) (p j))) :
    ((Finset.univ : Finset I).noncommProd p
      (fun _ _ _ _ hij => hcomm hij)).range = ⨅ i, (p i).range := by
  refine (range_noncommProd (Finset.univ : Finset I) p _ (fun i _ => hp i)).trans ?_
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    apply (Submodule.mem_iInf _).mpr
    intro i
    exact (Submodule.mem_iInf _).mp
      ((Submodule.mem_iInf _).mp hx i) (Finset.mem_univ i)
  · intro hx
    apply (Submodule.mem_iInf _).mpr
    intro i
    apply (Submodule.mem_iInf _).mpr
    intro _
    exact (Submodule.mem_iInf _).mp hx i

end LinearMap

namespace Module.Finite

variable {R : Type uR} {M : Type uM} {I : Type uI}
variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- A finite intersection of ranges of pairwise commuting idempotent endomorphisms of a
finitely generated semimodule is finitely generated. No projectivity hypothesis is required.
The scalars may be an arbitrary semiring. -/
theorem iInf_range_of_commuting_idempotents [_root_.Finite I] [Module.Finite R M]
    (p : I → Module.End R M) (hp : ∀ i, IsIdempotentElem (p i))
    (hcomm : Pairwise (fun i j => Commute (p i) (p j))) :
    Module.Finite R ↥(⨅ i, (p i).range) := by
  let : Fintype I := Fintype.ofFinite I
  rw [← LinearMap.range_noncommProd_univ p hp hcomm]
  exact Module.Finite.range _

end Module.Finite

namespace Module.Projective

variable {R : Type uR} {M : Type uM} {I : Type uI}
variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- A finite intersection of ranges of pairwise commuting idempotent endomorphisms of a
projective module is projective. No finite-generation hypothesis is required. The
split-summand principle is discussed in Weibel, *The K-book*, Chapter I, §2. Here the
scalars are allowed to be an arbitrary semiring. -/
theorem iInf_range_of_commuting_idempotents [_root_.Finite I] [Module.Projective R M]
    (p : I → Module.End R M) (hp : ∀ i, IsIdempotentElem (p i))
    (hcomm : Pairwise (fun i j => Commute (p i) (p j))) :
    Module.Projective R ↥(⨅ i, (p i).range) := by
  let : Fintype I := Fintype.ofFinite I
  rw [← LinearMap.range_noncommProd_univ p hp hcomm]
  exact Module.Projective.range_of_isIdempotentElem _
    (IsIdempotentElem.noncommProd _ _ _ (fun i _ => hp i))

end Module.Projective
