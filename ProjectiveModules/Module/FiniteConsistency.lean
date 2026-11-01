/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Finite consistency of row-finite linear systems

A row is a finitely supported coefficient vector, but a solution is an arbitrary
function on the coordinate type. If the target satisfies `Module.Baer`, solving
every finite set of rows suffices to solve all rows simultaneously. Over a
semisimple ring this gives `Finsupp.exists_solution_iff_finite` for every left
module, in particular for modules over division rings.

The proof evaluates each finitely supported relation using one finite solution,
factors the prescribed values through the row span, and extends from that span.
Evaluation is linear in the coefficient vector; for noncommutative scalars no
linearity in the product of unknowns is asserted.

## References

The finite-support/span-extension argument is due to Formal Frontier Agents.
We use Mathlib's formalizations of Baer's criterion by Jujian Zhang, semisimple
modules by Aaron Anderson, linear combinations by Johannes Hölzl, and quotient
isomorphisms by Johannes Hölzl, Mario Carneiro, Kevin Buzzard and Yury Kudryashov.
-/

@[expose] public section

universe uR uM uI uJ

variable {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module R M]

/-- Every left module over a semisimple ring satisfies Baer's ideal-extension
criterion, without a size restriction relating the scalar and module universes. -/
theorem Module.Baer.of_isSemisimpleRing [IsSemisimpleRing R] : Module.Baer R M := by
  intro K g
  obtain ⟨L, hL⟩ :=
    IsSemisimpleModule.extension_property K.subtype K.subtype_injective g
  refine ⟨L, fun r hr => ?_⟩
  exact LinearMap.congr_fun hL ⟨r, hr⟩

variable {I : Type uI} {J : Type uJ}

/-- A row-finite linear system with values in a module satisfying Baer's criterion
has a solution if every finite set of rows has a solution. The assignments for
different finite sets need not be compatible, and the full solution need not
have finite support. Scalars need not commute. -/
theorem Module.Baer.exists_solution_of_finite (hM : Module.Baer R M)
    (a : I → (J →₀ R)) (b : I → M)
    (hfinite : ∀ s : Finset I, ∃ x : J → M,
      ∀ i ∈ s, (a i).sum (fun j r => r • x j) = b i) :
    ∃ x : J → M, ∀ i, (a i).sum (fun j r => r • x j) = b i := by
  classical
  let T : (I →₀ R) →ₗ[R] (J →₀ R) := Finsupp.linearCombination R a
  let q : (I →₀ R) →ₗ[R] M := Finsupp.linearCombination R b
  -- Each relation involves only finitely many rows, so one finite solution
  -- shows that the same relation annihilates the prescribed values.
  have hker : LinearMap.ker T ≤ LinearMap.ker q := by
    intro c hc
    obtain ⟨x, hx⟩ := hfinite c.support
    have heval : Finsupp.linearCombination R x (T c) = q c := by
      change Finsupp.linearCombination R x (Finsupp.linearCombination R a c) =
        Finsupp.linearCombination R b c
      rw [Finsupp.linearCombination_linearCombination]
      simp only [Finsupp.linearCombination_apply]
      exact Finsupp.sum_congr fun i hi => congrArg (fun m : M => c i • m) (hx i hi)
    apply LinearMap.mem_ker.mpr
    rw [← heval, LinearMap.mem_ker.mp hc, map_zero]
  let g : LinearMap.range T →ₗ[R] M :=
    ((LinearMap.ker T).liftQ q hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hg (c : I →₀ R) (hc : T c ∈ LinearMap.range T) : g ⟨T c, hc⟩ = q c := by
    change (LinearMap.ker T).liftQ q hker (T.quotKerEquivRange.symm ⟨T c, hc⟩) = q c
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    exact LinearMap.congr_fun ((LinearMap.ker T).liftQ_mkQ q hker) c
  obtain ⟨L, hL⟩ := hM.extension_property (M := LinearMap.range T) (N := J →₀ R)
    (LinearMap.range T).subtype (LinearMap.range T).subtype_injective g
  have hLa (i : I) : L (a i) = b i := by
    have hi : T (Finsupp.single i 1) = a i := by simp [T]
    have hmem : T (Finsupp.single i 1) ∈ LinearMap.range T :=
      ⟨Finsupp.single i 1, rfl⟩
    calc
      L (a i) = L (T (Finsupp.single i 1)) := congrArg L hi.symm
      _ = g ⟨T (Finsupp.single i 1), hmem⟩ :=
        LinearMap.congr_fun hL ⟨T (Finsupp.single i 1), hmem⟩
      _ = q (Finsupp.single i 1) := hg _ hmem
      _ = b i := by simp [q]
  let x : J → M := fun j => L (Finsupp.single j 1)
  have hEval : Finsupp.linearCombination R x = L := by
    apply Finsupp.lhom_ext
    intro j r
    rw [Finsupp.linearCombination_single]
    dsimp only [x]
    rw [← Finsupp.smul_single_one j r, map_smul]
  refine ⟨x, fun i => ?_⟩
  rw [← Finsupp.linearCombination_apply, hEval]
  exact hLa i

/-- Over a semisimple ring, a row-finite linear system in any left module has a
solution exactly when every finite set of rows has a solution. Row and coordinate
types and the scalar and target types may have independent universes. In
particular this applies to division rings, with no dimension or countability
restriction. -/
theorem Finsupp.exists_solution_iff_finite [IsSemisimpleRing R]
    (a : I → (J →₀ R)) (b : I → M) :
    (∃ x : J → M, ∀ i, (a i).sum (fun j r => r • x j) = b i) ↔
      ∀ s : Finset I, ∃ x : J → M,
        ∀ i ∈ s, (a i).sum (fun j r => r • x j) = b i := by
  constructor
  · rintro ⟨x, hx⟩ s
    exact ⟨x, fun i _ => hx i⟩
  · exact Module.Baer.exists_solution_of_finite
      (Module.Baer.of_isSemisimpleRing (R := R) (M := M)) a b
