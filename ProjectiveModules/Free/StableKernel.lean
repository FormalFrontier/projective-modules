/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Free.StablePresentation
public import ProjectiveModules.Module.ProjectiveComplement
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.Equiv.Opposite

/-!
# Stably free kernels and finite matrix presentations

A surjection from a stably free module onto a finite stably free module has a
stably free kernel. Finite stably free modules are precisely kernels of
surjections between finite coordinate modules. Matrix multiplication on the
left, linear over the opposite ring, gives the corresponding finite-matrix
specialization for right modules. No rank restriction or invariant basis
number assumption is involved.

Weibel's kernel argument for finite free modules motivates these statements.
The surjective-kernel statement extends it to stably free domains and finite
stably free targets. The presentation uses Mathlib's stably-free API and the
finite-coordinate equivalence in `ProjectiveModules.Free.StablePresentation`;
the splitting uses the projective-module equivalence formalized earlier by
Prism in Formal Frontier.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Definition I.1.2.
* Mathlib, `Mathlib.Algebra.Module.StablyFree.Basic` and
  `Mathlib.LinearAlgebra.Matrix.ToLin`.
* Prism (Formal Frontier), finite stable presentations and projective
  surjection splitting.
-/

@[expose] public section

universe uR uM uN uP uι uκ

namespace Module.IsStablyFree

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]

/-- The kernel of a surjection onto a finite stably free module is stably free
when its domain is stably free. This extends Weibel's finite-free kernel
argument to stably free modules, using projective splitting and Mathlib's
stably-free product characterization. -/
theorem ker_of_surjective [IsStablyFree R M] [Module.Finite R N]
    [IsStablyFree R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    IsStablyFree R (LinearMap.ker f) := by
  classical
  let K := LinearMap.ker f
  obtain ⟨T, hTgroup, hTmodule, hTfinite, hTfree, hMfree⟩ :=
    IsStablyFree.exist_free_prod R M
  let _ : AddCommGroup T := hTgroup
  let _ : Module R T := hTmodule
  let _ : Module.Finite R T := hTfinite
  let _ : Module.Free R T := hTfree
  let _ : Module.Free R (M × T) := hMfree
  obtain ⟨Q, hQgroup, hQmodule, hQfinite, hQfree, hNQfree⟩ :=
    IsStablyFree.exist_free_prod R N
  let _ : AddCommGroup Q := hQgroup
  let _ : Module R Q := hQmodule
  let _ : Module.Finite R Q := hQfinite
  let _ : Module.Free R Q := hQfree
  let _ : Module.Free R (N × Q) := hNQfree
  let split : (N × K) ≃ₗ[R] M := Module.Projective.prodKerEquivOfSurjective f hf
  let e : (K × ((N × Q) × T)) ≃ₗ[R] ((M × T) × Q) :=
    (LinearEquiv.prodAssoc R K (N × Q) T).symm |>.trans
      (((LinearEquiv.prodAssoc R K N Q).symm).prodCongr (LinearEquiv.refl R T)) |>.trans
      (((LinearEquiv.prodComm R K N).prodCongr (LinearEquiv.refl R Q)).prodCongr
        (LinearEquiv.refl R T)) |>.trans
      (LinearEquiv.prodAssoc R (N × K) Q T) |>.trans
      ((LinearEquiv.refl R (N × K)).prodCongr (LinearEquiv.prodComm R Q T)) |>.trans
      (LinearEquiv.prodAssoc R (N × K) T Q).symm |>.trans
      ((split.prodCongr (LinearEquiv.refl R T)).prodCongr (LinearEquiv.refl R Q))
  let _ : Module.Free R (K × ((N × Q) × T)) := Module.Free.of_equiv e.symm
  exact IsStablyFree.of_free_prod R K ((N × Q) × T)

end Module.IsStablyFree

namespace Module

/-- A module is finite and stably free exactly when it is linearly equivalent
to the kernel of a surjection between finite free coordinate modules. The
finite/stably-free-to-kernel direction uses the finite stable presentation
theorem; the kernel-to-finite/stably-free direction uses splitting of a
surjection onto a projective finite free module. -/
theorem finite_isStablyFree_iff_exists_fin_surjective_ker_equiv
    (R : Type uR) [Ring R] (P : Type uP) [AddCommGroup P] [Module R P] :
    (Module.Finite R P ∧ Module.IsStablyFree R P) ↔
      ∃ m n : ℕ, ∃ f : (Fin n → R) →ₗ[R] (Fin m → R),
        Function.Surjective f ∧ Nonempty (P ≃ₗ[R] LinearMap.ker f) := by
  classical
  constructor
  · intro hP
    obtain ⟨m, n, ⟨e⟩⟩ :=
      (exists_fin_prod_linearEquiv_iff_finite_isStablyFree R P).mpr hP
    let f : (Fin n → R) →ₗ[R] (Fin m → R) :=
      (LinearMap.snd R P (Fin m → R)).comp e.symm.toLinearMap
    have hf : Function.Surjective f := by
      intro y
      refine ⟨e (0, y), ?_⟩
      simp [f]
    let g : P →ₗ[R] LinearMap.ker f :=
      LinearMap.codRestrict (LinearMap.ker f)
        (e.toLinearMap.comp (LinearMap.inl R P (Fin m → R))) (by
          intro p
          simp [LinearMap.mem_ker, f])
    have hg : Function.Bijective g := by
      constructor
      · intro p q hpq
        have heq := congrArg (fun x : Fin n → R ↦ (e.symm x).1)
          (congrArg Subtype.val hpq)
        change (e.symm (e (p, 0))).1 = (e.symm (e (q, 0))).1 at heq
        simpa only [e.symm_apply_apply] using heq
      · intro k
        have hk : (e.symm (k : Fin n → R)).2 = 0 := by
          have h := LinearMap.mem_ker.mp k.property
          change (e.symm (k : Fin n → R)).2 = 0 at h
          exact h
        refine ⟨(e.symm (k : Fin n → R)).1, ?_⟩
        apply Subtype.ext
        change e ((e.symm (k : Fin n → R)).1, 0) = (k : Fin n → R)
        have heq : (e.symm (k : Fin n → R)) =
            ((e.symm (k : Fin n → R)).1, 0) := Prod.ext rfl hk
        rw [← heq]
        exact e.apply_symm_apply (k : Fin n → R)
    exact ⟨m, n, f, hf, ⟨LinearEquiv.ofBijective g hg⟩⟩
  · rintro ⟨m, n, f, hf, ⟨e⟩⟩
    let _ : Module.IsStablyFree R (LinearMap.ker f) :=
      Module.IsStablyFree.ker_of_surjective f hf
    let split : ((Fin m → R) × LinearMap.ker f) ≃ₗ[R] (Fin n → R) :=
      Module.Projective.prodKerEquivOfSurjective f hf
    let _ : Module.Finite R ((Fin m → R) × LinearMap.ker f) :=
      Module.Finite.equiv split.symm
    have hkerFinite : Module.Finite R (LinearMap.ker f) :=
      Module.Finite.of_surjective (LinearMap.snd R (Fin m → R) (LinearMap.ker f))
        LinearMap.snd_surjective
    let _ : Module.Finite R (LinearMap.ker f) := hkerFinite
    exact ⟨Module.Finite.equiv e.symm, Module.IsStablyFree.equiv e.symm⟩

end Module

namespace Matrix

/-- For a finite matrix over any ring, a surjective right-linear column map
has finite stably free kernel. The map sends `x` to
`fun i ↦ ∑ j, A i j * x j`, with scalars acting from the opposite ring; it
does not reverse matrix coefficients. This finite-index formulation of the
matrix-kernel result in Weibel, *The K-book*, Definition I.1.2 allows arbitrary
finite row and column index types in place of the source's finite coordinate
sets, and expresses its right-module map using the opposite ring. -/
theorem finite_isStablyFree_ker_mulVecBilin_of_surjective
    {R : Type uR} [Ring R]
    {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ R)
    (hA : Function.Surjective (Matrix.mulVecBilin R Rᵐᵒᵖ A)) :
    Module.Finite Rᵐᵒᵖ (LinearMap.ker (Matrix.mulVecBilin R Rᵐᵒᵖ A)) ∧
      Module.IsStablyFree Rᵐᵒᵖ (LinearMap.ker (Matrix.mulVecBilin R Rᵐᵒᵖ A)) := by
  let regular : Rᵐᵒᵖ ≃ₗ[Rᵐᵒᵖ] R :=
    (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  let _ : Module.Free Rᵐᵒᵖ R := Module.Free.of_equiv regular
  let _ : Module.Finite Rᵐᵒᵖ R := Module.Finite.equiv regular
  let _ : Module.Finite Rᵐᵒᵖ (κ → R) := inferInstance
  let _ : Module.Free Rᵐᵒᵖ (κ → R) := Module.Free.pi _ _
  let _ : Module.IsStablyFree Rᵐᵒᵖ (κ → R) := inferInstance
  let _ : Module.Finite Rᵐᵒᵖ (ι → R) := inferInstance
  let _ : Module.Free Rᵐᵒᵖ (ι → R) := Module.Free.pi _ _
  let _ : Module.IsStablyFree Rᵐᵒᵖ (ι → R) := inferInstance
  have hstable := Module.IsStablyFree.ker_of_surjective
    (Matrix.mulVecBilin R Rᵐᵒᵖ A) hA
  let split := Module.Projective.prodKerEquivOfSurjective
    (Matrix.mulVecBilin R Rᵐᵒᵖ A) hA
  let _ : Module.Finite Rᵐᵒᵖ ((ι → R) ×
      LinearMap.ker (Matrix.mulVecBilin R Rᵐᵒᵖ A)) :=
    Module.Finite.equiv split.symm
  have hkerFinite : Module.Finite Rᵐᵒᵖ
      (LinearMap.ker (Matrix.mulVecBilin R Rᵐᵒᵖ A)) :=
    Module.Finite.of_surjective
      (LinearMap.snd Rᵐᵒᵖ (ι → R)
        (LinearMap.ker (Matrix.mulVecBilin R Rᵐᵒᵖ A))) LinearMap.snd_surjective
  exact ⟨hkerFinite, hstable⟩

end Matrix
