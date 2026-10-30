/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules

/-!
# A semilinear tensor-Hom comparison with an infinite source

The diagonal homomorphism from `ℕ` to `ℕ × ℕ` is not surjective. The source
`ℕ →₀ ℕ` is countably free, whereas the tensor factor is the finite free module
`Fin 2 → ℕ × ℕ`. A coordinate homomorphism tensored with the first vector has
nonzero canonical image, detected by the left unitor. The public bijectivity
theorem then identifies its preimage uniquely. No finiteness of the Hom source
is needed.
-/

open scoped TensorProduct

namespace ProjectiveModulesTests

private abbrev S := ℕ × ℕ
private abbrev L := ℕ →₀ ℕ
private abbrev N := Fin 2 → S

private def diagonal : ℕ →+* S := Nat.castRingHom S

private noncomputable def coordinate : L →ₛₗ[diagonal] S :=
  diagonal.toSemilinearMap.comp (Finsupp.lapply 0)

/-- The comparison has a nonzero value and a unique tensor preimage, even for a
countably free source and a nonsurjective scalar homomorphism of semirings. -/
theorem diagonal_tensorHom_nonzero_unique :
    ¬ Function.Surjective diagonal ∧
      ∃ g : L →ₛₗ[diagonal] S ⊗[S] N, g ≠ 0 ∧
        ∃! t : (L →ₛₗ[diagonal] S) ⊗[S] N,
          TensorProduct.rTensorHomToHomRTensor diagonal L S N t = g := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h (0, 1)
    have h0 : n = 0 := by simpa [diagonal] using congrArg Prod.fst hn
    have h1 : n = 1 := by simpa [diagonal] using congrArg Prod.snd hn
    exact Nat.zero_ne_one (h0.symm.trans h1)
  · let v : N := Pi.single 0 1
    let g := TensorProduct.rTensorHomToHomRTensor diagonal L S N
      (coordinate ⊗ₜ[S] v)
    have hc : coordinate (Finsupp.single 0 1) = 1 := by
      change diagonal ((Finsupp.single 0 1) 0) = 1
      rw [Finsupp.single_eq_same, map_one]
    have heval : g (Finsupp.single 0 1) = (1 : S) ⊗ₜ[S] v := by
      change TensorProduct.rTensorHomToHomRTensor diagonal L S N
        (coordinate ⊗ₜ[S] v) (Finsupp.single 0 1) = _
      rw [TensorProduct.rTensorHomToHomRTensor_apply, hc]
    have hg : g ≠ 0 := by
      intro hzero
      have hz : (1 : S) ⊗ₜ[S] v = 0 :=
        heval.symm.trans (LinearMap.congr_fun hzero (Finsupp.single 0 1))
      have hv := congrArg (TensorProduct.lid S N) hz
      rw [TensorProduct.lid_tmul, one_smul, map_zero] at hv
      have hv0 := congrArg (fun x : N => (x 0).1) hv
      have hv1 : (v 0).1 = 1 := by simp [v]
      exact Nat.one_ne_zero (hv1.symm.trans hv0)
    refine ⟨g, hg, ?_⟩
    obtain ⟨t, ht⟩ :=
      (TensorProduct.rTensorHomToHomRTensor_bijective_of_finite_projective_right
        (L := L) (M := S) (N := N) diagonal).2 g
    refine ⟨t, ht, fun u hu => ?_⟩
    exact
      (TensorProduct.rTensorHomToHomRTensor_bijective_of_finite_projective_right
        (L := L) (M := S) (N := N) diagonal).1 (hu.trans ht.symm)

end ProjectiveModulesTests
