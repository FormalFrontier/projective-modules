/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Trace

/-!
# Partial trace of tensor symmetry over the natural numbers

On the standard semimodule `V = Fin 2 → ℕ`, tensor symmetry is an actual
linear map `V ⊗[ℕ] V →ₗ[ℕ] V ⊗[ℕ] V`, rather than a prescribed pure tensor
of two linear maps. Its partial trace over the first factor is the identity
of `V`. The proof reconstructs the inverse tensor–Hom image using the standard
basis, then applies the rank-one trace formula. The zero-input boundary uses
only the inherited linear-map interface.

The tensor symmetry is the existing Mathlib construction by Kenny Lau and
Mario Carneiro. The standard function basis is formalized by Johannes Hölzl,
and the tensor–Hom equivalence by Oliver Nash and Antoine Labelle; no new
carrier or scalar action is introduced.
-/

noncomputable section

open scoped TensorProduct

namespace ProjectiveModulesTests

private abbrev V := Fin 2 → ℕ

private def tensorSwap : V ⊗[ℕ] V →ₗ[ℕ] V ⊗[ℕ] V :=
  (TensorProduct.comm ℕ V V).toLinearMap

/-- The partial trace of tensor symmetry on `Fin 2 → ℕ` is the identity. -/
private theorem partialTrace_tensorSwap :
    LinearMap.partialTraceOfFiniteProjective ℕ V V V tensorSwap = LinearMap.id := by
  let b := Pi.basisFun ℕ (Fin 2)
  have hsum (m : V) : ∑ i : Fin 2, b.coord i m • b i = m := by
    simpa only [Module.Basis.coord_apply] using b.sum_repr m
  apply LinearMap.ext
  intro n
  have hinv :
      (rTensorHomEquivHomRTensor ℕ V V V).symm
          ((TensorProduct.curry tensorSwap).flip n) =
        ∑ i : Fin 2, (b.coord i).smulRight n ⊗ₜ[ℕ] b i := by
    apply (rTensorHomEquivHomRTensor ℕ V V V).symm_apply_eq.mpr
    apply LinearMap.ext
    intro m
    simp only [LinearMap.flip_apply, tensorSwap,
      rTensorHomEquivHomRTensor_apply, map_sum]
    calc
      n ⊗ₜ[ℕ] m = n ⊗ₜ[ℕ] (∑ i : Fin 2, b.coord i m • b i) :=
        congrArg (fun v : V => n ⊗ₜ[ℕ] v) (hsum m).symm
      _ = ∑ i : Fin 2, (b.coord i m • n) ⊗ₜ[ℕ] b i := by
        simp only [TensorProduct.tmul_sum, TensorProduct.smul_tmul]
  calc
    LinearMap.partialTraceOfFiniteProjective ℕ V V V tensorSwap n =
        TensorProduct.lid ℕ V
          ((LinearMap.traceOfFiniteProjective ℕ V).rTensor V
            ((rTensorHomEquivHomRTensor ℕ V V V).symm
              ((TensorProduct.curry tensorSwap).flip n))) :=
      LinearMap.partialTraceOfFiniteProjective_apply ℕ V V V tensorSwap n
    _ = TensorProduct.lid ℕ V
          ((LinearMap.traceOfFiniteProjective ℕ V).rTensor V
            (∑ i : Fin 2, (b.coord i).smulRight n ⊗ₜ[ℕ] b i)) :=
      congrArg (fun t => TensorProduct.lid ℕ V
        ((LinearMap.traceOfFiniteProjective ℕ V).rTensor V t)) hinv
    _ = LinearMap.id n := by
      simpa only [map_sum, LinearMap.rTensor_tmul,
        LinearMap.traceOfFiniteProjective_smulRight, TensorProduct.lid_tmul,
        LinearMap.id_apply] using hsum n

/-- Tracing the scalar unit factor leaves tensor symmetry unchanged. -/
example :
    LinearMap.partialTraceOfFiniteProjective ℕ ℕ (V ⊗[ℕ] V) (V ⊗[ℕ] V)
      (TensorProduct.map ((LinearMap.id : ℕ →ₗ[ℕ] ℕ).smulRight (1 : ℕ)) tensorSwap) =
        tensorSwap := by
  calc
    _ = LinearMap.traceOfFiniteProjective ℕ ℕ
        ((LinearMap.id : ℕ →ₗ[ℕ] ℕ).smulRight (1 : ℕ)) • tensorSwap :=
      LinearMap.partialTraceOfFiniteProjective_tensorProduct ℕ ℕ (V ⊗[ℕ] V) (V ⊗[ℕ] V)
        ((LinearMap.id : ℕ →ₗ[ℕ] ℕ).smulRight (1 : ℕ)) tensorSwap
    _ = tensorSwap := by
      rw [LinearMap.traceOfFiniteProjective_smulRight, LinearMap.id_apply, one_smul]

example :
    LinearMap.partialTraceOfFiniteProjective ℕ V V V
      (0 : V ⊗[ℕ] V →ₗ[ℕ] V ⊗[ℕ] V) = (0 : V →ₗ[ℕ] V) :=
  (LinearMap.partialTraceOfFiniteProjective ℕ V V V).map_zero

/-- Naturality for the coordinate-zero embedding
and projection around tensor symmetry, with scalar partial trace the identity. -/
private theorem partialTrace_tensorSwap_coordinateSquare :
    LinearMap.partialTraceOfFiniteProjective ℕ V ℕ ℕ
      (((LinearMap.proj (0 : Fin 2) : V →ₗ[ℕ] ℕ).lTensor V).comp
        (tensorSwap.comp
          (((LinearMap.id : ℕ →ₗ[ℕ] ℕ).smulRight
            (Pi.single (0 : Fin 2) (1 : ℕ)) : ℕ →ₗ[ℕ] V).lTensor V))) =
      (LinearMap.id : ℕ →ₗ[ℕ] ℕ) := by
  calc
    _ =
        (LinearMap.proj (0 : Fin 2) : V →ₗ[ℕ] ℕ).comp
          ((LinearMap.partialTraceOfFiniteProjective ℕ V V V tensorSwap).comp
            ((LinearMap.id : ℕ →ₗ[ℕ] ℕ).smulRight
              (Pi.single (0 : Fin 2) (1 : ℕ)) : ℕ →ₗ[ℕ] V)) :=
      LinearMap.partialTraceOfFiniteProjective_naturality ℕ V V V ℕ ℕ tensorSwap
        ((LinearMap.id : ℕ →ₗ[ℕ] ℕ).smulRight (Pi.single (0 : Fin 2) (1 : ℕ)))
        (LinearMap.proj (0 : Fin 2))
    _ =
        (LinearMap.proj (0 : Fin 2) : V →ₗ[ℕ] ℕ).comp
          ((LinearMap.id : V →ₗ[ℕ] V).comp
            ((LinearMap.id : ℕ →ₗ[ℕ] ℕ).smulRight
              (Pi.single (0 : Fin 2) (1 : ℕ)) : ℕ →ₗ[ℕ] V)) :=
      congrArg (fun g : V →ₗ[ℕ] V =>
        (LinearMap.proj (0 : Fin 2) : V →ₗ[ℕ] ℕ).comp
          (g.comp
            ((LinearMap.id : ℕ →ₗ[ℕ] ℕ).smulRight
              (Pi.single (0 : Fin 2) (1 : ℕ)) : ℕ →ₗ[ℕ] V)))
        partialTrace_tensorSwap
    _ = (LinearMap.id : ℕ →ₗ[ℕ] ℕ) := by
      apply LinearMap.ext
      intro n
      simp [LinearMap.comp_apply, LinearMap.smulRight_apply]

end ProjectiveModulesTests
