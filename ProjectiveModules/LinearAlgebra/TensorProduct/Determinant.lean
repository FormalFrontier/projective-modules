/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-!
# Determinants of tensor products of endomorphisms

For finite free modules over a commutative ring, the determinant of a tensor product of
endomorphisms is the product of their determinants, raised to the ranks of the opposite factors.

The proof uses Mathlib's tensor-coordinate formula `TensorProduct.toMatrix_map`, Kronecker
determinant formula `Matrix.det_kronecker`, and comparison theorem `LinearMap.det_toMatrix`.

## References

* Mathlib's `Mathlib.LinearAlgebra.TensorProduct.Matrix`, by Eric Wieser.
* Mathlib's `Mathlib.LinearAlgebra.Matrix.Kronecker`, by Filippo A. E. Nuccio and Eric Wieser.
-/

@[expose] public section

universe uR uP uQ

namespace LinearMap

variable {R : Type uR} [CommRing R]
variable {P : Type uP} [AddCommGroup P] [Module R P]
variable {Q : Type uQ} [AddCommGroup Q] [Module R Q]

/-- The determinant of the tensor product of two endomorphisms of finite free modules is
the product of their determinants, raised to the ranks of the opposite factors. -/
theorem det_tensorProduct_map [Module.Free R P] [Module.Finite R P]
    [Module.Free R Q] [Module.Finite R Q] (f : P →ₗ[R] P) (g : Q →ₗ[R] Q) :
    LinearMap.det (TensorProduct.map f g) =
      LinearMap.det f ^ Module.finrank R Q * LinearMap.det g ^ Module.finrank R P := by
  classical
  nontriviality R
  let bP := Module.finBasis R P
  let bQ := Module.finBasis R Q
  rw [← LinearMap.det_toMatrix (bP.tensorProduct bQ), TensorProduct.toMatrix_map,
    Matrix.det_kronecker]
  simp only [LinearMap.det_toMatrix, Fintype.card_fin]

end LinearMap
