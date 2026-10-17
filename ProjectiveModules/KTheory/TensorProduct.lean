/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.K0
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Tensor products of projective module classes

For a commutative ring `R`, `KTheory.ProjectiveClass.tensorMul` sends the classes
of finite projective right modules `M` and `N` to the class of
`M ⊗[Rᵐᵒᵖ] N`. The original right-module structures supply the canonical tensor
module structure. The ring may be the zero ring, and the module carriers may
inhabit independent universes.

## Implementation notes

The construction descends an isomorphism-invariant function in each argument.
It defines a binary function, without adding multiplicative instances on
`ProjectiveClass` or `K0` or changing their direct-sum additive structures.

## References and credits

The tensor-product operation on projective classes appears in Charles A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*, Chapter II.
This construction uses this library's finite-projective representatives and
isomorphism-invariant function descent, together with Mathlib's tensor
congruence and finite-generation and projectivity instances for tensor products.
-/

@[expose] public section

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace KTheory.ProjectiveClass

variable (R : Type u) [CommRing R]

private theorem tensorClass_congr_right
    (X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ)
    {Y Y' : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ} (e : Y ≅ Y') :
    of R (X ⊗[Rᵐᵒᵖ] Y) = of R (X ⊗[Rᵐᵒᵖ] Y') :=
  of_eq_of_equiv R _
    (TensorProduct.congr (LinearEquiv.refl Rᵐᵒᵖ X)
      (ModuleCat.FiniteProjective.isoToLinearEquiv e))

private noncomputable def tensorMulAux
    (X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ) :
    ProjectiveClass R → ProjectiveClass R :=
  liftFunction R
    (fun Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ ↦ of R (X ⊗[Rᵐᵒᵖ] Y))
    (tensorClass_congr_right R X)

private theorem tensorMulAux_of
    (X Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ) :
    tensorMulAux R X (of R Y) = of R (X ⊗[Rᵐᵒᵖ] Y) := by
  exact liftFunction_of R
    (fun Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ ↦ of R (X ⊗[Rᵐᵒᵖ] Y))
    (tensorClass_congr_right R X) Y

private theorem tensorMulAux_congr
    {X X' : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ} (e : X ≅ X') :
    tensorMulAux R X = tensorMulAux R X' := by
  funext b
  exact induction_on R b (fun Y ↦ by
    rw [tensorMulAux_of, tensorMulAux_of]
    exact of_eq_of_equiv R _
      (TensorProduct.congr (ModuleCat.FiniteProjective.isoToLinearEquiv e)
        (LinearEquiv.refl Rᵐᵒᵖ Y)))

/-- Tensor product of finite projective right-module classes over a commutative
ring, with tensor product taken over the opposite scalar ring. -/
@[no_expose]
noncomputable def tensorMul : ProjectiveClass R → ProjectiveClass R → ProjectiveClass R :=
  liftFunction R (tensorMulAux R) (tensorMulAux_congr R)

/-- On reference-module classes, tensor multiplication evaluates to the class
of the tensor product. -/
theorem tensorMul_of (X Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ) :
    tensorMul R (of R X) (of R Y) = of R (X ⊗[Rᵐᵒᵖ] Y) := by
  calc
    tensorMul R (of R X) (of R Y) = tensorMulAux R X (of R Y) :=
      congrFun (liftFunction_of R (tensorMulAux R) (tensorMulAux_congr R) X) (of R Y)
    _ = of R (X ⊗[Rᵐᵒᵖ] Y) := tensorMulAux_of R X Y

/-- Tensor multiplication computes the class of the tensor product for finite
projective right modules in independent carrier universes. -/
@[simp]
theorem tensorMul_of_module
    (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (N : Type w) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    tensorMul R (of R M) (of R N) = of R (M ⊗[Rᵐᵒᵖ] N) := by
  rw [← of_repr R M, ← of_repr R N, tensorMul_of]
  exact of_eq_of_equiv R _
    (TensorProduct.congr (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ M)
      (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ N))

end KTheory.ProjectiveClass
