/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Products of continuous semilinear maps

Two continuous semilinear maps with the same domain and scalar homomorphism determine a
continuous semilinear map into the product of their codomains. This construction needs only
additive commutative monoids with module structures and topologies; continuity of addition or
scalar multiplication is not required.

The projection and eta laws characterize this pairing, and pairing commutes with precomposition.
For the identity scalar homomorphism it agrees with `ContinuousLinearMap.prod`.

## References

* Mathlib's `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic` supplies continuous
  semilinear maps and their composition.
* Mathlib's `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd` and
  `Mathlib.LinearAlgebra.Prod` supply the corresponding linear product constructions.
* Mathlib's `Mathlib.Topology.Constructions.SumProd` supplies continuity of pairing.
-/

@[expose] public section

universe uR uS uT uW uX uY uZ

namespace ContinuousLinearMap

section Semilinear

variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S] {σ : R →+* S}
  {X : Type uX} {Y : Type uY} {Z : Type uZ}
  [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  [TopologicalSpace Y] [AddCommMonoid Y] [Module S Y]
  [TopologicalSpace Z] [AddCommMonoid Z] [Module S Z]

/-- Pair two continuous semilinear maps with the same domain and scalar homomorphism. -/
def prodSemilinear (a : X →SL[σ] Y) (b : X →SL[σ] Z) : X →SL[σ] (Y × Z) where
  toLinearMap :=
    { toFun := fun x => (a x, b x)
      map_add' := fun x y => Prod.ext (map_add a x y) (map_add b x y)
      map_smul' := fun r x => Prod.ext (map_smulₛₗ a r x) (map_smulₛₗ b r x) }
  cont := a.continuous.prodMk b.continuous

/-- The semilinear pairing evaluates coordinatewise. -/
@[simp]
theorem prodSemilinear_apply (a : X →SL[σ] Y) (b : X →SL[σ] Z) (x : X) :
    prodSemilinear a b x = (a x, b x) :=
  rfl

/-- The first projection of a semilinear pairing is its first component. -/
@[simp]
theorem fst_comp_prodSemilinear (a : X →SL[σ] Y) (b : X →SL[σ] Z) :
    (fst S Y Z).comp (prodSemilinear a b) = a :=
  ext fun _ => rfl

/-- The second projection of a semilinear pairing is its second component. -/
@[simp]
theorem snd_comp_prodSemilinear (a : X →SL[σ] Y) (b : X →SL[σ] Z) :
    (snd S Y Z).comp (prodSemilinear a b) = b :=
  ext fun _ => rfl

/-- A continuous semilinear map into a product is the pairing of its two projections. -/
@[simp]
theorem prodSemilinear_eta (h : X →SL[σ] (Y × Z)) :
    prodSemilinear ((fst S Y Z).comp h) ((snd S Y Z).comp h) = h :=
  ext fun _ => Prod.ext rfl rfl

end Semilinear

section Composition

variable {A : Type uR} {B : Type uS} {C : Type uT}
  [Semiring A] [Semiring B] [Semiring C]
  {σ₁₂ : A →+* B} {σ₂₃ : B →+* C} {σ₁₃ : A →+* C}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  {W : Type uW} {X : Type uX} {Y : Type uY} {Z : Type uZ}
  [TopologicalSpace W] [AddCommMonoid W] [Module A W]
  [TopologicalSpace X] [AddCommMonoid X] [Module B X]
  [TopologicalSpace Y] [AddCommMonoid Y] [Module C Y]
  [TopologicalSpace Z] [AddCommMonoid Z] [Module C Z]

/-- Precomposition commutes with semilinear pairing along compatible scalar homomorphisms. -/
theorem prodSemilinear_comp (a : X →SL[σ₂₃] Y) (b : X →SL[σ₂₃] Z) (g : W →SL[σ₁₂] X) :
    ((prodSemilinear a b).comp g : W →SL[σ₁₃] (Y × Z)) =
      prodSemilinear (a.comp g) (b.comp g) :=
  ext fun _ => rfl

end Composition

section Linear

variable {R : Type uR} [Semiring R] {X : Type uX} {Y : Type uY} {Z : Type uZ}
  [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y]
  [TopologicalSpace Z] [AddCommMonoid Z] [Module R Z]

/-- Semilinear pairing for the identity scalar homomorphism agrees with linear pairing. -/
theorem prodSemilinear_eq_prod (a : X →L[R] Y) (b : X →L[R] Z) :
    prodSemilinear a b = a.prod b :=
  ext fun _ => rfl

end Linear

end ContinuousLinearMap
