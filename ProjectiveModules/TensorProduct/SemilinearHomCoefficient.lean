/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearMap.ChangeOfScalars
public import ProjectiveModules.TensorProduct.RightModule
public import ProjectiveModules.TensorProduct.SemilinearHom
public import ProjectiveModules.TensorProduct.SemilinearHomProjective

/-!
# Coefficient extension of semilinear Hom

Let `σ : R →+* S`, where `R` is a semiring and `S` is commutative, and let `T`
be an `S`-algebra, not necessarily commutative. The coefficient comparison
`TensorProduct.semilinearHomCoeffMap` sends `f ⊗ₜ[S] t` to the semilinear map
`m ↦ f m ⊗ₜ[S] t`, with scalar homomorphism `(algebraMap S T).comp σ`.

Both tensor products carry the right-factor coefficient action
`TensorProduct.rightModule`: the action on `n ⊗ₜ[S] u` is `n ⊗ₜ[S] (t * u)`.
The semilinear-map target uses this same action pointwise. Restricting it along
`algebraMap S T` equals the stock `S`-module structure as module data; the
comparison uses this equality and the value-preserving additive equivalences
`LinearMap.semilinearCompHomAddEquiv`.

The comparison is `T`-linear without finiteness assumptions. For a finite
projective source over `R`, `TensorProduct.semilinearHomCoeffEquiv` is the
resulting equivalence, using `TensorProduct.semilinearHomTensorMap_bijective`.
Neither finiteness of the Hom target nor flatness of the coefficient algebra is
required. `TensorProduct.homCoeffEquiv` specializes to ordinary `S`-linear Hom
by taking `σ = RingHom.id S`.

## References

- Mathlib's formalizations of semilinear maps and tensor products, for scalar
  restriction, pointwise scalar actions and the tensor commutor.
- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 17, for the linear
  tensor-Hom comparison. Here the source semiring need not be commutative and
  the Hom maps are semilinear.
-/

@[expose] public section

universe uR uS uT uM uN

namespace TensorProduct

section Coefficients

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [Semiring R] [CommSemiring S] [Semiring T] [Algebra S T]
variable (σ : R →+* S)
variable {M : Type uM} {N : Type uN}
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module S N]

/-- The pointwise coefficient module on the semilinear target. The
right-factor module is pinned in the carrier and in both target-module
arguments of `LinearMap.semilinearModule`. -/
@[instance_reducible]
def semilinearHomCoeffModule :
    Module T
      (@LinearMap R T _ _ ((algebraMap S T).comp σ) M (N ⊗[S] T)
        _ _ _ (rightModule S T N T)) :=
  @LinearMap.semilinearModule (R := R) (S := T) (T := T)
    (L := M) (M := N ⊗[S] T)
    _ _ _ _ _ _ (rightModule S T N T) (rightModule S T N T)
    ((algebraMap S T).comp σ) (rightModule_compHom_smulCommClass S T N σ)

/-- The chosen target coefficient action is pointwise. -/
theorem semilinearHomCoeffModule_smul_apply (t : T)
    (f : @LinearMap R T _ _ ((algebraMap S T).comp σ) M (N ⊗[S] T)
      _ _ _ (rightModule S T N T)) (m : M) :
    (@SMul.smul T _ (semilinearHomCoeffModule (M := M) (N := N) σ).toSMul t f) m =
      @SMul.smul T _ (rightModule S T N T).toSMul t (f m) :=
  rfl

-- Align the base actions, then compose the value-preserving additive
-- restriction-of-scalars equivalences.
private def semilinearCompHomBridge {Q : Type*} [AddCommMonoid Q]
    [Module S Q] [Module T Q] (α : S →+* T)
    (h : Module.compHom Q α = (inferInstance : Module S Q)) :
    (M →ₛₗ[σ] Q) ≃+ (M →ₛₗ[α.comp σ] Q) := by
  cases h
  letI : Module S Q := Module.compHom Q α
  exact (LinearMap.semilinearCompHomAddEquiv (L := M) (M := Q) σ).trans
    (LinearMap.semilinearCompHomAddEquiv (L := M) (M := Q) (α.comp σ)).symm

omit [Algebra S T] in
private theorem semilinearCompHomBridge_apply {Q : Type*} [AddCommMonoid Q]
    [Module S Q] [Module T Q] (α : S →+* T)
    (h : Module.compHom Q α = (inferInstance : Module S Q))
    (f : M →ₛₗ[σ] Q) (m : M) :
    semilinearCompHomBridge σ α h f m = f m := by
  cases h
  rfl

/-- The coefficient-extension comparison, linear for the chosen right-factor
`T`-actions. Its underlying additive map is the canonical comparison followed
by the value-preserving scalar-restriction equivalences. -/
@[no_expose]
def semilinearHomCoeffMap :
    @LinearMap T T _ _ (RingHom.id T)
      ((M →ₛₗ[σ] N) ⊗[S] T)
      (@LinearMap R T _ _ ((algebraMap S T).comp σ) M (N ⊗[S] T)
        _ _ _ (rightModule S T N T))
      _ _ (rightModule S T (M →ₛₗ[σ] N) T)
      (semilinearHomCoeffModule (M := M) (N := N) σ) := by
  letI : Module T (N ⊗[S] T) := rightModule S T N T
  letI : Module T ((M →ₛₗ[σ] N) ⊗[S] T) :=
    rightModule S T (M →ₛₗ[σ] N) T
  letI : Module T (M →ₛₗ[(algebraMap S T).comp σ] (N ⊗[S] T)) :=
    semilinearHomCoeffModule (M := M) (N := N) σ
  let e := semilinearCompHomBridge (M := M) σ (algebraMap S T)
    (rightModule_compHom S T N)
  exact
    { toFun := fun x => e (semilinearHomTensorMap σ x)
      map_add' := by
        intro x y
        simp only [map_add]
      map_smul' := by
        intro t x
        ext m
        change
          e (semilinearHomTensorMap σ
            (@SMul.smul T _ (rightModule S T (M →ₛₗ[σ] N) T).toSMul t x)) m =
          (@SMul.smul T _ (semilinearHomCoeffModule (M := M) (N := N) σ).toSMul
            t (e (semilinearHomTensorMap σ x))) m
        simpa only [e, semilinearHomCoeffModule_smul_apply,
          semilinearCompHomBridge_apply] using
          semilinearHomTensorMap_rightModule_smul_apply σ t x m }

/-- The coefficient comparison preserves every value of the generic
comparison, not just its values on pure tensors. -/
@[simp]
theorem semilinearHomCoeffMap_apply (x : (M →ₛₗ[σ] N) ⊗[S] T) (m : M) :
    semilinearHomCoeffMap (T := T) σ x m = semilinearHomTensorMap σ x m := by
  let : Module T (N ⊗[S] T) := rightModule S T N T
  change semilinearCompHomBridge σ (algebraMap S T)
    (rightModule_compHom S T N) (semilinearHomTensorMap σ x) m = _
  exact semilinearCompHomBridge_apply σ (algebraMap S T)
    (rightModule_compHom S T N) (semilinearHomTensorMap σ x) m

/-- The coefficient comparison has the canonical pure-tensor formula. -/
theorem semilinearHomCoeffMap_tmul (f : M →ₛₗ[σ] N) (t : T) (m : M) :
    semilinearHomCoeffMap (T := T) σ (f ⊗ₜ[S] t) m = f m ⊗ₜ[S] t := by
  rw [semilinearHomCoeffMap_apply, semilinearHomTensorMap_tmul]

/-- Canonical coefficient extension of semilinear Hom from a finite
projective source. The coefficient semiring may be noncommutative; neither
flatness of the coefficient algebra nor finiteness of the target is required.
The two tensor actions are the named right-factor actions. -/
@[no_expose]
noncomputable def semilinearHomCoeffEquiv
    [Module.Finite R M] [Module.Projective R M] :
    @LinearEquiv T T _ _ (RingHom.id T) (RingHom.id T) _ _
      ((M →ₛₗ[σ] N) ⊗[S] T)
      (@LinearMap R T _ _ ((algebraMap S T).comp σ) M (N ⊗[S] T)
        _ _ _ (rightModule S T N T))
      _ _ (rightModule S T (M →ₛₗ[σ] N) T)
      (semilinearHomCoeffModule (M := M) (N := N) σ) := by
  letI : Module T (N ⊗[S] T) := rightModule S T N T
  letI : Module T ((M →ₛₗ[σ] N) ⊗[S] T) :=
    rightModule S T (M →ₛₗ[σ] N) T
  letI : Module T (M →ₛₗ[(algebraMap S T).comp σ] (N ⊗[S] T)) :=
    semilinearHomCoeffModule (M := M) (N := N) σ
  refine LinearEquiv.ofBijective (semilinearHomCoeffMap (T := T) (N := N) σ) ?_
  let e := semilinearCompHomBridge (M := M) σ (algebraMap S T)
    (rightModule_compHom S T N)
  exact e.bijective.comp
    (semilinearHomTensorMap_bijective (M := M) (N := N) (P := T) σ)

/-- The equivalence has the canonical coefficient comparison as its
forward linear map. -/
@[simp]
theorem semilinearHomCoeffEquiv_toLinearMap
    [Module.Finite R M] [Module.Projective R M] :
    @LinearEquiv.toLinearMap T T _ _ (RingHom.id T) (RingHom.id T) _ _
      ((M →ₛₗ[σ] N) ⊗[S] T)
      (@LinearMap R T _ _ ((algebraMap S T).comp σ) M (N ⊗[S] T)
        _ _ _ (rightModule S T N T))
      _ _ (rightModule S T (M →ₛₗ[σ] N) T)
      (semilinearHomCoeffModule (M := M) (N := N) σ)
      (semilinearHomCoeffEquiv (T := T) (M := M) (N := N) σ) =
      semilinearHomCoeffMap (T := T) (M := M) (N := N) σ := by
  let : Module T (N ⊗[S] T) := rightModule S T N T
  let : Module T ((M →ₛₗ[σ] N) ⊗[S] T) :=
    rightModule S T (M →ₛₗ[σ] N) T
  let : Module T (M →ₛₗ[(algebraMap S T).comp σ] (N ⊗[S] T)) :=
    semilinearHomCoeffModule (M := M) (N := N) σ
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro m
  calc
    _ = semilinearHomTensorMap σ x m := by
      change semilinearHomCoeffMap (T := T) (M := M) (N := N) σ x m = _
      exact semilinearHomCoeffMap_apply σ x m
    _ = semilinearHomCoeffMap (T := T) (M := M) (N := N) σ x m :=
      (semilinearHomCoeffMap_apply σ x m).symm

/-- Evaluation of coefficient extension on a pure tensor. -/
@[simp]
theorem semilinearHomCoeffEquiv_tmul
    [Module.Finite R M] [Module.Projective R M]
    (f : M →ₛₗ[σ] N) (t : T) (m : M) :
    semilinearHomCoeffEquiv (T := T) (M := M) (N := N) σ (f ⊗ₜ[S] t) m =
      f m ⊗ₜ[S] t := by
  change semilinearHomCoeffMap (T := T) (M := M) (N := N) σ (f ⊗ₜ[S] t) m = _
  exact semilinearHomCoeffMap_tmul σ f t m

end Coefficients

section Identity

variable {S : Type uS} {T : Type uT}
variable [CommSemiring S] [Semiring T] [Algebra S T]
variable {M : Type uM} {N : Type uN}
variable [AddCommMonoid M] [AddCommMonoid N] [Module S M] [Module S N]
variable [Module.Finite S M] [Module.Projective S M]

/-- The identity-homomorphism specialization: coefficient extension of
ordinary linear Hom, with the right-factor coefficient actions. -/
noncomputable def homCoeffEquiv :
    @LinearEquiv T T _ _ (RingHom.id T) (RingHom.id T) _ _
      ((M →ₗ[S] N) ⊗[S] T)
      (@LinearMap S T _ _ (algebraMap S T) M (N ⊗[S] T)
        _ _ _ (rightModule S T N T))
      _ _ (rightModule S T (M →ₗ[S] N) T)
      (semilinearHomCoeffModule (M := M) (N := N) (RingHom.id S)) :=
  semilinearHomCoeffEquiv (T := T) (RingHom.id S)

/-- The ordinary linear specialization has the same canonical formula. -/
@[simp]
theorem homCoeffEquiv_tmul (f : M →ₗ[S] N) (t : T) (m : M) :
    homCoeffEquiv (S := S) (T := T) (M := M) (N := N) (f ⊗ₜ[S] t) m =
      f m ⊗ₜ[S] t :=
  semilinearHomCoeffEquiv_tmul (RingHom.id S) f t m

end Identity

end TensorProduct
