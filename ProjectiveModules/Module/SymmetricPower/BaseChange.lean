/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.SymmetricPower.Basic
public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-!
# Scalar extension for finite symmetric powers

For a homomorphism of commutative semirings `R → S`, scalar extension commutes
with the symmetric power on any finite family of labels. The comparison is
`S`-linear, and the universes of `R`, `S`, and the original module are independent.

`SymmetricPower.baseChange` sends each labelled vector to its tensor with `1`.
`SymmetricPower.baseChangeInverse` collects the coefficients of a labelled family
of pure tensors by multiplying them. Their two composition identities select
`SymmetricPower.baseChangeEquiv`. The generator formulas characterize both maps,
and the comparison is natural in linear maps of the original modules.

The empty family is included: in degree zero, both symmetric powers identify with
their scalar semirings, and the comparison agrees with the scalar-unit map. No
flatness, freeness, finite-generation, projectivity, characteristic, or factorial
assumption is needed.

## Implementation notes

The labels on the two sides are `ULift (Fin n)` in the respective scalar
universes. Finite multilinear extension is constructed privately, slot by slot
using the tensor-product universal property. Public characteristic equations do
not expose that construction.

## References

* N. Bourbaki, *Algebra I*, Chapters 1–3.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*.
-/

public section

universe uR uS uM uN uI

open scoped TensorProduct

noncomputable section

namespace SymmetricPower

variable (R : Type uR) [CommSemiring R]
variable (S : Type uS) [CommSemiring S] [Algebra R S]
variable (M : Type uM) [AddCommMonoid M] [Module R M]
variable (n : ℕ)

/-- The extension-of-scalars map on the degree-`n` symmetric power.
Each labelled vector is sent to its tensor with `1`. -/
def baseChange :
    (S ⊗[R] SymmetricPower R (ULift.{uR} (Fin n)) M) →ₗ[S]
      SymmetricPower S (ULift.{uS} (Fin n)) (S ⊗[R] M) := by
  let _ : Module R (SymmetricPower S (ULift.{uS} (Fin n)) (S ⊗[R] M)) :=
    Module.restrictScalars R S _
  let _ : IsScalarTower R S
      (SymmetricPower S (ULift.{uS} (Fin n)) (S ⊗[R] M)) := by
    exact IsScalarTower.restrictScalars R S _
  let _ : SMulCommClass R S
      (SymmetricPower S (ULift.{uS} (Fin n)) (S ⊗[R] M)) := by
    infer_instance
  let a : ULift.{uS} (Fin n) ≃ ULift.{uR} (Fin n) :=
    { toFun := fun i => ULift.up i.down
      invFun := fun i => ULift.up i.down
      left_inv := fun i => by cases i; rfl
      right_inv := fun i => by cases i; rfl }
  let p : MultilinearMap R (fun _ : ULift.{uR} (Fin n) => M)
      (SymmetricPower S (ULift.{uS} (Fin n)) (S ⊗[R] M)) :=
    (((tprod S : MultilinearMap S (fun _ : ULift.{uS} (Fin n) => S ⊗[R] M)
      (SymmetricPower S (ULift.{uS} (Fin n)) (S ⊗[R] M))).restrictScalars R).compLinearMap
        (fun _ => TensorProduct.mk R S M (1 : S))).domDomCongr a
  have hp (x : ULift.{uR} (Fin n) → M) :
      p x = tprod S (fun i : ULift.{uS} (Fin n) => (1 : S) ⊗ₜ[R] x (a i)) := by
    simp [p, MultilinearMap.compLinearMap_apply, MultilinearMap.coe_restrictScalars,
      TensorProduct.mk_apply]
  have hperm (e : Equiv.Perm (ULift.{uR} (Fin n)))
      (x : ULift.{uR} (Fin n) → M) : p (fun i => x (e i)) = p x := by
    rw [hp, hp]
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using
      (tprod_equiv (R := S) ((a.trans e).trans a.symm)
        (fun i : ULift.{uS} (Fin n) => (1 : S) ⊗ₜ[R] x (a i)))
  let f := lift p hperm
  exact TensorProduct.AlgebraTensorModule.lift
    { toFun := fun s => s • f
      map_add' := fun s t => add_smul s t f
      map_smul' := fun s t => mul_smul s t f }

/-- The forward comparison on every labelled symmetric generator, with an
arbitrary outer coefficient. -/
@[simp] theorem baseChange_tmul_tprod (s : S) (x : ULift.{uR} (Fin n) → M) :
    baseChange R S M n (s ⊗ₜ[R] tprod R x) =
      s • tprod S (fun i : ULift.{uS} (Fin n) =>
        (1 : S) ⊗ₜ[R] x (ULift.up i.down : ULift.{uR} (Fin n))) := by
  simp [baseChange, LinearMap.smul_apply, lift_tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.coe_restrictScalars,
    TensorProduct.mk_apply]

/-- An `S`-linear map out of the scalar-extended symmetric power is determined
by its values on all labelled generators and all outer coefficients. -/
theorem baseChange_ext
    {N : Type uN} [AddCommMonoid N] [Module S N]
    {f g : (S ⊗[R] SymmetricPower R (ULift.{uR} (Fin n)) M) →ₗ[S] N}
    (h : ∀ (s : S) (x : ULift.{uR} (Fin n) → M),
      f (s ⊗ₜ[R] tprod R x) = g (s ⊗ₜ[R] tprod R x)) : f = g := by
  let _ : Module R N := Module.restrictScalars R S N
  let _ : IsScalarTower R S N := by
    exact IsScalarTower.restrictScalars R S N
  apply TensorProduct.AlgebraTensorModule.ext
  intro s y
  have hs : (f.restrictScalars R).comp
      ((TensorProduct.mk R S (SymmetricPower R (ULift.{uR} (Fin n)) M)) s) =
      (g.restrictScalars R).comp
        ((TensorProduct.mk R S (SymmetricPower R (ULift.{uR} (Fin n)) M)) s) := by
    apply hom_ext
    intro x
    exact h s x
  exact LinearMap.congr_fun hs y

/-- The labelled generator formula characterizes the extension-of-scalars map. -/
theorem baseChange_eq
    (f : (S ⊗[R] SymmetricPower R (ULift.{uR} (Fin n)) M) →ₗ[S]
      SymmetricPower S (ULift.{uS} (Fin n)) (S ⊗[R] M))
    (h : ∀ (s : S) (x : ULift.{uR} (Fin n) → M),
      f (s ⊗ₜ[R] tprod R x) =
        s • tprod S (fun i : ULift.{uS} (Fin n) =>
          (1 : S) ⊗ₜ[R] x (ULift.up i.down : ULift.{uR} (Fin n)))) :
    f = baseChange R S M n := by
  apply baseChange_ext R S M n
  intro s x
  exact (h s x).trans (baseChange_tmul_tprod R S M n s x).symm

/-- In degree zero, the forward comparison is the canonical scalar unit map. -/
theorem baseChange_zero_unit :
    (isEmptyEquiv (R := S) (ι := ULift.{uS} (Fin 0))
        (M := S ⊗[R] M)).toLinearMap.comp (baseChange R S M 0) =
      (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp
        ((isEmptyEquiv (R := R) (ι := ULift.{uR} (Fin 0))
          (M := M)).toLinearMap.baseChange S) := by
  apply baseChange_ext R S M 0
  intro s x
  simp [baseChange_tmul_tprod, isEmptyEquiv_tprod,
    LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul]

end SymmetricPower

end

noncomputable section

open TensorProduct

namespace SymmetricPower

section Extension

variable (R : Type uR) [CommSemiring R]
variable (S : Type uS) [CommSemiring S] [Algebra R S]
variable (M : Type uM) [AddCommMonoid M] [Module R M]
variable (N : Type uN) [AddCommMonoid N] [Module R N] [Module S N]
  [IsScalarTower R S N] [SMulCommClass R S N]

/-- The pointwise scalar actions on finite forms commute. -/
private instance finiteFormScalarComm (n : ℕ) :
    SMulCommClass S R (MultilinearMap S (fun _ : Fin n => S ⊗[R] M) N) where
  smul_comm s r f := by
    ext z
    exact (smul_comm r s (f z)).symm

/-- The pointwise scalar actions on finite forms form the same scalar tower. -/
private instance finiteFormScalarTower (n : ℕ) :
    IsScalarTower R S (MultilinearMap S (fun _ : Fin n => S ⊗[R] M) N) where
  smul_assoc r s f := by
    ext z
    exact smul_assoc r s (f z)

/-- Extension of an ordinary linear map to a scalar-extended source. -/
private def tensorExtend (f : M →ₗ[R] N) : S ⊗[R] M →ₗ[S] N :=
  TensorProduct.AlgebraTensorModule.lift.equiv R S R S M N
    ((LinearMap.id : S →ₗ[S] S).smulRight f)

private theorem tensorExtend_tmul (f : M →ₗ[R] N) (s : S) (x : M) :
    tensorExtend R S M N f (s ⊗ₜ[R] x) = s • f x :=
  TensorProduct.AlgebraTensorModule.lift_tmul _ s x

/-- The tensor extension is linear in the original linear map. -/
private def tensorExtendLinear : (M →ₗ[R] N) →ₗ[R] (S ⊗[R] M →ₗ[S] N) where
  toFun := tensorExtend R S M N
  map_add' f g := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s x
    simp only [tensorExtend_tmul, LinearMap.add_apply, smul_add]
  map_smul' r f := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s x
    simp only [tensorExtend_tmul, LinearMap.smul_apply]
    exact smul_comm s r (f x)

/-- Finite slot extension, linear in the original multilinear form. -/
private def extendFinite : (n : ℕ) →
    MultilinearMap R (fun _ : Fin n => M) N →ₗ[R]
      MultilinearMap S (fun _ : Fin n => S ⊗[R] M) N
  | 0 => {
      toFun := fun f => MultilinearMap.constOfIsEmpty S
        (fun _ : Fin 0 => S ⊗[R] M) (f (fun i => isEmptyElim i))
      map_add' := by intro f g; ext x; rfl
      map_smul' := by intro r f; ext x; rfl }
  | n + 1 =>
      ((multilinearCurryLeftEquiv S
          (fun _ : Fin (n + 1) => S ⊗[R] M) N).symm.toLinearMap.restrictScalars R).comp
        ((tensorExtendLinear R S M
            (MultilinearMap S (fun _ : Fin n => S ⊗[R] M) N)).comp
          (((LinearMap.llcomp (R := R) (R₂ := R) (R₃ := R)
              (M := M)
              (N := MultilinearMap R (fun _ : Fin n => M) N)
              (P := MultilinearMap S (fun _ : Fin n => S ⊗[R] M) N)
              (σ₁₂ := RingHom.id R) (σ₂₃ := RingHom.id R)
              (σ₁₃ := RingHom.id R)) (extendFinite n)).comp
            (multilinearCurryLeftEquiv R (fun _ : Fin (n + 1) => M) N).toLinearMap))

private theorem extendFinite_tmul (n : ℕ)
    (f : MultilinearMap R (fun _ : Fin n => M) N)
    (s : Fin n → S) (x : Fin n → M) :
    extendFinite R S M N n f (fun i => s i ⊗ₜ[R] x i) =
      (∏ i : Fin n, s i) • f x := by
  induction n with
  | zero =>
      change f (fun i : Fin 0 => isEmptyElim i) = (∏ i : Fin 0, s i) • f x
      simp only [Fin.prod_univ_zero, one_smul]
      congr 1
      funext i
      exact isEmptyElim i
  | succ n ih =>
      change tensorExtend R S M
          (MultilinearMap S (fun _ : Fin n => S ⊗[R] M) N)
          ((extendFinite R S M N n).comp f.curryLeft)
          (s 0 ⊗ₜ[R] x 0) (fun i => s i.succ ⊗ₜ[R] x i.succ) = _
      rw [tensorExtend_tmul]
      change s 0 • extendFinite R S M N n (f.curryLeft (x 0))
        (fun i => s i.succ ⊗ₜ[R] x i.succ) = _
      rw [ih, MultilinearMap.curryLeft_apply, Fin.prod_univ_succ, smul_smul]
      congr 1
      exact congrArg f (by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl)

end Extension

section TensorGenerators

variable {R : Type uR} [CommSemiring R]
variable {S : Type uS} [CommSemiring S] [Algebra R S]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {N : Type uN} [AddCommMonoid N] [Module S N]

private theorem pureTensor_span :
    Submodule.span S (Set.range (fun p : S × M => p.1 ⊗ₜ[R] p.2)) = ⊤ := by
  have hmem (z : S ⊗[R] M) :
      z ∈ Submodule.span S (Set.range (fun p : S × M => p.1 ⊗ₜ[R] p.2)) := by
    induction z using TensorProduct.inductionOn with
    | tmul s x => exact Submodule.subset_span ⟨(s, x), rfl⟩
    | add z w hz hw => exact Submodule.add_mem _ hz hw
  exact top_unique (by intro z _; exact hmem z)

private theorem tensorSlots_ext {ι : Type uI} [Finite ι]
    {f g : MultilinearMap S (fun _ : ι => S ⊗[R] M) N}
    (h : ∀ (s : ι → S) (x : ι → M),
      f (fun i => s i ⊗ₜ[R] x i) = g (fun i => s i ⊗ₜ[R] x i)) : f = g := by
  apply MultilinearMap.ext_of_span_eq_top
    (g := fun {_ : ι} (p : S × M) => p.1 ⊗ₜ[R] p.2)
    (fun _ => pureTensor_span (R := R) (S := S) (M := M))
  intro p
  exact h (fun i => (p i).1) (fun i => (p i).2)

end TensorGenerators

section Inverse

variable (R : Type uR) [CommSemiring R]
variable (S : Type uS) [CommSemiring S] [Algebra R S]
variable (M : Type uM) [AddCommMonoid M] [Module R M]

/-- The original symmetric product with finite, unlifted labels. -/
private def finiteSymmetricForm (n : ℕ) :
    MultilinearMap R (fun _ : Fin n => M)
      (SymmetricPower R (ULift.{uR} (Fin n)) M) where
  toFun x := tprod R (fun i : ULift.{uR} (Fin n) => x i.down)
  map_update_add' x i a b := by
    have hu (c : M) :
        (fun j : ULift.{uR} (Fin n) => Function.update x i c j.down) =
          Function.update (fun j : ULift.{uR} (Fin n) => x j.down) (ULift.up i) c := by
      ext j
      rcases j with ⟨j⟩
      by_cases h : j = i <;> simp [h]
    simpa only [hu] using
      (tprod R (ι := ULift.{uR} (Fin n))).map_update_add
        (fun j : ULift.{uR} (Fin n) => x j.down) (ULift.up i) a b
  map_update_smul' x i r a := by
    have hu (c : M) :
        (fun j : ULift.{uR} (Fin n) => Function.update x i c j.down) =
          Function.update (fun j : ULift.{uR} (Fin n) => x j.down) (ULift.up i) c := by
      ext j
      rcases j with ⟨j⟩
      by_cases h : j = i <;> simp [h]
    simpa only [hu] using
      (tprod R (ι := ULift.{uR} (Fin n))).map_update_smul
        (fun j : ULift.{uR} (Fin n) => x j.down) (ULift.up i) r a

/-- Scalar-extended symmetric multiplication, before quotient descent. -/
private def baseChangeSlots (n : ℕ) :
    MultilinearMap S (fun _ : ULift.{uS} (Fin n) => S ⊗[R] M)
      (S ⊗[R] SymmetricPower R (ULift.{uR} (Fin n)) M) := by
  let f := extendFinite R S M
    (S ⊗[R] SymmetricPower R (ULift.{uR} (Fin n)) M) n
    ((TensorProduct.mk R S (SymmetricPower R (ULift.{uR} (Fin n)) M) 1).compMultilinearMap
      (finiteSymmetricForm R M n))
  exact {
    toFun := fun z => f (fun j => z (ULift.up j))
    map_update_add' := by
      intro _ z i a b
      have hu (c : S ⊗[R] M) :
          (fun j : Fin n => Function.update z i c (ULift.up j)) =
            Function.update (fun j : Fin n => z (ULift.up j)) i.down c := by
        ext j
        rcases i with ⟨i⟩
        by_cases h : j = i <;> simp [h]
      simpa only [hu] using f.map_update_add (fun j => z (ULift.up j)) i.down a b
    map_update_smul' := by
      intro _ z i s a
      have hu (c : S ⊗[R] M) :
          (fun j : Fin n => Function.update z i c (ULift.up j)) =
            Function.update (fun j : Fin n => z (ULift.up j)) i.down c := by
        ext j
        rcases i with ⟨i⟩
        by_cases h : j = i <;> simp [h]
      simpa only [hu] using f.map_update_smul (fun j => z (ULift.up j)) i.down s a }

private theorem baseChangeSlots_tmul (n : ℕ)
    (s : ULift.{uS} (Fin n) → S) (x : ULift.{uS} (Fin n) → M) :
    baseChangeSlots R S M n (fun i => s i ⊗ₜ[R] x i) =
      (∏ j : Fin n, s (ULift.up j)) ⊗ₜ[R]
        tprod R (fun i : ULift.{uR} (Fin n) => x (ULift.up i.down)) := by
  change extendFinite R S M
      (S ⊗[R] SymmetricPower R (ULift.{uR} (Fin n)) M) n _
      (fun j => s (ULift.up j) ⊗ₜ[R] x (ULift.up j)) = _
  rw [extendFinite_tmul]
  change (∏ j : Fin n, s (ULift.up j)) •
    ((1 : S) ⊗ₜ[R] tprod R (fun i : ULift.{uR} (Fin n) => x (ULift.up i.down))) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem baseChangeSlots_perm (n : ℕ)
    (e : Equiv.Perm (ULift.{uS} (Fin n)))
    (z : ULift.{uS} (Fin n) → S ⊗[R] M) :
    baseChangeSlots R S M n (fun i => z (e i)) = baseChangeSlots R S M n z := by
  let a : Fin n ≃ ULift.{uS} (Fin n) :=
    ⟨ULift.up, ULift.down, fun _ => rfl, fun i => by cases i; rfl⟩
  let b : ULift.{uR} (Fin n) ≃ ULift.{uS} (Fin n) :=
    ⟨fun i => ULift.up i.down, fun i => ULift.up i.down,
      fun i => by cases i; rfl, fun i => by cases i; rfl⟩
  let eFin : Equiv.Perm (Fin n) := (a.trans e).trans a.symm
  let eR : Equiv.Perm (ULift.{uR} (Fin n)) := (b.trans e).trans b.symm
  have hp : (baseChangeSlots R S M n).domDomCongr e = baseChangeSlots R S M n := by
    apply tensorSlots_ext
    intro s x
    change baseChangeSlots R S M n (fun i => s (e i) ⊗ₜ[R] x (e i)) = _
    rw [baseChangeSlots_tmul, baseChangeSlots_tmul]
    have hc : (∏ j : Fin n, s (e (ULift.up j))) = ∏ j : Fin n, s (ULift.up j) := by
      simpa [eFin, a] using Equiv.prod_comp eFin (fun j => s (ULift.up j))
    have hx :
        tprod R (fun i : ULift.{uR} (Fin n) => x (e (ULift.up i.down))) =
          tprod R (fun i : ULift.{uR} (Fin n) => x (ULift.up i.down)) := by
      simpa [eR, b] using
        tprod_equiv eR (fun i : ULift.{uR} (Fin n) => x (ULift.up i.down))
    rw [hc, hx]
  exact congrArg (fun f : MultilinearMap S
    (fun _ : ULift.{uS} (Fin n) => S ⊗[R] M)
    (S ⊗[R] SymmetricPower R (ULift.{uR} (Fin n)) M) => f z) hp

/-- Collect the scalar coefficients of a finite symmetric tensor after extension of scalars. -/
def baseChangeInverse (n : ℕ) :
    SymmetricPower S (ULift.{uS} (Fin n)) (S ⊗[R] M) →ₗ[S]
      (S ⊗[R] SymmetricPower R (ULift.{uR} (Fin n)) M) :=
  lift (baseChangeSlots R S M n) (baseChangeSlots_perm R S M n)

/-- On independently labelled pure slots, scalar coefficients multiply. -/
@[simp] theorem baseChangeInverse_tprod_tmul (n : ℕ)
    (s : ULift.{uS} (Fin n) → S) (x : ULift.{uS} (Fin n) → M) :
    baseChangeInverse R S M n (tprod S (fun i => s i ⊗ₜ[R] x i)) =
      (∏ j : Fin n, s (ULift.up j : ULift.{uS} (Fin n))) ⊗ₜ[R]
        tprod R (fun i : ULift.{uR} (Fin n) =>
          x (ULift.up i.down : ULift.{uS} (Fin n))) := by
  rw [baseChangeInverse, lift_tprod, baseChangeSlots_tmul]

/-- Linear maps out of the extended finite symmetric power are determined by all
independently labelled families of pure tensors, including the empty family. -/
theorem baseChange_hom_ext (n : ℕ)
    {N : Type uN} [AddCommMonoid N] [Module S N]
    {f g : SymmetricPower S (ULift.{uS} (Fin n)) (S ⊗[R] M) →ₗ[S] N}
    (h : ∀ (s : ULift.{uS} (Fin n) → S) (x : ULift.{uS} (Fin n) → M),
      f (tprod S (fun i => s i ⊗ₜ[R] x i)) =
        g (tprod S (fun i => s i ⊗ₜ[R] x i))) : f = g := by
  have hm : f.compMultilinearMap (tprod S) = g.compMultilinearMap (tprod S) := by
    apply tensorSlots_ext
    exact h
  apply hom_ext
  intro x
  exact congrArg (fun p : MultilinearMap S
    (fun _ : ULift.{uS} (Fin n) => S ⊗[R] M) N => p x) hm

/-- The all-labelled pure-slot formula uniquely characterizes coefficient collection. -/
theorem baseChangeInverse_unique (n : ℕ)
    (g : SymmetricPower S (ULift.{uS} (Fin n)) (S ⊗[R] M) →ₗ[S]
      (S ⊗[R] SymmetricPower R (ULift.{uR} (Fin n)) M))
    (h : ∀ (s : ULift.{uS} (Fin n) → S) (x : ULift.{uS} (Fin n) → M),
      g (tprod S (fun i => s i ⊗ₜ[R] x i)) =
        (∏ j : Fin n, s (ULift.up j : ULift.{uS} (Fin n))) ⊗ₜ[R]
          tprod R (fun i : ULift.{uR} (Fin n) =>
            x (ULift.up i.down : ULift.{uS} (Fin n)))) :
    g = baseChangeInverse R S M n := by
  apply baseChange_hom_ext R S M n
  intro s x
  rw [h, baseChangeInverse_tprod_tmul]

/-- Coefficient collection preserves the degree-zero unit under the canonical
empty-index equivalences and the S-linear right tensor unitor. -/
theorem baseChangeInverse_zero :
    (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp
        (((isEmptyEquiv (R := R) (ι := ULift.{uR} (Fin 0)) (M := M)).toLinearMap.baseChange S).comp
          (baseChangeInverse R S M 0)) =
      (isEmptyEquiv (R := S) (ι := ULift.{uS} (Fin 0))
        (M := S ⊗[R] M)).toLinearMap := by
  apply baseChange_hom_ext R S M 0
  intro s x
  simp only [LinearMap.comp_apply, baseChangeInverse_tprod_tmul, Fin.prod_univ_zero,
    LinearMap.baseChange_tmul]
  change (TensorProduct.AlgebraTensorModule.rid R S S)
      ((1 : S) ⊗ₜ[R]
        (isEmptyEquiv (R := R) (ι := ULift.{uR} (Fin 0)) (M := M))
          (tprod R (fun i : ULift.{uR} (Fin 0) =>
            x (ULift.up i.down : ULift.{uS} (Fin 0))))) =
    (isEmptyEquiv (R := S) (ι := ULift.{uS} (Fin 0)) (M := S ⊗[R] M))
      (tprod S (fun i : ULift.{uS} (Fin 0) => s i ⊗ₜ[R] x i))
  rw [isEmptyEquiv_tprod, isEmptyEquiv_tprod,
    TensorProduct.AlgebraTensorModule.rid_tmul]
  exact one_smul R (1 : S)

end Inverse

end SymmetricPower

end

noncomputable section

namespace SymmetricPower

variable (R : Type uR) [CommSemiring R]
variable (S : Type uS) [CommSemiring S] [Algebra R S]
variable (M : Type uM) [AddCommMonoid M] [Module R M]
variable (n : ℕ)

private theorem baseChange_tprod_tmul_coefficients
    (s : ULift.{uS} (Fin n) → S) (x : ULift.{uS} (Fin n) → M) :
    tprod S (fun i => s i ⊗ₜ[R] x i) =
      (∏ j : Fin n, s (ULift.up j : ULift.{uS} (Fin n))) •
        tprod S (fun i : ULift.{uS} (Fin n) => (1 : S) ⊗ₜ[R] x i) := by
  classical
  let e : Fin n ≃ ULift.{uS} (Fin n) :=
    { toFun := ULift.up
      invFun := ULift.down
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hp : (∏ i : ULift.{uS} (Fin n), s i) =
      ∏ j : Fin n, s (ULift.up j : ULift.{uS} (Fin n)) :=
    (Equiv.prod_comp e s).symm
  have hs (i : ULift.{uS} (Fin n)) :
      s i • ((1 : S) ⊗ₜ[R] x i) = s i ⊗ₜ[R] x i := by
    rw [TensorProduct.smul_tmul']
    simp
  have h := MultilinearMap.map_smul_univ (tprod S) s
    (fun i : ULift.{uS} (Fin n) => (1 : S) ⊗ₜ[R] x i)
  simp_rw [hs] at h
  rw [hp] at h
  exact h

/-- Collecting coefficients after extending them is the identity. -/
theorem baseChangeInverse_comp_baseChange :
    (baseChangeInverse R S M n).comp (baseChange R S M n) =
      LinearMap.id := by
  apply baseChange_ext R S M n
  intro s x
  change baseChangeInverse R S M n
      (baseChange R S M n (s ⊗ₜ[R] tprod R x)) = s ⊗ₜ[R] tprod R x
  rw [baseChange_tmul_tprod, LinearMap.map_smul, baseChangeInverse_tprod_tmul]
  simp only [Finset.prod_const_one]
  change s • ((1 : S) ⊗ₜ[R] tprod R x) = s ⊗ₜ[R] tprod R x
  rw [TensorProduct.smul_tmul']
  simp

/-- Extending coefficients after collecting them is the identity. -/
theorem baseChange_comp_baseChangeInverse :
    (baseChange R S M n).comp (baseChangeInverse R S M n) =
      LinearMap.id := by
  apply baseChange_hom_ext R S M n
  intro s x
  change baseChange R S M n
      (baseChangeInverse R S M n (tprod S (fun i => s i ⊗ₜ[R] x i))) =
    tprod S (fun i => s i ⊗ₜ[R] x i)
  rw [baseChangeInverse_tprod_tmul, baseChange_tmul_tprod]
  change (∏ j : Fin n, s (ULift.up j : ULift.{uS} (Fin n))) •
      tprod S (fun i : ULift.{uS} (Fin n) => (1 : S) ⊗ₜ[R] x i) =
    tprod S (fun i => s i ⊗ₜ[R] x i)
  exact (baseChange_tprod_tmul_coefficients R S M n s x).symm

/-- Scalar extension commutes with finite symmetric powers.

This is the finite-degree symmetric-algebra comparison of Bourbaki, *Algebra I*,
stated for semimodules over commutative semirings. -/
def baseChangeEquiv :
    (S ⊗[R] SymmetricPower R (ULift.{uR} (Fin n)) M) ≃ₗ[S]
      SymmetricPower S (ULift.{uS} (Fin n)) (S ⊗[R] M) :=
  LinearEquiv.ofLinearMap (baseChange R S M n) (baseChangeInverse R S M n)
    (baseChange_comp_baseChangeInverse R S M n)
    (baseChangeInverse_comp_baseChange R S M n)

/-- The forward linear map of the comparison is coefficient extension. -/
@[simp] theorem baseChangeEquiv_toLinearMap :
    (baseChangeEquiv R S M n).toLinearMap = baseChange R S M n := by
  exact LinearEquiv.toLinearMap_ofLinearMap _ _ _ _

/-- The inverse linear map of the comparison is coefficient collection. -/
@[simp] theorem baseChangeEquiv_symm_toLinearMap :
    (baseChangeEquiv R S M n).symm.toLinearMap = baseChangeInverse R S M n := by
  unfold baseChangeEquiv
  rw [LinearEquiv.symm_ofLinearMap]
  exact LinearEquiv.toLinearMap_ofLinearMap _ _ _ _

/-- The comparison extends each symmetric generator with unit coefficients. -/
@[simp] theorem baseChangeEquiv_tmul_tprod
    (s : S) (x : ULift.{uR} (Fin n) → M) :
    baseChangeEquiv R S M n (s ⊗ₜ[R] tprod R x) =
      s • tprod S (fun i : ULift.{uS} (Fin n) =>
        (1 : S) ⊗ₜ[R] x (ULift.up i.down : ULift.{uR} (Fin n))) := by
  change (baseChangeEquiv R S M n).toLinearMap (s ⊗ₜ[R] tprod R x) = _
  rw [baseChangeEquiv_toLinearMap, baseChange_tmul_tprod]

/-- The inverse comparison collects all independently labelled coefficients. -/
@[simp] theorem baseChangeEquiv_symm_tprod_tmul
    (s : ULift.{uS} (Fin n) → S) (x : ULift.{uS} (Fin n) → M) :
    (baseChangeEquiv R S M n).symm (tprod S (fun i => s i ⊗ₜ[R] x i)) =
      (∏ j : Fin n, s (ULift.up j : ULift.{uS} (Fin n))) ⊗ₜ[R]
        tprod R (fun i : ULift.{uR} (Fin n) =>
          x (ULift.up i.down : ULift.{uS} (Fin n))) := by
  change (baseChangeEquiv R S M n).symm.toLinearMap
    (tprod S (fun i => s i ⊗ₜ[R] x i)) = _
  rw [baseChangeEquiv_symm_toLinearMap, baseChangeInverse_tprod_tmul]

/-- In degree zero, the comparison is the canonical scalar-unit map. -/
theorem baseChangeEquiv_zero_unit :
    (isEmptyEquiv (R := S) (ι := ULift.{uS} (Fin 0))
        (M := S ⊗[R] M)).toLinearMap.comp (baseChangeEquiv R S M 0).toLinearMap =
      (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp
        ((isEmptyEquiv (R := R) (ι := ULift.{uR} (Fin 0))
          (M := M)).toLinearMap.baseChange S) := by
  rw [baseChangeEquiv_toLinearMap]
  exact baseChange_zero_unit R S M

/-- In degree zero, the inverse comparison preserves the canonical scalar unit. -/
theorem baseChangeEquiv_symm_zero_unit :
    (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp
        (((isEmptyEquiv (R := R) (ι := ULift.{uR} (Fin 0))
          (M := M)).toLinearMap.baseChange S).comp
            (baseChangeEquiv R S M 0).symm.toLinearMap) =
      (isEmptyEquiv (R := S) (ι := ULift.{uS} (Fin 0))
        (M := S ⊗[R] M)).toLinearMap := by
  rw [baseChangeEquiv_symm_toLinearMap]
  exact baseChangeInverse_zero R S M

end SymmetricPower

end

noncomputable section

namespace SymmetricPower

variable (R : Type uR) [CommSemiring R]
variable (S : Type uS) [CommSemiring S] [Algebra R S]
variable (M : Type uM) [AddCommMonoid M] [Module R M]
variable (n : ℕ)

/-- Extension of scalars on finite symmetric powers commutes with the map induced
by a linear map of modules. -/
theorem baseChange_natural
    {N : Type uN} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    (baseChange R S N n).comp
        ((map (R := R) (ι := ULift.{uR} (Fin n)) f).baseChange S) =
      (map (R := S) (ι := ULift.{uS} (Fin n)) (f.baseChange S)).comp
        (baseChange R S M n) := by
  apply baseChange_ext R S M n
  intro s x
  change baseChange R S N n
      (((map (R := R) (ι := ULift.{uR} (Fin n)) f).baseChange S)
        (s ⊗ₜ[R] tprod R x)) =
    map (R := S) (ι := ULift.{uS} (Fin n)) (f.baseChange S)
      (baseChange R S M n (s ⊗ₜ[R] tprod R x))
  simp only [LinearMap.baseChange_tmul, map_tprod, baseChange_tmul_tprod,
    LinearMap.map_smul]

/-- The scalar-extension equivalence for finite symmetric powers is natural in
the module. -/
theorem baseChangeEquiv_natural
    {N : Type uN} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    (map (R := S) (ι := ULift.{uS} (Fin n)) (f.baseChange S)).comp
        (baseChangeEquiv R S M n).toLinearMap =
      (baseChangeEquiv R S N n).toLinearMap.comp
        ((map (R := R) (ι := ULift.{uR} (Fin n)) f).baseChange S) := by
  rw [baseChangeEquiv_toLinearMap, baseChangeEquiv_toLinearMap]
  exact (baseChange_natural R S M n f).symm

end SymmetricPower

end
