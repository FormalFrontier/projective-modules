/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.BaseChange
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# Exterior powers and extension of scalars

For every degree, exterior powers commute with extension of scalars. The equivalence
`exteriorPower.baseChangeEquiv` is characterized on pure wedges and is natural in the
module. It agrees with `ExteriorAlgebra.equivBaseChange` on the homogeneous components.

The degree inclusion is split by the grading of the exterior algebra. Tensoring this
splitting makes the comparison with the base-changed submodule injective; no flatness
hypothesis is needed.
-/

@[expose] public section

open scoped TensorProduct

universe uR uS uM uN

namespace exteriorPower

section SplitSubmodule

variable {R : Type uR} [CommSemiring R]
variable {S : Type uS} [Semiring S] [Algebra R S]
variable {M : Type uM} [AddCommMonoid M] [Module R M]

private theorem subtype_comp_toBaseChange (p : Submodule R M) :
    (p.baseChange S).subtype.comp (p.toBaseChange S) = p.subtype.baseChange S := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s x
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
  change (p.toBaseChange S (s ⊗ₜ[R] x) : S ⊗[R] M) = s ⊗ₜ[R] (x : M)
  exact p.coe_toBaseChange_tmul S s x

private theorem toBaseChange_injective_of_leftInverse (p : Submodule R M)
    (retract : M →ₗ[R] p) (h : Function.LeftInverse retract p.subtype) :
    Function.Injective (p.toBaseChange S) := by
  have hc : retract.comp p.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact h x
  have hb : (retract.baseChange S).comp (p.subtype.baseChange S) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hc, LinearMap.baseChange_id]
  intro x y hxy
  have ht := congrArg (fun z => retract.baseChange S ((p.baseChange S).subtype z)) hxy
  change ((retract.baseChange S).comp
    ((p.baseChange S).subtype.comp (p.toBaseChange S))) x =
    ((retract.baseChange S).comp
      ((p.baseChange S).subtype.comp (p.toBaseChange S))) y at ht
  rw [subtype_comp_toBaseChange, hb] at ht
  exact ht

end SplitSubmodule

variable {R : Type uR} [CommRing R]
variable {S : Type uS} [CommRing S] [Algebra R S]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]

private noncomputable def degreeRetraction (n : ℕ) :
    ExteriorAlgebra R M →ₗ[R] ⋀[R]^n M :=
  (DirectSum.component R ℕ (fun i : ℕ => ⋀[R]^i M) n).comp
    (DirectSum.decomposeLinearEquiv (fun i : ℕ => ⋀[R]^i M)).toLinearMap

private theorem degreeRetraction_leftInverse (n : ℕ) :
    Function.LeftInverse (degreeRetraction (R := R) (M := M) n) (⋀[R]^n M).subtype := by
  intro x
  change DirectSum.component R ℕ (fun i : ℕ => ⋀[R]^i M) n
    (DirectSum.decomposeLinearEquiv (fun i : ℕ => ⋀[R]^i M) (x : ExteriorAlgebra R M)) = x
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.component.lof_self]

/-- Exterior powers commute with extension of scalars, in every degree and without
any flatness or finiteness assumption on the scalar algebra or the module. -/
noncomputable def baseChangeEquiv (n : ℕ) :
    S ⊗[R] (⋀[R]^n M) ≃ₗ[S] ⋀[S]^n (S ⊗[R] M) :=
  (LinearEquiv.ofBijective ((⋀[R]^n M).toBaseChange S) (by
    exact ⟨toBaseChange_injective_of_leftInverse _ (degreeRetraction n)
        (degreeRetraction_leftInverse n),
      (⋀[R]^n M).toBaseChange_surjective S⟩)).trans
    ((ExteriorAlgebra.equivBaseChange (R := R) (S := S) (M := M)).toLinearEquiv.ofSubmodules
      (⋀[S]^n (S ⊗[R] M)) ((⋀[R]^n M).baseChange S)
      (ExteriorAlgebra.equivBaseChange_map_exteriorPower n)).symm

/-- The degreewise equivalence agrees with the ambient exterior-algebra equivalence. -/
theorem baseChangeEquiv_ambient_apply (n : ℕ) (x : S ⊗[R] (⋀[R]^n M)) :
    ExteriorAlgebra.equivBaseChange (R := R) (S := S) (M := M)
        (baseChangeEquiv (R := R) (S := S) (M := M) n x :
          ExteriorAlgebra S (S ⊗[R] M)) =
      (⋀[R]^n M).subtype.baseChange S x := by
  let e := (ExteriorAlgebra.equivBaseChange (R := R) (S := S) (M := M)).toLinearEquiv
  simp only [baseChangeEquiv, LinearEquiv.trans_apply]
  change e
    (((e.ofSubmodules (⋀[S]^n (S ⊗[R] M)) ((⋀[R]^n M).baseChange S)
      (ExteriorAlgebra.equivBaseChange_map_exteriorPower n)).symm
        ((⋀[R]^n M).toBaseChange S x)) : ExteriorAlgebra S (S ⊗[R] M)) = _
  rw [LinearEquiv.ofSubmodules_symm_apply, e.apply_symm_apply]
  exact LinearMap.congr_fun (subtype_comp_toBaseChange (S := S) (⋀[R]^n M)) x

/-- The commuting square relating extension of scalars in one degree to extension
of scalars of the whole exterior algebra. -/
theorem baseChangeEquiv_ambient (n : ℕ) :
    (ExteriorAlgebra.equivBaseChange (R := R) (S := S) (M := M)).toLinearEquiv.toLinearMap.comp
        ((⋀[S]^n (S ⊗[R] M)).subtype.comp
          (baseChangeEquiv (R := R) (S := S) (M := M) n).toLinearMap) =
      (⋀[R]^n M).subtype.baseChange S := by
  apply LinearMap.ext
  intro x
  exact baseChangeEquiv_ambient_apply n x

private theorem equivBaseChange_ιMulti_one_tmul (n : ℕ) (v : Fin n → M) :
    ExteriorAlgebra.equivBaseChange (R := R) (S := S) (M := M)
        (ExteriorAlgebra.ιMulti S n (fun i => (1 : S) ⊗ₜ[R] v i)) =
      (1 : S) ⊗ₜ[R] ExteriorAlgebra.ιMulti R n v := by
  induction n with
  | zero =>
      simp only [ExteriorAlgebra.ιMulti_zero_apply, map_one, Algebra.TensorProduct.one_def]
  | succ n ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul,
        ExteriorAlgebra.equivBaseChange_apply_ι_tmul]
      change ((1 : S) ⊗ₜ[R] ExteriorAlgebra.ι R (v 0)) *
        ExteriorAlgebra.equivBaseChange (R := R) (S := S) (M := M)
          (ExteriorAlgebra.ιMulti S n (fun i => (1 : S) ⊗ₜ[R] Matrix.vecTail v i)) = _
      rw [ih, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        ExteriorAlgebra.ιMulti_succ_apply]

/-- Extension of scalars sends a tensor of a pure wedge to the wedge of the
unit tensors, scaled by its coefficient. -/
@[simp] theorem baseChangeEquiv_tmul_ιMulti (n : ℕ) (s : S) (v : Fin n → M) :
    baseChangeEquiv (R := R) (S := S) (M := M) n (s ⊗ₜ[R] ιMulti R n v) =
      s • ιMulti S n (fun i => (1 : S) ⊗ₜ[R] v i) := by
  apply Subtype.val_injective
  apply (ExteriorAlgebra.equivBaseChange (R := R) (S := S) (M := M)).injective
  rw [baseChangeEquiv_ambient_apply, LinearMap.baseChange_tmul]
  simp only [Submodule.coe_smul, ιMulti_apply_coe, map_smul,
    equivBaseChange_ιMulti_one_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact congrArg (fun x : ExteriorAlgebra R M => s ⊗ₜ[R] x) (ιMulti_apply_coe R n v)

/-- The inverse comparison sends a wedge of unit tensors to the unit tensor of
the corresponding wedge. -/
@[simp] theorem baseChangeEquiv_symm_ιMulti (n : ℕ) (v : Fin n → M) :
    (baseChangeEquiv (R := R) (S := S) (M := M) n).symm
        (ιMulti S n (fun i => (1 : S) ⊗ₜ[R] v i)) =
      (1 : S) ⊗ₜ[R] ιMulti R n v := by
  apply (baseChangeEquiv (R := R) (S := S) (M := M) n).injective
  simp only [LinearEquiv.apply_symm_apply, baseChangeEquiv_tmul_ιMulti, one_smul]

/-- Linear maps out of a base-changed exterior power are determined by the
unit tensors of pure wedges. -/
@[ext] theorem baseChange_linearMap_ext (n : ℕ) {P : Type*}
    [AddCommMonoid P] [Module S P] {f g : S ⊗[R] (⋀[R]^n M) →ₗ[S] P}
    (h : ∀ v : Fin n → M,
      f ((1 : S) ⊗ₜ[R] ιMulti R n v) = g ((1 : S) ⊗ₜ[R] ιMulti R n v)) : f = g := by
  -- Balance scalars in the source; the target needs only its given S-action.
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
      have hx : x ∈ Submodule.span R (Set.range (ιMulti R n : (Fin n → M) → ⋀[R]^n M)) := by
        rw [ιMulti_span]
        trivial
      have heq : ∀ s : S, f (s ⊗ₜ[R] x) = g (s ⊗ₜ[R] x) := by
        refine Submodule.span_induction (p := fun x _ =>
          ∀ s : S, f (s ⊗ₜ[R] x) = g (s ⊗ₜ[R] x)) ?_ ?_ ?_ ?_ hx
        · rintro _ ⟨v, rfl⟩ s
          have hs := congrArg (fun y => s • y) (h v)
          simpa only [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hs
        · intro s
          simp
        · intro x y _ _ hx hy s
          simp only [TensorProduct.tmul_add, map_add, hx s, hy s]
        · intro r x _ hx s
          simpa only [← TensorProduct.smul_tmul] using hx (r • s)
      exact heq s
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Equivalences agreeing on the unit tensors of pure wedges are equal. -/
theorem baseChangeEquiv_ext (n : ℕ)
    {E F : S ⊗[R] (⋀[R]^n M) ≃ₗ[S] ⋀[S]^n (S ⊗[R] M)}
    (h : ∀ v : Fin n → M,
      E ((1 : S) ⊗ₜ[R] ιMulti R n v) = F ((1 : S) ⊗ₜ[R] ιMulti R n v)) : E = F := by
  have heq : E.toLinearMap = F.toLinearMap := baseChange_linearMap_ext n h
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun heq x

/-- The pure-wedge formula uniquely characterizes the scalar-extension equivalence. -/
theorem baseChangeEquiv_unique (n : ℕ)
    (E : S ⊗[R] (⋀[R]^n M) ≃ₗ[S] ⋀[S]^n (S ⊗[R] M))
    (h : ∀ v : Fin n → M,
      E ((1 : S) ⊗ₜ[R] ιMulti R n v) =
        ιMulti S n (fun i => (1 : S) ⊗ₜ[R] v i)) :
    E = baseChangeEquiv (R := R) (S := S) (M := M) n := by
  apply baseChangeEquiv_ext n
  intro v
  simpa only [baseChangeEquiv_tmul_ιMulti, one_smul] using h v

/-- Extension of scalars on exterior powers is natural with respect to every
linear map of the original modules. -/
theorem baseChangeEquiv_naturality (n : ℕ) (f : M →ₗ[R] N) :
    (baseChangeEquiv (R := R) (S := S) (M := N) n).toLinearMap.comp
        ((map n f).baseChange S) =
      (map n (f.baseChange S)).comp
        (baseChangeEquiv (R := R) (S := S) (M := M) n).toLinearMap := by
  apply baseChange_linearMap_ext n
  intro v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
    map_apply_ιMulti, baseChangeEquiv_tmul_ιMulti, one_smul, Function.comp_def]

end exteriorPower
