/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Dual
public import ProjectiveModules.KTheory.Ring
import ProjectiveModules.TensorProduct.SemilinearHomProjective

@[expose] public section

/-!
# Multiplicative opposite-ring duality

For a commutative ring, opposite-ring duality on finite projective classes and on
`K₀` is stated as a ring equivalence extending the corresponding additive equivalence.
Each ring equivalence retains the whole original additive equivalence.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*.
-/

universe u

open scoped TensorProduct

namespace KTheory

variable (R : Type u) [CommRing R]

namespace ProjectiveClass

/-- Opposite-ring duality preserves products of finite projective classes over a
commutative ring. For background on these products and duality, see Weibel,
*The K-book*. -/
theorem dualEquiv_mul (x y : ProjectiveClass R) :
    dualEquiv R (x * y) = dualEquiv R x * dualEquiv R y := by
  have bridge (M : Type u) (N : Type u)
      [AddCommGroup M] [Module Rᵐᵒᵖ M]
      [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
      [AddCommGroup N] [Module Rᵐᵒᵖ N]
      [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
      dualEquiv R (of R (M ⊗[Rᵐᵒᵖ] N)) =
        dualEquiv R (of R M) * dualEquiv R (of R N) := by
    let S := Rᵐᵒᵖᵐᵒᵖ
    let σ : Rᵐᵒᵖ →+* S :=
      { toFun := MulOpposite.op
        map_one' := rfl
        map_mul' := by
          intro a b
          change MulOpposite.op (a * b) = MulOpposite.op (b * a)
          rw [mul_comm]
        map_zero' := rfl
        map_add' := by intros; rfl }
    let D (P : Type _) [AddCommGroup P] [Module Rᵐᵒᵖ P] : ModuleCat S :=
      (ModuleCat.restrictScalars (RingEquiv.opOp R).symm.toRingHom).obj
        ((ModuleCat.rightDual R).obj (Opposite.op (ModuleCat.of Rᵐᵒᵖ P)))
    let δ (P : Type _) [AddCommGroup P] [Module Rᵐᵒᵖ P] (f : D P) :
        P →ₗ[Rᵐᵒᵖ] R :=
      (show P →ₗ[Rᵐᵒᵖ] R from f)
    have δ_zero (P : Type _) [AddCommGroup P] [Module Rᵐᵒᵖ P] (p : P) :
        δ P (0 : D P) p = 0 := by
      rfl
    have δ_add (P : Type _) [AddCommGroup P] [Module Rᵐᵒᵖ P]
        (f g : D P) (p : P) :
        δ P (f + g) p = δ P f p + δ P g p := by
      rfl
    have δ_smul (P : Type _) [AddCommGroup P] [Module Rᵐᵒᵖ P]
        (s : S) (f : D P) (p : P) :
        δ P (s • f) p = (RingEquiv.opOp R).symm s * δ P f p := by
      rfl
    let eD (P : Type _) [AddCommGroup P] [Module Rᵐᵒᵖ P] :
        D P ≃ₗ[S] (P →ₛₗ[σ] S) :=
      { toFun := fun f =>
          { toFun := fun p => (RingEquiv.opOp R) (δ P f p)
            map_add' := by
              intro p q
              rw [map_add, map_add]
            map_smul' := by
              intro r p
              change (RingEquiv.opOp R) (δ P f (r • p)) =
                MulOpposite.op r * (RingEquiv.opOp R) (δ P f p)
              rw [map_smul]
              change (RingEquiv.opOp R) (δ P f p * MulOpposite.unop r) =
                MulOpposite.op r * (RingEquiv.opOp R) (δ P f p)
              rw [map_mul]
              change (RingEquiv.opOp R) (δ P f p) * MulOpposite.op r =
                MulOpposite.op r * (RingEquiv.opOp R) (δ P f p)
              exact mul_comm _ _ }
        invFun := fun f =>
          (show P →ₗ[Rᵐᵒᵖ] R from
            { toFun := fun p => (RingEquiv.opOp R).symm (f p)
              map_add' := by
                intro p q
                rw [map_add f, map_add]
              map_smul' := by
                intro r p
                change (RingEquiv.opOp R).symm (f (r • p)) =
                  (RingEquiv.opOp R).symm (f p) * MulOpposite.unop r
                rw [map_smulₛₗ]
                change (RingEquiv.opOp R).symm (MulOpposite.op r * f p) =
                  (RingEquiv.opOp R).symm (f p) * MulOpposite.unop r
                rw [map_mul]
                change MulOpposite.unop r * (RingEquiv.opOp R).symm (f p) =
                  (RingEquiv.opOp R).symm (f p) * MulOpposite.unop r
                exact mul_comm _ _ })
        left_inv := by
          intro f
          apply LinearMap.ext
          intro p
          exact (RingEquiv.opOp R).symm_apply_apply (δ P f p)
        right_inv := by
          intro f
          apply LinearMap.ext
          intro p
          exact (RingEquiv.opOp R).apply_symm_apply (f p)
        map_add' := by
          intro f g
          apply LinearMap.ext
          intro p
          change (RingEquiv.opOp R) (δ P f p + δ P g p) =
            (RingEquiv.opOp R) (δ P f p) + (RingEquiv.opOp R) (δ P g p)
          exact map_add _ _ _
        map_smul' := by
          intro s f
          apply LinearMap.ext
          intro p
          change (RingEquiv.opOp R) (δ P (s • f) p) =
            s * (RingEquiv.opOp R) (δ P f p)
          rw [δ_smul, map_mul, RingEquiv.apply_symm_apply] }
    let μ : D M ⊗[S] D N →ₗ[S] D (M ⊗[Rᵐᵒᵖ] N) :=
      TensorProduct.lift
        { toFun := fun f =>
            { toFun := fun g =>
                TensorProduct.lift
                  { toFun := fun m =>
                      { toFun := fun n => δ M f m * δ N g n
                        map_add' := by
                          intro n n'
                          rw [map_add, mul_add]
                        map_smul' := by
                          intro r n
                          change δ M f m * δ N g (r • n) =
                            (δ M f m * δ N g n) * MulOpposite.unop r
                          rw [map_smul]
                          change δ M f m * (δ N g n * MulOpposite.unop r) =
                            (δ M f m * δ N g n) * MulOpposite.unop r
                          exact (mul_assoc _ _ _).symm }
                    map_add' := by
                      intro m m'
                      apply LinearMap.ext
                      intro n
                      change δ M f (m + m') * δ N g n =
                        δ M f m * δ N g n + δ M f m' * δ N g n
                      rw [map_add, add_mul]
                    map_smul' := by
                      intro r m
                      apply LinearMap.ext
                      intro n
                      change δ M f (r • m) * δ N g n =
                        (δ M f m * δ N g n) * MulOpposite.unop r
                      rw [map_smul]
                      change (δ M f m * MulOpposite.unop r) * δ N g n =
                        (δ M f m * δ N g n) * MulOpposite.unop r
                      ac_rfl }
              map_add' := by
                intro g g'
                apply TensorProduct.ext
                apply LinearMap.ext
                intro m
                apply LinearMap.ext
                intro n
                change δ M f m * (δ N g n + δ N g' n) =
                  δ M f m * δ N g n + δ M f m * δ N g' n
                exact mul_add _ _ _
              map_smul' := by
                intro s g
                apply TensorProduct.ext
                apply LinearMap.ext
                intro m
                apply LinearMap.ext
                intro n
                change δ M f m * δ N (s • g) n =
                  δ (M ⊗[Rᵐᵒᵖ] N) (s • _) (m ⊗ₜ[Rᵐᵒᵖ] n)
                simp only [δ_smul]
                ac_rfl }
          map_add' := by
            intro f f'
            apply LinearMap.ext
            intro g
            apply TensorProduct.ext
            apply LinearMap.ext
            intro m
            apply LinearMap.ext
            intro n
            change (δ M f m + δ M f' m) * δ N g n =
              δ M f m * δ N g n + δ M f' m * δ N g n
            exact add_mul _ _ _
          map_smul' := by
            intro s f
            apply LinearMap.ext
            intro g
            apply TensorProduct.ext
            apply LinearMap.ext
            intro m
            apply LinearMap.ext
            intro n
            change δ M (s • f) m * δ N g n =
              δ (M ⊗[Rᵐᵒᵖ] N) (s • _) (m ⊗ₜ[Rᵐᵒᵖ] n)
            simp only [δ_smul]
            exact mul_assoc _ _ _ }
    have μ_tmul (f : D M) (g : D N) (m : M) (n : N) :
        δ (M ⊗[Rᵐᵒᵖ] N) (μ (f ⊗ₜ[S] g)) (m ⊗ₜ[Rᵐᵒᵖ] n) =
          δ M f m * δ N g n := by
      rfl
    let E : D M ⊗[S] D N ≃ₗ[S] (M →ₛₗ[σ] (S ⊗[S] D N)) :=
      (TensorProduct.congr (eD M) (LinearEquiv.refl S (D N))).trans
        (LinearEquiv.ofBijective (TensorProduct.semilinearHomTensorMap σ)
          (TensorProduct.semilinearHomTensorMap_bijective σ))
    have evaluation (z : D M ⊗[S] D N) (m : M) (n : N) :
        δ N ((TensorProduct.lid S (D N)) (E z m)) n =
          δ (M ⊗[Rᵐᵒᵖ] N) (μ z) (m ⊗ₜ[Rᵐᵒᵖ] n) := by
      let ε (P : Type _) [AddCommGroup P] [Module Rᵐᵒᵖ P] (p : P) :
          D P →ₗ[S] S :=
        { toFun := fun f => eD P f p
          map_add' := by
            intro f g
            change (eD P (f + g)) p = (eD P f + eD P g) p
            rw [map_add]
          map_smul' := by
            intro s f
            change (eD P (s • f)) p = (s • eD P f) p
            rw [map_smul] }
      let k : D M ⊗[S] D N →ₗ[S] D N :=
        { toFun := fun w => (TensorProduct.lid S (D N)) (E w m)
          map_add' := by
            intro v w
            simp only [map_add, LinearMap.add_apply]
          map_smul' := by
            intro s w
            simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
      have h :
          (ε N n).comp k =
            (ε (M ⊗[Rᵐᵒᵖ] N) (m ⊗ₜ[Rᵐᵒᵖ] n)).comp μ := by
        apply TensorProduct.ext
        apply LinearMap.ext
        intro f
        apply LinearMap.ext
        intro g
        change (RingEquiv.opOp R)
            (δ N ((TensorProduct.lid S (D N)) (E (f ⊗ₜ[S] g) m)) n) =
          (RingEquiv.opOp R)
            (δ (M ⊗[Rᵐᵒᵖ] N) (μ (f ⊗ₜ[S] g)) (m ⊗ₜ[Rᵐᵒᵖ] n))
        apply congrArg (RingEquiv.opOp R)
        rw [μ_tmul]
        change δ N ((TensorProduct.lid S (D N))
          (TensorProduct.semilinearHomTensorMap σ ((eD M f) ⊗ₜ[S] g) m)) n =
            δ M f m * δ N g n
        rw [TensorProduct.semilinearHomTensorMap_tmul]
        change ((RingEquiv.opOp R).symm ((RingEquiv.opOp R) (δ M f m))) *
          δ N g n = δ M f m * δ N g n
        rw [RingEquiv.symm_apply_apply]
      apply (RingEquiv.opOp R).injective
      change ((ε N n).comp k) z =
        ((ε (M ⊗[Rᵐᵒᵖ] N) (m ⊗ₜ[Rᵐᵒᵖ] n)).comp μ) z
      exact congrArg (fun F : D M ⊗[S] D N →ₗ[S] S => F z) h
    let slice (h : D (M ⊗[Rᵐᵒᵖ] N)) (m : M) : D N :=
      (show N →ₗ[Rᵐᵒᵖ] R from
        { toFun := fun n => δ (M ⊗[Rᵐᵒᵖ] N) h (m ⊗ₜ[Rᵐᵒᵖ] n)
          map_add' := by
            intro n n'
            rw [TensorProduct.tmul_add, map_add]
          map_smul' := by
            intro r n
            change δ (M ⊗[Rᵐᵒᵖ] N) h (m ⊗ₜ[Rᵐᵒᵖ] (r • n)) =
              δ (M ⊗[Rᵐᵒᵖ] N) h (m ⊗ₜ[Rᵐᵒᵖ] n) * MulOpposite.unop r
            simp })
    let unit : D N →ₗ[S] S ⊗[S] D N :=
      (TensorProduct.lid S (D N)).symm.toLinearMap
    let curry (h : D (M ⊗[Rᵐᵒᵖ] N)) : M →ₛₗ[σ] (S ⊗[S] D N) :=
      { toFun := fun m => unit (slice h m)
        map_add' := by
          intro m m'
          rw [← map_add]
          congr 1
          apply LinearMap.ext
          intro n
          change δ (M ⊗[Rᵐᵒᵖ] N) h ((m + m') ⊗ₜ[Rᵐᵒᵖ] n) =
            δ (M ⊗[Rᵐᵒᵖ] N) h (m ⊗ₜ[Rᵐᵒᵖ] n) +
              δ (M ⊗[Rᵐᵒᵖ] N) h (m' ⊗ₜ[Rᵐᵒᵖ] n)
          rw [TensorProduct.add_tmul, map_add]
        map_smul' := by
          intro r m
          rw [← map_smul]
          congr 1
          apply LinearMap.ext
          intro n
          change δ (M ⊗[Rᵐᵒᵖ] N) h ((r • m) ⊗ₜ[Rᵐᵒᵖ] n) =
            MulOpposite.unop r * δ (M ⊗[Rᵐᵒᵖ] N) h (m ⊗ₜ[Rᵐᵒᵖ] n)
          rw [← TensorProduct.smul_tmul', map_smul]
          change δ (M ⊗[Rᵐᵒᵖ] N) h (m ⊗ₜ[Rᵐᵒᵖ] n) * MulOpposite.unop r =
            MulOpposite.unop r * δ (M ⊗[Rᵐᵒᵖ] N) h (m ⊗ₜ[Rᵐᵒᵖ] n)
          exact mul_comm _ _ }
    have hμ : Function.Bijective μ := by
      constructor
      · intro z w hzw
        apply E.injective
        apply LinearMap.ext
        intro m
        apply (TensorProduct.lid S (D N)).injective
        apply LinearMap.ext
        intro n
        exact (evaluation z m n).trans
          ((congrArg (fun h : D (M ⊗[Rᵐᵒᵖ] N) =>
            δ (M ⊗[Rᵐᵒᵖ] N) h (m ⊗ₜ[Rᵐᵒᵖ] n)) hzw).trans
              (evaluation w m n).symm)
      · intro h
        refine ⟨E.symm (curry h), ?_⟩
        apply TensorProduct.ext
        apply LinearMap.ext
        intro m
        apply LinearMap.ext
        intro n
        change δ (M ⊗[Rᵐᵒᵖ] N) (μ (E.symm (curry h)))
          (m ⊗ₜ[Rᵐᵒᵖ] n) = δ (M ⊗[Rᵐᵒᵖ] N) h (m ⊗ₜ[Rᵐᵒᵖ] n)
        rw [← evaluation, E.apply_symm_apply]
        change δ N ((TensorProduct.lid S (D N))
          ((TensorProduct.lid S (D N)).symm (slice h m))) n =
            δ (M ⊗[Rᵐᵒᵖ] N) h (m ⊗ₜ[Rᵐᵒᵖ] n)
        rw [LinearEquiv.apply_symm_apply]
        rfl
    let hM := ModuleCat.isFiniteProjective_rightDual_restrictScalars R
      (ModuleCat.of Rᵐᵒᵖ M) ⟨inferInstance, inferInstance⟩
    let hN := ModuleCat.isFiniteProjective_rightDual_restrictScalars R
      (ModuleCat.of Rᵐᵒᵖ N) ⟨inferInstance, inferInstance⟩
    let hMN := ModuleCat.isFiniteProjective_rightDual_restrictScalars R
      (ModuleCat.of Rᵐᵒᵖ (M ⊗[Rᵐᵒᵖ] N)) ⟨inferInstance, inferInstance⟩
    let : Module.Finite S (D M) := hM.1
    let : Module.Projective S (D M) := hM.2
    let : Module.Finite S (D N) := hN.1
    let : Module.Projective S (D N) := hN.2
    let : Module.Finite S (D (M ⊗[Rᵐᵒᵖ] N)) := hMN.1
    let : Module.Projective S (D (M ⊗[Rᵐᵒᵖ] N)) := hMN.2
    rw [dualEquiv_of_module R (M ⊗[Rᵐᵒᵖ] N),
      dualEquiv_of_module R M, dualEquiv_of_module R N,
      of_mul Rᵐᵒᵖ (D M) (D N)]
    exact of_eq_of_equiv (R := Rᵐᵒᵖ)
      (M := D (M ⊗[Rᵐᵒᵖ] N)) (LinearEquiv.ofBijective μ hμ).symm
  refine induction_on (R := R) x ?_
  intro M
  refine induction_on (R := R) y ?_
  intro N
  rw [of_mul R M N]
  exact bridge M N

/-- Opposite-ring duality as a ring equivalence of finite projective classes. -/
noncomputable def dualRingEquiv :
    ProjectiveClass R ≃+* ProjectiveClass Rᵐᵒᵖ :=
  { dualEquiv R with map_mul' := dualEquiv_mul R }

/-- The additive equivalence underlying multiplicative opposite-ring duality is the
original opposite-ring additive duality. -/
theorem dualRingEquiv_toAddEquiv :
    (dualRingEquiv R).toAddEquiv = dualEquiv R := rfl

end ProjectiveClass

namespace K0

/-- Opposite-ring duality preserves products in `K₀` over a commutative ring.
For background on the Grothendieck-ring construction, see Weibel, *The K-book*. -/
theorem dualEquiv_mul (x y : K0 R) :
    dualEquiv R (x * y) = dualEquiv R x * dualEquiv R y := by
  have dual_ofClass (a : ProjectiveClass R) :
      dualEquiv R (ofClassRingHom R a) =
        ofClassRingHom Rᵐᵒᵖ (ProjectiveClass.dualEquiv R a) := by
    refine ProjectiveClass.induction_on (R := R) a ?_
    intro M
    simp only [ofClassRingHom_of, ProjectiveClass.dualEquiv_of_module,
      dualEquiv_of_module]
  have dual_mul_ofClass (a b : ProjectiveClass R) :
      dualEquiv R (ofClassRingHom R a * ofClassRingHom R b) =
        dualEquiv R (ofClassRingHom R a) * dualEquiv R (ofClassRingHom R b) := by
    calc
      dualEquiv R (ofClassRingHom R a * ofClassRingHom R b) =
          dualEquiv R (ofClassRingHom R (a * b)) :=
        congrArg (dualEquiv R) ((ofClassRingHom R).map_mul a b).symm
      _ = ofClassRingHom Rᵐᵒᵖ (ProjectiveClass.dualEquiv R (a * b)) :=
        dual_ofClass (a * b)
      _ = ofClassRingHom Rᵐᵒᵖ
          (ProjectiveClass.dualEquiv R a * ProjectiveClass.dualEquiv R b) :=
        congrArg (ofClassRingHom Rᵐᵒᵖ) (ProjectiveClass.dualEquiv_mul R a b)
      _ = ofClassRingHom Rᵐᵒᵖ (ProjectiveClass.dualEquiv R a) *
          ofClassRingHom Rᵐᵒᵖ (ProjectiveClass.dualEquiv R b) :=
        (ofClassRingHom Rᵐᵒᵖ).map_mul _ _
      _ = dualEquiv R (ofClassRingHom R a) * dualEquiv R (ofClassRingHom R b) :=
        congrArg₂ (· * ·) (dual_ofClass a).symm (dual_ofClass b).symm
  -- Extend from generator pairs, first in the right variable and then in the left.
  have dual_mul_left (a : ProjectiveClass R) (z : K0 R) :
      dualEquiv R (ofClassRingHom R a * z) =
        dualEquiv R (ofClassRingHom R a) * dualEquiv R z := by
    let f : K0 R →+ K0 Rᵐᵒᵖ :=
      { toFun := fun z => dualEquiv R (ofClassRingHom R a * z)
        map_zero' := by rw [mul_zero, map_zero]
        map_add' := by
          intro z w
          rw [mul_add, map_add] }
    let g : K0 R →+ K0 Rᵐᵒᵖ :=
      { toFun := fun z => dualEquiv R (ofClassRingHom R a) * dualEquiv R z
        map_zero' := by
          rw [map_zero]
          exact MulZeroClass.mul_zero
            (dualEquiv R (ofClassRingHom R a) : K0 Rᵐᵒᵖ)
        map_add' := by
          intro z w
          rw [map_add, mul_add] }
    have h : f = g := by
      apply hom_ext_ofClass (R := R)
      intro b
      change dualEquiv R (ofClassRingHom R a * ofClass R b) =
        dualEquiv R (ofClassRingHom R a) * dualEquiv R (ofClass R b)
      simpa only [ofClassRingHom_apply] using dual_mul_ofClass a b
    exact congrArg (fun h : K0 R →+ K0 Rᵐᵒᵖ => h z) h
  let f : K0 R →+ K0 Rᵐᵒᵖ :=
    { toFun := fun z => dualEquiv R (z * y)
      map_zero' := by rw [zero_mul, map_zero]
      map_add' := by
        intro z w
        rw [add_mul, map_add] }
  let g : K0 R →+ K0 Rᵐᵒᵖ :=
    { toFun := fun z => dualEquiv R z * dualEquiv R y
      map_zero' := by
        rw [map_zero]
        exact MulZeroClass.zero_mul (dualEquiv R y : K0 Rᵐᵒᵖ)
      map_add' := by
        intro z w
        rw [map_add, add_mul] }
  have h : f = g := by
    apply hom_ext_ofClass (R := R)
    intro a
    change dualEquiv R (ofClass R a * y) =
      dualEquiv R (ofClass R a) * dualEquiv R y
    simpa only [ofClassRingHom_apply] using dual_mul_left a y
  exact congrArg (fun h : K0 R →+ K0 Rᵐᵒᵖ => h x) h

/-- Opposite-ring duality as a ring equivalence of Grothendieck rings. -/
noncomputable def dualRingEquiv : K0 R ≃+* K0 Rᵐᵒᵖ :=
  { dualEquiv R with map_mul' := dualEquiv_mul R }

/-- The additive equivalence underlying multiplicative opposite-ring duality is the
original opposite-ring additive duality. -/
theorem dualRingEquiv_toAddEquiv :
    (dualRingEquiv R).toAddEquiv = dualEquiv R := rfl

end K0

/-- Over the integers, duality sends the class of the tensor product of the free
right modules of ranks two and three to the product of their dual classes. -/
example :
    K0.dualRingEquiv ℤ
        (K0.of ℤ ((Fin 2 → ℤᵐᵒᵖ) ⊗[ℤᵐᵒᵖ] (Fin 3 → ℤᵐᵒᵖ))) =
      K0.dualRingEquiv ℤ (K0.of ℤ (Fin 2 → ℤᵐᵒᵖ)) *
        K0.dualRingEquiv ℤ (K0.of ℤ (Fin 3 → ℤᵐᵒᵖ)) := by
  rw [← K0.of_mul ℤ (Fin 2 → ℤᵐᵒᵖ) (Fin 3 → ℤᵐᵒᵖ)]
  exact (K0.dualRingEquiv ℤ).map_mul
    (K0.of ℤ (Fin 2 → ℤᵐᵒᵖ)) (K0.of ℤ (Fin 3 → ℤᵐᵒᵖ))

end KTheory
