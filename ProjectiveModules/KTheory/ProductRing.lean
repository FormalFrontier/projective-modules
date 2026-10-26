/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.Product
public import ProjectiveModules.KTheory.Ring

import ProjectiveModules.KTheory.RingScalarExtension

/-!
# Ring laws for the K₀ product comparison

The additive product comparison `KTheory.K0.piMap` preserves the tensor unit
and multiplication for arbitrary families of commutative rings. The index
and scalar universes are independent, and empty families and zero factors
are allowed. The underlying additive comparison is defined for arbitrary
unital rings.

Right modules are represented as left modules over the opposite ring. The
regular-module formula uses both scalar and carrier `Rᵐᵒᵖ`. The Bool-indexed
integer example realizes a corner module from free factor modules of ranks
one and zero: its class is a coordinate idempotent and an inverse image
under `KTheory.K0.piEquiv`, while the module is not free.

## References and credits

* Charles A. Weibel, *The K-book* (2013), provides general background on
  algebraic K₀ and tensor-product multiplication.
* Mathlib supplies the rings, modules, opposite rings and finite function modules.
* Projective Modules supplies the finite-projective coefficient products,
  the additive comparison `KTheory.K0.piMap` and finite-family equivalence
  `KTheory.K0.piEquiv`, right scalar extension and tensor-product K₀ formalizations.
* The tensor ring in `ProjectiveModules.KTheory.Ring` uses the group-completion
  ring infrastructure of `GroupTheory.MonoidLocalization.GrothendieckGroup.Ring`.
-/

@[expose] public section

universe uι uR

namespace KTheory.K0

/-- For any family of unital rings, the free rank-one right module uses the
regular opposite-ring carrier and action, and is sent to the corresponding
regular factor modules. The opposite-ring and scalar-extension constructions
are from Mathlib and Projective Modules. -/
theorem piMap_of_regular {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)] :
    piMap Ri (of (∀ i, Ri i) (∀ i, Ri i)ᵐᵒᵖ) =
      fun i ↦ of (Ri i) (Ri i)ᵐᵒᵖ := by
  funext i
  exact map_of_self (Pi.evalRingHom Ri i)

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, CommRing (Ri i)]

/-- The additive product comparison preserves the tensor unit,
without a finiteness or nontriviality hypothesis. The comparison and tensor
unit come from Projective Modules' scalar-extension and tensor-product K₀
formalizations. -/
@[simp]
theorem piMap_one : piMap Ri (1 : K0 (∀ i, Ri i)) = 1 := by
  funext i
  change map (Pi.evalRingHom Ri i) (1 : K0 (∀ i, Ri i)) = (1 : K0 (Ri i))
  simpa only [one_eq_of] using map_of_self (Pi.evalRingHom Ri i)

/-- The additive product comparison preserves tensor multiplication
for an arbitrary family of commutative rings. This formulation combines
Projective Modules' additive comparison and tensor-product K₀ formalization;
Weibel, *The K-book* (2013), gives general background on this multiplication. -/
theorem piMap_mul (x y : K0 (∀ i, Ri i)) :
    piMap Ri (x * y) = piMap Ri x * piMap Ri y := by
  funext i
  change map (Pi.evalRingHom Ri i) (x * y) =
    map (Pi.evalRingHom Ri i) x * map (Pi.evalRingHom Ri i) y
  let F : K0 (∀ i, Ri i) →+* K0 (Ri i) :=
    Algebra.GrothendieckAddGroup.liftRingHom
      ((ofClassRingHom (Ri i)).comp
        (ProjectiveClass.mapRingHom (Pi.evalRingHom Ri i)))
  have hF : F.toAddMonoidHom = map (Pi.evalRingHom Ri i) := by
    apply hom_ext_ofClass (∀ i, Ri i)
    intro a
    change F (ofClass (∀ i, Ri i) a) = _
    dsimp only [F]
    rw [Algebra.GrothendieckAddGroup.liftRingHom_apply]
    change lift (∀ i, Ri i) _ (ofClass (∀ i, Ri i) a) = _
    rw [lift_ofClass]
    change ((ofClassRingHom (Ri i)).comp
      (ProjectiveClass.mapRingHom (Pi.evalRingHom Ri i))) a = _
    rw [RingHom.comp_apply, ofClassRingHom_apply,
      ProjectiveClass.mapRingHom_apply, map_ofClass]
  have hmul : F.toAddMonoidHom (x * y) =
      F.toAddMonoidHom x * F.toAddMonoidHom y :=
    F.map_mul x y
  simpa only [hF] using hmul

end Pi

/-- A product-realized corner over `Bool → ℤ`: the factor at `false`
has rank one and the factor at `true` has rank zero. Its K₀ class is the
inverse image of the coordinate idempotent, and is idempotent, although the
module is not free. The module is formed by the finite-projective product
constructor. This formulation uses Mathlib's finite function modules and
Projective Modules' finite-projective coefficient products and additive
finite-product equivalence. -/
theorem bool_int_corner_realization :
    let P := ModuleCat.FiniteProjective.pi (fun _ : Bool ↦ ℤ)
      (fun b ↦ ModuleCat.FiniteProjective.of ℤᵐᵒᵖ
        (Fin (if b then 0 else 1) → ℤᵐᵒᵖ))
    let p := of (Bool → ℤ) P
    let e : Bool → K0 ℤ := fun b ↦ if b then 0 else 1
    piMap (fun _ : Bool ↦ ℤ) p = e ∧
      (piEquiv (fun _ : Bool ↦ ℤ)).symm e = p ∧
      p * p = p ∧
      ¬ Module.Free (Bool → ℤ)ᵐᵒᵖ P := by
  classical
  let Mi : Bool → ModuleCat.FiniteProjective ℤᵐᵒᵖ := fun b ↦
    ModuleCat.FiniteProjective.of ℤᵐᵒᵖ
      (Fin (if b then 0 else 1) → ℤᵐᵒᵖ)
  let P := ModuleCat.FiniteProjective.pi (fun _ : Bool ↦ ℤ) Mi
  let p := of (Bool → ℤ) P
  let e : Bool → K0 ℤ := fun b ↦ if b then 0 else 1
  change piMap (fun _ : Bool ↦ ℤ) p = e ∧
    (piEquiv (fun _ : Bool ↦ ℤ)).symm e = p ∧
    p * p = p ∧ ¬ Module.Free (Bool → ℤ)ᵐᵒᵖ P
  have hfactor : (fun b ↦ of ℤ (Mi b)) = e := by
    funext b
    cases b
    · change of ℤ (Fin 1 → ℤᵐᵒᵖ) = 1
      calc
        of ℤ (Fin 1 → ℤᵐᵒᵖ) = of ℤ ℤᵐᵒᵖ := by
          unfold of
          rw [ProjectiveClass.of_fin_fun_eq_nsmul, one_nsmul]
        _ = 1 := of_self ℤ
    · change of ℤ (Fin 0 → ℤᵐᵒᵖ) = 0
      exact of_zero ℤ _
  have hinv : (piEquiv (fun _ : Bool ↦ ℤ)).symm e = p := by
    rw [← hfactor]
    exact piEquiv_symm_of_module (fun _ : Bool ↦ ℤ) Mi
  have hforward : piMap (fun _ : Bool ↦ ℤ) p = e := by
    change piEquiv (fun _ : Bool ↦ ℤ) p = e
    rw [← hinv]
    exact (piEquiv (fun _ : Bool ↦ ℤ)).apply_symm_apply e
  refine ⟨hforward, hinv, ?_, ?_⟩
  · apply (piEquiv (fun _ : Bool ↦ ℤ)).injective
    change piMap (fun _ : Bool ↦ ℤ) (p * p) = piMap (fun _ : Bool ↦ ℤ) p
    rw [piMap_mul, hforward]
    funext b
    cases b <;> simp [e]
  · intro hfree
    have : Nontrivial P := by
      refine ⟨⟨ModuleCat.FiniteProjective.piMk (fun _ : Bool ↦ ℤ) Mi
        (fun _ _ ↦ 1), 0, ?_⟩⟩
      intro h
      have hi := congrArg (fun y : P ↦ y false (0 : Fin 1)) h
      change (1 : ℤᵐᵒᵖ) = 0 at hi
      exact one_ne_zero hi
    have : Module.Free (Bool → ℤ)ᵐᵒᵖ P := hfree
    have : FaithfulSMul (Bool → ℤ)ᵐᵒᵖ P := inferInstance
    have hzero :
        (MulOpposite.op (fun b : Bool ↦ if b then (1 : ℤ) else 0) :
          (Bool → ℤ)ᵐᵒᵖ) = 0 :=
      FaithfulSMul.eq_of_smul_eq_smul fun y : P ↦ by
        rw [zero_smul]
        apply (ModuleCat.FiniteProjective.pi_ext_iff
          (fun _ : Bool ↦ ℤ) Mi _ _).2
        intro b
        rw [ModuleCat.FiniteProjective.pi_smul_apply]
        cases b
        · change MulOpposite.op (0 : ℤ) • y false = 0
          simp only [MulOpposite.op_zero, zero_smul]
        · change (MulOpposite.op (1 : ℤ) • y true : Fin 0 → ℤᵐᵒᵖ) = 0
          exact @Subsingleton.elim (Fin 0 → ℤᵐᵒᵖ) inferInstance _ _
    have hi := congrArg (fun a : (Bool → ℤ)ᵐᵒᵖ ↦ a.unop true) hzero
    change (1 : ℤ) = 0 at hi
    exact one_ne_zero hi

end KTheory.K0
