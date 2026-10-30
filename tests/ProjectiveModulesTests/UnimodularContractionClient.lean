/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.ExteriorAlgebra.ContractionExactness
import ProjectiveModules.ExteriorAlgebra.ContractionNaturality
import ProjectiveModules.ExteriorAlgebra.ContractionRightModule

/-!
A non-exterior integral example of contraction exactness, the cycle splitting, and its
naturality under a noninjective quadratic isometry.
-/

noncomputable section

namespace ProjectiveModulesTests.UnimodularContraction

private def μ : Module.Dual ℤ (ℤ × ℤ) := LinearMap.fst ℤ ℤ ℤ
private def Q : QuadraticForm ℤ (ℤ × ℤ) := QuadraticMap.linMulLin μ μ
private def m : ℤ × ℤ := (1, 0)

private def evaluate : CliffordAlgebra Q →ₐ[ℤ] ℤ :=
  CliffordAlgebra.lift Q ⟨μ, fun _ => rfl⟩

private theorem algebra_one_ne_zero : (1 : CliffordAlgebra Q) ≠ 0 := by
  intro h
  have hz : (1 : ℤ) = 0 := by
    simpa only [map_one, map_zero] using congrArg evaluate h
  exact one_ne_zero hz

private def unitCycle : LinearMap.ker (CliffordAlgebra.contractLeft (Q := Q) μ) :=
  ⟨1, by
    change CliffordAlgebra.contractLeft μ (1 : CliffordAlgebra Q) = 0
    simp only [CliffordAlgebra.contractLeft_one]⟩

private def e := CliffordAlgebra.contractLeftKerProdEquiv (Q := Q) μ m (by rfl)

-- Creation has square the identity, rather than square zero, in this example.
example :
    (LinearMap.mulLeft ℤ (CliffordAlgebra.ι Q m)).comp
      (LinearMap.mulLeft ℤ (CliffordAlgebra.ι Q m)) =
        (LinearMap.id : CliffordAlgebra Q →ₗ[ℤ] CliffordAlgebra Q) := by
  simpa only [show Q m = 1 from rfl, one_smul] using
    CliffordAlgebra.mulLeft_ι_comp_self (Q := Q) m

-- The same nonzero algebra has exact contraction and two genuine cycle coordinates.
example :
    (1 : CliffordAlgebra Q) ≠ 0 ∧
    LinearMap.range (CliffordAlgebra.contractLeft (Q := Q) μ) =
      LinearMap.ker (CliffordAlgebra.contractLeft (Q := Q) μ) ∧
    e (1 : CliffordAlgebra Q) = (unitCycle, 0) ∧
    e (CliffordAlgebra.ι Q m) = (0, unitCycle) ∧
    e.symm (unitCycle, unitCycle) = 1 + CliffordAlgebra.ι Q m := by
  refine ⟨algebra_one_ne_zero, ?_, ?_, ?_, ?_⟩
  · exact CliffordAlgebra.range_contractLeft_eq_ker_of_surjective (Q := Q) μ
      (fun r => ⟨(r, 0), rfl⟩)
  · exact CliffordAlgebra.contractLeftKerProdEquiv_apply_coe μ m (by rfl) unitCycle
  · simpa only [e, CliffordAlgebra.contractLeftKerLift_apply,
      show (unitCycle : CliffordAlgebra Q) = 1 from rfl, mul_one] using
      CliffordAlgebra.contractLeftKerProdEquiv_apply_kerLift (Q := Q) μ m (by rfl) unitCycle
  · simpa only [e, show (unitCycle : CliffordAlgebra Q) = 1 from rfl, mul_one] using
      CliffordAlgebra.contractLeftKerProdEquiv_symm_apply (Q := Q) μ m (by rfl)
        (unitCycle, unitCycle)

private def n : ℤ × ℤ := (0, 1)
private def ν : Module.Dual ℤ (ℤ × ℤ) := LinearMap.snd ℤ ℤ ℤ

private def b : CliffordAlgebra.contractLeftKerSubalgebra (Q := Q) μ :=
  ⟨CliffordAlgebra.ι Q n, by
    rw [CliffordAlgebra.mem_contractLeftKerSubalgebra]
    simp only [CliffordAlgebra.contractLeft_ι, show μ n = 0 from rfl, map_zero]⟩

private def eRight := CliffordAlgebra.contractLeftKerProdEquivRight (Q := Q) μ m (by rfl)

-- A non-base-scalar cycle acts on the right; reversing the product changes a coordinate.
example :
    CliffordAlgebra.contractLeft μ (b : CliffordAlgebra Q) = 0 ∧
    CliffordAlgebra.contractLeft ν (b : CliffordAlgebra Q) = 1 ∧
    (b : CliffordAlgebra Q) ≠ 0 ∧
    (∀ r : ℤ, (b : CliffordAlgebra Q) ≠ algebraMap ℤ (CliffordAlgebra Q) r) ∧
    eRight ((1 + CliffordAlgebra.ι Q m) * (b : CliffordAlgebra Q)) = (b, b) ∧
    eRight.symm (b, b) = (b : CliffordAlgebra Q) +
      CliffordAlgebra.ι Q m * (b : CliffordAlgebra Q) ∧
    eRight ((b : CliffordAlgebra Q) * (1 + CliffordAlgebra.ι Q m)) = (b, -b) ∧
    (b : CliffordAlgebra Q) ≠ -(b : CliffordAlgebra Q) := by
  have hν : CliffordAlgebra.contractLeft ν (b : CliffordAlgebra Q) = 1 := by
    simp only [b, CliffordAlgebra.contractLeft_ι, show ν n = 1 from rfl, map_one]
  have hscalar (r : ℤ) : CliffordAlgebra.contractLeft (Q := Q) ν
      (algebraMap ℤ (CliffordAlgebra Q) r) = 0 := by
    simp only [CliffordAlgebra.contractLeft_algebraMap]
  have hunit : eRight (1 + CliffordAlgebra.ι Q m) = (1, 1) := by
    have hsymm : eRight.symm (1, 1) = 1 + CliffordAlgebra.ι Q m := by
      simpa only [eRight, Subalgebra.coe_one, mul_one] using
        CliffordAlgebra.contractLeftKerProdEquivRight_symm_apply (Q := Q) μ m (by rfl)
          ((1, 1) : CliffordAlgebra.contractLeftKerSubalgebra (Q := Q) μ ×
            CliffordAlgebra.contractLeftKerSubalgebra (Q := Q) μ)
    have h := eRight.apply_symm_apply (1, 1)
    rw [hsymm] at h
    exact h
  refine ⟨(CliffordAlgebra.mem_contractLeftKerSubalgebra μ _).mp b.property,
    hν, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hz
    have h := congrArg (CliffordAlgebra.contractLeft (Q := Q) ν) hz
    rw [hν, map_zero] at h
    exact algebra_one_ne_zero h
  · intro r hr
    have h := congrArg (CliffordAlgebra.contractLeft (Q := Q) ν) hr
    rw [hν, hscalar] at h
    exact algebra_one_ne_zero h
  · have hone : MulOpposite.op b •
        (1 : CliffordAlgebra.contractLeftKerSubalgebra (Q := Q) μ) = b := by
      apply Subtype.ext
      simp only [CliffordAlgebra.contractLeftKerSubalgebra_coe_opposite_smul,
        MulOpposite.unop_op, Subalgebra.coe_one, one_mul]
    calc
      eRight ((1 + CliffordAlgebra.ι Q m) * (b : CliffordAlgebra Q)) =
          eRight (MulOpposite.op b • (1 + CliffordAlgebra.ι Q m)) := by
        rw [CliffordAlgebra.contractLeftKerSubalgebra_opposite_smul, MulOpposite.unop_op]
      _ = MulOpposite.op b • eRight (1 + CliffordAlgebra.ι Q m) :=
        eRight.map_smul _ _
      _ = (b, b) := by
        rw [hunit]
        exact Prod.ext hone hone
  · exact CliffordAlgebra.contractLeftKerProdEquivRight_symm_apply μ m (by rfl) (b, b)
  · have hanti : (b : CliffordAlgebra Q) * CliffordAlgebra.ι Q m =
        -(CliffordAlgebra.ι Q m * (b : CliffordAlgebra Q)) := by
      simpa only [b, show QuadraticMap.polar Q n m = 0 from rfl, map_zero, zero_sub] using
        CliffordAlgebra.ι_mul_ι_comm (Q := Q) n m
    have hrev : eRight.symm (b, -b) =
        (b : CliffordAlgebra Q) * (1 + CliffordAlgebra.ι Q m) := by
      calc
        eRight.symm (b, -b) = (b : CliffordAlgebra Q) +
            CliffordAlgebra.ι Q m * (↑(-b) : CliffordAlgebra Q) :=
          CliffordAlgebra.contractLeftKerProdEquivRight_symm_apply (Q := Q) μ m (by rfl)
            ((b, -b) : CliffordAlgebra.contractLeftKerSubalgebra (Q := Q) μ ×
              CliffordAlgebra.contractLeftKerSubalgebra (Q := Q) μ)
        _ = (b : CliffordAlgebra Q) * (1 + CliffordAlgebra.ι Q m) := by
          simp only [Subalgebra.coe_neg, mul_neg, mul_add, mul_one, hanti]
    rw [← hrev, LinearEquiv.apply_symm_apply]
  · intro h
    have hcontract : (1 : CliffordAlgebra Q) = -1 := by
      simpa only [hν, map_neg] using
        congrArg (CliffordAlgebra.contractLeft (Q := Q) ν) h
    have hz : (1 : ℤ) = -1 := by
      simpa only [map_one, map_neg] using congrArg evaluate hcontract
    exact (by decide : (1 : ℤ) ≠ -1) hz

private def sourceQ : QuadraticForm ℤ ((ℤ × ℤ) × ℤ) :=
  QuadraticMap.linMulLin (μ.comp (LinearMap.fst ℤ (ℤ × ℤ) ℤ))
    (μ.comp (LinearMap.fst ℤ (ℤ × ℤ) ℤ))

private def mSource : (ℤ × ℤ) × ℤ := (m, 0)

private def f : sourceQ →qᵢ Q :=
  { LinearMap.fst ℤ (ℤ × ℤ) ℤ with map_app' := fun _ => rfl }

private def evaluateSource : CliffordAlgebra sourceQ →ₐ[ℤ] ℤ :=
  CliffordAlgebra.lift sourceQ ⟨μ.comp f.toLinearMap, fun _ => rfl⟩

private def unitCycleSource :
    LinearMap.ker (CliffordAlgebra.contractLeft (Q := sourceQ) (μ.comp f.toLinearMap)) :=
  ⟨1, by
    change CliffordAlgebra.contractLeft (μ.comp f.toLinearMap)
      (1 : CliffordAlgebra sourceQ) = 0
    simp only [CliffordAlgebra.contractLeft_one]⟩

private def eSource := CliffordAlgebra.contractLeftKerProdEquiv (Q := sourceQ)
  (μ.comp f.toLinearMap) mSource (by rfl)

private def F := CliffordAlgebra.contractLeftKerMap f μ

-- The projection loses a direction, but preserves both nonzero splitting coordinates.
example :
    ¬ Function.Injective f ∧
    (1 : CliffordAlgebra sourceQ) ≠ 0 ∧
    (1 : CliffordAlgebra Q) ≠ 0 ∧
    sourceQ mSource = 1 ∧ Q (f mSource) = 1 ∧
    F unitCycleSource = unitCycle ∧
    e (CliffordAlgebra.map f (1 : CliffordAlgebra sourceQ)) = (unitCycle, 0) ∧
    e (CliffordAlgebra.map f (CliffordAlgebra.ι sourceQ mSource)) = (0, unitCycle) ∧
    e (CliffordAlgebra.map f (1 + CliffordAlgebra.ι sourceQ mSource)) =
      (unitCycle, unitCycle) := by
  have hF : F unitCycleSource = unitCycle := by
    apply Subtype.ext
    simp only [F, CliffordAlgebra.contractLeftKerMap_apply,
      show (unitCycleSource : CliffordAlgebra sourceQ) = 1 from rfl,
      show (unitCycle : CliffordAlgebra Q) = 1 from rfl, map_one]
  have hsquare (x : CliffordAlgebra sourceQ) :
      e (CliffordAlgebra.map f x) = (F.prodMap F) (eSource x) :=
    LinearMap.congr_fun
      (CliffordAlgebra.contractLeftKerProdEquiv_map f μ mSource (by rfl)) x
  refine ⟨?_, ?_, algebra_one_ne_zero, rfl, rfl, hF, ?_, ?_, ?_⟩
  · intro hf
    have h := hf (show f (((0, 0), 1) : (ℤ × ℤ) × ℤ) = f 0 from rfl)
    exact one_ne_zero (show (1 : ℤ) = 0 from congrArg Prod.snd h)
  · intro h
    have hz : (1 : ℤ) = 0 := by
      simpa only [map_one, map_zero] using congrArg evaluateSource h
    exact one_ne_zero hz
  · have hs : eSource (1 : CliffordAlgebra sourceQ) = (unitCycleSource, 0) :=
      CliffordAlgebra.contractLeftKerProdEquiv_apply_coe
        (μ.comp f.toLinearMap) mSource (by rfl) unitCycleSource
    simpa only [hs, LinearMap.prodMap_apply, hF, map_zero] using hsquare 1
  · have hs : eSource (CliffordAlgebra.ι sourceQ mSource) = (0, unitCycleSource) := by
      simpa only [eSource, CliffordAlgebra.contractLeftKerLift_apply,
        show (unitCycleSource : CliffordAlgebra sourceQ) = 1 from rfl, mul_one] using
        CliffordAlgebra.contractLeftKerProdEquiv_apply_kerLift (Q := sourceQ)
          (μ.comp f.toLinearMap) mSource (by rfl) unitCycleSource
    simpa only [hs, LinearMap.prodMap_apply, map_zero, hF] using
      hsquare (CliffordAlgebra.ι sourceQ mSource)
  · have hs : eSource.symm (unitCycleSource, unitCycleSource) =
        1 + CliffordAlgebra.ι sourceQ mSource := by
      simpa only [eSource, show (unitCycleSource : CliffordAlgebra sourceQ) = 1 from rfl,
        mul_one] using
        CliffordAlgebra.contractLeftKerProdEquiv_symm_apply (Q := sourceQ)
          (μ.comp f.toLinearMap) mSource (by rfl) (unitCycleSource, unitCycleSource)
    have h := LinearMap.congr_fun
      (CliffordAlgebra.map_conj_contractLeftKerProdEquiv f μ mSource (by rfl))
      (unitCycleSource, unitCycleSource)
    change e (CliffordAlgebra.map f (eSource.symm (unitCycleSource, unitCycleSource))) =
      (F.prodMap F) (unitCycleSource, unitCycleSource) at h
    simpa only [hs, LinearMap.prodMap_apply, hF] using h

end ProjectiveModulesTests.UnimodularContraction
