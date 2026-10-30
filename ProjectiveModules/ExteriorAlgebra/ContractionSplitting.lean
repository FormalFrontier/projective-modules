/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorAlgebra.Contraction
public import Mathlib.Algebra.Exact.Basic

/-!
# Splitting left contraction into two copies of its kernel

For an arbitrary quadratic form, left multiplication by a vector gives a linear map from
cycles to the original Clifford algebra. If the covector pairs to one with that vector,
this map is a section of contraction onto cycles. The resulting linear equivalence has
coordinates contraction after left multiplication, and contraction; its inverse adds the
first cycle to the left multiple of the second.

The splitting is obtained from Mathlib's `Function.Exact.splitSurjectiveEquiv`, applied to
the kernel inclusion and contraction corestricted to its kernel. The contraction and its
square-zero theorem are Mathlib's constructions by Eric Wieser; the general splitting
producer is due to Antoine Chambert-Loir. The section identity uses the contraction–creation
identity from `ProjectiveModules.ExteriorAlgebra.Contraction`. No square-zero hypothesis on
left multiplication, restriction on the quadratic form, or invertibility of two is needed.
-/

@[expose] public section

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace CliffordAlgebra

variable {Q : QuadraticForm R M}
variable (μ : Module.Dual R M) (m : M)

/-- Left multiplication by a vector, restricted to the canonical kernel of contraction.
It is defined for every covector and vector; its section identity requires unit pairing. -/
def contractLeftKerLift :
    LinearMap.ker (contractLeft (Q := Q) μ) →ₗ[R] CliffordAlgebra Q :=
  (LinearMap.mulLeft R (ι Q m)).comp (LinearMap.ker (contractLeft (Q := Q) μ)).subtype

/-- The underlying function of the cycle lift is ordinary left multiplication. -/
theorem contractLeftKerLift_coe :
    (contractLeftKerLift (Q := Q) μ m :
      LinearMap.ker (contractLeft (Q := Q) μ) → CliffordAlgebra Q) =
      fun z : LinearMap.ker (contractLeft (Q := Q) μ) =>
        ι Q m * (z : CliffordAlgebra Q) :=
  rfl

/-- Evaluation of the cycle lift uses the original Clifford-algebra multiplication. -/
@[simp]
theorem contractLeftKerLift_apply (z : LinearMap.ker (contractLeft (Q := Q) μ)) :
    contractLeftKerLift μ m z = ι Q m * (z : CliffordAlgebra Q) :=
  rfl

/-- Unit pairing makes the cycle lift a section of contraction, with values viewed in the
original Clifford algebra. -/
theorem contractLeft_comp_contractLeftKerLift (hμm : μ m = 1) :
    (contractLeft (Q := Q) μ).comp (contractLeftKerLift μ m) =
      (LinearMap.ker (contractLeft (Q := Q) μ)).subtype := by
  apply LinearMap.ext
  intro z
  have h := LinearMap.congr_fun
    (contractLeft_comp_mulLeft_add_mulLeft_comp_of_eq_one (Q := Q) μ m hμm)
    (z : CliffordAlgebra Q)
  change contractLeft μ (ι Q m * (z : CliffordAlgebra Q)) +
    ι Q m * contractLeft μ (z : CliffordAlgebra Q) = (z : CliffordAlgebra Q) at h
  simpa only [LinearMap.comp_apply, contractLeftKerLift_apply, Submodule.subtype_apply,
    show contractLeft μ (z : CliffordAlgebra Q) = 0 from z.property,
    mul_zero, add_zero] using h

/-- Pointwise section identity for the cycle lift under unit pairing. -/
theorem contractLeft_contractLeftKerLift (hμm : μ m = 1)
    (z : LinearMap.ker (contractLeft (Q := Q) μ)) :
    contractLeft μ (contractLeftKerLift μ m z) = (z : CliffordAlgebra Q) :=
  LinearMap.congr_fun (contractLeft_comp_contractLeftKerLift μ m hμm) z

private def contractLeftToKer : CliffordAlgebra Q →ₗ[R]
    LinearMap.ker (contractLeft (Q := Q) μ) :=
  (contractLeft (Q := Q) μ).codRestrict
    (LinearMap.ker (contractLeft (Q := Q) μ)) (fun x => by
      change contractLeft μ (contractLeft μ x) = 0
      exact contractLeft_contractLeft μ x)

private theorem contractLeftToKer_exact :
    Function.Exact (LinearMap.ker (contractLeft (Q := Q) μ)).subtype
      (contractLeftToKer μ) := by
  apply LinearMap.exact_iff.mpr
  simp only [contractLeftToKer, LinearMap.ker_codRestrict, Submodule.range_subtype]

private theorem contractLeftToKer_comp_lift (hμm : μ m = 1) :
    (contractLeftToKer (Q := Q) μ).comp (contractLeftKerLift μ m) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact contractLeft_contractLeftKerLift μ m hμm z

/-- A vector pairing to one with the covector splits the original Clifford algebra into two
copies of the canonical kernel of contraction. The coordinates are `d (ι Q m * x)` and `d x`,
and the inverse sends `(z, w)` to `z + ι Q m * w`. -/
def contractLeftKerProdEquiv (hμm : μ m = 1) : CliffordAlgebra Q ≃ₗ[R]
    LinearMap.ker (contractLeft (Q := Q) μ) ×
      LinearMap.ker (contractLeft (Q := Q) μ) :=
  (Function.Exact.splitSurjectiveEquiv
    (f := (LinearMap.ker (contractLeft (Q := Q) μ)).subtype)
    (g := (contractLeft (Q := Q) μ).codRestrict
      (LinearMap.ker (contractLeft (Q := Q) μ)) (fun x => by
        change contractLeft μ (contractLeft μ x) = 0
        exact contractLeft_contractLeft μ x))
    (by exact contractLeftToKer_exact (Q := Q) μ)
    (LinearMap.ker (contractLeft (Q := Q) μ)).injective_subtype
    ⟨contractLeftKerLift μ m, by exact contractLeftToKer_comp_lift μ m hμm⟩).1

/-- The inverse of the stock splitting retains the first cycle and lifts the second. -/
@[simp]
theorem contractLeftKerProdEquiv_symm_apply (hμm : μ m = 1)
    (p : LinearMap.ker (contractLeft (Q := Q) μ) ×
      LinearMap.ker (contractLeft (Q := Q) μ)) :
    (contractLeftKerProdEquiv μ m hμm).symm p =
      (p.1 : CliffordAlgebra Q) + ι Q m * (p.2 : CliffordAlgebra Q) :=
  rfl

/-- The second coordinate of the splitting is the original contraction. -/
@[simp]
theorem contractLeftKerProdEquiv_apply_snd (hμm : μ m = 1) (x : CliffordAlgebra Q) :
    ((contractLeftKerProdEquiv μ m hμm x).2 : CliffordAlgebra Q) =
      contractLeft μ x := by
  have h := (Function.Exact.splitSurjectiveEquiv
    (contractLeftToKer_exact (Q := Q) μ)
    (LinearMap.ker (contractLeft (Q := Q) μ)).injective_subtype
    ⟨contractLeftKerLift μ m, contractLeftToKer_comp_lift μ m hμm⟩).2.2
  exact (congrArg
    (fun z : LinearMap.ker (contractLeft (Q := Q) μ) => (z : CliffordAlgebra Q))
    (LinearMap.congr_fun h x)).symm

/-- The first coordinate is contraction after left multiplication, not an unspecified
projection supplied by the splitting lemma. -/
@[simp]
theorem contractLeftKerProdEquiv_apply_fst (hμm : μ m = 1) (x : CliffordAlgebra Q) :
    ((contractLeftKerProdEquiv μ m hμm x).1 : CliffordAlgebra Q) =
      contractLeft μ (ι Q m * x) := by
  have hdecomp := (contractLeftKerProdEquiv μ m hμm).symm_apply_apply x
  rw [contractLeftKerProdEquiv_symm_apply, contractLeftKerProdEquiv_apply_snd] at hdecomp
  have hcartan := LinearMap.congr_fun
    (contractLeft_comp_mulLeft_add_mulLeft_comp_of_eq_one (Q := Q) μ m hμm) x
  change contractLeft μ (ι Q m * x) + ι Q m * contractLeft μ x = x at hcartan
  exact add_right_cancel (hdecomp.trans hcartan.symm)

/-- Both coordinates, with their canonical square-zero membership proofs. -/
theorem contractLeftKerProdEquiv_apply (hμm : μ m = 1) (x : CliffordAlgebra Q) :
    contractLeftKerProdEquiv μ m hμm x =
      (⟨contractLeft μ (ι Q m * x), contractLeft_contractLeft μ (ι Q m * x)⟩,
        ⟨contractLeft μ x, contractLeft_contractLeft μ x⟩) := by
  apply Prod.ext
  · apply Subtype.ext
    exact contractLeftKerProdEquiv_apply_fst μ m hμm x
  · apply Subtype.ext
    exact contractLeftKerProdEquiv_apply_snd μ m hμm x

/-- The kernel inclusion is the first summand of the stock splitting. -/
@[simp]
theorem contractLeftKerProdEquiv_apply_coe (hμm : μ m = 1)
    (z : LinearMap.ker (contractLeft (Q := Q) μ)) :
    contractLeftKerProdEquiv μ m hμm (z : CliffordAlgebra Q) = (z, 0) := by
  have h := (Function.Exact.splitSurjectiveEquiv
    (contractLeftToKer_exact (Q := Q) μ)
    (LinearMap.ker (contractLeft (Q := Q) μ)).injective_subtype
    ⟨contractLeftKerLift μ m, contractLeftToKer_comp_lift μ m hμm⟩).2.1
  have hz := LinearMap.congr_fun h z
  change (z : CliffordAlgebra Q) = (contractLeftKerProdEquiv μ m hμm).symm (z, 0) at hz
  rw [hz, LinearEquiv.apply_symm_apply]

/-- The cycle lift is the second summand; in particular its contraction coordinate is the
input cycle and its first coordinate vanishes. -/
theorem contractLeftKerProdEquiv_apply_kerLift (hμm : μ m = 1)
    (z : LinearMap.ker (contractLeft (Q := Q) μ)) :
    contractLeftKerProdEquiv μ m hμm (contractLeftKerLift μ m z) = (0, z) := by
  have h : (contractLeftKerProdEquiv μ m hμm).symm (0, z) =
      contractLeftKerLift μ m z := by
    rw [contractLeftKerProdEquiv_symm_apply]
    change (0 : CliffordAlgebra Q) + ι Q m * (z : CliffordAlgebra Q) =
      ι Q m * (z : CliffordAlgebra Q)
    exact zero_add _
  rw [← h, LinearEquiv.apply_symm_apply]

/-- Under unit pairing, equality is detected by the two canonical contraction coordinates. -/
theorem contractLeft_ext_of_eq_one (hμm : μ m = 1) {x y : CliffordAlgebra Q}
    (hfst : contractLeft μ (ι Q m * x) = contractLeft μ (ι Q m * y))
    (hsnd : contractLeft μ x = contractLeft μ y) : x = y := by
  apply (contractLeftKerProdEquiv μ m hμm).injective
  apply Prod.ext
  · apply Subtype.ext
    simpa only [contractLeftKerProdEquiv_apply_fst] using hfst
  · apply Subtype.ext
    simpa only [contractLeftKerProdEquiv_apply_snd] using hsnd

end CliffordAlgebra
