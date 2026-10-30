/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorAlgebra.ContractionSplitting
public import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Equiv.Opposite
import Mathlib.Algebra.Module.RingHom

/-!
# Left contraction as a right module over its cycles

The kernel of left contraction is a unital subalgebra of the original Clifford algebra.
Its opposite acts on that same algebra by restricted right multiplication, compatibly with
the original base-ring action. The twisted product rule makes contraction right-linear over
cycles, without requiring the cycle subalgebra to be commutative.

A vector pairing to one with the covector upgrades `contractLeftKerProdEquiv` to a linear
equivalence over the opposite cycle algebra. Its additive equivalence, both contraction
coordinates, and inverse are unchanged; restricting scalars recovers the original splitting.
The quadratic form is arbitrary: left multiplication by the vector still squares to its
quadratic value, not necessarily to zero.

## References

The constructions reuse Mathlib's Clifford contraction by Eric Wieser, its
submodule-to-subalgebra constructor, opposite regular module, restriction along a ring
homomorphism, scalar-tower criterion, and `AddEquiv.toLinearEquiv`. The splitting and its
coordinate equations are those of `ProjectiveModules.ExteriorAlgebra.ContractionSplitting`,
which uses Antoine Chambert-Loir's `Function.Exact.splitSurjectiveEquiv` from Mathlib.
-/

@[expose] public section

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace CliffordAlgebra

variable {Q : QuadraticForm R M}
variable (μ : Module.Dual R M)

/-- The original kernel of left contraction, regarded as a unital subalgebra. -/
def contractLeftKerSubalgebra : Subalgebra R (CliffordAlgebra Q) :=
  (LinearMap.ker (contractLeft (Q := Q) μ)).toSubalgebra
    (by
      apply LinearMap.mem_ker.mpr
      exact contractLeft_one Q μ)
    (fun x y hx hy => by
      apply LinearMap.mem_ker.mpr
      simp only [contractLeft_mul, LinearMap.mem_ker.mp hx, LinearMap.mem_ker.mp hy,
        zero_mul, mul_zero, add_zero])

/-- Membership in the cycle subalgebra is vanishing of the original contraction. -/
@[simp]
theorem mem_contractLeftKerSubalgebra (x : CliffordAlgebra Q) :
    x ∈ contractLeftKerSubalgebra μ ↔ contractLeft μ x = 0 :=
  Iff.rfl

/-- Forgetting multiplication recovers the original kernel submodule. -/
@[simp]
theorem contractLeftKerSubalgebra_toSubmodule :
    (contractLeftKerSubalgebra (Q := Q) μ).toSubmodule =
      LinearMap.ker (contractLeft (Q := Q) μ) :=
  Submodule.toSubalgebra_toSubmodule _ _ _

/-- Opposite cycle scalars act on the original Clifford algebra by restriction of its
right regular module along the opposite of the subalgebra inclusion. -/
instance contractLeftKerSubalgebraOppositeModule :
    Module (contractLeftKerSubalgebra (Q := Q) μ)ᵐᵒᵖ (CliffordAlgebra Q) :=
  Module.compHom (CliffordAlgebra Q) (contractLeftKerSubalgebra μ).val.toRingHom.op

/-- The restricted opposite action is ordinary right multiplication, not a transported
scalar action supplied by a splitting. -/
@[simp]
theorem contractLeftKerSubalgebra_opposite_smul
    (b : (contractLeftKerSubalgebra (Q := Q) μ)ᵐᵒᵖ) (x : CliffordAlgebra Q) :
    b • x = x * (b.unop : CliffordAlgebra Q) :=
  rfl

/-- The stock right regular action on cycles agrees with the ambient multiplication. -/
@[simp]
theorem contractLeftKerSubalgebra_coe_opposite_smul
    (b : (contractLeftKerSubalgebra (Q := Q) μ)ᵐᵒᵖ)
    (z : contractLeftKerSubalgebra (Q := Q) μ) :
    ((b • z : contractLeftKerSubalgebra μ) : CliffordAlgebra Q) =
      (z : CliffordAlgebra Q) * (b.unop : CliffordAlgebra Q) :=
  rfl

/-- Restricted right multiplication is compatible with the original base-ring action. -/
instance contractLeftKerSubalgebraScalarTower :
    IsScalarTower R (contractLeftKerSubalgebra (Q := Q) μ)ᵐᵒᵖ (CliffordAlgebra Q) :=
  IsScalarTower.of_algebraMap_smul fun r x => by
    rw [contractLeftKerSubalgebra_opposite_smul, MulOpposite.algebraMap_apply,
      MulOpposite.unop_op, Subalgebra.coe_algebraMap]
    exact (Algebra.commutes r x).symm.trans (Algebra.smul_def r x).symm

/-- A cycle, coerced to the original algebra, has zero left contraction. -/
@[simp]
theorem contractLeft_coe_contractLeftKerSubalgebra
    (b : contractLeftKerSubalgebra (Q := Q) μ) :
    contractLeft μ (b : CliffordAlgebra Q) = 0 :=
  (mem_contractLeftKerSubalgebra μ _).mp b.property

/-- Contraction commutes with right multiplication by a cycle. The left factor can be
inhomogeneous, and no commutativity of the cycle subalgebra is needed. -/
@[simp]
theorem contractLeft_mul_cycle (x : CliffordAlgebra Q)
    (b : contractLeftKerSubalgebra (Q := Q) μ) :
    contractLeft μ (x * (b : CliffordAlgebra Q)) =
      contractLeft μ x * (b : CliffordAlgebra Q) := by
  rw [contractLeft_mul, contractLeft_coe_contractLeftKerSubalgebra, mul_zero, add_zero]

variable (m : M)

/-- Unit pairing refines the original contraction splitting to a right-cycle linear
equivalence. This upgrades the same additive equivalence, retaining both its coordinates and
its inverse, for the restricted right-multiplication action. -/
def contractLeftKerProdEquivRight (hμm : μ m = 1) :
    CliffordAlgebra Q ≃ₗ[(contractLeftKerSubalgebra (Q := Q) μ)ᵐᵒᵖ]
      contractLeftKerSubalgebra (Q := Q) μ × contractLeftKerSubalgebra (Q := Q) μ := by
  let e : CliffordAlgebra Q ≃+
      contractLeftKerSubalgebra (Q := Q) μ × contractLeftKerSubalgebra (Q := Q) μ :=
    (contractLeftKerProdEquiv μ m hμm).toAddEquiv
  refine AddEquiv.toLinearEquiv
    (R := (contractLeftKerSubalgebra (Q := Q) μ)ᵐᵒᵖ)
    (M₂ := contractLeftKerSubalgebra (Q := Q) μ × contractLeftKerSubalgebra (Q := Q) μ)
    e ?_
  intro b x
  apply Prod.ext
  · apply Subtype.ext
    change ((e (b • x)).1 : CliffordAlgebra Q) =
      ((b • (e x).1 : contractLeftKerSubalgebra μ) : CliffordAlgebra Q)
    rw [contractLeftKerSubalgebra_coe_opposite_smul]
    change ((contractLeftKerProdEquiv μ m hμm (b • x)).1 : CliffordAlgebra Q) =
      ((contractLeftKerProdEquiv μ m hμm x).1 : CliffordAlgebra Q) *
        (b.unop : CliffordAlgebra Q)
    simp only [contractLeftKerSubalgebra_opposite_smul, contractLeftKerProdEquiv_apply_fst]
    rw [← mul_assoc, contractLeft_mul_cycle]
  · apply Subtype.ext
    change ((e (b • x)).2 : CliffordAlgebra Q) =
      ((b • (e x).2 : contractLeftKerSubalgebra μ) : CliffordAlgebra Q)
    rw [contractLeftKerSubalgebra_coe_opposite_smul]
    change ((contractLeftKerProdEquiv μ m hμm (b • x)).2 : CliffordAlgebra Q) =
      ((contractLeftKerProdEquiv μ m hμm x).2 : CliffordAlgebra Q) *
        (b.unop : CliffordAlgebra Q)
    simp only [contractLeftKerSubalgebra_opposite_smul, contractLeftKerProdEquiv_apply_snd]
    exact contractLeft_mul_cycle μ x b.unop

/-- The right-cycle refinement has exactly the original additive equivalence. -/
@[simp]
theorem contractLeftKerProdEquivRight_toAddEquiv (hμm : μ m = 1) :
    (contractLeftKerProdEquivRight (Q := Q) μ m hμm).toAddEquiv =
      (contractLeftKerProdEquiv μ m hμm).toAddEquiv :=
  rfl

/-- Restricting the right-cycle refinement to the original base ring recovers the original
linear splitting. -/
@[simp]
theorem contractLeftKerProdEquivRight_restrictScalars (hμm : μ m = 1) :
    (contractLeftKerProdEquivRight (Q := Q) μ m hμm).restrictScalars R =
      contractLeftKerProdEquiv μ m hμm := by
  apply LinearEquiv.ext
  intro x
  rfl

/-- The first coordinate remains contraction after left multiplication by the vector. -/
@[simp]
theorem contractLeftKerProdEquivRight_apply_fst (hμm : μ m = 1) (x : CliffordAlgebra Q) :
    ((contractLeftKerProdEquivRight μ m hμm x).1 : CliffordAlgebra Q) =
      contractLeft μ (ι Q m * x) :=
  contractLeftKerProdEquiv_apply_fst μ m hμm x

/-- The second coordinate remains the original left contraction. -/
@[simp]
theorem contractLeftKerProdEquivRight_apply_snd (hμm : μ m = 1) (x : CliffordAlgebra Q) :
    ((contractLeftKerProdEquivRight μ m hμm x).2 : CliffordAlgebra Q) =
      contractLeft μ x :=
  contractLeftKerProdEquiv_apply_snd μ m hμm x

/-- The inverse retains the original order: the first cycle plus the left multiple of the
second cycle. -/
@[simp]
theorem contractLeftKerProdEquivRight_symm_apply (hμm : μ m = 1)
    (p : contractLeftKerSubalgebra (Q := Q) μ × contractLeftKerSubalgebra (Q := Q) μ) :
    (contractLeftKerProdEquivRight μ m hμm).symm p =
      (p.1 : CliffordAlgebra Q) + ι Q m * (p.2 : CliffordAlgebra Q) :=
  contractLeftKerProdEquiv_symm_apply μ m hμm p

/-- A vector paired to one makes the Clifford algebra free as a right module over its cycle
subalgebra, without requiring finiteness or freeness of the original module. -/
theorem moduleFree_over_contractLeftKer (hμm : μ m = 1) :
    Module.Free (contractLeftKerSubalgebra (Q := Q) μ)ᵐᵒᵖ (CliffordAlgebra Q) := by
  let B := contractLeftKerSubalgebra (Q := Q) μ
  have : Module.Free Bᵐᵒᵖ B :=
    Module.Free.of_equiv (MulOpposite.opLinearEquiv (Bᵐᵒᵖ) (M := B)).symm
  exact Module.Free.of_equiv (contractLeftKerProdEquivRight (Q := Q) μ m hμm).symm

end CliffordAlgebra
