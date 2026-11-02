/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Koszul.Basic
public import ProjectiveModules.Module.SymmetricPower.Basis
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Finsupp.Order

/-!
# Tensor bases for finite free Koszul terms

For the coordinate module `Fin m → S`, exterior subsets and natural exponent
functions index the tensor product of the exterior and symmetric bases.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct
universe u

namespace Module.Koszul.CanonicalFreeContraction

/-- The coordinate module with `m` coordinates. -/
abbrev Carrier (S : Type u) (m : ℕ) : Type u := Fin m → S

/-- Exterior basis labels: subsets of cardinality `i`. -/
abbrev ExteriorLabel (m i : ℕ) : Type := Set.powersetCard (Fin m) i

/-- Exponent labels for the degree-`d` symmetric-power basis. -/
abbrev SymmetricLabel (m d : ℕ) : Type :=
  {a : Fin m →₀ ℕ //
    a.sum (fun _ k => k) = Nat.card (SymmetricIndex.{u} d)}

/-- Labels for the tensor product of the exterior and symmetric bases. -/
abbrev Label (m i d : ℕ) : Type :=
  ExteriorLabel m i × SymmetricLabel.{u} m d

variable (S : Type u) [CommRing S]

/-- The tensor-product basis of the exterior and symmetric powers. -/
def termBasis (m i d : ℕ) :
    Module.Basis (Label.{u} m i d) S (Term S (Carrier S m) i d) :=
  ((Pi.basisFun S (Fin m)).exteriorPower i).tensorProduct
    ((Pi.basisFun S (Fin m)).symmetricPower (ι := SymmetricIndex.{u} d))

end Module.Koszul.CanonicalFreeContraction
