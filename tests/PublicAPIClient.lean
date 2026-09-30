/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism; see docs/CREDITS.md
module

import ProjectiveModules
import ProjectiveModules.Module.ComponentwiseFreeExamples
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Ordinary aggregate-import regression clients

The production API is consumed through `ProjectiveModules`, without `import all`.
The second import deliberately brings the eight existing internal example proofs
into the default test closure; it adds no production export. These private clients
check explicit conclusions and boundary hypotheses, not full release verification.
-/

set_option warningAsError true

namespace ProjectiveModulesPublicAPIClient

open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct DirectSum Matrix LaurentPolynomial

universe u v w x

section Commutative

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

-- Deliberately before any finite/projective/invertible instance variables.
private theorem rank_one_iff :
    Module.Invertible R M ↔ Module.Finite R M ∧ Module.Projective R M ∧
      Module.rankAtStalk (R := R) M = 1 :=
  Module.invertible_iff_finite_projective_rankAtStalk_eq_one

private theorem rank_one_forward (h : Module.Invertible R M) :
    Module.Finite R M ∧ Module.Projective R M ∧ Module.rankAtStalk (R := R) M = 1 :=
  rank_one_iff.mp h

private theorem rank_one_reverse
    (h : Module.Finite R M ∧ Module.Projective R M ∧ Module.rankAtStalk (R := R) M = 1) :
    Module.Invertible R M := rank_one_iff.mpr h

private theorem exterior_projective [Module.Projective R M] (n : ℕ) :
    Module.Projective R (⋀[R]^n M) := inferInstance

private theorem invertible_scalar [Module.Invertible R M] (f : Module.End R M) :
    ∃! r : R, ∀ m : M, f m = r • m :=
  Module.Invertible.existsUnique_eq_smul R M f

private theorem base_change {S : Type w} [CommRing S] [Algebra R S] :
    Nonempty (ExteriorAlgebra S (S ⊗[R] M) ≃ₐ[S] S ⊗[R] ExteriorAlgebra R M) :=
  ⟨ExteriorAlgebra.equivBaseChange⟩

private theorem base_change_generator {S : Type w} [CommRing S] [Algebra R S]
    (s : S) (m : M) :
    ExteriorAlgebra.toBaseChange (ExteriorAlgebra.ι S (s ⊗ₜ[R] m)) =
      s ⊗ₜ[R] ExteriorAlgebra.ι R m :=
  ExteriorAlgebra.toBaseChange_ι_tmul s m

private theorem direct_sum (N : Type w) [AddCommGroup N] [Module R N] (k : ℕ) :
    Nonempty ((⋀[R]^k (M × N)) ≃ₗ[R]
      ⨁ i : Fin (k + 1), (⋀[R]^i.1 M) ⊗[R] (⋀[R]^(k-i.1) N)) :=
  ⟨exteriorPower.prodEquivDirectSum R M N k⟩

private theorem direct_sum_naturality {N : Type w} [AddCommGroup N] [Module R N]
    (k : ℕ) (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    (exteriorPower.prodEquivDirectSum R M N k).toLinearMap.comp
        (exteriorPower.map k (f.prodMap g)) =
      (exteriorPower.prodDirectSumMap R M N k f g).comp
        (exteriorPower.prodEquivDirectSum R M N k).toLinearMap :=
  exteriorPower.prodEquivDirectSum_naturality R M N k f g

private theorem top_degree (n : ℕ) : Nonempty ((⋀[R]^n (Fin n → R)) ≃ₗ[R] R) :=
  ⟨exteriorPower.standardTopEquiv R n⟩

private theorem componentwise_finite (h : Module.ComponentwiseFree R M) :
    Module.Finite R M := h.finite

private theorem componentwise_projective (h : Module.ComponentwiseFree R M) :
    Module.Projective R M := h.projective

private theorem componentwise_classification {N : Type w} [AddCommGroup N] [Module R N]
    (hM : Module.ComponentwiseFree R M) (hN : Module.ComponentwiseFree R N)
    (h : Module.rankAtStalk (R := R) M = Module.rankAtStalk (R := R) N) :
    Nonempty (M ≃ₗ[R] N) :=
  hM.nonempty_linearEquiv_of_rankAtStalk_eq hN h

private theorem arbitrary_pid [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Projective R M] : Module.Free R M :=
  Module.Projective.free_of_pid R M

private theorem pid_submodule [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Free R M] (N : Submodule R M) : Module.Free R N :=
  N.free_of_pid_of_free

private theorem determinant_matrix (n : ℕ) (g : Matrix (Fin n) (Fin n) R) :
    exteriorPower.determinant R (Fin n → R) n (Matrix.toLin' g) = Matrix.det g :=
  exteriorPower.determinant_toLin' R n g

private theorem dual_change {S : Type w} [CommRing S] [Algebra R S]
    {N : Type x} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite R M] [Module.Projective R M]
    {j : M →ₗ[R] N} (ibc : IsBaseChange S j) : IsBaseChange S ibc.toDual :=
  ibc.dual_of_projective

private theorem evaluation_change {S : Type w} [CommRing S] [Algebra R S]
    {N : Type x} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite R M] [Module.Projective R M]
    {j : M →ₗ[R] N} (ibc : IsBaseChange S j) :
    IsBaseChange S (IsBaseChange.toContractBaseChangeOfProjective ibc) :=
  ibc.contract_of_projective

end Commutative

private theorem arbitrary_integer_finsupp_submodule
    (N : Submodule ℤ (ℕ →₀ ℤ)) : Module.CountablyGenerated ℤ N :=
  Module.CountablyGenerated.submodule_of_isNoetherianRing
    (Module.CountablyGenerated.finsupp (R := ℤ) ℕ) N

private theorem zero_integer_finsupp_submodule :
    Module.CountablyGenerated ℤ (⊥ : Submodule ℤ (ℕ →₀ ℤ)) :=
  arbitrary_integer_finsupp_submodule ⊥

private theorem characteristic_two_base_change :
    Nonempty (ExteriorAlgebra (ZMod 2) ((ZMod 2) ⊗[ℤ] ℤ) ≃ₐ[ZMod 2]
      (ZMod 2) ⊗[ℤ] ExteriorAlgebra ℤ ℤ) :=
  ⟨ExteriorAlgebra.equivBaseChange⟩

private theorem degree_zero :
    Nonempty ((⋀[ℤ]^0 (ℤ × ℤ)) ≃ₗ[ℤ]
      ⨁ i : Fin (0+1), (⋀[ℤ]^i.1 ℤ) ⊗[ℤ] (⋀[ℤ]^(0-i.1) ℤ)) :=
  direct_sum ℤ 0

private theorem degree_one :
    Nonempty ((⋀[ℤ]^1 (ℤ × ℤ)) ≃ₗ[ℤ]
      ⨁ i : Fin (1+1), (⋀[ℤ]^i.1 ℤ) ⊗[ℤ] (⋀[ℤ]^(1-i.1) ℤ)) :=
  direct_sum ℤ 1

private theorem zero_module_top :
    Nonempty ((⋀[ZMod 1]^0 (Fin 0 → ZMod 1)) ≃ₗ[ZMod 1] ZMod 1) :=
  top_degree 0

section ArbitraryRings

variable {R : Type u} [Ring R] {S : Type v} [Ring S]
variable {P : Type w} [AddCommGroup P] [Module R P]

private theorem cancellation (n : ℕ) (h : (P × (Fin n →₀ R)) ≃ₗ[R] (ℕ →₀ R)) :
    Nonempty (P ≃ₗ[R] (ℕ →₀ R)) :=
  ⟨Module.Free.natFinsuppEquivOfProdFinFinsuppEquiv R n h⟩

private theorem cancellation_functions (n : ℕ) (h : (P × (Fin n → R)) ≃ₗ[R] (ℕ →₀ R)) :
    Nonempty (P ≃ₗ[R] (ℕ →₀ R)) :=
  ⟨Module.Free.natFinsuppEquivOfProdFinEquiv R n h⟩

private theorem empty_cancellation (h : (P × (Fin 0 →₀ R)) ≃ₗ[R] (ℕ →₀ R)) :
    Nonempty (P ≃ₗ[R] (ℕ →₀ R)) := cancellation 0 h

private theorem countable_absorption {Q : Type x} [AddCommGroup Q] [Module R Q]
    (h : (ℕ →₀ R) ≃ₗ[R] P × Q) : Nonempty ((P × (ℕ →₀ R)) ≃ₗ[R] (ℕ →₀ R)) :=
  ⟨Module.Free.prodNatFinsuppEquivOfSplit R P Q h⟩

private theorem finite_semisimple [IsSemisimpleRing R]
    [Module.IsStablyFree R P] [Module.Finite R P] : Module.Free R P :=
  Module.free_of_finite_isStablyFree_of_isSemisimpleRing R P

private theorem finite_countable [Module.Finite R P] : Module.CountablyGenerated R P :=
  Module.CountablyGenerated.of_finite

private theorem explicit_complement [Module.Projective R P] (n : ℕ) :
    (∃ v : Fin n → P, Submodule.span R (Set.range v) = ⊤) ↔
      ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
        Nonempty ((P × Q) ≃ₗ[R] (Fin n → R)) :=
  Module.Projective.exists_fin_generating_family_iff_exists_prod_equiv n

variable {M : Type w} [AddCommGroup M] [Module Rᵐᵒᵖ M]

private theorem arbitrary_local [Module.Projective Rᵐᵒᵖ M]
    (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hu : ∀ r ∉ I, IsUnit r) :
    Module.Free Rᵐᵒᵖ M :=
  Module.Projective.free_of_isUnit_compl_arbitraryRank I hI hu

private theorem tensor_injective [Module.Projective Rᵐᵒᵖ M]
    {N : Type x} [AddCommGroup N] [Module R N]
    (i : P →ₗ[R] N) (hi : Function.Injective i) :
    Function.Injective (BalancedTensorProduct.mapRight (M := M) i) :=
  Module.Projective.balancedTensor_injective i hi

private theorem right_balance (f : R →+* S) (r : R) (m : M) (s : S) :
    ModuleCat.RightExtension.tmul f (MulOpposite.op r • m) s =
      ModuleCat.RightExtension.tmul f m (f r * s) :=
  ModuleCat.RightExtension.smul_tmul f r m s

private theorem right_map_surjective (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (ModuleCat.RightExtension.tmulOne f (M := M)) :=
  ModuleCat.RightExtension.tmulOne_surjective f hf

private theorem extension_projective (f : R →+* S) [Module.Projective Rᵐᵒᵖ M] :
    Module.Projective Sᵐᵒᵖ (ModuleCat.RightExtension.Obj f M) := inferInstance

private theorem extension_finite (f : R →+* S) [Module.Finite Rᵐᵒᵖ M] :
    Module.Finite Sᵐᵒᵖ (ModuleCat.RightExtension.Obj f M) := inferInstance

private theorem finite_right_coordinates (f : R →+* S) (n : ℕ) :
    Nonempty (ModuleCat.RightExtension.Obj f (Fin n → R) ≃ₗ[Sᵐᵒᵖ] (Fin n → S)) :=
  ⟨ModuleCat.RightExtension.rightFreeLinearEquiv f (Fin n)⟩

private theorem empty_right_coordinates (f : R →+* S) :
    Nonempty (ModuleCat.RightExtension.Obj f (Fin 0 → R) ≃ₗ[Sᵐᵒᵖ] (Fin 0 → S)) :=
  finite_right_coordinates f 0

private theorem right_matrix_order (n : ℕ) (f g : Module.End Rᵐᵒᵖ (Fin n → R)) :
    Module.rightEndomorphismMatrixEquiv R (Fin n) (f.comp g) =
      Module.rightEndomorphismMatrixEquiv R (Fin n) f *
        Module.rightEndomorphismMatrixEquiv R (Fin n) g :=
  Module.rightEndomorphismMatrixEquiv_comp R (Fin n) f g

private theorem right_matrix_columns (n : ℕ) (f : Module.End Rᵐᵒᵖ (Fin n → R))
    (a : Fin n → R) : Module.rightEndomorphismMatrixEquiv R (Fin n) f *ᵥ a = f a :=
  Module.rightEndomorphismMatrixEquiv_mulVec R (Fin n) f a

private theorem empty_right_matrix :
    Nonempty (Module.End Rᵐᵒᵖ (Fin 0 → R) ≃+* Matrix (Fin 0) (Fin 0) R) :=
  ⟨Module.rightEndomorphismMatrixEquiv R (Fin 0)⟩

private theorem quotient_right (I : Ideal R) [I.IsTwoSided] :
    Nonempty (ModuleCat.RightExtension.Obj (Ideal.Quotient.mk I) M ≃ₗ[(R ⧸ I)ᵐᵒᵖ]
      ModuleCat.RightExtension.IdealQuotient (M := M) I) :=
  ⟨ModuleCat.RightExtension.idealQuotientLinearEquiv I⟩

end ArbitraryRings

section SemiringHom

variable {R : Type u} [Semiring R]
variable {P : Type v} {L : Type w} {M : Type x}
variable [AddCommMonoid P] [AddCommMonoid L] [AddCommMonoid M]
variable [Module R P] [Module R L] [Module R M]

private theorem hom_injective (i : L →ₗ[R] M) (hi : Function.Injective i) :
    Function.Injective (LinearMap.postcomp (P := P) i) := LinearMap.postcomp_injective i hi

private theorem hom_surjective [Module.Projective R P] (f : L →ₗ[R] M)
    (hf : Function.Surjective f) : Function.Surjective (LinearMap.postcomp (P := P) f) :=
  Module.Projective.postcomp_surjective f hf

private theorem countable_closure {ι : Type v} (p : (ι →₀ R) →ₗ[R] (ι →₀ R))
    {s : Set ι} (hs : s.Countable) :
    ∃ t : Set ι, s ⊆ t ∧ t.Countable ∧
      Finsupp.supported R R t ≤ (Finsupp.supported R R t).comap p :=
  p.exists_countable_invariant_supported hs

private theorem transfinite_increment {ι : Type v} {p : (ι →₀ R) →ₗ[R] (ι →₀ R)}
    (F : LinearMap.CountableInvariantCoordinateFiltration p) (i : ι) :
    (F.through i \ F.before i).Countable := F.increment_countable i

end SemiringHom

section Categories

variable (R : Type u) [Ring R] (M N : ModuleCat.{v} R)

private theorem stable_zero : ModuleCat.FactorsThroughProjective R (0 : M ⟶ N) :=
  ModuleCat.FactorsThroughProjective.zero

private theorem ext_detection [Small.{v} R] (f : M ⟶ N) :
    ModuleCat.FactorsThroughProjective R f ↔
      ∀ (A : ModuleCat.{v} R), (Ext.mk₀ f).precomp A (zero_add 1) = 0 :=
  ModuleCat.FactorsThroughProjective.iff_ext_one_precomp_eq_zero f

private theorem finite_projective_object (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] :
    Nonempty (ModuleCat.FiniteProjective.{u,v} R) :=
  ⟨ModuleCat.FiniteProjective.of R P⟩

end Categories

private theorem laurent_right (F : Type u) [Field F] (P : Type v) [AddCommGroup P]
    [Module F[T;T⁻¹]ᵐᵒᵖ P] [Module.Finite F[T;T⁻¹]ᵐᵒᵖ P]
    [Module.Projective F[T;T⁻¹]ᵐᵒᵖ P] : Module.Free F[T;T⁻¹]ᵐᵒᵖ P :=
  LaurentPolynomial.op_module_free_of_finite_projective F P

end ProjectiveModulesPublicAPIClient
