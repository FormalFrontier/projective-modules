/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Multilinear.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Logic.Equiv.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import ProjectiveModules.Module.SymmetricPower.Basic

/-!
# Bases and projectivity of finite symmetric powers

Finite labelings determine finitely supported natural-valued functions whose total mass
is the cardinality of the set of tensor factors. A supplied basis induces a monomial basis
of each finite symmetric power. The basis index and the semimodule need not be finite.

## References

- C. Weibel, *The K-book*, Chapter I (symmetric powers of projective modules).
- Mathlib's `Basis.piTensorProduct` and `Module.Projective.iff_split`.
-/

@[expose] public section

universe u v w

namespace SymmetricPower

variable {ι : Type u} {J : Type w}

/-- The multiplicities of the labels of a finite family, with their total mass. -/
noncomputable def multidegree [Finite ι] (a : ι → J) :
    {d : J →₀ ℕ // d.sum (fun _ k => k) = Nat.card ι} := by
  classical
  letI := Fintype.ofFinite ι
  refine ⟨(Finset.univ.val.map a).toFinsupp, ?_⟩
  change (Finset.univ.val.map a).toFinsupp.sum (fun _ => id) = Nat.card ι
  rw [Multiset.toFinsupp_sum_eq, Multiset.card_map]
  exact (Nat.card_eq_fintype_card (α := ι)).symm

/-- The multiplicity of a label is the cardinality of its fiber. -/
@[simp] theorem multidegree_apply [Finite ι] (a : ι → J) (j : J) :
    (multidegree a).1 j = Nat.card {i : ι // a i = j} := by
  classical
  let := Fintype.ofFinite ι
  simp only [multidegree, Multiset.toFinsupp_apply, Multiset.count_map,
    Nat.card_eq_fintype_card, Fintype.card_subtype, eq_comm,
    Finset.card_def, Finset.filter_val]

/-- A multidegree is the finitely supported count function of the labels. -/
theorem coe_multidegree [Fintype ι] [DecidableEq J] (a : ι → J) :
    (multidegree a).1 = (Finset.univ.val.map a).toFinsupp := by
  ext j
  rw [multidegree_apply]
  simp only [Multiset.toFinsupp_apply, Multiset.count_map,
    Nat.card_eq_fintype_card, Fintype.card_subtype, eq_comm,
    Finset.card_def, Finset.filter_val]

/-- Permuting the factors leaves a multidegree unchanged. -/
theorem multidegree_comp_perm [Finite ι] (a : ι → J) (σ : Equiv.Perm ι) :
    multidegree (a ∘ σ) = multidegree a := by
  classical
  let := Fintype.ofFinite ι
  apply Subtype.ext
  simp only [coe_multidegree, ← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- Two finite labelings have the same multiplicities exactly when they differ by a permutation. -/
theorem multidegree_eq_iff [Finite ι] (a b : ι → J) :
    multidegree a = multidegree b ↔ ∃ σ : Equiv.Perm ι, a = b ∘ σ := by
  constructor
  · intro h
    classical
    let := Fintype.ofFinite ι
    have hc (j : J) : Fintype.card {i : ι // a i = j} =
        Fintype.card {i : ι // b i = j} := by
      have hj := congrArg (fun d : J →₀ ℕ => d j) (congrArg Subtype.val h)
      simpa only [multidegree_apply, Nat.card_eq_fintype_card] using hj
    let e (j : J) : {i : ι // a i = j} ≃ {i : ι // b i = j} :=
      Fintype.equivOfCardEq (hc j)
    refine ⟨Equiv.ofFiberEquiv e, ?_⟩
    funext i
    exact (Equiv.ofFiberEquiv_map e i).symm
  · rintro ⟨σ, rfl⟩
    exact multidegree_comp_perm b σ

/-- Every finitely supported multiplicity function of the required total mass is realized. -/
theorem multidegree_surjective [Finite ι] :
    Function.Surjective (multidegree (ι := ι) (J := J)) := by
  classical
  let := Fintype.ofFinite ι
  intro d
  let s : Sym J (Nat.card ι) := (Sym.equivNatSum J (Nat.card ι)).symm d
  obtain ⟨l, hl⟩ := Quotient.exists_rep (s : Multiset J)
  let v : List.Vector J (Nat.card ι) :=
    ⟨l, (congrArg Multiset.card hl).trans s.2⟩
  let e : ι ≃ Fin (Nat.card ι) :=
    Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card (α := ι)).symm
  let a : ι → J := v.get ∘ e
  refine ⟨a, ?_⟩
  have ha : Finset.univ.val.map a = (s : Multiset J) := by
    change Finset.univ.val.map (v.get ∘ e) = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv, Fin.univ_val_map]
    rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]
    exact hl
  apply Subtype.ext
  rw [coe_multidegree, ha]
  exact congrArg Subtype.val ((Sym.equivNatSum J (Nat.card ι)).apply_symm_apply d)

end SymmetricPower

namespace Module.Basis

open scoped TensorProduct

variable {R ι : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M] {J : Type w}

/-- The monomial basis of a finite symmetric power, indexed by multiplicities of basis vectors. -/
noncomputable def symmetricPower [Finite ι] (b : Basis J R M) :
    Basis {d : J →₀ ℕ // d.sum (fun _ k => k) = Nat.card ι}
      R (SymmetricPower R ι M) := by
  classical
  let D := {d : J →₀ ℕ // d.sum (fun _ k => k) = Nat.card ι}
  let c : Basis (ι → J) R (⨂[R] (_ : ι), M) :=
    _root_.Basis.piTensorProduct (fun _ : ι => b)
  let L : (⨂[R] (_ : ι), M) →ₗ[R] D →₀ R :=
    (Finsupp.lmapDomain R R (SymmetricPower.multidegree (ι := ι) (J := J))).comp
      c.repr.toLinearMap
  have hL (a : ι → J) :
      L (PiTensorProduct.tprod R (fun i => b (a i))) =
        Finsupp.single (SymmetricPower.multidegree a) 1 := by
    rw [← _root_.Basis.piTensorProduct_apply (fun _ : ι => b) a]
    change (Finsupp.lmapDomain R R SymmetricPower.multidegree) (c.repr (c a)) = _
    simp only [Module.Basis.repr_self, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  let f := L.compMultilinearMap (PiTensorProduct.tprod R)
  have hf (e : Equiv.Perm ι) : MultilinearMap.domDomCongr e f = f := by
    apply Module.Basis.ext_multilinear (fun _ : ι => b)
    intro a
    change L (PiTensorProduct.tprod R (fun i => b (a (e i)))) =
      L (PiTensorProduct.tprod R (fun i => b (a i)))
    rw [hL (fun i => a (e i)), hL a]
    exact congrArg (fun d => Finsupp.single d (1 : R))
      (SymmetricPower.multidegree_comp_perm a e)
  let φ := SymmetricPower.lift f (fun e x => DFunLike.congr_fun (hf e) x)
  have hφ (a : ι → J) : φ (SymmetricPower.tprod R (fun i => b (a i))) =
      Finsupp.single (SymmetricPower.multidegree a) 1 := by
    exact (SymmetricPower.lift_tprod f
      (fun e x => DFunLike.congr_fun (hf e) x) (fun i => b (a i))).trans (hL a)
  let s : D → (ι → J) := fun d =>
    Classical.choose (SymmetricPower.multidegree_surjective (ι := ι) (J := J) d)
  have hs (d : D) : SymmetricPower.multidegree (s d) = d :=
    Classical.choose_spec (SymmetricPower.multidegree_surjective (ι := ι) (J := J) d)
  let ψ : (D →₀ R) →ₗ[R] SymmetricPower R ι M :=
    Finsupp.linearCombination R (fun d => SymmetricPower.tprod R (fun i => b (s d i)))
  have hl : ψ.comp φ = LinearMap.id := by
    apply SymmetricPower.hom_ext
    have h : (ψ.comp φ).compMultilinearMap (SymmetricPower.tprod R) =
        SymmetricPower.tprod R := by
      apply Module.Basis.ext_multilinear (fun _ : ι => b)
      intro a
      change ψ (φ (SymmetricPower.tprod R (fun i => b (a i)))) =
        SymmetricPower.tprod R (fun i => b (a i))
      rw [hφ]
      change Finsupp.linearCombination R
        (fun d => SymmetricPower.tprod R (fun i => b (s d i)))
        (Finsupp.single (SymmetricPower.multidegree a) 1) = _
      rw [Finsupp.linearCombination_single, one_smul]
      obtain ⟨e, he⟩ := (SymmetricPower.multidegree_eq_iff
        (s (SymmetricPower.multidegree a)) a).mp (hs (SymmetricPower.multidegree a))
      simpa only [he, Function.comp_apply] using
        (SymmetricPower.tprod_equiv e (fun i => b (a i)))
    intro x
    exact DFunLike.congr_fun h x
  have hr : φ.comp ψ = LinearMap.id := by
    apply (Finsupp.basisSingleOne : Basis D R (D →₀ R)).ext
    intro d
    change φ (ψ (Finsupp.single d 1)) = Finsupp.single d 1
    change φ (Finsupp.linearCombination R
      (fun d => SymmetricPower.tprod R (fun i => b (s d i))) (Finsupp.single d 1)) = _
    rw [Finsupp.linearCombination_single, one_smul, hφ, hs]
  exact Basis.ofRepr (LinearEquiv.ofLinearMap φ ψ (by assumption) (by assumption))

/-- Monomial coordinates are obtained by pushing tensor coordinates along multiplicities. -/
theorem symmetricPower_repr_tprod [Finite ι] (b : Basis J R M) (x : ι → M) :
    (b.symmetricPower (ι := ι)).repr (SymmetricPower.tprod R x) =
      Finsupp.lmapDomain R R (SymmetricPower.multidegree (ι := ι) (J := J))
        ((_root_.Basis.piTensorProduct (fun _ : ι => b)).repr
          (PiTensorProduct.tprod R x)) := by
  classical
  simp only [symmetricPower, LinearEquiv.coe_ofLinearMap]
  erw [SymmetricPower.lift_tprod]
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]

/-- The monomial indexed by a multiplicity vector is the corresponding symmetric pure tensor. -/
@[simp]
theorem symmetricPower_apply_multidegree [Finite ι] (b : Basis J R M) (a : ι → J) :
    b.symmetricPower (SymmetricPower.multidegree a) =
      SymmetricPower.tprod R (fun i => b (a i)) := by
  classical
  apply (b.symmetricPower (ι := ι)).repr.injective
  rw [Module.Basis.repr_self, symmetricPower_repr_tprod,
    ← _root_.Basis.piTensorProduct_apply (fun _ : ι => b) a]
  simp only [Module.Basis.repr_self, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

end Module.Basis

namespace SymmetricPower

variable {R ι : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Finite symmetric powers of free semimodules are free. -/
instance instModuleFree [Finite ι] [Module.Free R M] :
    Module.Free R (SymmetricPower R ι M) :=
  Module.Free.of_basis ((Module.Free.chooseBasis R M).symmetricPower (ι := ι))

/-- Finite symmetric powers of projective semimodules are projective.
This extends the symmetric-power closure property in Weibel, *The K-book*, Chapter I,
to commutative semirings and without a finite-generation hypothesis. -/
instance instModuleProjective [Finite ι] [Module.Projective R M] :
    Module.Projective R (SymmetricPower R ι M) := by
  obtain ⟨F, hF, mF, freeF, i, r, h⟩ :=
    (Module.Projective.iff_split (R := R) (P := M)).mp
      (inferInstance : Module.Projective R M)
  let : AddCommMonoid F := hF
  let : Module R F := mF
  have : Module.Free R F := freeF
  exact Module.Projective.of_split (map (ι := ι) i) (map (ι := ι) r)
    (map_comp_eq_id (ι := ι) h)

end SymmetricPower
