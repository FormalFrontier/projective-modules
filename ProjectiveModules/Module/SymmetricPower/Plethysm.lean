/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Data.Fintype.Option
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.LinearAlgebra.Multilinear.TensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
public import ProjectiveModules.Module.SymmetricPower.Basic
public import ProjectiveModules.Module.SymmetricPower.Basis
import ProjectiveModules.Module.SymmetricPower.Tensor

/-!
# Flattening iterated symmetric powers

For a finite outer label set and an arbitrary inner label set, flattening maps
an iterated symmetric power to the symmetric power indexed by the product.
Finite-degree plethysm uses universe-lifted finite labels and is characterized
by its coefficient-one formula on independently labelled grids.

For a projective semimodule, every finite-degree plethysm admits a linear section
by projectivity of its target. No canonical or natural section is chosen.
-/

@[expose] public section

universe uR uM uN

open scoped BigOperators TensorProduct

namespace SymmetricPower

variable {R I J : Type uR} [CommSemiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {N : Type uN} [AddCommMonoid N] [Module R N]

section Indexed

universe uT

private def rowIndexEquiv {A B : Type uR} (e : A ≃ B) :
    (A × J) ≃ (B × J) :=
  Equiv.prodCongr e (Equiv.refl J)

private def optionRowEquiv (A : Type uR) :
    (PUnit.{uR + 1} ⊕ A) ≃ Option A :=
  (Equiv.sumComm (PUnit.{uR + 1}) A).trans
    (Equiv.optionEquivSumPUnit.{uR, uR} A).symm

private def optionGridEquiv (A : Type uR) :
    (J ⊕ (A × J)) ≃ (Option A × J) :=
  optionProdEquiv.symm

private theorem exists_rowProduct [Finite I] :
    ∃ f : MultilinearMap R (fun _ : I => SymmetricPower R J M)
        (SymmetricPower R (I × J) M),
      ∀ x : I → J → M,
        f (fun i => SymmetricPower.tprod R (x i)) =
          SymmetricPower.tprod R (fun k : I × J => x k.1 k.2) := by
  classical
  refine Finite.induction_empty_option (P := fun A : Type uR =>
    ∃ f : MultilinearMap R (fun _ : A => SymmetricPower R J M)
        (SymmetricPower R (A × J) M),
      ∀ x : A → J → M,
        f (fun i => SymmetricPower.tprod R (x i)) =
          SymmetricPower.tprod R (fun k : A × J => x k.1 k.2)) ?_ ?_ ?_ I
  · intro A B e h
    rcases h with ⟨f, hf⟩
    refine ⟨(SymmetricPower.reindex (R := R) (M := M)
      (rowIndexEquiv (J := J) e)).toLinearMap.compMultilinearMap
        (MultilinearMap.domDomCongr e f), ?_⟩
    intro x
    change SymmetricPower.reindex (R := R) (M := M)
      (rowIndexEquiv (J := J) e)
        (f (fun a => SymmetricPower.tprod R (x (e a)))) = _
    rw [hf, SymmetricPower.reindex_tprod]
    apply congrArg (SymmetricPower.tprod R)
    funext k
    change x (e (e.symm k.1)) k.2 = x k.1 k.2
    rw [e.apply_symm_apply]
  · refine ⟨MultilinearMap.constOfIsEmpty R
      (fun _ : PEmpty.{uR + 1} => SymmetricPower R J M)
      (SymmetricPower.tprod R
        (fun k : PEmpty.{uR + 1} × J => PEmpty.elim k.1)), ?_⟩
    intro x
    change SymmetricPower.tprod R
      (fun k : PEmpty.{uR + 1} × J => PEmpty.elim k.1) = _
    apply congrArg (SymmetricPower.tprod R)
    funext k
    exact PEmpty.elim k.1
  · intro A _ h
    rcases h with ⟨f, hf⟩
    let oneRow : MultilinearMap R
        (fun _ : PUnit.{uR + 1} => SymmetricPower R J M)
        (SymmetricPower R J M) :=
      MultilinearMap.ofSubsingleton R (SymmetricPower R J M)
        (SymmetricPower R J M) PUnit.unit (LinearMap.id : _ →ₗ[R] _)
    let productRows : MultilinearMap R
        (fun _ : PUnit.{uR + 1} ⊕ A => SymmetricPower R J M)
        (SymmetricPower R J M ⊗[R] SymmetricPower R (A × J) M) :=
      oneRow.domCoprod f
    let joined : MultilinearMap R
        (fun _ : Option A => SymmetricPower R J M)
        (SymmetricPower R J M ⊗[R] SymmetricPower R (A × J) M) :=
      MultilinearMap.domDomCongr (optionRowEquiv A) productRows
    refine ⟨((SymmetricPower.reindex (R := R) (M := M)
      (optionGridEquiv (J := J) A)).toLinearMap.comp
        (SymmetricPower.concat (R := R) (I := J) (J := A × J) (P := M))).compMultilinearMap
      joined, ?_⟩
    intro x
    change SymmetricPower.reindex (R := R) (M := M)
      (optionGridEquiv (J := J) A)
        (SymmetricPower.concat
          (SymmetricPower.tprod R (x none) ⊗ₜ[R]
            f (fun i => SymmetricPower.tprod R (x (some i))))) = _
    rw [hf, SymmetricPower.concat_tprod, SymmetricPower.reindex_tprod]
    apply congrArg (SymmetricPower.tprod R)
    funext k
    rcases k with ⟨i, j⟩
    cases i <;> rfl

private noncomputable def rowProduct [Finite I] :
    MultilinearMap R (fun _ : I => SymmetricPower R J M)
      (SymmetricPower R (I × J) M) :=
  Classical.choose (exists_rowProduct (R := R) (I := I) (J := J) (M := M))

private theorem rowProduct_tprod [Finite I] (x : I → J → M) :
    rowProduct (R := R) (I := I) (J := J) (M := M)
        (fun i => SymmetricPower.tprod R (x i)) =
      SymmetricPower.tprod R (fun k : I × J => x k.1 k.2) :=
  Classical.choose_spec
    (exists_rowProduct (R := R) (I := I) (J := J) (M := M)) x

private theorem multilinearMap_ext_tprod
    {T : Type uT} [AddCommMonoid T] [Module R T] [Finite I]
    {f g : MultilinearMap R (fun _ : I => SymmetricPower R J M) T}
    (h : ∀ x : I → J → M,
      f (fun i => SymmetricPower.tprod R (x i)) =
        g (fun i => SymmetricPower.tprod R (x i))) : f = g := by
  exact MultilinearMap.ext_of_span_eq_top
    (g := fun {_i : I} (x : J → M) => SymmetricPower.tprod R x)
    (fun _ => SymmetricPower.span_tprod_eq_top R J M) h

private theorem linearMap_ext_tprod_tprod
    {T : Type uT} [AddCommMonoid T] [Module R T] [Finite I]
    {f g : SymmetricPower R I (SymmetricPower R J M) →ₗ[R] T}
    (h : ∀ x : I → J → M,
      f (SymmetricPower.tprod R (fun i => SymmetricPower.tprod R (x i))) =
        g (SymmetricPower.tprod R (fun i => SymmetricPower.tprod R (x i)))) :
    f = g := by
  apply SymmetricPower.hom_ext
  have hm :
      f.compMultilinearMap (SymmetricPower.tprod R) =
        g.compMultilinearMap (SymmetricPower.tprod R) := by
    apply multilinearMap_ext_tprod
    intro x
    simpa only [LinearMap.compMultilinearMap_apply] using h x
  intro a
  simpa only [LinearMap.compMultilinearMap_apply] using
    congrArg
      (fun F : MultilinearMap R (fun _ : I => SymmetricPower R J M) T => F a) hm

private theorem rowProduct_perm [Finite I] (e : Equiv.Perm I)
    (a : I → SymmetricPower R J M) :
    rowProduct (R := R) (I := I) (J := J) (M := M) (fun i => a (e i)) =
      rowProduct (R := R) (I := I) (J := J) (M := M) a := by
  have h : MultilinearMap.domDomCongr e
      (rowProduct (R := R) (I := I) (J := J) (M := M)) =
        rowProduct (R := R) (I := I) (J := J) (M := M) := by
    apply multilinearMap_ext_tprod
    intro x
    change rowProduct (R := R) (I := I) (J := J) (M := M)
      (fun i => SymmetricPower.tprod R (x (e i))) = _
    rw [rowProduct_tprod, rowProduct_tprod]
    exact SymmetricPower.tprod_equiv (rowIndexEquiv (J := J) e)
      (fun k : I × J => x k.1 k.2)
  exact congrArg (fun f : MultilinearMap R
    (fun _ : I => SymmetricPower R J M) (SymmetricPower R (I × J) M) => f a) h

/-- Flatten finitely many outer symmetric factors with arbitrary inner labels. -/
@[no_expose] noncomputable def flatten [Finite I] :
    SymmetricPower R I (SymmetricPower R J M) →ₗ[R]
      SymmetricPower R (I × J) M :=
  SymmetricPower.lift
    (rowProduct (R := R) (I := I) (J := J) (M := M))
    (rowProduct_perm (R := R) (I := I) (J := J) (M := M))

/-- The flattening formula for every independently labelled grid. -/
theorem flatten_tprod [Finite I] (x : I → J → M) :
    flatten (R := R) (I := I) (J := J) (M := M)
        (SymmetricPower.tprod R (fun i => SymmetricPower.tprod R (x i))) =
      SymmetricPower.tprod R (fun k : I × J => x k.1 k.2) := by
  rw [flatten, SymmetricPower.lift_tprod, rowProduct_tprod]

/-- The full grid formula uniquely determines the R-linear map. -/
theorem flatten_unique [Finite I]
    (f : SymmetricPower R I (SymmetricPower R J M) →ₗ[R]
      SymmetricPower R (I × J) M)
    (hf : ∀ x : I → J → M,
      f (SymmetricPower.tprod R (fun i => SymmetricPower.tprod R (x i))) =
        SymmetricPower.tprod R (fun k : I × J => x k.1 k.2)) :
    f = flatten (R := R) (I := I) (J := J) (M := M) := by
  apply linearMap_ext_tprod_tprod
  intro x
  rw [hf x, flatten_tprod]

/-- Every target element has a preimage, including empty-label cases. -/
theorem flatten_surjective [Finite I] :
    Function.Surjective (flatten (R := R) (I := I) (J := J) (M := M)) := by
  have hspan :
      Submodule.span R
          (Set.range (SymmetricPower.tprod R (ι := I × J) (M := M))) ≤
        LinearMap.range (flatten (R := R) (I := I) (J := J) (M := M)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    apply LinearMap.mem_range.mpr
    refine ⟨SymmetricPower.tprod R
      (fun i => SymmetricPower.tprod R (fun j => x (i, j))), ?_⟩
    exact flatten_tprod (fun i j => x (i, j))
  rw [SymmetricPower.span_tprod_eq_top] at hspan
  intro z
  exact LinearMap.mem_range.mp (hspan (by trivial))

/-- Flattening commutes with linear maps. -/
theorem flatten_natural [Finite I] (f : M →ₗ[R] N) :
    (SymmetricPower.map (ι := I × J) f).comp
        (flatten (R := R) (I := I) (J := J) (M := M)) =
      (flatten (R := R) (I := I) (J := J) (M := N)).comp
        (SymmetricPower.map (ι := I)
          (SymmetricPower.map (ι := J) f)) := by
  apply linearMap_ext_tprod_tprod
  intro x
  simp only [LinearMap.comp_apply, SymmetricPower.map_tprod, flatten_tprod]

end Indexed

section FiniteDegree

private def finiteLabelEquiv (p q : ℕ) :
    (ULift.{uR} (Fin p) × ULift.{uR} (Fin q)) ≃
      ULift.{uR} (Fin (p * q)) :=
  ((Equiv.prodCongr (Equiv.ulift : ULift.{uR} (Fin p) ≃ Fin p)
      (Equiv.ulift : ULift.{uR} (Fin q) ≃ Fin q)).trans finProdFinEquiv).trans
    (Equiv.ulift : ULift.{uR} (Fin (p * q)) ≃ Fin (p * q)).symm

private theorem reindex_toLinearMap_eq (e e' : I ≃ J) :
    (SymmetricPower.reindex (R := R) (M := M) e).toLinearMap =
      (SymmetricPower.reindex (R := R) (M := M) e').toLinearMap := by
  apply SymmetricPower.hom_ext
  intro x
  change SymmetricPower.reindex e (SymmetricPower.tprod R x) =
    SymmetricPower.reindex e' (SymmetricPower.tprod R x)
  rw [SymmetricPower.reindex_tprod, SymmetricPower.reindex_tprod]
  have h := SymmetricPower.tprod_equiv (R := R) (e'.symm.trans e)
    (fun j => x (e.symm j))
  simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using h.symm

/-- Canonical finite-degree plethysm, specialized from finite outer flattening. -/
@[no_expose] noncomputable def plethysm (p q : ℕ) :
    SymmetricPower R (ULift.{uR} (Fin p))
        (SymmetricPower R (ULift.{uR} (Fin q)) M) →ₗ[R]
      SymmetricPower R (ULift.{uR} (Fin (p * q))) M :=
  (SymmetricPower.reindex (R := R) (M := M) (finiteLabelEquiv p q)).toLinearMap.comp
    (flatten (R := R) (I := ULift.{uR} (Fin p))
      (J := ULift.{uR} (Fin q)) (M := M))

/-- Any block-label bijection gives the same coefficient-one grid formula. -/
theorem plethysm_tprod (p q : ℕ)
    (x : ULift.{uR} (Fin p) → ULift.{uR} (Fin q) → M)
    (e : (ULift.{uR} (Fin p) × ULift.{uR} (Fin q)) ≃
      ULift.{uR} (Fin (p * q))) :
    plethysm (R := R) (M := M) p q
        (SymmetricPower.tprod R (fun i => SymmetricPower.tprod R (x i))) =
      SymmetricPower.tprod R
        (fun k => x (e.symm k).1 (e.symm k).2) := by
  change SymmetricPower.reindex (finiteLabelEquiv p q)
    (flatten (R := R) (I := ULift.{uR} (Fin p)) (J := ULift.{uR} (Fin q))
      (SymmetricPower.tprod R (fun i => SymmetricPower.tprod R (x i)))) = _
  rw [flatten_tprod]
  change (SymmetricPower.reindex (R := R) (M := M)
    (finiteLabelEquiv p q)).toLinearMap _ = _
  rw [reindex_toLinearMap_eq (R := R) (M := M) (finiteLabelEquiv p q) e]
  exact SymmetricPower.reindex_tprod e _

/-- The all-grid, all-bijection formula uniquely determines finite plethysm. -/
theorem plethysm_unique (p q : ℕ)
    (f : SymmetricPower R (ULift.{uR} (Fin p))
        (SymmetricPower R (ULift.{uR} (Fin q)) M) →ₗ[R]
      SymmetricPower R (ULift.{uR} (Fin (p * q))) M)
    (hf : ∀ (x : ULift.{uR} (Fin p) → ULift.{uR} (Fin q) → M)
      (e : (ULift.{uR} (Fin p) × ULift.{uR} (Fin q)) ≃
        ULift.{uR} (Fin (p * q))),
      f (SymmetricPower.tprod R (fun i => SymmetricPower.tprod R (x i))) =
        SymmetricPower.tprod R
          (fun k => x (e.symm k).1 (e.symm k).2)) :
    f = plethysm (R := R) (M := M) p q := by
  let c := finiteLabelEquiv.{uR} p q
  let E := SymmetricPower.reindex (R := R) (M := M) c
  have h : E.symm.toLinearMap.comp f =
      flatten (R := R) (I := ULift.{uR} (Fin p))
        (J := ULift.{uR} (Fin q)) (M := M) := by
    apply flatten_unique
    intro x
    change E.symm (f (SymmetricPower.tprod R
      (fun i => SymmetricPower.tprod R (x i)))) =
        SymmetricPower.tprod R (fun k => x k.1 k.2)
    rw [hf x c, ← SymmetricPower.reindex_tprod c
      (fun k : ULift.{uR} (Fin p) × ULift.{uR} (Fin q) => x k.1 k.2)]
    exact E.symm_apply_apply _
  apply LinearMap.ext
  intro z
  change f z = E (flatten (R := R) (I := ULift.{uR} (Fin p))
    (J := ULift.{uR} (Fin q)) (M := M) z)
  have hz := congrArg
    (fun g : SymmetricPower R (ULift.{uR} (Fin p))
        (SymmetricPower R (ULift.{uR} (Fin q)) M) →ₗ[R]
          SymmetricPower R (ULift.{uR} (Fin p) × ULift.{uR} (Fin q)) M => g z) h
  change E.symm (f z) = _ at hz
  rw [← hz]
  exact (E.apply_symm_apply (f z)).symm

/-- Surjectivity for all finite degrees, including zero. -/
theorem plethysm_surjective (p q : ℕ) :
    Function.Surjective (plethysm (R := R) (M := M) p q) := by
  intro y
  let E := SymmetricPower.reindex (R := R) (M := M) (finiteLabelEquiv p q)
  obtain ⟨z, hz⟩ := flatten_surjective (R := R) (I := ULift.{uR} (Fin p))
    (J := ULift.{uR} (Fin q)) (M := M) (E.symm y)
  refine ⟨z, ?_⟩
  change E (flatten (R := R) (I := ULift.{uR} (Fin p))
    (J := ULift.{uR} (Fin q)) (M := M) z) = y
  rw [hz]
  exact E.apply_symm_apply y

/-- Plethysm commutes with linear maps. -/
theorem plethysm_natural (p q : ℕ) (f : M →ₗ[R] N) :
    (SymmetricPower.map (ι := ULift.{uR} (Fin (p * q))) f).comp
        (plethysm (R := R) (M := M) p q) =
      (plethysm (R := R) (M := N) p q).comp
        (SymmetricPower.map (ι := ULift.{uR} (Fin p))
          (SymmetricPower.map (ι := ULift.{uR} (Fin q)) f)) := by
  let c := finiteLabelEquiv.{uR} p q
  apply LinearMap.ext
  intro z
  change SymmetricPower.map f
      (SymmetricPower.reindex c
        (flatten (R := R) (I := ULift.{uR} (Fin p))
          (J := ULift.{uR} (Fin q)) (M := M) z)) =
    SymmetricPower.reindex c
      (flatten (R := R) (I := ULift.{uR} (Fin p))
        (J := ULift.{uR} (Fin q)) (M := N)
        (SymmetricPower.map (ι := ULift.{uR} (Fin p))
          (SymmetricPower.map (ι := ULift.{uR} (Fin q)) f) z))
  have hr := congrArg
    (fun g : SymmetricPower R (ULift.{uR} (Fin p) × ULift.{uR} (Fin q)) M →ₗ[R]
        SymmetricPower R (ULift.{uR} (Fin (p * q))) N =>
      g (flatten (R := R) (I := ULift.{uR} (Fin p))
        (J := ULift.{uR} (Fin q)) (M := M) z))
    (SymmetricPower.reindex_map (R := R) c f)
  have hn := congrArg
    (fun g : SymmetricPower R (ULift.{uR} (Fin p))
        (SymmetricPower R (ULift.{uR} (Fin q)) M) →ₗ[R]
          SymmetricPower R (ULift.{uR} (Fin p) × ULift.{uR} (Fin q)) N => g z)
    (flatten_natural (R := R) (I := ULift.{uR} (Fin p))
      (J := ULift.{uR} (Fin q)) f)
  exact hr.symm.trans (congrArg (SymmetricPower.reindex (R := R) (M := N) c) hn)

private theorem tprod_subsingleton_coordinate [Subsingleton I] (i₀ : I)
    (z : SymmetricPower R I M) :
    SymmetricPower.tprod R
        (fun _ : I => SymmetricPower.subsingletonEquiv (R := R) i₀ z) = z := by
  apply (SymmetricPower.subsingletonEquiv (R := R) (M := M) i₀).injective
  exact SymmetricPower.subsingletonEquiv_tprod (R := R) i₀ _

private theorem eq_empty_coordinate_smul [IsEmpty I] (x : I → M)
    (z : SymmetricPower R I M) :
    z = (SymmetricPower.isEmptyEquiv (R := R) (ι := I) (M := M)) z •
      SymmetricPower.tprod R x := by
  apply (SymmetricPower.isEmptyEquiv (R := R) (ι := I) (M := M)).injective
  rw [LinearEquiv.map_smul, SymmetricPower.isEmptyEquiv_tprod]
  change (SymmetricPower.isEmptyEquiv (R := R) (ι := I) (M := M)) z =
    (SymmetricPower.isEmptyEquiv (R := R) (ι := I) (M := M)) z * 1
  exact (mul_one _).symm

/-- Outer degree one is the canonical singleton identification. -/
theorem plethysm_one_left (q : ℕ)
    (e : ULift.{uR} (Fin (1 * q)) ≃ ULift.{uR} (Fin q))
    (z : SymmetricPower R (ULift.{uR} (Fin 1))
      (SymmetricPower R (ULift.{uR} (Fin q)) M)) :
    (SymmetricPower.reindex (R := R) (M := M) e)
        (plethysm (R := R) (M := M) 1 q z) =
      (SymmetricPower.subsingletonEquiv (R := R)
        (ι := ULift.{uR} (Fin 1))
        (M := SymmetricPower R (ULift.{uR} (Fin q)) M)
        (ULift.up (0 : Fin 1))) z := by
  let s := SymmetricPower.subsingletonEquiv (R := R)
    (ι := ULift.{uR} (Fin 1))
    (M := SymmetricPower R (ULift.{uR} (Fin q)) M) (ULift.up (0 : Fin 1))
  let b : (ULift.{uR} (Fin 1) × ULift.{uR} (Fin q)) ≃
      ULift.{uR} (Fin (1 * q)) :=
    (Equiv.uniqueProd (ULift.{uR} (Fin q)) (ULift.{uR} (Fin 1))).trans e.symm
  have h :
      ((SymmetricPower.reindex (R := R) (M := M) e).toLinearMap.comp
        (plethysm (R := R) (M := M) 1 q)).comp s.symm.toLinearMap =
      LinearMap.id := by
    apply SymmetricPower.hom_ext
    intro x
    change (SymmetricPower.reindex (R := R) (M := M) e)
        (plethysm (R := R) (M := M) 1 q (s.symm (SymmetricPower.tprod R x))) =
      SymmetricPower.tprod R x
    rw [show s.symm (SymmetricPower.tprod R x) =
        SymmetricPower.tprod R
          (fun _ : ULift.{uR} (Fin 1) => SymmetricPower.tprod R x) from
      SymmetricPower.subsingletonEquiv_symm_apply (R := R)
        (ULift.up (0 : Fin 1)) (SymmetricPower.tprod R x)]
    rw [plethysm_tprod (R := R) (M := M) 1 q (fun _ => x) b,
      SymmetricPower.reindex_tprod]
    apply congrArg (SymmetricPower.tprod R)
    funext k
    simp only [b, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply, Equiv.uniqueProd_symm_apply]
  have hz := congrArg
    (fun f : SymmetricPower R (ULift.{uR} (Fin q)) M →ₗ[R]
      SymmetricPower R (ULift.{uR} (Fin q)) M => f (s z)) h
  change (SymmetricPower.reindex (R := R) (M := M) e)
      (plethysm (R := R) (M := M) 1 q (s.symm (s z))) = s z at hz
  simpa only [LinearEquiv.symm_apply_apply] using hz

/-- Inner degree one is the symmetric map of the singleton identification. -/
theorem plethysm_one_right (p : ℕ)
    (e : ULift.{uR} (Fin (p * 1)) ≃ ULift.{uR} (Fin p))
    (z : SymmetricPower R (ULift.{uR} (Fin p))
      (SymmetricPower R (ULift.{uR} (Fin 1)) M)) :
    (SymmetricPower.reindex (R := R) (M := M) e)
        (plethysm (R := R) (M := M) p 1 z) =
      (SymmetricPower.map (ι := ULift.{uR} (Fin p))
        (SymmetricPower.subsingletonEquiv (R := R)
          (ι := ULift.{uR} (Fin 1)) (M := M)
          (ULift.up (0 : Fin 1))).toLinearMap) z := by
  let s := SymmetricPower.subsingletonEquiv (R := R)
    (ι := ULift.{uR} (Fin 1)) (M := M) (ULift.up (0 : Fin 1))
  let b : (ULift.{uR} (Fin p) × ULift.{uR} (Fin 1)) ≃
      ULift.{uR} (Fin (p * 1)) :=
    (Equiv.prodUnique (ULift.{uR} (Fin p)) (ULift.{uR} (Fin 1))).trans e.symm
  have h :
      (SymmetricPower.reindex (R := R) (M := M) e).toLinearMap.comp
          (plethysm (R := R) (M := M) p 1) =
        SymmetricPower.map (ι := ULift.{uR} (Fin p)) s.toLinearMap := by
    apply SymmetricPower.hom_ext
    intro a
    have ha : SymmetricPower.tprod R a =
        SymmetricPower.tprod R (fun i => SymmetricPower.tprod R
          (fun _ : ULift.{uR} (Fin 1) => s (a i))) := by
      apply congrArg (SymmetricPower.tprod R)
      funext i
      exact (tprod_subsingleton_coordinate (R := R)
        (ULift.up (0 : Fin 1)) (a i)).symm
    change (SymmetricPower.reindex (R := R) (M := M) e)
        (plethysm (R := R) (M := M) p 1 (SymmetricPower.tprod R a)) =
      SymmetricPower.map s.toLinearMap (SymmetricPower.tprod R a)
    calc
      _ = (SymmetricPower.reindex (R := R) (M := M) e)
          (plethysm (R := R) (M := M) p 1
            (SymmetricPower.tprod R (fun i => SymmetricPower.tprod R
              (fun _ : ULift.{uR} (Fin 1) => s (a i))))) :=
        congrArg (fun w => (SymmetricPower.reindex (R := R) (M := M) e)
          (plethysm (R := R) (M := M) p 1 w)) ha
      _ = SymmetricPower.tprod R (fun i => s (a i)) := by
        rw [plethysm_tprod (R := R) (M := M) p 1 (fun i _ => s (a i)) b,
          SymmetricPower.reindex_tprod]
        apply congrArg (SymmetricPower.tprod R)
        funext k
        simp only [b, Equiv.symm_trans_apply, Equiv.symm_symm,
          Equiv.apply_symm_apply, Equiv.prodUnique_symm_apply]
      _ = SymmetricPower.map s.toLinearMap (SymmetricPower.tprod R a) :=
        (SymmetricPower.map_tprod s.toLinearMap a).symm
  exact congrArg
    (fun f : SymmetricPower R (ULift.{uR} (Fin p))
      (SymmetricPower R (ULift.{uR} (Fin 1)) M) →ₗ[R]
      SymmetricPower R (ULift.{uR} (Fin p)) M => f z) h

/-- The degree-zero outer comparison square commutes on every source element. -/
theorem plethysm_zero_left (q : ℕ)
    (e : ULift.{uR} (Fin (0 * q)) ≃ ULift.{uR} (Fin 0))
    (z : SymmetricPower R (ULift.{uR} (Fin 0))
      (SymmetricPower R (ULift.{uR} (Fin q)) M)) :
    (SymmetricPower.isEmptyEquiv (R := R)
        (ι := ULift.{uR} (Fin 0)) (M := M))
      ((SymmetricPower.reindex (R := R) (M := M) e)
        (plethysm (R := R) (M := M) 0 q z)) =
      (SymmetricPower.isEmptyEquiv (R := R)
        (ι := ULift.{uR} (Fin 0))
        (M := SymmetricPower R (ULift.{uR} (Fin q)) M)) z := by
  let b : (ULift.{uR} (Fin 0) × ULift.{uR} (Fin q)) ≃
      ULift.{uR} (Fin (0 * q)) :=
    (Equiv.equivOfIsEmpty (ULift.{uR} (Fin 0) × ULift.{uR} (Fin q))
      (ULift.{uR} (Fin 0))).trans e.symm
  have h :
      (SymmetricPower.isEmptyEquiv (R := R)
        (ι := ULift.{uR} (Fin 0)) (M := M)).toLinearMap.comp
          ((SymmetricPower.reindex (R := R) (M := M) e).toLinearMap.comp
            (plethysm (R := R) (M := M) 0 q)) =
        (SymmetricPower.isEmptyEquiv (R := R)
          (ι := ULift.{uR} (Fin 0))
          (M := SymmetricPower R (ULift.{uR} (Fin q)) M)).toLinearMap := by
    apply SymmetricPower.hom_ext
    intro a
    let x : ULift.{uR} (Fin 0) → ULift.{uR} (Fin q) → M :=
      fun i => isEmptyElim i
    have ha : a = fun i => SymmetricPower.tprod R (x i) := by
      funext i
      exact isEmptyElim i
    change (SymmetricPower.isEmptyEquiv (R := R)
        (ι := ULift.{uR} (Fin 0)) (M := M))
        ((SymmetricPower.reindex (R := R) (M := M) e)
          (plethysm (R := R) (M := M) 0 q (SymmetricPower.tprod R a))) =
      (SymmetricPower.isEmptyEquiv (R := R)
        (ι := ULift.{uR} (Fin 0))
        (M := SymmetricPower R (ULift.{uR} (Fin q)) M))
        (SymmetricPower.tprod R a)
    rw [SymmetricPower.isEmptyEquiv_tprod, ha,
      plethysm_tprod (R := R) (M := M) 0 q x b,
      SymmetricPower.reindex_tprod, SymmetricPower.isEmptyEquiv_tprod]
  exact congrArg
    (fun f : SymmetricPower R (ULift.{uR} (Fin 0))
      (SymmetricPower R (ULift.{uR} (Fin q)) M) →ₗ[R] R => f z) h

/-- Inner degree zero multiplies the empty-unit coordinates of all outer entries. -/
theorem plethysm_zero_right (p : ℕ)
    (e : ULift.{uR} (Fin (p * 0)) ≃ ULift.{uR} (Fin 0))
    (a : ULift.{uR} (Fin p) →
      SymmetricPower R (ULift.{uR} (Fin 0)) M) :
    (SymmetricPower.isEmptyEquiv (R := R)
        (ι := ULift.{uR} (Fin 0)) (M := M))
      ((SymmetricPower.reindex (R := R) (M := M) e)
        (plethysm (R := R) (M := M) p 0 (SymmetricPower.tprod R a))) =
      ∏ i : ULift.{uR} (Fin p),
        (SymmetricPower.isEmptyEquiv (R := R)
          (ι := ULift.{uR} (Fin 0)) (M := M)) (a i) := by
  let c := SymmetricPower.isEmptyEquiv (R := R)
    (ι := ULift.{uR} (Fin 0)) (M := M)
  let v : ULift.{uR} (Fin 0) → M := fun j => isEmptyElim j
  let b : (ULift.{uR} (Fin p) × ULift.{uR} (Fin 0)) ≃
      ULift.{uR} (Fin (p * 0)) :=
    (Equiv.equivOfIsEmpty (ULift.{uR} (Fin p) × ULift.{uR} (Fin 0))
      (ULift.{uR} (Fin 0))).trans e.symm
  let F : SymmetricPower R (ULift.{uR} (Fin p))
      (SymmetricPower R (ULift.{uR} (Fin 0)) M) →ₗ[R] R :=
    c.toLinearMap.comp
      ((SymmetricPower.reindex (R := R) (M := M) e).toLinearMap.comp
        (plethysm (R := R) (M := M) p 0))
  have ha : a = fun i => c (a i) • SymmetricPower.tprod R v := by
    funext i
    exact eq_empty_coordinate_smul (R := R) v (a i)
  have hunit : F (SymmetricPower.tprod R
      (fun _ : ULift.{uR} (Fin p) => SymmetricPower.tprod R v)) = 1 := by
    change (SymmetricPower.isEmptyEquiv (R := R)
        (ι := ULift.{uR} (Fin 0)) (M := M))
        ((SymmetricPower.reindex (R := R) (M := M) e)
          (plethysm (R := R) (M := M) p 0 (SymmetricPower.tprod R
            (fun _ : ULift.{uR} (Fin p) => SymmetricPower.tprod R v)))) = 1
    rw [plethysm_tprod (R := R) (M := M) p 0 (fun _ => v) b,
      SymmetricPower.reindex_tprod, SymmetricPower.isEmptyEquiv_tprod]
  change F (SymmetricPower.tprod R a) = ∏ i : ULift.{uR} (Fin p), c (a i)
  calc
    _ = F (SymmetricPower.tprod R (fun i => c (a i) • SymmetricPower.tprod R v)) :=
      congrArg (fun w => F (SymmetricPower.tprod R w)) ha
    _ = (∏ i : ULift.{uR} (Fin p), c (a i)) •
        F (SymmetricPower.tprod R
          (fun _ : ULift.{uR} (Fin p) => SymmetricPower.tprod R v)) := by
      rw [MultilinearMap.map_smul_univ, F.map_smul]
    _ = ∏ i : ULift.{uR} (Fin p), c (a i) := by
      rw [hunit]
      change (∏ i : ULift.{uR} (Fin p), c (a i)) * 1 =
        ∏ i : ULift.{uR} (Fin p), c (a i)
      exact mul_one _

end FiniteDegree

/-- Plethysm on a projective semimodule admits a linear section in every pair of degrees.
This provides existence without choosing a canonical or natural section. -/
theorem plethysm_exists_section [Module.Projective R M] (p q : ℕ) :
    ∃ s : SymmetricPower R (ULift.{uR} (Fin (p * q))) M →ₗ[R]
        SymmetricPower R (ULift.{uR} (Fin p))
          (SymmetricPower R (ULift.{uR} (Fin q)) M),
      (plethysm (R := R) (M := M) p q).comp s = LinearMap.id := by
  exact Module.projective_lifting_property
    (plethysm (R := R) (M := M) p q) LinearMap.id
    (plethysm_surjective (R := R) (M := M) p q)


end SymmetricPower
