/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Symmetric

/-!
# Linear maps and functoriality of symmetric powers

The universal property of the permutation quotient holds for arbitrary index types.
No finiteness or projectivity hypothesis is needed.
-/

@[expose] public section

noncomputable section

universe u v w z

open scoped TensorProduct

namespace SymmetricPower

variable {R ι : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {P : Type z} [AddCommMonoid P] [Module R P]

/-- Every symmetric tensor has a representative in the tensor product. -/
theorem mk_surjective : Function.Surjective (mk R ι M) :=
  AddCon.mk'_surjective

/-- Passing a pure tensor to the quotient gives the symmetric pure tensor. -/
@[simp] theorem mk_tprod (x : ι → M) :
    mk R ι M (PiTensorProduct.tprod R x) = tprod R x := rfl

/-- Linear maps on symmetric powers are determined by their values on pure tensors. -/
@[ext] theorem hom_ext {f g : SymmetricPower R ι M →ₗ[R] N}
    (h : ∀ x, f (tprod R x) = g (tprod R x)) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := mk_surjective (R := R) (ι := ι) (M := M) x
  have h' : f.comp (mk R ι M) = g.comp (mk R ι M) := by
    apply PiTensorProduct.ext
    exact MultilinearMap.ext h
  exact DFunLike.congr_fun h' y

/-- A symmetric multilinear map descends uniquely to a linear map on the quotient. -/
def lift (f : MultilinearMap R (fun _ : ι => M) N)
    (h : ∀ (e : Equiv.Perm ι) x, f (fun i => x (e i)) = f x) :
    SymmetricPower R ι M →ₗ[R] N where
  __ := AddCon.lift (addConGen (Rel R ι M)) (PiTensorProduct.lift f).toAddMonoidHom
    (AddCon.addConGen_le.2 <| by
      intro x y hxy
      cases hxy with
      | perm e x =>
          change PiTensorProduct.lift f (PiTensorProduct.tprod R x) =
            PiTensorProduct.lift f (PiTensorProduct.tprod R (fun i => x (e i)))
          simpa only [PiTensorProduct.lift.tprod] using (h e x).symm)
  map_smul' r x := AddCon.induction_on x fun y => (PiTensorProduct.lift f).map_smul r y

/-- The descended map agrees with the tensor-product lift on representatives. -/
@[simp] theorem lift_mk
    (f : MultilinearMap R (fun _ : ι => M) N)
    (h : ∀ (e : Equiv.Perm ι) x, f (fun i => x (e i)) = f x)
    (x : ⨂[R] (_ : ι), M) :
    lift f h (mk R ι M x) = PiTensorProduct.lift f x := rfl

/-- Computation of the universal map on symmetric pure tensors. -/
@[simp] theorem lift_tprod
    (f : MultilinearMap R (fun _ : ι => M) N)
    (h : ∀ (e : Equiv.Perm ι) x, f (fun i => x (e i)) = f x) (x : ι → M) :
    lift f h (tprod R x) = f x := by
  rw [← mk_tprod, lift_mk, PiTensorProduct.lift.tprod]

/-- Uniqueness in the universal property of the symmetric power. -/
theorem lift_unique
    (f : MultilinearMap R (fun _ : ι => M) N)
    (h : ∀ (e : Equiv.Perm ι) x, f (fun i => x (e i)) = f x)
    (g : SymmetricPower R ι M →ₗ[R] N) (hg : ∀ x, g (tprod R x) = f x) :
    g = lift f h := by
  apply hom_ext
  intro x
  rw [lift_tprod]
  exact hg x

/-- The symmetric power represents permutation-invariant multilinear maps. -/
theorem existsUnique_lift (f : MultilinearMap R (fun _ : ι => M) N)
    (h : ∀ (e : Equiv.Perm ι) x, f (fun i => x (e i)) = f x) :
    ∃! g : SymmetricPower R ι M →ₗ[R] N, ∀ x, g (tprod R x) = f x :=
  ⟨lift f h, lift_tprod f h, fun g hg => lift_unique f h g hg⟩

/-- Descending a multilinear map commutes with linear postcomposition. -/
theorem comp_lift (g : N →ₗ[R] P) (f : MultilinearMap R (fun _ : ι => M) N)
    (h : ∀ (e : Equiv.Perm ι) x, f (fun i => x (e i)) = f x) :
    g.comp (lift f h) = lift (g.compMultilinearMap f)
      (fun e x => congrArg g (h e x)) := by
  apply hom_ext
  intro x
  exact (congrArg g (lift_tprod f h x)).trans
    (lift_tprod (g.compMultilinearMap f) (fun e x => congrArg g (h e x)) x).symm

/-- A linear map induces a linear map of symmetric powers. -/
def map (f : M →ₗ[R] N) : SymmetricPower R ι M →ₗ[R] SymmetricPower R ι N :=
  lift ((tprod R (ι := ι) (M := N)).compLinearMap (fun _ => f))
    (fun e x => tprod_equiv e (fun i => f (x i)))

/-- The induced map acts on each factor of a symmetric pure tensor. -/
@[simp] theorem map_tprod (f : M →ₗ[R] N) (x : ι → M) :
    map f (tprod R x) = tprod R (fun i => f (x i)) :=
  lift_tprod _ (fun e y => tprod_equiv e (fun i => f (y i))) x

/-- The identity map induces the identity on symmetric powers. -/
@[simp] theorem map_id : map (ι := ι) (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  apply hom_ext
  intro x
  simp only [map_tprod, LinearMap.id_apply]

/-- Symmetric powers preserve composition of linear maps. -/
theorem map_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    map (ι := ι) (g.comp f) = (map g).comp (map f) := by
  apply hom_ext
  intro x
  simp only [LinearMap.comp_apply, map_tprod]

/-- A split composition remains split after taking symmetric powers. -/
theorem map_comp_eq_id {f : M →ₗ[R] N} {g : N →ₗ[R] M}
    (h : g.comp f = LinearMap.id) :
    (map (ι := ι) g).comp (map f) = LinearMap.id := by
  rw [← map_comp, h, map_id]

/-- A surjective linear map induces a surjection of symmetric powers. -/
theorem map_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (map (ι := ι) f) := by
  classical
  apply LinearMap.range_eq_top.1
  apply le_antisymm le_top
  rw [← span_tprod_eq_top R ι N]
  apply Submodule.span_le.2
  rintro _ ⟨x, rfl⟩
  let y : ι → M := fun i => Classical.choose (hf (x i))
  refine ⟨tprod R y, ?_⟩
  rw [map_tprod]
  congr 1
  funext i
  exact Classical.choose_spec (hf (x i))

/-- The universal map is natural under linear maps of the tensor factors. -/
theorem lift_comp_map (f : M →ₗ[R] N)
    (g : MultilinearMap R (fun _ : ι => N) P)
    (h : ∀ (e : Equiv.Perm ι) x, g (fun i => x (e i)) = g x) :
    (lift g h).comp (map f) =
      lift (g.compLinearMap (fun _ => f))
        (fun e x => h e (fun i => f (x i))) := by
  apply hom_ext
  intro x
  exact (congrArg (lift g h) (map_tprod f x)).trans
    ((lift_tprod g h (fun i => f (x i))).trans
      (lift_tprod (g.compLinearMap (fun _ => f))
        (fun e x => h e (fun i => f (x i))) x).symm)

section Reindex

variable {κ τ : Type u}

/-- Reindexing tensor positions induces a linear equivalence of symmetric powers. -/
def reindex (e : ι ≃ κ) : SymmetricPower R ι M ≃ₗ[R] SymmetricPower R κ M := by
  let L {α β : Type u} (d : α ≃ β) :
      SymmetricPower R α M →ₗ[R] SymmetricPower R β M :=
    lift ((tprod R (ι := β) (M := M)).domDomCongr d.symm) (by
      intro σ x
      simpa only [MultilinearMap.domDomCongr_apply, Equiv.trans_apply,
        Equiv.symm_apply_apply] using
        tprod_equiv (R := R) (d.symm.trans (σ.trans d)) (fun k => x (d.symm k)))
  have hL {α β : Type u} (d : α ≃ β) (x : α → M) :
      L d (tprod R x) = tprod R (fun k => x (d.symm k)) := by
    exact lift_tprod _ _ x
  refine LinearEquiv.ofLinearMap (L e) (L e.symm) ?_ ?_
  · apply hom_ext
    intro x
    change L e (L e.symm (tprod R x)) = tprod R x
    rw [hL, hL]
    simp
  · apply hom_ext
    intro x
    change L e.symm (L e (tprod R x)) = tprod R x
    rw [hL, hL]
    simp

/-- Reindexing a pure tensor precomposes its factors by the inverse equivalence. -/
@[simp] theorem reindex_tprod (e : ι ≃ κ) (x : ι → M) :
    reindex (R := R) e (tprod R x) = tprod R (fun k => x (e.symm k)) := by
  simp only [reindex, LinearEquiv.coe_ofLinearMap, lift_tprod,
    MultilinearMap.domDomCongr_apply]

/-- Inverting a reindexing equivalence reverses the index equivalence. -/
@[simp] theorem reindex_symm (e : ι ≃ κ) :
    (reindex (R := R) (M := M) e).symm = reindex e.symm :=
  LinearEquiv.ext fun _ => rfl

/-- Reindexing by the identity equivalence is the identity. -/
@[simp] theorem reindex_refl :
    reindex (R := R) (M := M) (Equiv.refl ι) = LinearEquiv.refl R _ := by
  apply LinearEquiv.toLinearMap_injective
  apply hom_ext
  intro x
  simp

/-- Consecutive reindexings compose in the order of the index equivalences. -/
theorem reindex_trans (e : ι ≃ κ) (f : κ ≃ τ) :
    (reindex (R := R) (M := M) e).trans (reindex f) = reindex (e.trans f) := by
  apply LinearEquiv.toLinearMap_injective
  apply hom_ext
  intro x
  exact (congrArg (reindex (R := R) (M := M) f) (reindex_tprod e x)).trans
    ((reindex_tprod f (fun k => x (e.symm k))).trans
      (reindex_tprod (e.trans f) x).symm)

/-- Reindexing positions commutes with applying a linear map to the factors. -/
theorem reindex_map (e : ι ≃ κ) (f : M →ₗ[R] N) :
    (reindex (R := R) (M := N) e).toLinearMap.comp (map f) =
      (map (ι := κ) f).comp (reindex (R := R) (M := M) e).toLinearMap := by
  apply hom_ext
  intro x
  exact (congrArg (reindex (R := R) (M := N) e) (map_tprod f x)).trans
    ((reindex_tprod e (fun i => f (x i))).trans
      ((map_tprod (ι := κ) f (fun k => x (e.symm k))).symm.trans
        (congrArg (map (ι := κ) f) (reindex_tprod e x)).symm))

end Reindex

/-- Over a nonempty index type, a zero module has zero symmetric power. -/
instance instSubsingleton [Nonempty ι] [Subsingleton M] :
    Subsingleton (SymmetricPower R ι M) := by
  have h : (LinearMap.id : SymmetricPower R ι M →ₗ[R] SymmetricPower R ι M) = 0 := by
    apply hom_ext
    intro x
    have hx : tprod R x = 0 := by
      rw [Subsingleton.elim x (0 : ι → M)]
      exact (tprod R).map_zero
    simpa only [LinearMap.id_apply, LinearMap.zero_apply] using hx
  have hz (x : SymmetricPower R ι M) : x = 0 := by
    simpa only [LinearMap.id_apply, LinearMap.zero_apply] using DFunLike.congr_fun h x
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- With at most one tensor position, the permutation quotient preserves the tensor product. -/
def equivPiTensorProduct [Subsingleton ι] :
    SymmetricPower R ι M ≃ₗ[R] (⨂[R] (_ : ι), M) :=
  LinearEquiv.ofLinearMap
    (lift (PiTensorProduct.tprod R) (by
      intro e x
      exact congrArg (PiTensorProduct.tprod R)
        (funext fun i => congrArg x (Subsingleton.elim (e i) i))))
    (mk R ι M)
    (by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro x
      simp)
    (by
      apply hom_ext
      intro x
      simp)

/-- The comparison with the tensor product preserves pure tensors. -/
@[simp] theorem equivPiTensorProduct_tprod [Subsingleton ι] (x : ι → M) :
    equivPiTensorProduct (R := R) (tprod R x) = PiTensorProduct.tprod R x := by
  simp [equivPiTensorProduct]

/-- The inverse comparison is the quotient map. -/
@[simp] theorem equivPiTensorProduct_symm_apply [Subsingleton ι]
    (x : ⨂[R] (_ : ι), M) :
    (equivPiTensorProduct (R := R)).symm x = mk R ι M x := rfl

/-- The comparison inverts the quotient map. -/
@[simp] theorem equivPiTensorProduct_mk [Subsingleton ι] (x : ⨂[R] (_ : ι), M) :
    equivPiTensorProduct (mk R ι M x) = x := by
  simpa only [equivPiTensorProduct_symm_apply] using
    (equivPiTensorProduct (R := R) (ι := ι) (M := M)).apply_symm_apply x

/-- The symmetric power over an empty index type is the scalar module. -/
def isEmptyEquiv [IsEmpty ι] : SymmetricPower R ι M ≃ₗ[R] R :=
  equivPiTensorProduct.trans (PiTensorProduct.isEmptyEquiv ι)

/-- The empty pure tensor corresponds to the scalar one. -/
@[simp] theorem isEmptyEquiv_tprod [IsEmpty ι] (x : ι → M) :
    isEmptyEquiv (R := R) (tprod R x) = 1 := by
  simp [isEmptyEquiv]

/-- A scalar represents its multiple of the empty pure tensor. -/
@[simp] theorem isEmptyEquiv_symm_apply [IsEmpty ι] (r : R) :
    (isEmptyEquiv (R := R) (ι := ι) (M := M)).symm r =
      r • tprod R (fun i => isEmptyElim i) := by
  simp [isEmptyEquiv]

/-- The symmetric power over a singleton is the module at its sole position. -/
def subsingletonEquiv [Subsingleton ι] (i₀ : ι) : SymmetricPower R ι M ≃ₗ[R] M :=
  equivPiTensorProduct.trans (PiTensorProduct.subsingletonEquiv (s := fun _ : ι => M) i₀)

/-- A pure tensor at the sole position corresponds to that factor. -/
@[simp] theorem subsingletonEquiv_tprod [Subsingleton ι] (i₀ : ι) (x : ι → M) :
    subsingletonEquiv (R := R) i₀ (tprod R x) = x i₀ := by
  simp [subsingletonEquiv]

/-- The inverse singleton equivalence forms the corresponding pure tensor. -/
@[simp] theorem subsingletonEquiv_symm_apply [Subsingleton ι] (i₀ : ι) (x : M) :
    (subsingletonEquiv (R := R) i₀).symm x = tprod R (fun _ => x) := by
  simp [subsingletonEquiv]

end SymmetricPower
