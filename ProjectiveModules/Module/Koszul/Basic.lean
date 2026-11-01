/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.SymmetricPower.Tensor
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Data.Fin.SuccPred

/-!
# Bigraded Koszul differentials

The bigraded Koszul differential removes one exterior input with its position sign
and inserts that input into the symmetric factor. Its scalar ring and module have
independent universes, and its definition applies to every module over a commutative
ring. Symmetric insertion is defined more generally over a commutative semiring.

The alternating operation is Mathlib's `AlternatingMap.alternatizeUncurryFin`;
exterior descent uses `exteriorPower.alternatingMapLinearEquiv`. Symmetric insertion
uses the pointed-singleton equivalence, `SymmetricPower.concat`, and reindexing.

## Implementation notes

The lifted finite index only matches the symmetric-power API's scalar/index
universe. It does not identify the scalar and module universes. No homogeneous
complex, contraction, or Euler identity is asserted here.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory* (2013),
  for the Koszul construction underlying exterior-power identities.
-/

public section

noncomputable section

open scoped TensorProduct

universe u v w

namespace Module.Koszul

/-- A finite degree index in the universe of the scalar ring. -/
abbrev SymmetricIndex (d : ℕ) : Type u := ULift.{u} (Fin d)

private def successorIndexEquiv (d : ℕ) :
    SymmetricIndex.{u} 1 ⊕ SymmetricIndex.{u} d ≃ SymmetricIndex.{u} (d + 1) :=
  (Equiv.sumCongr
      (Equiv.ulift : SymmetricIndex.{u} 1 ≃ Fin 1)
      (Equiv.ulift : SymmetricIndex.{u} d ≃ Fin d)).trans
    ((finSumFinEquiv : Fin 1 ⊕ Fin d ≃ Fin (1 + d)).trans
      ((finCongr (show 1 + d = d + 1 by omega)).trans
        (Equiv.ulift : SymmetricIndex.{u} (d + 1) ≃ Fin (d + 1)).symm))

section Symmetric

variable (S : Type u) [CommSemiring S]
variable (P : Type v) [AddCommMonoid P] [Module S P]

/-- The degree-d symmetric power, using an index in the scalar universe. -/
abbrev SymmetricDegree (d : ℕ) :=
  SymmetricPower S (SymmetricIndex.{u} d) P

/-- Insertion of one module element into the symmetric factor. -/
def insert (d : ℕ) :
    P ⊗[S] SymmetricDegree S P d →ₗ[S] SymmetricDegree S P (d + 1) :=
  (SymmetricPower.reindex (R := S) (M := P) (successorIndexEquiv.{u} d)).toLinearMap.comp
    ((SymmetricPower.concat (R := S) (I := SymmetricIndex.{u} 1)
        (J := SymmetricIndex.{u} d) (P := P)).comp
      (TensorProduct.map
        ((SymmetricPower.subsingletonEquiv (R := S) (M := P)
          ((Equiv.ulift : SymmetricIndex.{u} 1 ≃ Fin 1).symm 0)).symm.toLinearMap)
        (LinearMap.id : SymmetricDegree S P d →ₗ[S] SymmetricDegree S P d)))

private def insertCurried (d : ℕ) :
    P →ₗ[S] SymmetricDegree S P d →ₗ[S] SymmetricDegree S P (d + 1) :=
  TensorProduct.lcurry (RingHom.id S) P (SymmetricDegree S P d)
    (SymmetricDegree S P (d + 1)) (insert S P d)

/-- Symmetric insertion places the new input first in a pure tuple. -/
theorem insert_tprod (d : ℕ) (p : P) (x : SymmetricIndex.{u} d → P) :
    insert S P d (p ⊗ₜ[S] SymmetricPower.tprod S x) =
      SymmetricPower.tprod S
        (fun k : SymmetricIndex.{u} (d + 1) =>
          Fin.cases p (fun j : Fin d => x ⟨j⟩) k.down) := by
  let y : SymmetricIndex.{u} (d + 1) → P := fun k =>
    Fin.cases p (fun j : Fin d => x ⟨j⟩) k.down
  change SymmetricPower.reindex (R := S) (M := P) (successorIndexEquiv.{u} d)
    (SymmetricPower.concat
      (TensorProduct.map
        ((SymmetricPower.subsingletonEquiv (R := S) (M := P)
          ((Equiv.ulift : SymmetricIndex.{u} 1 ≃ Fin 1).symm 0)).symm.toLinearMap)
        (LinearMap.id : SymmetricDegree S P d →ₗ[S] SymmetricDegree S P d)
        (p ⊗ₜ[S] SymmetricPower.tprod S x))) = SymmetricPower.tprod S y
  rw [TensorProduct.map_tmul]
  change SymmetricPower.reindex (R := S) (M := P) (successorIndexEquiv.{u} d)
    (SymmetricPower.concat
      ((SymmetricPower.subsingletonEquiv (R := S) (M := P)
        ((Equiv.ulift : SymmetricIndex.{u} 1 ≃ Fin 1).symm 0)).symm p ⊗ₜ[S]
        SymmetricPower.tprod S x)) = SymmetricPower.tprod S y
  rw [SymmetricPower.subsingletonEquiv_symm_apply,
    SymmetricPower.concat_tprod, SymmetricPower.reindex_tprod]
  apply congrArg (fun z : SymmetricIndex.{u} (d + 1) → P => SymmetricPower.tprod S z)
  funext k
  have h : ∀ i : SymmetricIndex.{u} 1 ⊕ SymmetricIndex.{u} d,
      Sum.elim (fun _ => p) x i = y (successorIndexEquiv.{u} d i) := by
    intro i
    rcases i with i | i
    · rcases i with ⟨⟨i, hi⟩⟩
      have hi0 : i = 0 := by omega
      subst i
      have he : successorIndexEquiv.{u} d
          (Sum.inl (⟨⟨0, hi⟩⟩ : SymmetricIndex.{u} 1)) =
          (⟨(0 : Fin (d + 1))⟩ : SymmetricIndex.{u} (d + 1)) := by
        change (ULift.up
          (finCongr (show 1 + d = d + 1 by omega)
            ((finSumFinEquiv : Fin 1 ⊕ Fin d ≃ Fin (1 + d))
              (Sum.inl (⟨0, hi⟩ : Fin 1)))) : SymmetricIndex.{u} (d + 1)) =
          (⟨(0 : Fin (d + 1))⟩ : SymmetricIndex.{u} (d + 1))
        rw [finSumFinEquiv_apply_left, finCongr_apply_mk]
        rfl
      change p = y (successorIndexEquiv.{u} d
        (Sum.inl (⟨⟨0, hi⟩⟩ : SymmetricIndex.{u} 1)))
      rw [he]
      rfl
    · rcases i with ⟨i⟩
      have he : successorIndexEquiv.{u} d (Sum.inr (⟨i⟩ : SymmetricIndex.{u} d)) =
          (⟨i.succ⟩ : SymmetricIndex.{u} (d + 1)) := by
        change (ULift.up
          (finCongr (show 1 + d = d + 1 by omega)
            ((finSumFinEquiv : Fin 1 ⊕ Fin d ≃ Fin (1 + d)) (Sum.inr i))) :
            SymmetricIndex.{u} (d + 1)) =
          (⟨i.succ⟩ : SymmetricIndex.{u} (d + 1))
        rw [finSumFinEquiv_apply_right, finCongr_apply_mk]
        change (⟨⟨1 + i.val, by omega⟩⟩ : SymmetricIndex.{u} (d + 1)) = ⟨i.succ⟩
        congr 2; omega
      change x ⟨i⟩ = y (successorIndexEquiv.{u} d
        (Sum.inr (⟨i⟩ : SymmetricIndex.{u} d)))
      rw [he]
      rfl
  simpa only [Equiv.apply_symm_apply] using h ((successorIndexEquiv.{u} d).symm k)


private theorem insert_insert_comm (d : ℕ) (p q : P) (s : SymmetricDegree S P d) :
    insert S P (d + 1) (p ⊗ₜ[S] insert S P d (q ⊗ₜ[S] s)) =
      insert S P (d + 1) (q ⊗ₜ[S] insert S P d (p ⊗ₜ[S] s)) := by
  have h : (insertCurried S P (d + 1) p).comp (insertCurried S P d q) =
      (insertCurried S P (d + 1) q).comp (insertCurried S P d p) := by
    apply SymmetricPower.hom_ext (R := S) (ι := SymmetricIndex.{u} d) (M := P)
      (N := SymmetricDegree S P (d + 1 + 1))
    intro x
    change insertCurried S P (d + 1) p
        (insertCurried S P d q (SymmetricPower.tprod S x)) =
      insertCurried S P (d + 1) q
        (insertCurried S P d p (SymmetricPower.tprod S x))
    simp only [insertCurried, TensorProduct.lcurry_apply, insert_tprod]
    let a : SymmetricIndex.{u} (d + 1 + 1) := ⟨(0 : Fin (d + 1 + 1))⟩
    let b : SymmetricIndex.{u} (d + 1 + 1) := ⟨(0 : Fin (d + 1)).succ⟩
    let e : SymmetricIndex.{u} (d + 1 + 1) ≃ SymmetricIndex.{u} (d + 1 + 1) :=
      Equiv.swap a b
    let v : SymmetricIndex.{u} (d + 1 + 1) → P := fun k =>
      Fin.cases p (fun j : Fin (d + 1) =>
        Fin.cases q (fun l : Fin d => x ⟨l⟩) j) k.down
    let w : SymmetricIndex.{u} (d + 1 + 1) → P := fun k =>
      Fin.cases q (fun j : Fin (d + 1) =>
        Fin.cases p (fun l : Fin d => x ⟨l⟩) j) k.down
    change SymmetricPower.tprod S v = SymmetricPower.tprod S w
    have hvw : v = (fun k : SymmetricIndex.{u} (d + 1 + 1) => w (e k)) := by
      funext k
      rcases k with ⟨k⟩
      refine Fin.cases ?_ (fun j : Fin (d + 1) =>
        Fin.cases ?_ (fun l : Fin d => ?_) j) k
      · change p = w (Equiv.swap a b a)
        rw [Equiv.swap_apply_left a b]
        rfl
      · change q = w (Equiv.swap a b b)
        rw [Equiv.swap_apply_right a b]
        rfl
      · have h0 : (⟨l.succ.succ⟩ : SymmetricIndex.{u} (d + 1 + 1)) ≠ a := by
          intro he
          have hv := congrArg
            (fun z : SymmetricIndex.{u} (d + 1 + 1) => z.down.val) he
          change l.val + 1 + 1 = 0 at hv
          omega
        have h1 : (⟨l.succ.succ⟩ : SymmetricIndex.{u} (d + 1 + 1)) ≠ b := by
          intro he
          have hv := congrArg
            (fun z : SymmetricIndex.{u} (d + 1 + 1) => z.down.val) he
          change l.val + 1 + 1 = 1 at hv
          omega
        change x (⟨l⟩ : SymmetricIndex.{u} d) =
          w (Equiv.swap a b (⟨l.succ.succ⟩ : SymmetricIndex.{u} (d + 1 + 1)))
        rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
        rfl
    calc
      SymmetricPower.tprod S v =
          SymmetricPower.tprod S (fun k : SymmetricIndex.{u} (d + 1 + 1) => w (e k)) :=
        congrArg (fun z : SymmetricIndex.{u} (d + 1 + 1) → P => SymmetricPower.tprod S z) hvw
      SymmetricPower.tprod S (fun k : SymmetricIndex.{u} (d + 1 + 1) => w (e k)) =
          SymmetricPower.tprod S w :=
        SymmetricPower.tprod_equiv (R := S) (ι := SymmetricIndex.{u} (d + 1 + 1))
          (M := P) e w
  have hs := congrArg
    (fun g : SymmetricDegree S P d →ₗ[S] SymmetricDegree S P (d + 1 + 1) => g s) h
  change insertCurried S P (d + 1) p (insertCurried S P d q s) =
    insertCurried S P (d + 1) q (insertCurried S P d p s) at hs
  simpa only [insertCurried, TensorProduct.lcurry_apply] using hs

variable {S P}
variable {Q : Type w} [AddCommMonoid Q] [Module S Q]

/-- Symmetric insertion commutes with every module homomorphism. -/
theorem insert_natural (f : P →ₗ[S] Q) (d : ℕ) :
    (SymmetricPower.map (ι := SymmetricIndex.{u} (d + 1)) f).comp
        (insert S P d) =
      (insert S Q d).comp
        (TensorProduct.map f (SymmetricPower.map (ι := SymmetricIndex.{u} d) f)) := by
  apply TensorProduct.ext'
  intro p s
  have h : (SymmetricPower.map (ι := SymmetricIndex.{u} (d + 1)) f).comp
        (insertCurried S P d p) =
      (insertCurried S Q d (f p)).comp
        (SymmetricPower.map (ι := SymmetricIndex.{u} d) f) := by
    apply SymmetricPower.hom_ext
    intro x
    change SymmetricPower.map f (insertCurried S P d p (SymmetricPower.tprod S x)) =
      insertCurried S Q d (f p) (SymmetricPower.map f (SymmetricPower.tprod S x))
    simp only [insertCurried, TensorProduct.lcurry_apply, insert_tprod,
      SymmetricPower.map_tprod]
    apply congrArg
      (fun y : SymmetricIndex.{u} (d + 1) → Q => SymmetricPower.tprod S y)
    funext k
    rcases k with ⟨k⟩
    refine Fin.cases ?_ (fun j => ?_) k <;> rfl
  change SymmetricPower.map f (insert S P d (p ⊗ₜ[S] s)) =
    insert S Q d (TensorProduct.map f (SymmetricPower.map f) (p ⊗ₜ[S] s))
  rw [TensorProduct.map_tmul]
  have hs := congrArg
    (fun g : SymmetricDegree S P d →ₗ[S] SymmetricDegree S Q (d + 1) => g s) h
  change SymmetricPower.map f (insertCurried S P d p s) =
    insertCurried S Q d (f p) (SymmetricPower.map f s) at hs
  simpa only [insertCurried, TensorProduct.lcurry_apply] using hs


end Symmetric

section Differential

variable (S : Type u) [CommRing S]
variable (P : Type v) [AddCommGroup P] [Module S P]

/-- The exterior-symmetric term in bidegree (i,d). -/
abbrev Term (i d : ℕ) :=
  (⋀[S]^i P) ⊗[S] SymmetricDegree S P d

private abbrev termHomAddCommGroup (i d : ℕ) :
    AddCommGroup (SymmetricDegree S P d →ₗ[S] Term S P i (d + 1)) :=
  Module.addCommMonoidToAddCommGroup S

attribute [local instance] termHomAddCommGroup

private def alternatingSeed (i d : ℕ) :
    P →ₗ[S] P [⋀^Fin i]→ₗ[S]
      (SymmetricDegree S P d →ₗ[S] Term S P i (d + 1)) :=
  (exteriorPower.alternatingMapLinearEquiv (R := S) (M := P) (n := i)
      (N := SymmetricDegree S P d →ₗ[S] Term S P i (d + 1))).symm.toLinearMap.comp
    ((LinearMap.lflip (R₀ := S)
        ((LinearMap.llcomp S (SymmetricDegree S P d)
            (SymmetricDegree S P (d + 1)) (Term S P i (d + 1))).comp
          (TensorProduct.mk S (⋀[S]^i P) (SymmetricDegree S P (d + 1))))).comp
      (insertCurried S P d))

/-- The bigraded Koszul differential: exterior degree decreases and symmetric degree increases. -/
def delta (i d : ℕ) :
    Term S P (i + 1) d →ₗ[S] Term S P i (d + 1) :=
  TensorProduct.lift
    (exteriorPower.alternatingMapLinearEquiv (R := S) (M := P) (n := i + 1)
      (N := SymmetricDegree S P d →ₗ[S] Term S P i (d + 1))
      (AlternatingMap.alternatizeUncurryFin (alternatingSeed S P i d)))

/-- The Koszul differential is signed deletion times degree-one symmetric insertion. -/
theorem delta_ιMulti_tmul (i d : ℕ) (v : Fin (i + 1) → P)
    (s : SymmetricDegree S P d) :
    delta S P i d (exteriorPower.ιMulti S (i + 1) v ⊗ₜ[S] s) =
      ∑ a : Fin (i + 1), (-1 : S) ^ (a : ℕ) •
        (exteriorPower.ιMulti S i (fun b => v (Fin.succAbove a b)) ⊗ₜ[S]
          insert S P d (v a ⊗ₜ[S] s)) := by
  classical
  have hseed (p : P) (w : Fin i → P) :
      alternatingSeed S P i d p w s =
        exteriorPower.ιMulti S i w ⊗ₜ[S] insert S P d (p ⊗ₜ[S] s) := by
    simp only [alternatingSeed, insertCurried, LinearMap.comp_apply,
      LinearEquiv.coe_coe,
      exteriorPower.alternatingMapLinearEquiv_symm_apply,
      LinearMap.compAlternatingMap_apply, LinearMap.lflip_apply,
      LinearMap.flip_apply, LinearMap.llcomp_apply,
      TensorProduct.lcurry_apply, TensorProduct.mk_apply]
  have hremove (a : Fin (i + 1)) :
      Fin.removeNth a v = fun b : Fin i => v (Fin.succAbove a b) := by
    funext b
    exact Fin.removeNth_apply a v b
  rw [delta, TensorProduct.lift.tmul,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.alternatizeUncurryFin_apply]
  simp [hseed, hremove, ← Int.cast_smul_eq_zsmul S]


private theorem alternatizeUncurryFinLM_apply_eq
    {R : Type u} {M : Type v} {N : Type w} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] {n : ℕ}
    (f : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) :
    AlternatingMap.alternatizeUncurryFinLM f =
      AlternatingMap.alternatizeUncurryFin f := by
  rfl

private theorem delta_delta_ιMulti_tmul (i d : ℕ) (v : Fin (i + 2) → P)
    (s : SymmetricDegree S P d) :
    delta S P i (d + 1)
        (delta S P (i + 1) d (exteriorPower.ιMulti S (i + 2) v ⊗ₜ[S] s)) = 0 := by
  let L : P →ₗ[S] SymmetricDegree S P (d + 1) :=
    LinearMap.lflip (R₀ := S) (insertCurried S P d) s
  let K : SymmetricDegree S P (d + 2) →ₗ[S]
      P [⋀^Fin i]→ₗ[S] Term S P i (d + 2) :=
    (exteriorPower.alternatingMapLinearEquiv (R := S) (M := P) (n := i)
      (N := Term S P i (d + 2))).symm.toLinearMap.comp
        (LinearMap.lflip (R₀ := S)
          (TensorProduct.mk S (⋀[S]^i P) (SymmetricDegree S P (d + 2))))
  let F : P →ₗ[S] P →ₗ[S] P [⋀^Fin i]→ₗ[S] Term S P i (d + 2) :=
    (LinearMap.lflip (R₀ := S)
      ((insertCurried S P (d + 1)).compl₂ L)).compr₂ K
  have hF (p q : P) (w : Fin i → P) :
      F p q w = exteriorPower.ιMulti S i w ⊗ₜ[S]
        insert S P (d + 1) (q ⊗ₜ[S] insert S P d (p ⊗ₜ[S] s)) := by
    simp [F, L, K, insertCurried, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
      LinearMap.lflip_apply, LinearMap.flip_apply, TensorProduct.lcurry_apply,
      exteriorPower.alternatingMapLinearEquiv_symm_apply,
      LinearMap.compAlternatingMap_apply, TensorProduct.mk_apply]
  have hsym : ∀ p q, F p q = F q p := by
    intro p q
    apply AlternatingMap.ext
    intro w
    rw [hF, hF, insert_insert_comm S P d q p s]
  have halt :=
    AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
      (R := S) (M := P) (N := Term S P i (d + 2)) (n := i) (f := F) hsym
  have hz := congrArg
    (fun A : P [⋀^Fin (i + 2)]→ₗ[S] Term S P i (d + 2) => A v) halt
  have hremove (a : Fin (i + 2)) (b : Fin (i + 1)) :
      Fin.removeNth b (Fin.removeNth a v) =
        fun c : Fin i => v (Fin.succAbove a (Fin.succAbove b c)) := by
    funext c
    simp only [Fin.removeNth_apply]
  have hsum :
      (∑ a : Fin (i + 2), (-1 : S) ^ (a : ℕ) •
        ∑ b : Fin (i + 1), (-1 : S) ^ (b : ℕ) •
          (exteriorPower.ιMulti S i
              (fun c => v (Fin.succAbove a (Fin.succAbove b c))) ⊗ₜ[S]
            insert S P (d + 1)
              (v (Fin.succAbove a b) ⊗ₜ[S] insert S P d (v a ⊗ₜ[S] s)))) = 0 := by
    simpa [AlternatingMap.alternatizeUncurryFin_apply,
      alternatizeUncurryFinLM_apply_eq, hF, hremove, Fin.removeNth_apply,
      ← Int.cast_smul_eq_zsmul S] using hz
  rw [delta_ιMulti_tmul]
  simp only [map_sum, map_smul, delta_ιMulti_tmul]
  exact hsum

/-- Two successive bigraded Koszul differentials compose to zero.
For the Koszul construction, see Weibel, *The K-book* (2013). -/
theorem delta_comp_delta (i d : ℕ) :
    (delta S P i (d + 1)).comp (delta S P (i + 1) d) = 0 := by
  apply TensorProduct.ext'
  intro x s
  let G : (⋀[S]^(i + 2) P) →ₗ[S] Term S P i (d + 2) :=
    LinearMap.lflip (R₀ := S)
      (TensorProduct.lcurry (RingHom.id S) (⋀[S]^(i + 2) P)
        (SymmetricDegree S P d) (Term S P i (d + 2))
        ((delta S P i (d + 1)).comp (delta S P (i + 1) d))) s
  have hG : G = 0 := by
    refine exteriorPower.linearMap_ext (R := S) (n := i + 2) (M := P)
      (N := Term S P i (d + 2)) (f := G) (g := 0) ?_
    apply AlternatingMap.ext
    intro v
    simpa [G, TensorProduct.lcurry_apply, LinearMap.lflip_apply,
      LinearMap.flip_apply, LinearMap.compAlternatingMap_apply] using
      delta_delta_ιMulti_tmul S P i d v s
  have hx := congrArg (fun g : (⋀[S]^(i + 2) P) →ₗ[S] Term S P i (d + 2) => g x) hG
  simpa [G, TensorProduct.lcurry_apply, LinearMap.lflip_apply,
    LinearMap.flip_apply] using hx


variable {S P}
variable {Q : Type w} [AddCommGroup Q] [Module S Q]

/-- The bigraded Koszul differential commutes with every module homomorphism. -/
theorem delta_natural (f : P →ₗ[S] Q) (i d : ℕ) :
    (TensorProduct.map (exteriorPower.map i f)
        (SymmetricPower.map (ι := SymmetricIndex.{u} (d + 1)) f)).comp
        (delta S P i d) =
      (delta S Q i d).comp
        (TensorProduct.map (exteriorPower.map (i + 1) f)
          (SymmetricPower.map (ι := SymmetricIndex.{u} d) f)) := by
  classical
  have hinsert (p : P) (s : SymmetricDegree S P d) :
      (SymmetricPower.map (ι := SymmetricIndex.{u} (d + 1)) f)
          (insert S P d (p ⊗ₜ[S] s)) =
        insert S Q d
          (f p ⊗ₜ[S] (SymmetricPower.map (ι := SymmetricIndex.{u} d) f) s) := by
    have h := congrArg
      (fun L : P ⊗[S] SymmetricDegree S P d →ₗ[S]
          SymmetricDegree S Q (d + 1) => L (p ⊗ₜ[S] s))
      (insert_natural f d)
    simpa only [LinearMap.comp_apply, TensorProduct.map_tmul] using h
  apply TensorProduct.ext
  apply LinearMap.ext_on_range
    (exteriorPower.ιMulti_span S (i + 1) (M := P))
  intro v
  apply LinearMap.ext
  intro s
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
    LinearMap.comp_apply, TensorProduct.map_tmul,
    exteriorPower.map_apply_ιMulti]
  simp [delta_ιMulti_tmul, TensorProduct.map_tmul,
    exteriorPower.map_apply_ιMulti, hinsert]
  rfl


end Differential

end Module.Koszul
