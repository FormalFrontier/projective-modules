/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.TensorProduct
public import ProjectiveModules.ExteriorPower.Equiv
public import ProjectiveModules.TensorPower.BaseChange
public import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.LocalProperties.Exactness
import ProjectiveModules.Localization.TensorProduct

/-!
# The exterior-power map for an invertible line

`exteriorPower.invertibleTwistMap` is the canonical linear map
`TensorPower R n L ⊗[R] (⋀[R]^n P) →ₗ[R] ⋀[R]^n (L ⊗[R] P)` for an invertible
`R`-module `L`. It sends a tensor of a pure tensor and a pure wedge to the wedge
of the pairwise tensors. It is bijective, giving `exteriorPower.invertibleTwistEquiv`.
The module `P` is arbitrary, and the construction includes degrees zero and one.

The map is defined by the multilinear and alternating universal properties, not
by transporting a map along a chosen trivialization. Local trivializations of `L`
are used only in the proofs of alternation and bijectivity: after localization,
all line entries are scalar multiples of one generator, so repeated `P` entries
give zero directly and the map has the scalar-multiplication normal form.
A scalar-extension comparison square connects this normal form to the global map.
The proofs use full module localizations and do not require flatness of `P` or
invertibility of any factorial.

The characteristic formula determines the map uniquely. Naturality holds for
arbitrary linear maps of both modules, including noninvertible maps between the
invertible lines. In degrees zero and one, the map agrees with the canonical
scalar multiplication and tensor-product identifications, respectively.

The line-factor case of Weibel's determinant tensor-product formula, Exercise I.3.4,
concerns finitely generated projective `P` of constant rank in its top exterior degree.
The equivalence here permits arbitrary `P` and every exterior degree. The ring and the
modules may lie in independent universes.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  [Exercise I.3.4](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.pdf).
-/

@[expose] public section

open scoped TensorProduct

universe uR uS uL uP uL' uQ uN

namespace exteriorPower

variable (R : Type uR) [CommRing R]
variable (L : Type uL) [AddCommGroup L] [Module R L]
variable (P : Type uP) [AddCommGroup P] [Module R P]

private theorem tensorWedgeSource_ext (n : ℕ) {N : Type uN}
    [AddCommGroup N] [Module R N]
    {F G : TensorPower R n L ⊗[R] (⋀[R]^n P) →ₗ[R] N}
    (h : ∀ (l : Fin n → L) (p : Fin n → P),
      F (PiTensorProduct.tprod R l ⊗ₜ[R] ιMulti R n p) =
        G (PiTensorProduct.tprod R l ⊗ₜ[R] ιMulti R n p)) : F = G := by
  apply TensorProduct.curry_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro l
  apply linearMap_ext
  apply AlternatingMap.ext
  intro p
  exact h l p

private theorem tensorWedgeBaseChangeSource_ext
    (S : Type uS) [CommRing S] [Algebra R S] (n : ℕ) {N : Type uN}
    [AddCommGroup N] [Module S N]
    {F G : S ⊗[R] (TensorPower R n L ⊗[R] (⋀[R]^n P)) →ₗ[S] N}
    (h : ∀ (s : S) (l : Fin n → L) (p : Fin n → P),
      F (s ⊗ₜ[R] (PiTensorProduct.tprod R l ⊗ₜ[R] ιMulti R n p)) =
        G (s ⊗ₜ[R] (PiTensorProduct.tprod R l ⊗ₜ[R] ιMulti R n p))) : F = G := by
  let : Module R N := Module.compHom N (algebraMap R S)
  let : IsScalarTower R S N := ⟨fun r s x => by
    change (r • s) • x = (algebraMap R S r) • (s • x)
    rw [Algebra.smul_def, mul_smul]⟩
  apply TensorProduct.AlgebraTensorModule.curry_injective
  apply LinearMap.ext
  intro s
  apply tensorWedgeSource_ext R L P n
  exact h s

/-- Scalar extension of the source of the exterior-power twist. This comparison
uses binary tensor-product base change and the tensor-power and exterior-power
base-change equivalences, including their degree-zero comparisons. -/
noncomputable def invertibleTwistSourceBaseChangeEquiv
    (S : Type uS) [CommRing S] [Algebra R S] (n : ℕ) :
    S ⊗[R] (TensorPower R n L ⊗[R] (⋀[R]^n P)) ≃ₗ[S]
      TensorPower S n (S ⊗[R] L) ⊗[S] (⋀[S]^n (S ⊗[R] P)) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange R S
    (TensorPower R n L) (⋀[R]^n P)).trans
      (TensorProduct.congr (TensorPower.baseChangeEquiv R S n L)
        (baseChangeEquiv (R := R) (S := S) (M := P) n))

/-- On a tensor of a pure tensor and a pure wedge, the source comparison extends
all entries by unit tensors and lets the original coefficient act on the result. -/
@[simp] theorem invertibleTwistSourceBaseChangeEquiv_tmul_tprod_tmul_ιMulti
    (S : Type uS) [CommRing S] [Algebra R S] (n : ℕ)
    (s : S) (l : Fin n → L) (p : Fin n → P) :
    invertibleTwistSourceBaseChangeEquiv R L P S n
        (s ⊗ₜ[R] (PiTensorProduct.tprod R l ⊗ₜ[R] ιMulti R n p)) =
      s • (PiTensorProduct.tprod S (fun i => (1 : S) ⊗ₜ[R] l i) ⊗ₜ[S]
        ιMulti S n (fun i => (1 : S) ⊗ₜ[R] p i)) := by
  simp only [invertibleTwistSourceBaseChangeEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul,
    TensorPower.baseChangeEquiv_tmul_tprod, baseChangeEquiv_tmul_ιMulti,
    one_smul, TensorProduct.smul_tmul']

/-- Scalar extension of the target of the exterior-power twist. Exterior-power
base change is followed by the exterior power of binary tensor-product base change. -/
noncomputable def invertibleTwistTargetBaseChangeEquiv
    (S : Type uS) [CommRing S] [Algebra R S] (n : ℕ) :
    S ⊗[R] (⋀[R]^n (L ⊗[R] P)) ≃ₗ[S]
      ⋀[S]^n ((S ⊗[R] L) ⊗[S] (S ⊗[R] P)) :=
  (baseChangeEquiv (R := R) (S := S) (M := L ⊗[R] P) n).trans
    (congr n (TensorProduct.AlgebraTensorModule.distribBaseChange R S L P))

/-- The target comparison extends the entries of a wedge of pairwise tensors
by unit tensors, with the original coefficient acting on the wedge. -/
@[simp] theorem invertibleTwistTargetBaseChangeEquiv_tmul_ιMulti
    (S : Type uS) [CommRing S] [Algebra R S] (n : ℕ)
    (s : S) (l : Fin n → L) (p : Fin n → P) :
    invertibleTwistTargetBaseChangeEquiv R L P S n
        (s ⊗ₜ[R] ιMulti R n (fun i => l i ⊗ₜ[R] p i)) =
      s • ιMulti S n (fun i => ((1 : S) ⊗ₜ[R] l i) ⊗ₜ[S]
        ((1 : S) ⊗ₜ[R] p i)) := by
  simp only [invertibleTwistTargetBaseChangeEquiv, LinearEquiv.trans_apply,
    baseChangeEquiv_tmul_ιMulti, _root_.map_smul, congr_ιMulti,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]

variable [Module.Invertible R L]

private theorem tensorWedge_eq_zero (n : ℕ) (l : Fin n → L) (p : Fin n → P)
    {i j : Fin n} (hp : p i = p j) (hij : i ≠ j) :
    ιMulti R n (fun k => l k ⊗ₜ[R] p k) = 0 := by
  classical
  let W (J : Ideal R) [J.IsMaximal] :=
    Localization J.primeCompl ⊗[R] (⋀[R]^n (L ⊗[R] P))
  let loc (J : Ideal R) [J.IsMaximal] :
      (⋀[R]^n (L ⊗[R] P)) →ₗ[R] W J :=
    TensorProduct.mk R (Localization J.primeCompl) _ 1
  apply Module.eq_zero_of_localization_maximal W loc
  intro J hJ
  let S := Localization J.primeCompl
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free S (S ⊗[R] L))
  let c : S ⊗[R] (L ⊗[R] P) ≃ₗ[S] S ⊗[R] P :=
    (TensorProduct.AlgebraTensorModule.distribBaseChange R S L P).trans
      ((TensorProduct.congr e (LinearEquiv.refl S (S ⊗[R] P))).trans
        (TensorProduct.lid S (S ⊗[R] P)))
  have hc (x : L) (y : P) :
      c ((1 : S) ⊗ₜ[R] (x ⊗ₜ[R] y)) =
        e ((1 : S) ⊗ₜ[R] x) • ((1 : S) ⊗ₜ[R] y) := by
    simp only [c, LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.lid_tmul]
  change (1 : S) ⊗ₜ[R] ιMulti R n (fun k => l k ⊗ₜ[R] p k) = 0
  apply (baseChangeEquiv (R := R) (S := S) (M := L ⊗[R] P) n).injective
  apply map_injective (n := n) (f := c.toLinearMap) c.symm.toLinearMap (by
    apply LinearMap.ext
    intro x
    exact c.symm_apply_apply x)
  simp only [map_zero, baseChangeEquiv_tmul_ιMulti, one_smul,
    map_apply_ιMulti, Function.comp_def, LinearEquiv.coe_coe]
  simp_rw [hc]
  rw [AlternatingMap.map_smul_univ]
  rw [(ιMulti S n).map_eq_zero_of_eq (fun k => (1 : S) ⊗ₜ[R] p k)
    (congrArg (fun y : P => (1 : S) ⊗ₜ[R] y) hp) hij, smul_zero]

/-- The canonical exterior-power map for an invertible module `L`, characterized by
`(tprod l) ⊗ ιMulti p ↦ ιMulti (fun i => l i ⊗ p i)`. It is constructed by the
multilinear and alternating universal properties, for every degree and arbitrary `P`. -/
noncomputable def invertibleTwistMap (n : ℕ) :
    TensorPower R n L ⊗[R] (⋀[R]^n P) →ₗ[R] ⋀[R]^n (L ⊗[R] P) :=
  let alternating (l : Fin n → L) : P [⋀^Fin n]→ₗ[R] (⋀[R]^n (L ⊗[R] P)) :=
    { (ιMulti R n).toMultilinearMap.compLinearMap
        (fun i => TensorProduct.mk R L P (l i)) with
      map_eq_zero_of_eq' := by
        intro p i j hp hij
        exact tensorWedge_eq_zero R L P n l p hp hij }
  let multilinear : MultilinearMap R (fun _ : Fin n => L)
      (P [⋀^Fin n]→ₗ[R] (⋀[R]^n (L ⊗[R] P))) :=
    { toFun := alternating
      map_update_add' := by
        intro _ l i x y
        apply AlternatingMap.ext
        intro p
        exact ((ιMulti R n).toMultilinearMap.compLinearMap
          (fun k => (TensorProduct.mk R L P).flip (p k))).map_update_add l i x y
      map_update_smul' := by
        intro _ l i r x
        apply AlternatingMap.ext
        intro p
        exact ((ιMulti R n).toMultilinearMap.compLinearMap
          (fun k => (TensorProduct.mk R L P).flip (p k))).map_update_smul l i r x }
  TensorProduct.lift (PiTensorProduct.lift
    ((alternatingMapLinearEquiv (R := R) (n := n) (M := P)
      (N := ⋀[R]^n (L ⊗[R] P))).toLinearMap.compMultilinearMap multilinear))

/-- The twist map sends a pure tensor tensored with a pure wedge to the wedge of
the pairwise tensors. The line entries need not be equal. -/
@[simp] theorem invertibleTwistMap_tprod_tmul_ιMulti (n : ℕ)
    (l : Fin n → L) (p : Fin n → P) :
    invertibleTwistMap R L P n (PiTensorProduct.tprod R l ⊗ₜ[R] ιMulti R n p) =
      ιMulti R n (fun i => l i ⊗ₜ[R] p i) := by
  simp only [invertibleTwistMap, TensorProduct.lift.tmul, PiTensorProduct.lift.tprod,
    LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- The pure-tensor/pure-wedge formula uniquely determines the twist map. -/
theorem invertibleTwistMap_unique (n : ℕ)
    (F : TensorPower R n L ⊗[R] (⋀[R]^n P) →ₗ[R] ⋀[R]^n (L ⊗[R] P))
    (h : ∀ (l : Fin n → L) (p : Fin n → P),
      F (PiTensorProduct.tprod R l ⊗ₜ[R] ιMulti R n p) =
        ιMulti R n (fun i => l i ⊗ₜ[R] p i)) :
    F = invertibleTwistMap R L P n := by
  apply tensorWedgeSource_ext R L P n
  intro l p
  rw [h, invertibleTwistMap_tprod_tmul_ιMulti]

/-- The twist map is natural for arbitrary linear maps of the invertible lines
and arbitrary linear maps of the other modules; neither map need be an isomorphism. -/
theorem invertibleTwistMap_naturality (n : ℕ)
    {L' : Type uL'} [AddCommGroup L'] [Module R L'] [Module.Invertible R L']
    {Q : Type uQ} [AddCommGroup Q] [Module R Q]
    (α : L →ₗ[R] L') (f : P →ₗ[R] Q) :
    (map n (TensorProduct.map α f)).comp (invertibleTwistMap R L P n) =
      (invertibleTwistMap R L' Q n).comp
        (TensorProduct.map (PiTensorProduct.map (fun _ : Fin n => α)) (map n f)) := by
  apply tensorWedgeSource_ext R L P n
  intro l p
  simp only [LinearMap.comp_apply, invertibleTwistMap_tprod_tmul_ιMulti,
    map_apply_ιMulti, TensorProduct.map_tmul, PiTensorProduct.map_tprod,
    Function.comp_def]

/-- The canonical twist map commutes with extension of scalars. The source
comparison combines binary, tensor-power and exterior-power base change; the target
comparison uses exterior-power base change and binary tensor-product base change. -/
theorem invertibleTwistMap_baseChange
    (S : Type uS) [CommRing S] [Algebra R S] (n : ℕ) :
    (invertibleTwistTargetBaseChangeEquiv R L P S n).toLinearMap.comp
        ((invertibleTwistMap R L P n).baseChange S) =
      (invertibleTwistMap S (S ⊗[R] L) (S ⊗[R] P) n).comp
        (invertibleTwistSourceBaseChangeEquiv R L P S n).toLinearMap := by
  apply tensorWedgeBaseChangeSource_ext R L P S n
  intro s l p
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
    invertibleTwistMap_tprod_tmul_ιMulti,
    invertibleTwistSourceBaseChangeEquiv_tmul_tprod_tmul_ιMulti,
    invertibleTwistTargetBaseChangeEquiv_tmul_ιMulti, _root_.map_smul, LinearEquiv.coe_coe]

private noncomputable def tensorPowerScalarEquiv (n : ℕ) :
    TensorPower R n R ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap
    (PiTensorProduct.lift (MultilinearMap.mkPiAlgebra R (Fin n) R))
    ((LinearMap.id : R →ₗ[R] R).smulRight
      (PiTensorProduct.tprod R (fun _ : Fin n => (1 : R))))
    (by
      apply LinearMap.ext
      intro r
      simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
        _root_.map_smul, PiTensorProduct.lift.tprod, MultilinearMap.mkPiAlgebra_apply,
        Finset.prod_const_one, smul_eq_mul, mul_one])
    (by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro a
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        LinearMap.smulRight_apply, LinearMap.id_apply, PiTensorProduct.lift.tprod,
        MultilinearMap.mkPiAlgebra_apply]
      simpa only [smul_eq_mul, mul_one] using
        ((PiTensorProduct.tprod R).map_smul_univ a (fun _ : Fin n => (1 : R))).symm)

private theorem tensorPowerScalarEquiv_tprod (n : ℕ) (a : Fin n → R) :
    tensorPowerScalarEquiv R n (PiTensorProduct.tprod R a) = ∏ i, a i := by
  simp only [tensorPowerScalarEquiv, LinearEquiv.coe_ofLinearMap,
    PiTensorProduct.lift.tprod, MultilinearMap.mkPiAlgebra_apply]

private theorem invertibleTwistMap_bijective_of_linearEquiv (n : ℕ) (e : L ≃ₗ[R] R) :
    Function.Bijective (invertibleTwistMap R L P n) := by
  let c : L ⊗[R] P ≃ₗ[R] P :=
    (TensorProduct.congr e (LinearEquiv.refl R P)).trans (TensorProduct.lid R P)
  let a : TensorPower R n L ⊗[R] (⋀[R]^n P) ≃ₗ[R] ⋀[R]^n P :=
    (TensorProduct.congr (PiTensorProduct.congr (fun _ : Fin n => e))
      (LinearEquiv.refl R (⋀[R]^n P))).trans
        ((TensorProduct.congr (tensorPowerScalarEquiv R n)
          (LinearEquiv.refl R (⋀[R]^n P))).trans (TensorProduct.lid R (⋀[R]^n P)))
  let b : (⋀[R]^n (L ⊗[R] P)) →ₗ[R] ⋀[R]^n P := map n c.toLinearMap
  have hb : Function.Injective b := map_injective (n := n) c.symm.toLinearMap (by
    apply LinearMap.ext
    intro x
    exact c.symm_apply_apply x)
  have hc (l : L) (p : P) : c (l ⊗ₜ[R] p) = e l • p := by
    simp only [c, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, TensorProduct.lid_tmul]
  have h : b.comp (invertibleTwistMap R L P n) = a.toLinearMap := by
    apply tensorWedgeSource_ext R L P n
    intro l p
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      invertibleTwistMap_tprod_tmul_ιMulti, b,
      map_apply_ιMulti, Function.comp_def, hc, a, LinearEquiv.trans_apply,
      TensorProduct.congr_tmul, PiTensorProduct.congr_tprod,
      LinearEquiv.refl_apply, tensorPowerScalarEquiv_tprod, TensorProduct.lid_tmul]
    exact (ιMulti R n).map_smul_univ (fun i => e (l i)) p
  constructor
  · intro x y hxy
    apply a.injective
    exact (LinearMap.congr_fun h x).symm.trans
      ((congrArg b hxy).trans (LinearMap.congr_fun h y))
  · intro y
    obtain ⟨x, hx⟩ := a.surjective (b y)
    exact ⟨x, hb ((LinearMap.congr_fun h x).trans hx)⟩

/-- The canonical exterior-power twist map is bijective for every invertible
module and every degree, with no flatness or finiteness assumption on `P`.
Bijectivity is checked on full localizations at maximal ideals. -/
theorem invertibleTwistMap_bijective (n : ℕ) :
    Function.Bijective (invertibleTwistMap R L P n) := by
  classical
  apply _root_.bijective_of_localized_maximal (invertibleTwistMap R L P n)
  intro J hJ
  let S := Localization J.primeCompl
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free S (S ⊗[R] L))
  have hlocal : Function.Bijective
      (invertibleTwistMap S (S ⊗[R] L) (S ⊗[R] P) n) :=
    invertibleTwistMap_bijective_of_linearEquiv S (S ⊗[R] L) (S ⊗[R] P) n e
  let a := invertibleTwistSourceBaseChangeEquiv R L P S n
  let b := invertibleTwistTargetBaseChangeEquiv R L P S n
  have heq : (invertibleTwistMap R L P n).baseChange S =
      b.symm.toLinearMap.comp
        ((invertibleTwistMap S (S ⊗[R] L) (S ⊗[R] P) n).comp a.toLinearMap) := by
    apply LinearMap.ext
    intro x
    apply b.injective
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using
        LinearMap.congr_fun (invertibleTwistMap_baseChange R L P S n) x
  have hb : Function.Bijective ((invertibleTwistMap R L P n).baseChange S) := by
    rw [heq]
    exact b.symm.bijective.comp (hlocal.comp a.bijective)
  let a' := LocalizedModule.equivTensorProduct J.primeCompl
    (TensorPower R n L ⊗[R] (⋀[R]^n P))
  let b' := LocalizedModule.equivTensorProduct J.primeCompl (⋀[R]^n (L ⊗[R] P))
  have hmap : (fun z => b'.symm
      ((invertibleTwistMap R L P n).baseChange S (a' z))) =
      LocalizedModule.map J.primeCompl (invertibleTwistMap R L P n) := by
    funext z
    apply b'.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (LocalizedModule.equivTensorProduct_map J.primeCompl
      (invertibleTwistMap R L P n) z).symm
  rw [← hmap]
  exact b'.symm.bijective.comp (hb.comp a'.bijective)

/-- The canonical exterior-power twist equivalence for an invertible `R`-module `L`
and an arbitrary `R`-module `P`, in every degree.

Its forward map is `invertibleTwistMap`, constructed by the multilinear and
alternating universal properties. It sends `(tprod l) ⊗ (ιMulti p)` to
`ιMulti (fun i => l i ⊗ p i)`.

For finitely generated projective `P` of constant rank `n`, this recovers the
rank-one specialization of Weibel's determinant formula, Exercise I.3.4.
No finiteness, projectivity or flatness assumption is imposed on `P` in general. -/
noncomputable def invertibleTwistEquiv (n : ℕ) :
    TensorPower R n L ⊗[R] (⋀[R]^n P) ≃ₗ[R] ⋀[R]^n (L ⊗[R] P) :=
  LinearEquiv.ofBijective (invertibleTwistMap R L P n)
    (invertibleTwistMap_bijective R L P n)

/-- The linear map underlying the twist equivalence is the canonical twist map. -/
@[simp] theorem invertibleTwistEquiv_toLinearMap (n : ℕ) :
    (invertibleTwistEquiv R L P n).toLinearMap = invertibleTwistMap R L P n := rfl

/-- The twist equivalence wedges the pairwise tensors of arbitrary pure entries. -/
@[simp] theorem invertibleTwistEquiv_tprod_tmul_ιMulti (n : ℕ)
    (l : Fin n → L) (p : Fin n → P) :
    invertibleTwistEquiv R L P n (PiTensorProduct.tprod R l ⊗ₜ[R] ιMulti R n p) =
      ιMulti R n (fun i => l i ⊗ₜ[R] p i) :=
  invertibleTwistMap_tprod_tmul_ιMulti R L P n l p

/-- The inverse twist sends a wedge of pairwise pure tensors to the tensor of
the line entries tensored with the wedge of the other entries. -/
@[simp] theorem invertibleTwistEquiv_symm_ιMulti (n : ℕ)
    (l : Fin n → L) (p : Fin n → P) :
    (invertibleTwistEquiv R L P n).symm
        (ιMulti R n (fun i => l i ⊗ₜ[R] p i)) =
      PiTensorProduct.tprod R l ⊗ₜ[R] ιMulti R n p := by
  apply (invertibleTwistEquiv R L P n).injective
  rw [LinearEquiv.apply_symm_apply, invertibleTwistEquiv_tprod_tmul_ιMulti]

/-- The twist equivalence is natural for every linear map of the invertible
lines and every linear map of the other modules, not just isomorphisms. -/
theorem invertibleTwistEquiv_naturality (n : ℕ)
    {L' : Type uL'} [AddCommGroup L'] [Module R L'] [Module.Invertible R L']
    {Q : Type uQ} [AddCommGroup Q] [Module R Q]
    (α : L →ₗ[R] L') (f : P →ₗ[R] Q) :
    (map n (TensorProduct.map α f)).comp (invertibleTwistEquiv R L P n).toLinearMap =
      (invertibleTwistEquiv R L' Q n).toLinearMap.comp
        (TensorProduct.map (PiTensorProduct.map (fun _ : Fin n => α)) (map n f)) := by
  simpa only [invertibleTwistEquiv_toLinearMap] using
    invertibleTwistMap_naturality R L P n α f

/-- Inverse twists are natural for arbitrary morphisms of the invertible lines
and arbitrary morphisms of the other modules. -/
theorem invertibleTwistEquiv_symm_naturality (n : ℕ)
    {L' : Type uL'} [AddCommGroup L'] [Module R L'] [Module.Invertible R L']
    {Q : Type uQ} [AddCommGroup Q] [Module R Q]
    (α : L →ₗ[R] L') (f : P →ₗ[R] Q) :
    (TensorProduct.map (PiTensorProduct.map (fun _ : Fin n => α)) (map n f)).comp
        (invertibleTwistEquiv R L P n).symm.toLinearMap =
      (invertibleTwistEquiv R L' Q n).symm.toLinearMap.comp
        (map n (TensorProduct.map α f)) := by
  apply LinearMap.ext
  intro x
  apply (invertibleTwistEquiv R L' Q n).injective
  have h := LinearMap.congr_fun (invertibleTwistEquiv_naturality R L P n α f)
    ((invertibleTwistEquiv R L P n).symm x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using h.symm

/-- In degree zero, the twist map is multiplication `R ⊗[R] R → R` under
the canonical empty-tensor and empty-wedge identifications. -/
theorem invertibleTwistMap_zero :
    (zeroEquiv R (L ⊗[R] P)).toLinearMap.comp (invertibleTwistMap R L P 0) =
      (TensorProduct.lid R R).toLinearMap.comp
        (TensorProduct.map
          (PiTensorProduct.isEmptyEquiv (R := R) (s := fun _ : Fin 0 => L)
            (Fin 0)).toLinearMap
          (zeroEquiv R P).toLinearMap) := by
  apply tensorWedgeSource_ext R L P 0
  intro l p
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    invertibleTwistMap_tprod_tmul_ιMulti, zeroEquiv_ιMulti, TensorProduct.map_tmul,
    PiTensorProduct.isEmptyEquiv_apply_tprod, TensorProduct.lid_tmul, one_smul]

/-- In degree one, the twist map is the canonical identification with `L ⊗[R] P`
on both sides. -/
theorem invertibleTwistMap_one :
    (oneEquiv R (L ⊗[R] P)).toLinearMap.comp (invertibleTwistMap R L P 1) =
      TensorProduct.map
        (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 => L)
          (0 : Fin 1)).toLinearMap
        (oneEquiv R P).toLinearMap := by
  apply tensorWedgeSource_ext R L P 1
  intro l p
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    invertibleTwistMap_tprod_tmul_ιMulti, oneEquiv_ιMulti, TensorProduct.map_tmul,
    PiTensorProduct.subsingletonEquiv_apply_tprod]

/-- In degree zero, the twist equivalence is scalar multiplication under the
canonical identifications of the empty tensor and exterior powers with `R`. -/
theorem invertibleTwistEquiv_zero :
    (invertibleTwistEquiv R L P 0).trans (zeroEquiv R (L ⊗[R] P)) =
      (TensorProduct.congr
        (PiTensorProduct.isEmptyEquiv (R := R) (s := fun _ : Fin 0 => L) (Fin 0))
        (zeroEquiv R P)).trans (TensorProduct.lid R R) := by
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (invertibleTwistMap_zero R L P) x

/-- In degree one, the twist equivalence is the tensor product of the canonical
singleton-tensor and singleton-wedge identifications. -/
theorem invertibleTwistEquiv_one :
    (invertibleTwistEquiv R L P 1).trans (oneEquiv R (L ⊗[R] P)) =
      TensorProduct.congr
        (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 => L)
          (0 : Fin 1))
        (oneEquiv R P) := by
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (invertibleTwistMap_one R L P) x

end exteriorPower
