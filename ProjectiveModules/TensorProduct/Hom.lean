/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import ProjectiveModules.LinearMap.Finsupp

/-!
# Tensor-Hom comparison maps for projective tensor factors

The canonical map `TensorProduct.rTensorHomToHomRTensor σ L M N` is bijective
when the tensor factor `N` is finite projective, with arbitrary source `L`.
It is also surjective when `L` is finite over `R` and `N` is projective over `S`;
this requires neither projectivity of `L` nor finite generation of `N`.
The coefficient module `M` is arbitrary in both results. Scalars are commutative
semirings, all additive structures are commutative monoids, and the carrier
universes are independent. The scalar homomorphism `σ` need not be injective or
surjective.

Naturality in all three modules holds without finiteness or projectivity.
The dual specialization is connected to Mathlib's `dualTensorHom` by the tensor
left unitor. For finite projective `L` over a single scalar semiring, Mathlib's
`rTensorHomEquivHomRTensor_toLinearMap` and `rTensorHomEquivHomRTensor_apply`
already identify the same canonical map with its finite-source equivalence.

The proofs follow the free comparison and retract strategy of Mathlib's
Contraction formalization, generalized from duals to semilinear Hom. The
finite-projective-right comparison uses `TensorProduct.piScalarRight`. For
finite-source surjectivity, `TensorProduct.finsuppScalarRight` handles an
arbitrary free tensor factor, and the finite-source semilinear Finsupp comparison
supplies a lift before descent along a projective retraction. Neither proof
chooses a basis.

## References

- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 17, for the
  linear tensor-Hom comparison. Here the scalars are generalized to commutative
  semirings and the Hom maps to semilinear maps.
- Mathlib's Contraction formalization by Oliver Nash and Antoine Labelle
  (`Mathlib.LinearAlgebra.Contraction`), for the finite-free and retract strategy.
- Mathlib's tensor maps by Kenny Lau and Mario Carneiro, and tensor products with
  finite products by Judith Ludwig and Christian Merten.
- Mathlib's projective-module formalization by Kevin Buzzard and Antoine Labelle.
- Mathlib's finitely supported Hom comparison by Johan Commelin
  (`Mathlib.RingTheory.Finiteness.Finsupp`), and tensor products with finitely
  supported functions by Johannes Hölzl and Antoine Chambert-Loir
  (`Mathlib.LinearAlgebra.DirectSum.Finsupp`).
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

universe uR uS uL uM uN uL' uM' uN' uι

section Semilinear

variable {R : Type uR} {S : Type uS} [CommSemiring R] [CommSemiring S]
variable (σ : R →+* S)
variable {L : Type uL} {M : Type uM} {N : Type uN}
variable [AddCommMonoid L] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R L] [Module S M] [Module S N]

/-- The canonical tensor-Hom map is natural in the source, Hom target and tensor
factor. This identity holds for arbitrary tensors and does not require any
finiteness or projectivity assumptions. The Hom map is Mathlib's semilinear
precomposition followed by postcomposition. -/
theorem rTensorHomToHomRTensor_natural
    {L' : Type uL'} {M' : Type uM'} {N' : Type uN'}
    [AddCommMonoid L'] [AddCommMonoid M'] [AddCommMonoid N']
    [Module R L'] [Module S M'] [Module S N']
    (a : L' →ₗ[R] L) (b : M →ₗ[S] M') (c : N →ₗ[S] N')
    (t : (L →ₛₗ[σ] M) ⊗[S] N) (l : L') :
    rTensorHomToHomRTensor σ L' M' N'
        (map ((LinearMap.llcomp S L' M M' b).comp
          (LinearMap.lcompₛₗ S M σ a)) c t) l =
      map b c (rTensorHomToHomRTensor σ L M N t (a l)) := by
  induction t using TensorProduct.inductionOn with
  | tmul f n =>
      simp only [map_tmul, rTensorHomToHomRTensor_apply, LinearMap.comp_apply,
        LinearMap.llcomp_apply, LinearMap.lcompₛₗ_apply]
  | add t₁ t₂ h₁ h₂ =>
      simp only [map_add, LinearMap.add_apply, h₁, h₂]

/-- The canonical tensor-Hom map is natural in its tensor factor, with the
source and Hom target fixed. No finiteness or projectivity is required. -/
theorem rTensorHomToHomRTensor_natural_right
    {P : Type uN'} [AddCommMonoid P] [Module S P]
    (c : N →ₗ[S] P) (t : (L →ₛₗ[σ] M) ⊗[S] N) (l : L) :
    rTensorHomToHomRTensor σ L M P (map LinearMap.id c t) l =
      map LinearMap.id c (rTensorHomToHomRTensor σ L M N t l) := by
  have hcomp : (LinearMap.llcomp S L M M (LinearMap.id : M →ₗ[S] M)).comp
      (LinearMap.lcompₛₗ S M σ (LinearMap.id : L →ₗ[R] L)) = LinearMap.id := by
    ext f l
    rfl
  simpa only [hcomp, LinearMap.id_apply] using
    rTensorHomToHomRTensor_natural σ LinearMap.id LinearMap.id c t l

private theorem rTensorHomToHomRTensor_fun_bijective
    (ι : Type uι) [Finite ι] :
    Function.Bijective (rTensorHomToHomRTensor σ L M (ι → S)) := by
  classical
  let := Fintype.ofFinite ι
  let eT := piScalarRight S S (L →ₛₗ[σ] M) ι
  let eM := piScalarRight S S M ι
  have hcoord (t : (L →ₛₗ[σ] M) ⊗[S] (ι → S)) (l : L) (i : ι) :
      eM (rTensorHomToHomRTensor σ L M (ι → S) t l) i = eT t i l := by
    induction t using TensorProduct.inductionOn with
    | tmul f n => simp [eM, eT]
    | add t u ht hu => simp [ht, hu]
  constructor
  · intro t u h
    apply eT.injective
    funext i
    apply LinearMap.ext
    intro l
    rw [← hcoord, ← hcoord, h]
  · intro h
    refine ⟨eT.symm (fun i => (LinearMap.proj i).comp (eM.toLinearMap.comp h)), ?_⟩
    apply LinearMap.ext
    intro l
    apply eM.injective
    funext i
    rw [hcoord]
    simp

private theorem rTensorHomToHomRTensor_finsupp_surjective
    (ι : Type uι) [Module.Finite R L] :
    Function.Surjective (rTensorHomToHomRTensor σ L M (ι →₀ S)) := by
  classical
  let eH := finsuppScalarRight S S (L →ₛₗ[σ] M) ι
  let eM := finsuppScalarRight S S M ι
  have hcoord (t : (L →ₛₗ[σ] M) ⊗[S] (ι →₀ S)) (l : L) (i : ι) :
      eM (rTensorHomToHomRTensor σ L M (ι →₀ S) t l) i = eH t i l := by
    induction t using TensorProduct.inductionOn with
    | tmul g n => simp [eM, eH]
    | add t u ht hu => simp [ht, hu]
  intro f
  obtain ⟨g, hg⟩ :=
    (LinearMap.finsuppLinearMapₛₗ_bijective_of_moduleFinite
      (L := L) (M := M) (ι := ι) S σ).2 (eM.toLinearMap.comp f)
  refine ⟨eH.symm g, ?_⟩
  apply LinearMap.ext
  intro l
  apply eM.injective
  apply Finsupp.ext
  intro i
  rw [hcoord, LinearEquiv.apply_symm_apply]
  simpa only [LinearMap.finsuppLinearMapₛₗ_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe] using
    congrArg (fun h : L →ₛₗ[σ] (ι →₀ M) => h l i) hg

/-- Surjectivity of the canonical semilinear tensor-Hom map descends along a
retraction of its tensor factor. -/
theorem rTensorHomToHomRTensor_surjective_of_comp_eq_id_right
    {P : Type uN'} [AddCommMonoid P] [Module S P]
    (s : N →ₗ[S] P) (p : P →ₗ[S] N) (hps : p.comp s = LinearMap.id)
    (h : Function.Surjective (rTensorHomToHomRTensor σ L M P)) :
    Function.Surjective (rTensorHomToHomRTensor σ L M N) := by
  intro f
  obtain ⟨t, ht⟩ := h ((map (LinearMap.id : M →ₗ[S] M) s).comp f)
  refine ⟨map LinearMap.id p t, ?_⟩
  ext l
  have hn := rTensorHomToHomRTensor_natural_right σ p t l
  simpa only [ht, LinearMap.comp_apply, map_map, LinearMap.id_comp, hps,
    map_id, LinearMap.id_apply] using hn

/-- Bijectivity of the canonical semilinear tensor-Hom map descends along a
retraction of its tensor factor. This generalizes Mathlib's corresponding
right-retract transport for `dualTensorHom`. -/
theorem rTensorHomToHomRTensor_bijective_of_comp_eq_id_right
    {P : Type uN'} [AddCommMonoid P] [Module S P]
    (s : N →ₗ[S] P) (p : P →ₗ[S] N) (hps : p.comp s = LinearMap.id)
    (h : Function.Bijective (rTensorHomToHomRTensor σ L M P)) :
    Function.Bijective (rTensorHomToHomRTensor σ L M N) := by
  refine ⟨?_, rTensorHomToHomRTensor_surjective_of_comp_eq_id_right σ s p hps h.2⟩
  intro t u htu
  have hsu : map LinearMap.id s t = map LinearMap.id s u := by
    apply h.1
    ext l
    rw [rTensorHomToHomRTensor_natural_right σ,
      rTensorHomToHomRTensor_natural_right σ, htu]
  have := congrArg (map (LinearMap.id : (L →ₛₗ[σ] M) →ₗ[S] (L →ₛₗ[σ] M)) p) hsu
  simpa only [map_map, LinearMap.id_comp, hps, map_id, LinearMap.id_apply] using this

/-- Tensoring semilinear Hom with a finite projective module commutes with Hom:
Mathlib's canonical `rTensorHomToHomRTensor` is bijective. Only the tensor factor
is finite projective; the source and Hom target are unrestricted. This generalizes
the linear tensor-Hom comparison in Chapter 17 of May's *A Concise Course in
Algebraic Topology* to semirings and semilinear maps. -/
theorem rTensorHomToHomRTensor_bijective_of_finite_projective_right
    [Module.Finite S N] [Module.Projective S N] :
    Function.Bijective (rTensorHomToHomRTensor σ L M N) := by
  obtain ⟨n, p, s, _, _, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective S N
  exact rTensorHomToHomRTensor_bijective_of_comp_eq_id_right σ s p hps
    (rTensorHomToHomRTensor_fun_bijective σ (Fin n))

/-- If the source is finitely generated and the tensor factor is projective,
the canonical semilinear tensor-Hom map is surjective. Neither projectivity of
the source nor finite generation of the tensor factor is needed. The proof
extends Mathlib's finite-source contraction argument from linear duals to
semilinear Hom. -/
theorem rTensorHomToHomRTensor_surjective_of_finite_left_projective_right
    [Module.Finite R L] [Module.Projective S N] :
    Function.Surjective (rTensorHomToHomRTensor σ L M N) := by
  obtain ⟨s, hps⟩ := Module.projective_def'.mp ‹Module.Projective S N›
  exact rTensorHomToHomRTensor_surjective_of_comp_eq_id_right σ s
    (Finsupp.linearCombination S id) hps
    (rTensorHomToHomRTensor_finsupp_surjective σ N)

end Semilinear

section LeftUnitor

variable (R : Type uR) (L : Type uL) (N : Type uN)
variable [CommSemiring R] [AddCommMonoid L] [AddCommMonoid N]
variable [Module R L] [Module R N]

/-- For scalar-valued linear maps, postcomposing the tensor-Hom comparison with the
canonical left tensor unitor gives `dualTensorHom`. This identifies the dual
specialization without introducing another comparison map or equivalence. -/
theorem rTensorHomToHomRTensor_comp_lid :
    (LinearMap.compRight R (TensorProduct.lid R N).toLinearMap).comp
        (rTensorHomToHomRTensor (RingHom.id R) L R N) =
      dualTensorHom R L N := by
  apply TensorProduct.ext'
  intro f n
  apply LinearMap.ext
  intro l
  simp only [LinearMap.comp_apply, LinearMap.compRight_apply,
    rTensorHomToHomRTensor_apply, LinearEquiv.coe_toLinearMap, lid_tmul,
    dualTensorHom_apply]

end LeftUnitor

end TensorProduct
