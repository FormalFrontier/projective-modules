/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.TensorProduct.Finite
public import ProjectiveModules.Dual.TensorProduct
public import ProjectiveModules.LinearMap.Finsupp
public import ProjectiveModules.TensorProduct.SemilinearHomProjective

/-!
# Semilinear tensor-Hom comparisons

The canonical map `TensorProduct.rTensorHomToHomRTensor σ L M N` is bijective
when the source `L` is finite projective over `R`, with arbitrary tensor factor
`N`. The equivalence `TensorProduct.rTensorHomEquivHomRTensor` has exactly this
canonical forward map and specializes to Mathlib's root-namespace
`rTensorHomEquivHomRTensor` when `σ` is the identity.

For a projective tensor factor `N` over `S`, the same canonical map is injective
with arbitrary source `L`. It is bijective if, in addition, either `L` is finite
over `R` or `N` is finite over `S`. Finite-source bijectivity thus needs neither
projectivity of `L` nor finite generation of `N`. The coefficient module `M` is
arbitrary throughout. For these semilinear comparisons, scalars are commutative
semirings, all additive structures are commutative monoids, and the carrier
universes are independent. The scalar homomorphism `σ` need not be injective or
surjective.

In the identity-scalar case, a flat tensor factor `N` gives injectivity when `L`
is finitely generated, over a commutative semiring. Over a commutative ring,
finite presentation of `L` gives bijectivity. The coefficient module `M` remains
arbitrary, and neither `L` nor `N` is required to be projective.

Naturality in all three modules holds without finiteness or projectivity.
The dual specialization is connected to Mathlib's `dualTensorHom` by the tensor
left unitor.

For a finite projective source, the proof specializes
`TensorProduct.semilinearHomTensorMap_bijective`, whose source scalars may be
noncommutative. Evaluation on a finite basis identifies that comparison with
`TensorProduct.piLeft`, and source naturality descends bijectivity along a
finite free projective splitting. No algebra structure, scalar extension, or
finiteness, projectivity or flatness of `S` over `R`, or of `N` over `S`, is
needed.

Projective-right injectivity follows by tensoring the jointly pair-separating
family of evaluation maps with a projective module. The surjectivity proofs
follow the free comparison and retract strategy of Mathlib's Contraction
formalization, generalized from duals to semilinear Hom. The finite-projective-right
comparison uses `TensorProduct.piScalarRight`. For
finite-source surjectivity, `TensorProduct.finsuppScalarRight` handles an
arbitrary free tensor factor, and the finite-source semilinear Finsupp comparison
supplies a lift before descent along a projective retraction. Neither proof
chooses a basis.

For the finite-presentation comparison with a flat tensor factor, Hom turns a
finite free presentation into a left-exact sequence. Flatness preserves this
sequence after tensoring. Naturality and the left-exact five lemma then reduce
the comparison to the existing finite-projective-source case.

## References

- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 17, for the
  linear tensor-Hom comparison. Here the scalars are generalized to commutative
  semirings and the Hom maps to semilinear maps.
- Mathlib's Contraction formalization by Oliver Nash and Antoine Labelle
  (`Mathlib.LinearAlgebra.Contraction`), for the finite-free and retract strategy.
- Mathlib's finite-presentation formalization by Andrew Yang
  (`Mathlib.Algebra.Module.FinitePresentation`), whose
  `Module.FinitePresentation.isBaseChange_map` uses the finite free presentation
  and left-exact comparison strategy.
- Mathlib's Hom left-exactness by Nailin Guan, flatness by Johan Commelin,
  Jujian Zhang and Yongle Hu, and module five lemma by Christian Merten
  (`Mathlib.LinearAlgebra.LeftExact`, `Mathlib.RingTheory.Flat.Basic` and
  `Mathlib.Algebra.FiveLemma`).
- Mathlib's tensor maps by Kenny Lau and Mario Carneiro, and tensor products with
  finite products by Judith Ludwig and Christian Merten.
- Mathlib's projective-module formalization by Kevin Buzzard and Antoine Labelle,
  and scalar extension and its Hom equivalence by Kim Morrison and Johan Commelin
  (`Mathlib.RingTheory.TensorProduct.Basic` and
  `Mathlib.RingTheory.TensorProduct.Finite`).
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

/-- Evaluation of the canonical tensor-Hom map at a source element is the right
tensor of the corresponding evaluation map. This holds for arbitrary tensors,
without finiteness or projectivity assumptions. -/
theorem rTensorHomToHomRTensor_apply_eq_rTensor
    (t : (L →ₛₗ[σ] M) ⊗[S] N) (l : L) :
    rTensorHomToHomRTensor σ L M N t l =
      (LinearMap.flip (LinearMap.id :
        (L →ₛₗ[σ] M) →ₗ[S] (L →ₛₗ[σ] M)) l).rTensor N t := by
  have h :
      (LinearMap.flip (LinearMap.id :
        (L →ₛₗ[σ] (M ⊗[S] N)) →ₗ[S] (L →ₛₗ[σ] (M ⊗[S] N))) l).comp
          (rTensorHomToHomRTensor σ L M N) =
        (LinearMap.flip (LinearMap.id :
          (L →ₛₗ[σ] M) →ₗ[S] (L →ₛₗ[σ] M)) l).rTensor N := by
    apply TensorProduct.ext'
    intro f n
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.id_apply,
      rTensorHomToHomRTensor_apply, LinearMap.rTensor_tmul]
  simpa only [LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.id_apply] using
    DFunLike.congr_fun h t

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

/-- The canonical semilinear tensor-Hom comparison is injective when its tensor
factor is projective. The source and Hom target are arbitrary; neither finite
generation of the tensor factor nor projectivity of the source is required. -/
theorem rTensorHomToHomRTensor_injective_of_projective_right
    [Module.Projective S N] :
    Function.Injective (rTensorHomToHomRTensor σ L M N) := by
  intro x y hxy
  apply (forall_map_id_right_apply_eq_iff_of_projective
    (R := S) (P := N) (B := fun _ : L => M)
    (fun l => LinearMap.flip (LinearMap.id :
      (L →ₛₗ[σ] M) →ₗ[S] (L →ₛₗ[σ] M)) l)
    (fun f g hfg => LinearMap.ext hfg) x y).mp
  intro l
  simpa only [← LinearMap.rTensor_def,
    ← rTensorHomToHomRTensor_apply_eq_rTensor] using
    congrArg (fun f : L →ₛₗ[σ] (M ⊗[S] N) => f l) hxy

private theorem rTensorHomToHomRTensor_fun_surjective
    (ι : Type uι) [Finite ι] :
    Function.Surjective (rTensorHomToHomRTensor σ L M (ι → S)) := by
  classical
  let := Fintype.ofFinite ι
  let eT := piScalarRight S S (L →ₛₗ[σ] M) ι
  let eM := piScalarRight S S M ι
  have hcoord (t : (L →ₛₗ[σ] M) ⊗[S] (ι → S)) (l : L) (i : ι) :
      eM (rTensorHomToHomRTensor σ L M (ι → S) t l) i = eT t i l := by
    induction t using TensorProduct.inductionOn with
    | tmul f n => simp [eM, eT]
    | add t u ht hu => simp [ht, hu]
  intro h
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
  refine ⟨rTensorHomToHomRTensor_injective_of_projective_right σ, ?_⟩
  obtain ⟨n, p, s, _, _, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective S N
  exact rTensorHomToHomRTensor_surjective_of_comp_eq_id_right σ s p hps
    (rTensorHomToHomRTensor_fun_surjective σ (Fin n))

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

/-- Tensoring semilinear Hom from a finitely generated source with a projective
module commutes with Hom: the canonical tensor-Hom map is bijective. Neither
projectivity of the source nor finite generation of the tensor factor is
required. -/
theorem rTensorHomToHomRTensor_bijective_of_finite_left_projective_right
    [Module.Finite R L] [Module.Projective S N] :
    Function.Bijective (rTensorHomToHomRTensor σ L M N) :=
  ⟨rTensorHomToHomRTensor_injective_of_projective_right σ,
    rTensorHomToHomRTensor_surjective_of_finite_left_projective_right σ⟩

section FiniteProjectiveLeft

variable [Module.Finite R L] [Module.Projective R L]

variable (L M N) in
/-- Tensoring semilinear Hom out of a finite projective source commutes with Hom.
The forward linear map is exactly `rTensorHomToHomRTensor σ L M N`. No condition
is imposed on the tensor factor `N` beyond its `S`-module structure.

This extends Mathlib's linear finite-projective-source tensor-Hom equivalence
(and the linear comparison in Chapter 17 of May's *A Concise Course in Algebraic
Topology*) to arbitrary scalar homomorphisms between commutative semirings. -/
noncomputable def rTensorHomEquivHomRTensor :
    (L →ₛₗ[σ] M) ⊗[S] N ≃ₗ[S] (L →ₛₗ[σ] (M ⊗[S] N)) :=
  LinearEquiv.ofBijective (rTensorHomToHomRTensor σ L M N) (by
    simpa only [semilinearHomTensorMap_eq_rTensorHomToHomRTensor] using
      (semilinearHomTensorMap_bijective (M := L) (N := M) (P := N) σ))

/-- The finite-projective-source equivalence has the canonical tensor-Hom map
as its forward linear map. -/
@[simp]
theorem rTensorHomEquivHomRTensor_toLinearMap :
    (rTensorHomEquivHomRTensor σ L M N).toLinearMap =
      rTensorHomToHomRTensor σ L M N :=
  rfl

/-- The finite-projective-source equivalence evaluates by the canonical
semilinear tensor-Hom comparison, on arbitrary tensors. -/
@[simp]
theorem rTensorHomEquivHomRTensor_apply (t : (L →ₛₗ[σ] M) ⊗[S] N) :
    rTensorHomEquivHomRTensor σ L M N t = rTensorHomToHomRTensor σ L M N t := by
  rw [← LinearEquiv.coe_toLinearMap, rTensorHomEquivHomRTensor_toLinearMap]

/-- On a pure tensor, the finite-projective-source equivalence tensors the
value of the semilinear map with the given element of the tensor factor. -/
theorem rTensorHomEquivHomRTensor_tmul (f : L →ₛₗ[σ] M) (n : N) (l : L) :
    rTensorHomEquivHomRTensor σ L M N (f ⊗ₜ[S] n) l = f l ⊗ₜ[S] n := by
  rw [rTensorHomEquivHomRTensor_apply, rTensorHomToHomRTensor_apply]

/-- The inverse finite-projective-source equivalence cancels the canonical
comparison on arbitrary tensors. -/
@[simp]
theorem rTensorHomEquivHomRTensor_symm_apply_apply (t : (L →ₛₗ[σ] M) ⊗[S] N) :
    (rTensorHomEquivHomRTensor σ L M N).symm (rTensorHomToHomRTensor σ L M N t) = t := by
  rw [← rTensorHomEquivHomRTensor_apply]
  exact LinearEquiv.symm_apply_apply _ _

/-- Applying the canonical comparison to the inverse equivalence recovers
any semilinear map into the tensor product. -/
@[simp]
theorem rTensorHomEquivHomRTensor_apply_symm_apply (f : L →ₛₗ[σ] (M ⊗[S] N)) :
    rTensorHomToHomRTensor σ L M N ((rTensorHomEquivHomRTensor σ L M N).symm f) = f := by
  rw [← rTensorHomEquivHomRTensor_apply]
  exact LinearEquiv.apply_symm_apply _ _

/-- For a finite projective source, the canonical semilinear tensor-Hom map is
bijective. The coefficient module and tensor factor are arbitrary `S`-modules.
This is the arbitrary-scalar-homomorphism version of Mathlib's
`rTensorHomEquivHomRTensor`, obtained by specializing the arbitrary-source
semilinear comparison. -/
theorem rTensorHomToHomRTensor_bijective_of_finite_projective_left :
    Function.Bijective (rTensorHomToHomRTensor σ L M N) := by
  rw [← rTensorHomEquivHomRTensor_toLinearMap]
  exact (rTensorHomEquivHomRTensor σ L M N).bijective

end FiniteProjectiveLeft

end Semilinear

section IdentityScalars

variable {R : Type uR} [CommSemiring R]
variable {L : Type uL} {M : Type uM} {N : Type uN}
variable [AddCommMonoid L] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R L] [Module R M] [Module R N]
variable [Module.Finite R L] [Module.Projective R L]

/-- For the identity scalar homomorphism, the semilinear tensor-Hom equivalence
is Mathlib's linear equivalence, over arbitrary commutative semirings and
additive commutative monoids, with only the source finite projective. -/
@[simp]
theorem rTensorHomEquivHomRTensor_id :
    rTensorHomEquivHomRTensor (RingHom.id R) L M N =
      _root_.rTensorHomEquivHomRTensor R L M N := by
  apply LinearEquiv.toLinearMap_injective
  rw [rTensorHomEquivHomRTensor_toLinearMap,
    _root_.rTensorHomEquivHomRTensor_toLinearMap]

end IdentityScalars

section FlatRight

/-- Over a commutative semiring, the canonical tensor-Hom comparison is injective
when its source is finitely generated and its tensor factor is flat. The Hom
target is arbitrary; neither the source nor tensor factor need be projective. -/
theorem rTensorHomToHomRTensor_injective_of_finite_left_flat_right
    {R : Type uR} [CommSemiring R]
    {L : Type uL} {M : Type uM} {N : Type uN}
    [AddCommMonoid L] [AddCommMonoid M] [AddCommMonoid N]
    [Module R L] [Module R M] [Module R N]
    [Module.Finite R L] [Module.Flat R N] :
    Function.Injective (rTensorHomToHomRTensor (RingHom.id R) L M N) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R L
  have hpre : Function.Injective (LinearMap.lcomp R M p) :=
    LinearMap.lcomp_injective_of_surjective (S := R) (N := M) p hp
  have htensor : Function.Injective ((LinearMap.lcomp R M p).rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := N) _ hpre
  have hcomp :
      (LinearMap.llcomp R (Fin n → R) M M (LinearMap.id : M →ₗ[R] M)).comp
        (LinearMap.lcompₛₗ R M (RingHom.id R) p) = LinearMap.lcomp R M p := by
    ext f l
    rfl
  have hnatural (t : (L →ₗ[R] M) ⊗[R] N) (l : Fin n → R) :
      rTensorHomToHomRTensor (RingHom.id R) (Fin n → R) M N
          ((LinearMap.lcomp R M p).rTensor N t) l =
        rTensorHomToHomRTensor (RingHom.id R) L M N t (p l) := by
    simpa only [hcomp, LinearMap.rTensor_def, map_id, LinearMap.id_apply] using
      rTensorHomToHomRTensor_natural (RingHom.id R) p
        (LinearMap.id : M →ₗ[R] M) (LinearMap.id : N →ₗ[R] N) t l
  intro x y hxy
  apply htensor
  apply
    (rTensorHomToHomRTensor_bijective_of_finite_projective_left
      (RingHom.id R) (L := Fin n → R) (M := M) (N := N)).1
  apply LinearMap.ext
  intro l
  rw [hnatural, hnatural, hxy]

/-- Over a commutative ring, tensoring Hom from a finitely presented source with a
flat module commutes with Hom: the canonical tensor-Hom comparison is bijective.
The Hom target is arbitrary, and no projectivity is required of the source or
tensor factor. The proof follows the finite-presentation/left-exact comparison
strategy of Mathlib's `Module.FinitePresentation.isBaseChange_map`, using flat
tensor exactness and
`LinearMap.bijective_of_bijective_of_injective_of_left_exact`. -/
theorem rTensorHomToHomRTensor_bijective_of_finitePresentation_left_flat_right
    {R : Type uR} [CommRing R]
    {L : Type uL} {M : Type uM} {N : Type uN}
    [AddCommMonoid L] [AddCommMonoid M] [AddCommMonoid N]
    [Module R L] [Module R M] [Module R N]
    [Module.FinitePresentation R L] [Module.Flat R N] :
    Function.Bijective (rTensorHomToHomRTensor (RingHom.id R) L M N) := by
  let : AddCommGroup L := Module.addCommMonoidToAddCommGroup R (M := L)
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R (M := M)
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R (M := N)
  obtain ⟨n, m, p, q, hp, hqp⟩ := Module.FinitePresentation.exists_fin' R L
  refine LinearMap.bijective_of_bijective_of_injective_of_left_exact
    (R := R)
    (M₁ := (L →ₗ[R] M) ⊗[R] N)
    (M₂ := ((Fin n → R) →ₗ[R] M) ⊗[R] N)
    (M₃ := ((Fin m → R) →ₗ[R] M) ⊗[R] N)
    (N₁ := L →ₗ[R] (M ⊗[R] N))
    (N₂ := (Fin n → R) →ₗ[R] (M ⊗[R] N))
    (N₃ := (Fin m → R) →ₗ[R] (M ⊗[R] N))
    ((LinearMap.lcomp R M p).rTensor N) ((LinearMap.lcomp R M q).rTensor N)
    (LinearMap.lcomp R (M ⊗[R] N) p) (LinearMap.lcomp R (M ⊗[R] N) q)
    (rTensorHomToHomRTensor (RingHom.id R) L M N)
    (rTensorHomToHomRTensor (RingHom.id R) (Fin n → R) M N)
    (rTensorHomToHomRTensor (RingHom.id R) (Fin m → R) M N) ?_ ?_
    (Module.Flat.rTensor_exact N
      (LinearMap.exact_lcomp_of_exact_of_surjective M hqp hp))
    (LinearMap.exact_lcomp_of_exact_of_surjective (M ⊗[R] N) hqp hp)
    (rTensorHomToHomRTensor_bijective_of_finite_projective_left
      (L := Fin n → R) (M := M) (N := N) (RingHom.id R))
    (rTensorHomToHomRTensor_bijective_of_finite_projective_left
      (L := Fin m → R) (M := M) (N := N) (RingHom.id R)).injective
    (Module.Flat.rTensor_preserves_injective_linearMap _
      (LinearMap.lcomp_injective_of_surjective p hp)) ?_
  · refine LinearMap.ext fun t ↦ LinearMap.ext fun l ↦ ?_
    have hcomp :
        (LinearMap.llcomp R (Fin n → R) M M (LinearMap.id : M →ₗ[R] M)).comp
            (LinearMap.lcompₛₗ R M (RingHom.id R) p) = LinearMap.lcomp R M p := by
      ext f x
      rfl
    simpa only [LinearMap.comp_apply, LinearMap.lcomp_apply, LinearMap.rTensor_def,
      hcomp, map_id, LinearMap.id_apply] using
      (rTensorHomToHomRTensor_natural (RingHom.id R) p
        (LinearMap.id : M →ₗ[R] M) (LinearMap.id : N →ₗ[R] N) t l).symm
  · refine LinearMap.ext fun t ↦ LinearMap.ext fun l ↦ ?_
    have hcomp :
        (LinearMap.llcomp R (Fin m → R) M M (LinearMap.id : M →ₗ[R] M)).comp
            (LinearMap.lcompₛₗ R M (RingHom.id R) q) = LinearMap.lcomp R M q := by
      ext f x
      rfl
    simpa only [LinearMap.comp_apply, LinearMap.lcomp_apply, LinearMap.rTensor_def,
      hcomp, map_id, LinearMap.id_apply] using
      (rTensorHomToHomRTensor_natural (RingHom.id R) q
        (LinearMap.id : M →ₗ[R] M) (LinearMap.id : N →ₗ[R] N) t l).symm
  · exact LinearMap.lcomp_injective_of_surjective (S := R) (N := M ⊗[R] N) p hp

end FlatRight

section BaseChange

variable (R : Type uR) (S : Type uS) (L : Type uL) (M : Type uM)
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [AddCommMonoid L] [AddCommMonoid M] [Module R L] [Module R M]

/-- The induced Hom base-change map is the identity-scalar tensor-Hom comparison,
conjugated by the tensor commutors and the scalar-extension Hom adjunction.
No finiteness or flatness is required.

The canonical components are Mathlib's tensor commutors, formalized by Kenny Lau
and Mario Carneiro, and `LinearMap.liftBaseChangeEquiv`, formalized by Kim Morrison
and Johan Commelin. -/
theorem _root_.LinearMap.liftBaseChange_baseChangeHom_eq :
    (LinearMap.liftBaseChange S (LinearMap.baseChangeHom R S L M)).restrictScalars R =
      ((LinearMap.liftBaseChangeEquiv S :
        (L →ₗ[R] S ⊗[R] M) ≃ₗ[S]
          (S ⊗[R] L →ₗ[S] S ⊗[R] M)).restrictScalars R).toLinearMap.comp
        ((LinearEquiv.congrRight (M := L) (TensorProduct.comm R M S)).toLinearMap.comp
          ((rTensorHomToHomRTensor (RingHom.id R) L M S).comp
            (TensorProduct.comm R S (L →ₗ[R] M)).toLinearMap)) := by
  apply TensorProduct.ext'
  intro s f
  apply AlgebraTensorModule.ext
  intro s' l
  simp [smul_tmul', mul_comm]

/-- The algebra-base-change condition for Hom is equivalent to bijectivity of the
canonical tensor-Hom comparison with the algebra as tensor factor. This equivalence
requires no finite presentation, projectivity or flatness.

The proof uses the canonical conjugacy
`LinearMap.liftBaseChange_baseChangeHom_eq` and Andrew Yang's Mathlib
`IsBaseChange.equiv` and `IsBaseChange.of_equiv`. -/
theorem isBaseChange_baseChangeHom_iff :
    IsBaseChange S (LinearMap.baseChangeHom R S L M) ↔
      Function.Bijective (rTensorHomToHomRTensor (RingHom.id R) L M S) := by
  have hbij :
      Function.Bijective
        ((LinearMap.liftBaseChange S (LinearMap.baseChangeHom R S L M)).restrictScalars R) ↔
      Function.Bijective (rTensorHomToHomRTensor (RingHom.id R) L M S) := by
    rw [LinearMap.liftBaseChange_baseChangeHom_eq]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe,
      EquivLike.comp_bijective, EquivLike.bijective_comp]
  constructor
  · intro h
    apply hbij.mp
    have he : h.equiv.toLinearMap =
        LinearMap.liftBaseChange S (LinearMap.baseChangeHom R S L M) := by
      apply AlgebraTensorModule.ext
      intro s f
      simp only [LinearEquiv.coe_coe, IsBaseChange.equiv_tmul,
        LinearMap.liftBaseChange_tmul]
    rw [← he]
    exact (h.equiv.restrictScalars R).bijective
  · intro h
    refine IsBaseChange.of_equiv
      (LinearEquiv.ofBijective
        (LinearMap.liftBaseChange S (LinearMap.baseChangeHom R S L M)) (hbij.mpr h)) ?_
    intro f
    exact LinearMap.liftBaseChange_one_tmul S _ f

end BaseChange

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
