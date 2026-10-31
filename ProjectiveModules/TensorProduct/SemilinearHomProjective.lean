/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Finiteness.Projective
public import ProjectiveModules.LinearMap.ChangeOfScalars
public import ProjectiveModules.TensorProduct.SemilinearHom
public import ProjectiveModules.TensorProduct.SemilinearHomNaturality

/-!
# Tensoring semilinear Hom from a finite projective module

`TensorProduct.semilinearHomTensorMap_bijective` states that tensoring semilinear
Hom out of a finite projective source commutes with Hom. The source scalars form
an arbitrary semiring, the target scalars form a commutative semiring, and the
scalar homomorphism is arbitrary. The Hom target and tensor factor are arbitrary
modules over the target scalars.

For a source with a finite basis, evaluation on the basis identifies the
comparison with `TensorProduct.piLeft`. A finite projective source is a retract
of a finite free module, and source naturality descends bijectivity along this
retraction. The finite free cover comes from finite generation, without any
nontriviality assumption on the source semiring.

## References

- Mathlib's projective-module and finiteness formalizations, for the finite free
  cover and projective splitting (`Mathlib.RingTheory.Finiteness.Projective`).
- Mathlib's basis construction of linear maps and tensor products with finite
  products (`Mathlib.LinearAlgebra.Basis.Defs` and
  `Mathlib.LinearAlgebra.TensorProduct.Pi`).
- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 17, for the linear
  tensor-Hom comparison. Here the source semiring need not be commutative and
  the Hom maps are semilinear.
-/

@[expose] public section

universe uR uS uM uN uP uι

namespace TensorProduct

variable {R : Type uR} {S : Type uS}
variable [Semiring R] [CommSemiring S]
variable (σ : R →+* S)
variable {M : Type uM} {N : Type uN} {P : Type uP}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module S N] [Module S P]

private noncomputable def semilinearHomBasisEquiv
    {ι : Type uι} (b : Module.Basis ι R M) :
    (M →ₛₗ[σ] N) ≃ₗ[S] (ι → N) := by
  letI : Module R N := Module.compHom N σ
  letI : SMulCommClass R S N := SMul.comp.smulCommClass (α := N) (β := S) σ
  exact (LinearMap.semilinearCompHomEquiv S σ).trans (b.constr S).symm

private theorem semilinearHomBasisEquiv_apply
    {ι : Type uι} (b : Module.Basis ι R M) (f : M →ₛₗ[σ] N) (i : ι) :
    semilinearHomBasisEquiv σ b f i = f (b i) := by
  simp [semilinearHomBasisEquiv, LinearMap.semilinearCompHomEquiv_apply]

private theorem semilinearHomTensorMap_bijective_of_basis
    {ι : Type uι} [Finite ι] (b : Module.Basis ι R M) :
    Function.Bijective (semilinearHomTensorMap (M := M) (N := N) (P := P) σ) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let eN := semilinearHomBasisEquiv (N := N) σ b
  let eQ := semilinearHomBasisEquiv (N := N ⊗[S] P) σ b
  let ePi := TensorProduct.piLeft S P (fun _ : ι => N)
  have hcomp :
      eQ.toLinearMap.comp (semilinearHomTensorMap σ) =
        ePi.toLinearMap.comp (eN.rTensor P).toLinearMap := by
    apply TensorProduct.ext'
    intro f p
    funext i
    simp [eN, eQ, ePi, semilinearHomBasisEquiv_apply, TensorProduct.piLeft]
  have hbij : Function.Bijective
      (eQ.toLinearMap.comp (semilinearHomTensorMap σ)) := by
    rw [hcomp]
    exact ePi.bijective.comp (eN.rTensor P).bijective
  simpa only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective]
    using hbij

/-- Tensoring semilinear Hom out of a finite projective source commutes with Hom.
The scalar homomorphism is arbitrary, the source semiring need not be
commutative, and no finiteness, projectivity or flatness is required of either
the Hom target or the tensor factor. This extends the linear tensor-Hom
comparison in Chapter 17 of May's *A Concise Course in Algebraic Topology*. -/
theorem semilinearHomTensorMap_bijective
    [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (semilinearHomTensorMap (M := M) (N := N) (P := P) σ) := by
  obtain ⟨n, p, s, _, _, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hfree := semilinearHomTensorMap_bijective_of_basis
    (N := N) (P := P) σ (Pi.basisFun R (Fin n))
  have hleft :
      (LinearMap.lcompₛₗ S N σ s).comp (LinearMap.lcompₛₗ S N σ p) =
        LinearMap.id := by
    ext f m
    exact congrArg f (DFunLike.congr_fun hps m)
  have hinj : Function.Injective ((LinearMap.lcompₛₗ S N σ p).rTensor P) := by
    apply LinearMap.injective_of_comp_eq_id _ ((LinearMap.lcompₛₗ S N σ s).rTensor P)
    rw [← LinearMap.rTensor_comp, hleft, LinearMap.rTensor_id]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply hinj
    apply hfree.1
    ext v
    rw [semilinearHomTensorMap_natural_source_apply,
      semilinearHomTensorMap_natural_source_apply, hxy]
  · intro f
    obtain ⟨t, ht⟩ := hfree.2 ((LinearMap.lcompₛₗ S (N ⊗[S] P) σ p) f)
    refine ⟨(LinearMap.lcompₛₗ S N σ s).rTensor P t, ?_⟩
    ext m
    rw [semilinearHomTensorMap_natural_source_apply, ht]
    exact congrArg f (DFunLike.congr_fun hps m)

end TensorProduct
