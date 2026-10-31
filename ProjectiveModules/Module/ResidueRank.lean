/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Residue rank and base change

For commutative rings `R` and `S`, a ring homomorphism `f : R →+* S`, an arbitrary
`R`-module `M`, and any prime `q` of `S`,
`Module.lift_rank_residueField_tensor_baseChange` identifies the cardinal ranks of
`κ(q) ⊗[S] (S ⊗[R] M)` over `κ(q)` and
`κ(f⁻¹(q)) ⊗[R] M` over `κ(f⁻¹(q))`. Here `κ` denotes the residue field and
`f⁻¹(q)` is the contracted prime. The cardinals are lifted to a common universe, allowing
the rings and module to lie in independent universes. The extension `S ⊗[R] M` uses the
algebra structure on `S` associated to `f`.

The fibres may be infinite-dimensional. No finite-generation, flatness or projectivity
condition on `M`, injectivity condition on `f`, or nontriviality condition on the rings is
required. The maximal-ideal quotient comparison for an algebra identifies its maximal
fibre rank with the residue rank at the contracted prime, which need not be maximal.

The rank and tensor-product constructions use Mathlib's scalar-extension API.
-/

@[expose] public section

universe uR uS v vM

open scoped TensorProduct

namespace Module

/-- Cardinal dimension of a maximal fibre is preserved by base change, after lifting the
cardinals to a common universe. The coefficient field on the right is the residue field at the
contraction of the maximal ideal; the contraction need not itself be maximal. -/
theorem lift_rank_quotient_baseChange
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
    {P : Type v} [AddCommMonoid P] [Module R P]
    (m : Ideal S) [m.IsMaximal] :
    Cardinal.lift.{uR}
        (Module.rank (S ⧸ m) ((S ⧸ m) ⊗[S] (S ⊗[R] P))) =
      Cardinal.lift.{uS}
        (Module.rank (m.under R).ResidueField
          ((m.under R).ResidueField ⊗[R] P)) := by
  let K := S ⧸ m
  let k := (m.under R).ResidueField
  let : Field K := Ideal.Quotient.field m
  let f : R →ₐ[R] K := Algebra.ofId R K
  have hf (r : R) : f r = 0 ↔ r ∈ m.under R := by
    rw [Ideal.mem_under]
    change algebraMap R K r = 0 ↔ algebraMap R S r ∈ m
    rw [← Ideal.Quotient.mk_comp_algebraMap (R₁ := R) m]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hf₁ : m.under R ≤ RingHom.ker f := by
    intro r hr
    change f r = 0
    exact (hf r).mpr hr
  have hf₂ : (m.under R).primeCompl ≤ (IsUnit.submonoid K).comap f := by
    intro r hr
    change IsUnit (f r)
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact hr ((hf r).mp hz)
  -- The canonical residue-field map supplies the intermediate scalar action and tower.
  let β : k →ₐ[R] K := Ideal.ResidueField.liftₐ (m.under R) f hf₁ hf₂
  let : Algebra k K := RingHom.toAlgebra β.toRingHom
  let : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R K r = β (algebraMap R k r)
    exact (congrArg (fun g : R →+* K => g r) β.comp_algebraMap).symm
  have hS :
      Module.rank K (K ⊗[S] (S ⊗[R] P)) = Module.rank K (K ⊗[R] P) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S K K P).rank_eq
  have hk :
      Module.rank K (K ⊗[k] (k ⊗[R] P)) =
        Cardinal.lift.{uR} (Module.rank K (K ⊗[R] P)) := by
    calc
      Module.rank K (K ⊗[k] (k ⊗[R] P)) =
          Cardinal.lift.{max uS v} (Module.rank K (K ⊗[k] (k ⊗[R] P))) :=
        (Cardinal.lift_id'.{max uS v, uR} _).symm
      _ = Cardinal.lift.{max (max uR uS) v} (Module.rank K (K ⊗[R] P)) :=
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R k K K P).lift_rank_eq
      _ = Cardinal.lift.{uR} (Module.rank K (K ⊗[R] P)) :=
        congrFun (Cardinal.lift_umax.{max uS v, uR}) _
  let : AddCommGroup (k ⊗[R] P) := TensorProduct.addCommGroup
  let : Module.Free k (k ⊗[R] P) := Module.Free.of_divisionRing k (k ⊗[R] P)
  calc
    Cardinal.lift.{uR} (Module.rank K (K ⊗[S] (S ⊗[R] P))) =
        Cardinal.lift.{uR} (Module.rank K (K ⊗[R] P)) := congrArg Cardinal.lift hS
    _ = Module.rank K (K ⊗[k] (k ⊗[R] P)) := hk.symm
    _ = Cardinal.lift.{uS} (Module.rank k (k ⊗[R] P)) :=
      Module.rank_baseChange

/-- Cardinal dimension of a prime fibre is preserved by scalar extension along a ring
homomorphism, after lifting to a common universe. The module and the prime are arbitrary.
The proof combines Mathlib's scalar-extension rank formula and tensor cancellation with
the maximal-fibre comparison. -/
theorem lift_rank_residueField_tensor_baseChange
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (f : R →+* S) {M : Type vM} [AddCommMonoid M] [Module R M]
    (q : PrimeSpectrum S) :
    Cardinal.lift.{uR}
      (Module.rank q.asIdeal.ResidueField
        (@TensorProduct S _ q.asIdeal.ResidueField
          (@TensorProduct R _ S M _ _ (@Algebra.toModule R S _ _ f.toAlgebra) _)
          _ _ _
          (@TensorProduct.leftModule R S _ _ S M _ _ _
            (@Algebra.toModule R S _ _ f.toAlgebra) _
            (@Algebra.to_smulCommClass R S _ _ f.toAlgebra)))) =
      Cardinal.lift.{uS}
        (Module.rank (PrimeSpectrum.comap f q).asIdeal.ResidueField
          ((PrimeSpectrum.comap f q).asIdeal.ResidueField ⊗[R] M)) := by
  let : Algebra R S := f.toAlgebra
  let K := q.asIdeal.ResidueField
  let : Algebra R K := ((algebraMap S K).comp f).toAlgebra
  let : Module R K := Algebra.toModule
  let : IsScalarTower R S K :=
    IsScalarTower.of_algebraMap_eq' (by simp only [RingHom.algebraMap_toAlgebra])
  let : (⊥ : Ideal K).IsMaximal := Ideal.bot_isMaximal
  let : Field (K ⧸ (⊥ : Ideal K)) := Ideal.Quotient.field _
  -- The tensor action uses the canonical module of the composite R → S → K.
  let : Module K (K ⊗[R] M) :=
    @TensorProduct.leftModule R K _ _ K M _ _ _
      (@Algebra.toModule R K _ _ ((algebraMap S K).comp f).toAlgebra) _
      (@Algebra.to_smulCommClass R K _ _ ((algebraMap S K).comp f).toAlgebra)
  let : Module.Free K (K ⊗[R] M) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace K _)
  have hcontract : (⊥ : Ideal K).under R = (PrimeSpectrum.comap f q).asIdeal := by
    rw [Ideal.under_def, RingHom.algebraMap_toAlgebra, ← Ideal.comap_comap,
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField,
      PrimeSpectrum.comap_asIdeal]
  have hrank :
      Module.rank (K ⧸ (⊥ : Ideal K)) ((K ⧸ (⊥ : Ideal K)) ⊗[K] (K ⊗[R] M)) =
        Module.rank K (K ⊗[R] M) := by
    simpa only [← Cardinal.lift_umax, Cardinal.lift_id] using
      (Module.rank_baseChange (R := K ⧸ (⊥ : Ideal K)) (S := K) (M' := K ⊗[R] M))
  have hrank_congr (p p' : Ideal R) [p.IsPrime] [p'.IsPrime] (h : p = p') :
      Module.rank p.ResidueField (p.ResidueField ⊗[R] M) =
        Module.rank p'.ResidueField (p'.ResidueField ⊗[R] M) := by
    subst p'
    rfl
  have hbase := lift_rank_quotient_baseChange
    (R := R) (S := K) (P := M) (⊥ : Ideal K)
  rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R S K K M).rank_eq]
  calc
    Cardinal.lift.{uR} (Module.rank K (K ⊗[R] M)) =
        Cardinal.lift.{uR}
          (Module.rank (K ⧸ (⊥ : Ideal K))
            ((K ⧸ (⊥ : Ideal K)) ⊗[K] (K ⊗[R] M))) :=
      congrArg Cardinal.lift.{uR} hrank.symm
    _ = _ := hbase.trans (congrArg Cardinal.lift.{uS} (hrank_congr _ _ hcontract))

end Module
