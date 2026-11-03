/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.LinearAlgebra.Charpoly
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Commuting nilpotent perturbations of characteristic polynomials

The intrinsic characteristic polynomials of commuting endomorphisms of a finite
projective module differ by a nilpotent polynomial when the endomorphisms differ
by a nilpotent. Over a reduced coefficient ring they are equal.

The field argument uses the kernel of the difference and induction on its
nilpotence exponent. Scalar extension to the fraction fields of prime quotients
then shows that every coefficient of the polynomial difference is nilpotent.
No global rank, faithfulness, or nontriviality hypothesis is required.

## References

The field argument uses Mathlib's `Matrix.charpoly_fromBlocks_zero₂₁`. Scalar
extension uses the intrinsic characteristic-polynomial API in
`ProjectiveModules.LinearAlgebra.Charpoly`; nilpotence is detected in prime
quotients using Mathlib's ideal and polynomial APIs.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Module

/-- An invariant subspace gives an upper triangular matrix after choosing a
linear section of the quotient map. The section need not intertwine the
endomorphisms. -/
private theorem charpoly_eq_restrict_mul_quotient
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (f : Module.End K V) (U : Submodule K V)
    (hfU : ∀ x ∈ U, f x ∈ U) :
    f.charpoly = (f.restrict hfU).charpoly * (U.mapQ U f hfU).charpoly := by
  classical
  let fQ : Module.End K (V ⧸ U) := U.mapQ U f hfU
  have hfQ (x : V) : fQ (U.mkQ x) = U.mkQ (f x) :=
    LinearMap.congr_fun (U.mapQ_mkQ U (f := f) (h := hfU)) x
  let bU := Module.finBasis K U
  let bQ := Module.finBasis K (V ⧸ U)
  let s : (V ⧸ U) →ₗ[K] V :=
    bQ.constr K (fun i => (U.mkQ_surjective (bQ i)).choose)
  have hs (q : V ⧸ U) : U.mkQ (s q) = q := by
    have h : U.mkQ.comp s = LinearMap.id := by
      apply bQ.ext
      intro i
      simpa [s] using (U.mkQ_surjective (bQ i)).choose_spec
    exact LinearMap.congr_fun h q
  have hzero (x : V) : U.mkQ x = 0 ↔ x ∈ U := by
    change x ∈ LinearMap.ker U.mkQ ↔ x ∈ U
    rw [Submodule.ker_mkQ]
  have hU (x : U) : U.mkQ (x : V) = 0 :=
    (hzero _).mpr x.property
  let p : U × (V ⧸ U) →ₗ[K] V :=
    U.subtype.comp (LinearMap.fst K U (V ⧸ U)) +
      s.comp (LinearMap.snd K U (V ⧸ U))
  have hp_apply (x : U × (V ⧸ U)) : p x = (x.1 : V) + s x.2 := rfl
  have hp : Function.Bijective p := by
    constructor
    · intro x y hxy
      have hq : x.2 = y.2 := by
        simpa only [hp_apply, map_add, hU, hs, zero_add] using congrArg U.mkQ hxy
      apply Prod.ext
      · apply Subtype.ext
        change (x.1 : V) + s x.2 = (y.1 : V) + s y.2 at hxy
        rw [hq] at hxy
        exact add_right_cancel hxy
      · exact hq
    · intro x
      let u : U := ⟨x - s (U.mkQ x), by
        apply (hzero _).mp
        rw [map_sub, hs, sub_self]⟩
      refine ⟨(u, U.mkQ x), ?_⟩
      change x - s (U.mkQ x) + s (U.mkQ x) = x
      exact sub_add_cancel _ _
  let e : (U × (V ⧸ U)) ≃ₗ[K] V := LinearEquiv.ofBijective p hp
  have he (u : U) (q : V ⧸ U) : e (u, q) = (u : V) + s q := rfl
  let t : (V ⧸ U) →ₗ[K] U :=
    (f.comp s - s.comp fQ).codRestrict U (by
      intro q
      apply (hzero _).mp
      change U.mkQ (f (s q) - s (fQ q)) = 0
      rw [map_sub, ← hfQ, hs, hs, sub_self])
  have hconj (u : U) (q : V ⧸ U) :
      e.symm (f (e (u, q))) = ((f.restrict hfU) u + t q, fQ q) := by
    apply e.injective
    simp only [e.apply_symm_apply, he]
    change f ((u : V) + s q) =
      (f u + (f (s q) - s (fQ q))) + s (fQ q)
    rw [map_add]
    abel
  let b := (bU.prod bQ).map e
  have hmatrix : LinearMap.toMatrix b b f =
      Matrix.fromBlocks (LinearMap.toMatrix bU bU (f.restrict hfU))
        (LinearMap.toMatrix bQ bU t) 0 (LinearMap.toMatrix bQ bQ fQ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [LinearMap.toMatrix_apply, b, hconj]
  calc
    f.charpoly = (LinearMap.toMatrix b b f).charpoly := by
      rw [LinearMap.charpoly_toMatrix]
    _ = (Matrix.fromBlocks (LinearMap.toMatrix bU bU (f.restrict hfU))
        (LinearMap.toMatrix bQ bU t) 0 (LinearMap.toMatrix bQ bQ fQ)).charpoly := by
      rw [hmatrix]
    _ = (f.restrict hfU).charpoly * fQ.charpoly := by
      rw [Matrix.charpoly_fromBlocks_zero₂₁]
      simp only [LinearMap.charpoly_toMatrix]

/-- Over a field, pass to the kernel of the difference and lower the nilpotence
exponent on the quotient. The induction is uniform in the vector space. -/
private theorem charpoly_eq_of_commute_of_sub_pow_eq_zero
    {K : Type u} [Field K] (n : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module K V] [Module.Finite K V]
      (f g : Module.End K V), Commute f g → (f - g) ^ n = 0 →
        f.charpoly = g.charpoly := by
  induction n with
  | zero =>
    intro V _ _ _ f g _ hn
    have hfg : f = g := by
      ext x
      have hx : x = 0 := by
        simpa using LinearMap.congr_fun hn x
      simp [hx]
    rw [hfg]
  | succ n ih =>
    intro V _ _ _ f g hcomm hn
    let U : Submodule K V := LinearMap.ker (f - g)
    have hcomm_apply (x : V) : f (g x) = g (f x) :=
      LinearMap.congr_fun hcomm.eq x
    have hfU : ∀ x ∈ U, f x ∈ U := by
      intro x hx
      change (f - g) (f x) = 0
      change (f - g) x = 0 at hx
      calc
        (f - g) (f x) = f ((f - g) x) := by
          simp only [LinearMap.sub_apply, map_sub]
          rw [hcomm_apply]
        _ = 0 := by rw [hx, map_zero]
    have hgU : ∀ x ∈ U, g x ∈ U := by
      intro x hx
      change (f - g) (g x) = 0
      change (f - g) x = 0 at hx
      calc
        (f - g) (g x) = g ((f - g) x) := by
          simp only [LinearMap.sub_apply, map_sub]
          rw [hcomm_apply]
        _ = 0 := by rw [hx, map_zero]
    have hrestrict : f.restrict hfU = g.restrict hgU := by
      ext x
      have hx : f x - g x = 0 := x.property
      exact sub_eq_zero.mp hx
    let fQ : Module.End K (V ⧸ U) := U.mapQ U f hfU
    let gQ : Module.End K (V ⧸ U) := U.mapQ U g hgU
    have hfQ (x : V) : fQ (U.mkQ x) = U.mkQ (f x) :=
      LinearMap.congr_fun (U.mapQ_mkQ U (f := f) (h := hfU)) x
    have hgQ (x : V) : gQ (U.mkQ x) = U.mkQ (g x) :=
      LinearMap.congr_fun (U.mapQ_mkQ U (f := g) (h := hgU)) x
    have hcommQ : Commute fQ gQ := by
      change fQ * gQ = gQ * fQ
      apply LinearMap.ext
      intro x
      obtain ⟨x, rfl⟩ := U.mkQ_surjective x
      change fQ (gQ (U.mkQ x)) = gQ (fQ (U.mkQ x))
      rw [hgQ, hfQ, hfQ, hgQ, hcomm_apply]
    have hsubQ (x : V) : (fQ - gQ) (U.mkQ x) = U.mkQ ((f - g) x) := by
      rw [LinearMap.sub_apply, hfQ, hgQ, LinearMap.sub_apply, map_sub]
    have hpowQ (m : ℕ) (x : V) :
        ((fQ - gQ) ^ m) (U.mkQ x) = U.mkQ (((f - g) ^ m) x) := by
      induction m with
      | zero => simp
      | succ m hm =>
        rw [pow_succ', pow_succ']
        change (fQ - gQ) (((fQ - gQ) ^ m) (U.mkQ x)) =
          U.mkQ ((f - g) (((f - g) ^ m) x))
        rw [hm, hsubQ]
    have hnQ : (fQ - gQ) ^ n = 0 := by
      apply LinearMap.ext
      intro x
      obtain ⟨x, rfl⟩ := U.mkQ_surjective x
      rw [hpowQ]
      have hx : ((f - g) ^ n) x ∈ U := by
        change (f - g) (((f - g) ^ n) x) = 0
        simpa only [pow_succ', Module.End.mul_apply, LinearMap.zero_apply] using
          LinearMap.congr_fun hn x
      change ((f - g) ^ n) x ∈ LinearMap.ker U.mkQ
      rw [Submodule.ker_mkQ]
      exact hx
    have hquotient : fQ.charpoly = gQ.charpoly := ih fQ gQ hcommQ hnQ
    calc
      f.charpoly = (f.restrict hfU).charpoly * fQ.charpoly :=
        charpoly_eq_restrict_mul_quotient f U hfU
      _ = (g.restrict hgU).charpoly * gQ.charpoly := by
        rw [hrestrict, hquotient]
      _ = g.charpoly := (charpoly_eq_restrict_mul_quotient g U hgU).symm

variable (R : Type u) [CommRing R]
variable (P : Type v) [AddCommGroup P] [Module R P]
variable [Module.Finite R P] [Module.Projective R P]

/-- Compare the two characteristic polynomials after scalar extension to an
arbitrary field, independently of any construction of that field. -/
private theorem map_charpoly_eq_of_commute_of_isNilpotent_sub
    (f g : Module.End R P) (hcomm : Commute f g) (hnil : IsNilpotent (f - g))
    (K : Type w) [Field K] [Algebra R K] :
    Polynomial.map (algebraMap R K) (charpoly R P f) =
      Polynomial.map (algebraMap R K) (charpoly R P g) := by
  have hcommK : Commute (f.baseChange K) (g.baseChange K) := by
    change (f.baseChange K).comp (g.baseChange K) =
      (g.baseChange K).comp (f.baseChange K)
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    exact congrArg (fun h : Module.End R P => h.baseChange K) hcomm.eq
  obtain ⟨n, hn⟩ := hnil
  have hnK : (f.baseChange K - g.baseChange K) ^ n = 0 := by
    rw [← LinearMap.baseChange_sub, ← LinearMap.baseChange_pow, hn,
      LinearMap.baseChange_zero]
  rw [← charpoly_baseChange R P f K, ← charpoly_baseChange R P g K,
    charpoly_eq_charpoly, charpoly_eq_charpoly]
  exact charpoly_eq_of_commute_of_sub_pow_eq_zero n _ _ hcommK hnK

/-- Commuting endomorphisms of a finite projective module whose difference is
nilpotent have characteristic polynomials with nilpotent difference. -/
theorem isNilpotent_charpoly_sub_charpoly_of_commute
    (f g : Module.End R P) (hcomm : Commute f g) (hnil : IsNilpotent (f - g)) :
    IsNilpotent (charpoly R P f - charpoly R P g) := by
  classical
  apply Polynomial.isNilpotent_iff.mpr
  intro i
  let c := (charpoly R P f - charpoly R P g).coeff i
  have hc : c ∈ (⊥ : Ideal R).radical := by
    rw [Ideal.radical_eq_sInf]
    apply Ideal.mem_sInf.mpr
    intro I hI
    simp only [Set.mem_ofPred_eq] at hI
    have : I.IsPrime := by tauto
    let A := R ⧸ I
    let K := FractionRing A
    -- Fix the field structure before constructing the composite algebra.
    let : Field K := inferInstance
    let : Algebra R K :=
      ((algebraMap A K).comp (Ideal.Quotient.mk I)).toAlgebra
    have heq := map_charpoly_eq_of_commute_of_isNilpotent_sub R P f g hcomm hnil K
    have hzero : Polynomial.map (algebraMap R K)
        (charpoly R P f - charpoly R P g) = 0 := by
      rw [Polynomial.map_sub, heq, sub_self]
    have hcK : algebraMap R K c = 0 := by
      simpa [c] using congrArg (fun q : Polynomial K => q.coeff i) hzero
    have hcA : Ideal.Quotient.mk I c = 0 := by
      apply IsFractionRing.injective A K
      change algebraMap R K c = algebraMap A K 0
      simpa only [map_zero] using hcK
    exact Ideal.Quotient.eq_zero_iff_mem.mp hcA
  obtain ⟨n, hn⟩ := hc
  exact ⟨n, by simpa [c] using hn⟩

/-- Over a reduced commutative ring, commuting endomorphisms of a finite
projective module have equal characteristic polynomials if their difference is
nilpotent. -/
theorem charpoly_eq_charpoly_of_commute_of_isNilpotent_sub [IsReduced R]
    (f g : Module.End R P) (hcomm : Commute f g) (hnil : IsNilpotent (f - g)) :
    charpoly R P f = charpoly R P g := by
  apply sub_eq_zero.mp
  ext i
  simpa only [Polynomial.coeff_zero] using
    ((Polynomial.isNilpotent_iff.mp
      (isNilpotent_charpoly_sub_charpoly_of_commute R P f g hcomm hnil)) i).eq_zero

end Module
