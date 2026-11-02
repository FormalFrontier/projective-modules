/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine
public import ProjectiveModules.ExteriorPower.Top
import ProjectiveModules.ExteriorPower.BaseChange
import ProjectiveModules.ExteriorPower.ProdPairing
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Endomorphisms of determinant lines

An endomorphism of a finite projective module acts on its determinant line by
acting on the top exterior power on each stalk-rank fiber. The determinant is
the unique scalar inducing this action on the invertible determinant line.
The stalk rank may vary, and the coefficient ring need not be nontrivial.
An attained rank-zero fiber contributes its degree-zero exterior action.
Intertwining linear equivalences preserve the scalar determinant, so it is
invariant under conjugation.

The construction reuses `Module.DeterminantLine` and its component interface,
`Module.Invertible.toModuleEndRingEquiv`, and Mathlib's exterior-power and
scalar-extension maps. The comparison with the conditional exterior-power
determinant uses the top degree, not merely an invertible exterior power.
The finite-free comparison uses the top exterior-power interface in
`ProjectiveModules.ExteriorPower.Top`. For factors of constant stalk rank,
`Module.determinant_prodMap_of_rankAtStalk_eq` gives the product formula using
the ordered top exterior-product pairing.

## References

For the determinant of a finite projective module, see C. A. Weibel,
*The K-book: An Introduction to Algebraic K-theory*.
The determinant-line, conditional exterior-power determinant, and
invertible-module scalar-equivalence formalizations are the existing
ProjectiveModules interfaces; no new rank decomposition is used here.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w

namespace Module

variable (R : Type u) [CommRing R]

section FiniteProjective

variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

namespace DeterminantLine

/-- The action on a determinant line obtained by taking the top exterior-power
map of the scalar-extended endomorphism on every rank fiber. -/
def map (f : Module.End R P) : Module.End R (DeterminantLine R P) where
  toFun x := ofComponents R P (fun i ↦
    exteriorPower.map (rankFiberRank R P i) (f.baseChange (rankFiberRing R P i))
      (component R P i x))
  map_add' x y := by
    apply DeterminantLine.ext
    intro i
    simp only [component_ofComponents, component_add, map_add]
  map_smul' r x := by
    apply DeterminantLine.ext
    intro i
    simp only [component_ofComponents, component_smul, map_smul]
    rfl

/-- On each rank fiber, the determinant-line action is the exterior-power
map in that fiber's top degree. -/
@[simp] theorem component_map (f : Module.End R P) (i : rankFiberIndex R P)
    (x : DeterminantLine R P) :
    component R P i (map R P f x) =
      exteriorPower.map (rankFiberRank R P i) (f.baseChange (rankFiberRing R P i))
        (component R P i x) :=
  rfl

/-- The canonical determinant-line equivalence intertwines the induced actions
of intertwined endomorphisms. -/
theorem congr_map (Q : Type w) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q]
    (e : P ≃ₗ[R] Q) (f : Module.End R P) (g : Module.End R Q)
    (h : e.toLinearMap.comp f = g.comp e.toLinearMap) (x : DeterminantLine R P) :
    congr R P Q e (map R P f x) = map R Q g (congr R P Q e x) := by
  exact congr_naturality R P Q e f g h x

/-- The identity endomorphism acts identically on the determinant line. -/
@[simp] theorem map_id :
    map R P (LinearMap.id : Module.End R P) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply DeterminantLine.ext
  intro i
  simp only [component_map, LinearMap.baseChange_id, exteriorPower.map_id,
    LinearMap.id_apply]

/-- The determinant-line action respects composition. -/
theorem map_comp (f g : Module.End R P) :
    map R P (f.comp g) = (map R P f).comp (map R P g) := by
  apply LinearMap.ext
  intro x
  apply DeterminantLine.ext
  intro i
  simp only [component_map, LinearMap.baseChange_comp, exteriorPower.map_comp,
    LinearMap.comp_apply]

/-- The determinant-line action as a monoid homomorphism on all
endomorphisms. -/
def mapEndomorphismMonoidHom :
    Module.End R P →* Module.End R (DeterminantLine R P) where
  toFun := map R P
  map_one' := by
    change map R P (LinearMap.id : Module.End R P) = LinearMap.id
    exact map_id R P
  map_mul' f g := by
    simpa only [Module.End.mul_eq_comp] using map_comp R P f g

/-- The endomorphism monoid homomorphism evaluates to the determinant-line
map. -/
@[simp] theorem mapEndomorphismMonoidHom_apply (f : Module.End R P) :
    mapEndomorphismMonoidHom R P f = map R P f :=
  rfl

end DeterminantLine

private def determinantLineScalarEquiv : R ≃+* Module.End R (DeterminantLine R P) := by
  letI := determinantLine_invertible R P
  exact Module.Invertible.toModuleEndRingEquiv R (DeterminantLine R P)

/-- The scalar determinant of an endomorphism of a finite projective module.
It is the scalar of the induced action on the invertible determinant line;
no global constant-rank or freeness hypothesis is imposed. -/
def determinant : Module.End R P →* R := by
  letI := determinantLine_invertible R P
  exact (Module.Invertible.toModuleEndRingEquiv R (DeterminantLine R P)).symm.toMonoidHom.comp
    (DeterminantLine.mapEndomorphismMonoidHom R P)

namespace DeterminantLine

/-- The induced determinant-line endomorphism is multiplication by the
scalar determinant. -/
theorem map_eq_smul_determinant (f : Module.End R P) (x : DeterminantLine R P) :
    map R P f x = determinant R P f • x := by
  let e := determinantLineScalarEquiv R P
  change map R P f x = e (e.symm (map R P f)) x
  exact DFunLike.congr_fun (e.apply_symm_apply (map R P f)).symm x

/-- The top exterior-power action on a rank fiber is multiplication by the
corresponding component of the scalar determinant. -/
theorem component_map_eq_smul_determinant (f : Module.End R P)
    (i : rankFiberIndex R P) (x : DeterminantLine R P) :
    exteriorPower.map (rankFiberRank R P i) (f.baseChange (rankFiberRing R P i))
        (component R P i x) =
      rankFiberRingEquiv R P (determinant R P f) i • component R P i x := by
  rw [← component_map, map_eq_smul_determinant, component_smul]

/-- On every element of the top exterior power of a rank fiber, the induced
endomorphism is multiplication by the image of the scalar determinant in the
rank-fiber ring. -/
theorem rankFiber_map_eq_smul_determinant (f : Module.End R P)
    (i : rankFiberIndex R P)
    (y : ⋀[rankFiberRing R P i]^(rankFiberRank R P i) (rankFiberModule R P i)) :
    exteriorPower.map (rankFiberRank R P i) (f.baseChange (rankFiberRing R P i)) y =
      algebraMap R (rankFiberRing R P i) (determinant R P f) • y := by
  classical
  have hscalar : rankFiberRingEquiv R P (determinant R P f) i =
      algebraMap R (rankFiberRing R P i) (determinant R P f) := by
    simpa only [Algebra.algebraMap_self_apply, Pi.algebraMap_apply] using
      congrFun ((rankFiberRingEquiv R P).commutes (determinant R P f)) i
  simpa only [component_ofComponents, Pi.single_eq_same, hscalar] using
    component_map_eq_smul_determinant R P f i (ofComponents R P (Pi.single i y))

end DeterminantLine

/-- A scalar is the determinant exactly when it induces the determinant-line
action. -/
theorem determinant_eq_iff_map_eq_smul (f : Module.End R P) (r : R) :
    determinant R P f = r ↔
      ∀ x : DeterminantLine R P, DeterminantLine.map R P f x = r • x := by
  constructor
  · rintro rfl x
    exact DeterminantLine.map_eq_smul_determinant R P f x
  · intro h
    let e := determinantLineScalarEquiv R P
    apply e.injective
    change e (e.symm (DeterminantLine.map R P f)) = e r
    rw [e.apply_symm_apply]
    apply LinearMap.ext
    intro x
    exact h x

/-- Endomorphisms intertwined by a linear equivalence have equal scalar
determinants. -/
theorem determinant_eq_of_intertwining (Q : Type w) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q]
    (e : P ≃ₗ[R] Q) (f : Module.End R P) (g : Module.End R Q)
    (h : e.toLinearMap.comp f = g.comp e.toLinearMap) :
    determinant R P f = determinant R Q g := by
  apply (determinant_eq_iff_map_eq_smul R P f (determinant R Q g)).2
  intro x
  apply (DeterminantLine.congr R P Q e).injective
  rw [DeterminantLine.congr_map R P Q e f g h,
    DeterminantLine.map_eq_smul_determinant, LinearEquiv.map_smul]

/-- Conjugating an endomorphism by a linear equivalence preserves its scalar
determinant. -/
@[simp] theorem determinant_conj (Q : Type w) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q]
    (e : P ≃ₗ[R] Q) (f : Module.End R P) :
    determinant R Q (e.conj f) = determinant R P f := by
  symm
  apply determinant_eq_of_intertwining R P Q e f (e.conj f)
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]

/-- The determinant of the identity endomorphism is one. -/
@[simp] theorem determinant_id :
    determinant R P (LinearMap.id : Module.End R P) = 1 := by
  exact (determinant R P).map_one

/-- Determinants multiply under composition of arbitrary endomorphisms. -/
theorem determinant_comp (f g : Module.End R P) :
    determinant R P (f.comp g) = determinant R P f * determinant R P g := by
  simpa only [Module.End.mul_eq_comp] using (determinant R P).map_mul f g

/-- For constant stalk rank `n`, the scalar determinant agrees with the
conditional determinant of the `n`th exterior power. Its invertibility is
supplied by the top-degree rank hypothesis. -/
theorem determinant_eq_exteriorPower_determinant (n : ℕ)
    (h : rankAtStalk (R := R) P = fun _ ↦ n) (f : Module.End R P) :
    determinant R P f =
      @exteriorPower.determinant R _ P _ _ n
        (exteriorPower.invertible_of_rankAtStalk_eq n h) f := by
  let := exteriorPower.invertible_of_rankAtStalk_eq n h
  apply (determinant_eq_iff_map_eq_smul R P f _).2
  intro x
  apply DeterminantLine.ext
  intro i
  rw [DeterminantLine.component_map, DeterminantLine.component_smul]
  have hscalar : ∀ r : R,
      rankFiberRingEquiv R P r i = algebraMap R (rankFiberRing R P i) r := by
    intro r
    simpa only [Algebra.algebraMap_self_apply, Pi.algebraMap_apply] using
      congrFun ((rankFiberRingEquiv R P).commutes r) i
  rw [hscalar]
  have hi : rankFiberRank R P i = n :=
    rankFiberRank_eq_of_rankAtStalk_eq R P i (fun p ↦ congrFun h p)
  cases hi
  exact exteriorPower.map_baseChange_eq_smul _ f _
    (exteriorPower.map_eq_smul_determinant R P _ f)
    (DeterminantLine.component R P i x)

/-- The scalar determinant of a product endomorphism is the product of the scalar
determinants when both finite projective factors have constant stalk rank.
The ordered top exterior-product pairing places `P` before `Q`; the maps need
not be invertible, and the ring need not be nontrivial. -/
theorem determinant_prodMap_of_rankAtStalk_eq
    (Q : Type w) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q]
    {n m : ℕ}
    (hP : ∀ p : PrimeSpectrum R, rankAtStalk (R := R) P p = n)
    (hQ : ∀ p : PrimeSpectrum R, rankAtStalk (R := R) Q p = m)
    (f : Module.End R P) (g : Module.End R Q) :
    determinant R (P × Q) (f.prodMap g) = determinant R P f * determinant R Q g := by
  have hP' : rankAtStalk (R := R) P = fun _ ↦ n := funext hP
  have hQ' : rankAtStalk (R := R) Q = fun _ ↦ m := funext hQ
  have hPQ : rankAtStalk (R := R) (P × Q) = fun _ ↦ n + m := by
    ext p
    simp only [rankAtStalk_prod, Pi.add_apply, hP, hQ]
  let := exteriorPower.invertible_of_rankAtStalk_eq n hP'
  let := exteriorPower.invertible_of_rankAtStalk_eq m hQ'
  let := exteriorPower.invertible_of_rankAtStalk_eq (n + m) hPQ
  rw [determinant_eq_exteriorPower_determinant R (P × Q) (n + m) hPQ,
    determinant_eq_exteriorPower_determinant R P n hP',
    determinant_eq_exteriorPower_determinant R Q m hQ']
  apply (exteriorPower.determinant_eq_iff_map_eq_smul R (P × Q) (n + m) _ _).2
  have htensor :
      TensorProduct.map (exteriorPower.map n f) (exteriorPower.map m g) =
        (exteriorPower.determinant R P n f * exteriorPower.determinant R Q m g) •
          (LinearMap.id : Module.End R ((⋀[R]^n P) ⊗[R] (⋀[R]^m Q))) := by
    apply TensorProduct.ext'
    intro a b
    simp only [TensorProduct.map_tmul, exteriorPower.map_eq_smul_determinant,
      LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.smul_tmul_smul]
  intro z
  obtain ⟨x, rfl⟩ :=
    (exteriorPower.prodPairingEquiv R P Q n m hP' hQ').surjective z
  change exteriorPower.map (n + m) (f.prodMap g)
      (exteriorPower.prodPairing R P Q n m x) = _
  have h := LinearMap.congr_fun (exteriorPower.prodPairing_naturality R P Q n m f g) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, htensor,
    LinearMap.smul_apply, LinearMap.id_apply, map_smul] at h
  exact h

/-- The sole endomorphism of a zero module has determinant one. -/
theorem determinant_of_subsingleton [Subsingleton P] (f : Module.End R P) :
    determinant R P f = 1 := by
  rw [Subsingleton.elim f (LinearMap.id : Module.End R P)]
  exact determinant_id R P

end FiniteProjective

/-- On a finite free module, the scalar determinant agrees with
`LinearMap.det`. -/
theorem determinant_eq_det (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Free R P] (f : Module.End R P) :
    determinant R P f = LinearMap.det f := by
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      let := hR
      exact Subsingleton.elim _ _
  | inr hR =>
      let := hR
      have h : rankAtStalk (R := R) P = fun _ ↦ Module.finrank R P :=
        rankAtStalk_eq_finrank_of_free
      let := exteriorPower.invertible_of_rankAtStalk_eq (Module.finrank R P) h
      exact (determinant_eq_exteriorPower_determinant R P (Module.finrank R P) h f).trans
        ((Module.finBasis R P).exteriorPower_determinant_eq_det f)

end Module
