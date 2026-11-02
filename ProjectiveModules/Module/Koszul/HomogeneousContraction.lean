/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.Koszul.Homogeneous
public import ProjectiveModules.Module.Koszul.ProjectiveContraction

/-!
# Contraction components of homogeneous Koszul complexes

For a finite projective module, the projective Koszul contraction determines a
map from chain degree `i` to degree `i + 1` in each homogeneous complex. In the
finite range, its symmetric degree is reindexed by the equality
`n - (i + 1) + 1 = n - i`. At and above the top degree the component is zero.
The complex and its differential are those of `homogeneousComplex`.

In every total degree, the two-summand homotopy identity holds in positive
chain degrees, including the top and degrees above the finite range. The
chain-degree-zero identity requires positive total degree and has only the
differential-after-contraction summand. No full contraction is asserted for
total degree zero.

## References

- C. Weibel, *The K-book: An Introduction to Algebraic K-theory* (2013),
  for the Koszul construction and passage to projective summands.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u v

namespace Module.Koszul

variable (S : Type u) [CommRing S]
variable (P : Type v) [AddCommGroup P] [Module S P]

/-- In its finite range, a homogeneous complex has the exterior-symmetric object. -/
theorem homogeneousComplex_X_of_le (n i : ℕ) (h : i ≤ n) :
    (homogeneousComplex S P n).X i = ModuleCat.of S (Term S P i (n - i)) := by
  rw [homogeneousComplex_X, homogeneousTerm_of_le S P n i h]

/-- In the finite range, the bigraded and homogeneous raising hom types agree. -/
theorem homogeneousContraction_hom_eq (n i : ℕ) (h : i < n) :
    (ModuleCat.of S (Term S P i (n - i)) ⟶
      ModuleCat.of S (Term S P (i + 1) (n - (i + 1)))) =
    ((homogeneousComplex S P n).X i ⟶ (homogeneousComplex S P n).X (i + 1)) := by
  rw [homogeneousComplex_X_of_le S P n i (by omega),
    homogeneousComplex_X_of_le S P n (i + 1) (by omega)]

variable [Module.Finite S P] [Module.Projective S P]

/-- The projective contraction between the bigraded terms of total degree `n`.
Its source symmetric degree is positive, and the target symmetric degree is
`n - (i + 1)`, equivalently `n - i - 1`. -/
def homogeneousKappa (n i : ℕ) (h : i < n) :
    Term S P i (n - i) →ₗ[S] Term S P (i + 1) (n - (i + 1)) :=
  cast
    (congrArg
      (fun d => Term S P i d →ₗ[S] Term S P (i + 1) (n - (i + 1)))
      (homogeneousDegree_succ n i h))
    (ProjectiveContraction.kappa S P i (n - (i + 1)))

/-- The raising component on the homogeneous complex, extended by zero at and
above its top degree. -/
def homogeneousContraction (n i : ℕ) :
    (homogeneousComplex S P n).X i ⟶ (homogeneousComplex S P n).X (i + 1) :=
  if h : i < n then
    cast (homogeneousContraction_hom_eq S P n i h)
      (ModuleCat.ofHom (R := S)
        (X := Term S P i (n - i))
        (Y := Term S P (i + 1) (n - (i + 1))) (homogeneousKappa S P n i h))
  else 0

/-- Applying the reindexed contraction is applying the projective contraction
after the corresponding cast of the source symmetric degree. -/
theorem homogeneousKappa_apply (n i : ℕ) (h : i < n)
    (x : Term S P i (n - i)) :
    homogeneousKappa S P n i h x =
      ProjectiveContraction.kappa S P i (n - (i + 1))
        (cast (congrArg (Term S P i) (homogeneousDegree_succ n i h).symm) x) := by
  have hcast (a b : ℕ) (e : a = b)
      (f : Term S P i a →ₗ[S] Term S P (i + 1) (n - (i + 1)))
      (y : Term S P i b) :
      (cast
        (congrArg (fun d => Term S P i d →ₗ[S] Term S P (i + 1) (n - (i + 1))) e)
        f) y = f (cast (congrArg (Term S P i) e.symm) y) := by
    cases e
    rfl
  exact hcast _ _ (homogeneousDegree_succ n i h)
    (ProjectiveContraction.kappa S P i (n - (i + 1))) x

/-- In the finite range the component is the morphism of the reindexed
projective contraction, with the homogeneous objects identified. -/
theorem homogeneousContraction_heq_of_lt (n i : ℕ) (h : i < n) :
    HEq (homogeneousContraction S P n i)
      (ModuleCat.ofHom (R := S)
        (X := Term S P i (n - i))
        (Y := Term S P (i + 1) (n - (i + 1))) (homogeneousKappa S P n i h)) := by
  have hcast {A B : Type (max u v)} (e : A = B) (f : A) :
      HEq (cast e f) f := by
    cases e
    rfl
  unfold homogeneousContraction
  simp only [dite_eq_left h]
  exact hcast (homogeneousContraction_hom_eq S P n i h) _

/-- Evaluation of a component in the finite range, with both homogeneous
objects transported along their canonical object equalities. -/
theorem homogeneousContraction_apply_of_lt (n i : ℕ) (h : i < n)
    (x : Term S P i (n - i)) :
    homogeneousContraction S P n i
        (cast
          (congrArg (fun M : ModuleCat.{max u v} S => (M : Type (max u v)))
            (homogeneousComplex_X_of_le S P n i (by omega))).symm x) =
      cast
        (congrArg (fun M : ModuleCat.{max u v} S => (M : Type (max u v)))
          (homogeneousComplex_X_of_le S P n (i + 1) (by omega))).symm
        (homogeneousKappa S P n i h x) := by
  have happ {A B C D : ModuleCat.{max u v} S} (eA : A = C) (eB : B = D)
      (f : A ⟶ B) (y : A) (eHom : (A ⟶ B) = (C ⟶ D)) :
      (cast eHom f)
          (cast (congrArg (fun M : ModuleCat.{max u v} S => (M : Type (max u v))) eA) y) =
        cast (congrArg (fun M : ModuleCat.{max u v} S => (M : Type (max u v))) eB) (f y) := by
    cases eA
    cases eB
    rfl
  unfold homogeneousContraction
  simp only [dite_eq_left h]
  exact happ
    (homogeneousComplex_X_of_le S P n i (by omega)).symm
    (homogeneousComplex_X_of_le S P n (i + 1) (by omega)).symm
    (ModuleCat.ofHom (R := S)
      (X := Term S P i (n - i))
      (Y := Term S P (i + 1) (n - (i + 1))) (homogeneousKappa S P n i h)) x
    (homogeneousContraction_hom_eq S P n i h)

/-- At and above the top degree the raising component is the zero morphism. -/
@[simp]
theorem homogeneousContraction_eq_zero (n i : ℕ) (h : n ≤ i) :
    homogeneousContraction S P n i = 0 := by
  have h' : ¬ i < n := by omega
  simp [homogeneousContraction, h']

/-- At and above the top degree the component sends every element to zero. -/
theorem homogeneousContraction_apply_eq_zero (n i : ℕ) (h : n ≤ i)
    (x : (homogeneousComplex S P n).X i) :
    homogeneousContraction S P n i x = 0 := by
  rw [homogeneousContraction_eq_zero S P n i h]
  rfl

private theorem homogeneousComp_eq_id_of_heq
    {X Y X' Y' : ModuleCat.{max u v} S}
    {f : X ⟶ Y} {g : Y ⟶ X} {f' : X' ⟶ Y'} {g' : Y' ⟶ X'}
    (hX : X = X') (hY : Y = Y') (hf : HEq f f') (hg : HEq g g')
    (h : f' ≫ g' = 𝟙 X') : f ≫ g = 𝟙 X := by
  subst X'
  subst Y'
  have hf' : f = f' := eq_of_heq hf
  have hg' : g = g' := eq_of_heq hg
  simpa only [hf', hg'] using h

private theorem homogeneousAddComp_eq_id_of_heq
    {X Y Z X' Y' Z' : ModuleCat.{max u v} S}
    {f : X ⟶ Y} {g : Y ⟶ X} {a : X ⟶ Z} {b : Z ⟶ X}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ X'} {a' : X' ⟶ Z'} {b' : Z' ⟶ X'}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    (hf : HEq f f') (hg : HEq g g') (ha : HEq a a') (hb : HEq b b')
    (h : f' ≫ g' + a' ≫ b' = 𝟙 X') : f ≫ g + a ≫ b = 𝟙 X := by
  subst X'
  subst Y'
  subst Z'
  have hf' : f = f' := eq_of_heq hf
  have hg' : g = g' := eq_of_heq hg
  have ha' : a = a' := eq_of_heq ha
  have hb' : b = b' := eq_of_heq hb
  simpa only [hf', hg', ha', hb'] using h

omit [Module.Finite S P] [Module.Projective S P] in
private theorem homogeneousTerm_cast_add (i a b : ℕ) (h : a = b)
    (x y : Term S P i a) :
    cast (congrArg (Term S P i) h) (x + y) =
      cast (congrArg (Term S P i) h) x + cast (congrArg (Term S P i) h) y := by
  subst b
  rfl

private theorem homogeneousKappaDelta_cast (i a b : ℕ) (h : a = b)
    (x : Term S P (i + 1) a) :
    cast (congrArg (Term S P (i + 1)) h)
        (ProjectiveContraction.kappa S P i a (delta S P i a x)) =
      ProjectiveContraction.kappa S P i b
        (delta S P i b (cast (congrArg (Term S P (i + 1)) h) x)) := by
  subst b
  rfl

/-- In positive total degree, the chain-degree-zero homotopy equation has only
the differential-after-contraction summand. See Weibel, *The K-book* (2013). -/
theorem homogeneousContraction_homotopy_zero (n : ℕ) (hn : 0 < n) :
    homogeneousContraction S P n 0 ≫ (homogeneousComplex S P n).d 1 0 =
      𝟙 ((homogeneousComplex S P n).X 0) := by
  have hlinear :
      (homogeneousDelta S P n 0 hn).comp (homogeneousKappa S P n 0 hn) =
        (LinearMap.id : Term S P 0 (n - 0) →ₗ[S] Term S P 0 (n - 0)) := by
    apply LinearMap.ext
    intro x
    change homogeneousDelta S P n 0 hn (homogeneousKappa S P n 0 hn x) = x
    rw [homogeneousDelta_apply, homogeneousKappa_apply]
    have hx :
        delta S P 0 (n - (0 + 1))
            (ProjectiveContraction.kappa S P 0 (n - (0 + 1))
              (cast (congrArg (Term S P 0)
                (homogeneousDegree_succ n 0 hn).symm) x)) =
          cast (congrArg (Term S P 0) (homogeneousDegree_succ n 0 hn).symm) x := by
      exact congrArg
        (fun f => f (cast (congrArg (Term S P 0)
          (homogeneousDegree_succ n 0 hn).symm) x))
        (ProjectiveContraction.delta_comp_kappa_exterior_zero S P (n - (0 + 1)))
    rw [hx]
    simp
  have hd : HEq ((homogeneousComplex S P n).d (0 + 1) 0)
      (ModuleCat.ofHom (R := S)
        (X := Term S P (0 + 1) (n - (0 + 1)))
        (Y := Term S P 0 (n - 0))
        (homogeneousDelta S P n 0 hn)) := by
    rw [homogeneousComplex_d]
    exact homogeneousDifferential_heq_of_lt S P n 0 hn
  apply homogeneousComp_eq_id_of_heq S
    (homogeneousComplex_X_of_le S P n 0 (by omega))
    (homogeneousComplex_X_of_le S P n (0 + 1) (by omega))
    (homogeneousContraction_heq_of_lt S P n 0 hn) hd
  apply ModuleCat.hom_ext
  exact hlinear

/-- In every total degree, the two differential-contraction composites sum to
the identity in each positive chain degree, including the top and degrees above
the finite range. At total degree zero these chain objects are zero.
See Weibel, *The K-book* (2013). -/
theorem homogeneousContraction_homotopy_succ (n : ℕ) (i : ℕ) :
    homogeneousContraction S P n (i + 1) ≫
        (homogeneousComplex S P n).d (i + 2) (i + 1) +
      (homogeneousComplex S P n).d (i + 1) i ≫ homogeneousContraction S P n i =
      𝟙 ((homogeneousComplex S P n).X (i + 1)) := by
  by_cases habove : n < i + 1
  · exact (homogeneousComplex_isZero_X S P n (i + 1) habove).eq_of_src _ _
  by_cases hinterior : i + 1 < n
  · have hi : i < n := by omega
    have hlinear :
        (homogeneousDelta S P n (i + 1) hinterior).comp
            (homogeneousKappa S P n (i + 1) hinterior) +
          (homogeneousKappa S P n i hi).comp (homogeneousDelta S P n i hi) =
            (LinearMap.id : Term S P (i + 1) (n - (i + 1)) →ₗ[S]
              Term S P (i + 1) (n - (i + 1))) := by
      apply LinearMap.ext
      intro x
      change homogeneousDelta S P n (i + 1) hinterior
            (homogeneousKappa S P n (i + 1) hinterior x) +
          homogeneousKappa S P n i hi (homogeneousDelta S P n i hi x) = x
      rw [homogeneousDelta_apply, homogeneousKappa_apply,
        homogeneousKappa_apply, homogeneousDelta_apply]
      have e := homogeneousDegree_succ n (i + 1) hinterior
      let y : Term S P (i + 1) (n - ((i + 1) + 1) + 1) :=
        cast (congrArg (Term S P (i + 1)) e.symm) x
      have hm :
          delta S P (i + 1) (n - ((i + 1) + 1))
                (ProjectiveContraction.kappa S P (i + 1) (n - ((i + 1) + 1)) y) +
              ProjectiveContraction.kappa S P i (n - ((i + 1) + 1) + 1)
                (delta S P i (n - ((i + 1) + 1) + 1) y) = y := by
        exact congrArg (fun f => f y)
          (ProjectiveContraction.delta_comp_kappa_add_kappa_comp_delta S P i
            (n - ((i + 1) + 1)))
      have ht := congrArg
        (fun z => cast (congrArg (Term S P (i + 1)) e) z) hm
      rw [homogeneousTerm_cast_add S P (i + 1) _ _ e,
        homogeneousKappaDelta_cast S P i _ _ e] at ht
      simpa [y] using ht
    have hdq : HEq ((homogeneousComplex S P n).d ((i + 1) + 1) (i + 1))
        (ModuleCat.ofHom (R := S)
        (X := Term S P ((i + 1) + 1) (n - ((i + 1) + 1)))
        (Y := Term S P (i + 1) (n - (i + 1)))
        (homogeneousDelta S P n (i + 1) hinterior)) := by
      rw [homogeneousComplex_d]
      exact homogeneousDifferential_heq_of_lt S P n (i + 1) hinterior
    have hdi : HEq ((homogeneousComplex S P n).d (i + 1) i)
        (ModuleCat.ofHom (R := S)
        (X := Term S P (i + 1) (n - (i + 1)))
        (Y := Term S P i (n - i))
        (homogeneousDelta S P n i hi)) := by
      rw [homogeneousComplex_d]
      exact homogeneousDifferential_heq_of_lt S P n i hi
    apply homogeneousAddComp_eq_id_of_heq S
      (homogeneousComplex_X_of_le S P n (i + 1) (by omega))
      (homogeneousComplex_X_of_le S P n ((i + 1) + 1) (by omega))
      (homogeneousComplex_X_of_le S P n i (by omega))
      (homogeneousContraction_heq_of_lt S P n (i + 1) hinterior) hdq hdi
      (homogeneousContraction_heq_of_lt S P n i hi)
    apply ModuleCat.hom_ext
    exact hlinear
  · have htop : n = i + 1 := by omega
    have hi : i < n := by omega
    have hsymmetric : n - (i + 1) = 0 := by omega
    have hprojective :
        (ProjectiveContraction.kappa S P i (n - (i + 1))).comp
            (delta S P i (n - (i + 1))) =
          (LinearMap.id : Term S P (i + 1) (n - (i + 1)) →ₗ[S]
            Term S P (i + 1) (n - (i + 1))) := by
      rw [hsymmetric]
      exact ProjectiveContraction.kappa_comp_delta_symmetric_zero S P i
    have hlinear :
        (homogeneousKappa S P n i hi).comp (homogeneousDelta S P n i hi) =
          (LinearMap.id : Term S P (i + 1) (n - (i + 1)) →ₗ[S]
            Term S P (i + 1) (n - (i + 1))) := by
      apply LinearMap.ext
      intro x
      change homogeneousKappa S P n i hi (homogeneousDelta S P n i hi x) = x
      rw [homogeneousKappa_apply, homogeneousDelta_apply]
      have hx := congrArg (fun f => f x) hprojective
      simpa using hx
    have hdi : HEq ((homogeneousComplex S P n).d (i + 1) i)
        (ModuleCat.ofHom (R := S)
        (X := Term S P (i + 1) (n - (i + 1)))
        (Y := Term S P i (n - i))
        (homogeneousDelta S P n i hi)) := by
      rw [homogeneousComplex_d]
      exact homogeneousDifferential_heq_of_lt S P n i hi
    have hfinite : (homogeneousComplex S P n).d (i + 1) i ≫
        homogeneousContraction S P n i = 𝟙 ((homogeneousComplex S P n).X (i + 1)) := by
      apply homogeneousComp_eq_id_of_heq S
        (homogeneousComplex_X_of_le S P n (i + 1) (by omega))
        (homogeneousComplex_X_of_le S P n i (by omega)) hdi
        (homogeneousContraction_heq_of_lt S P n i hi)
      apply ModuleCat.hom_ext
      exact hlinear
    calc
      homogeneousContraction S P n (i + 1) ≫
            (homogeneousComplex S P n).d (i + 2) (i + 1) +
          (homogeneousComplex S P n).d (i + 1) i ≫ homogeneousContraction S P n i =
          (homogeneousComplex S P n).d (i + 1) i ≫ homogeneousContraction S P n i := by
        rw [homogeneousContraction_eq_zero S P n (i + 1) (by omega)]
        simp
      _ = 𝟙 ((homogeneousComplex S P n).X (i + 1)) := hfinite

end Module.Koszul
