/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.Trace.Prod
import ProjectiveModules.Module.Trace.Cyclicity
import ProjectiveModules.Module.Trace.Conjugation
import ProjectiveModulesTests.IdempotentSpanSemiringClient
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.Finiteness.Basic

/-!
# A heterogeneous nonfree function module with nonzero cross blocks

Let `R = ℕ × ℕ`, `e = (1, 0)` and `I = Ideal.span {e}`. The dependent family
on `Fin 3` has fibers `I`, `I` and `I × I`. Its function module has the
canonical pointwise operations and is finite projective but not free: the
nonzero scalar `(0, 1)` annihilates it, while a single supported generator is
nonzero.

The endomorphism sends `(a, b, (c, d))` to
`(2 • a + b + c, a + 3 • b + d, (a + c, b + d))`. All six off-diagonal
blocks are nonzero, including both projections and both injections between
`I` and `I × I`. Its diagonal contraction traces are `(2, 0)`, `(3, 0)` and
`(2, 0)`, and its whole contraction trace is `(7, 0)`.

The whole trace is computed by the canonical function-to-product equivalences,
conjugation invariance, and the binary block trace formula. The identity trace
on the ideal is computed separately: rectangular cyclicity moves its public
projection–inclusion retraction to the scalar rank-one projector. No formula
for traces on dependent function modules or finite-free comparison is used.

## References

The ideal's finite projectivity and nonfreeness use the idempotent-span
formalization in `ProjectiveModules.Module.LocallyConstantRank` and its
natural-number product client. The rank-one contraction and tensor–Hom APIs
are due to Oliver Nash and Antoine Labelle. The function, product and finitely
supported function constructions reuse Mathlib's formalizations.
-/

noncomputable section

namespace ProjectiveModulesTests.FiniteProjectiveTracePiNonfreeClient

abbrev R := ℕ × ℕ

def e : R := (1, 0)

abbrev I := Ideal.span {e}

abbrev J := I × I

/-- The heterogeneous family of two ideals and their binary product. -/
abbrev M : Fin 3 → Type :=
  Fin.cases I (Fin.cases I (fun _ => J))

instance idealFinite : Module.Finite R I :=
  IdempotentSpanSemiringClient.legacy_nat_product_projective_nonfree.1

instance idealProjective : Module.Projective R I :=
  IdempotentSpanSemiringClient.legacy_nat_product_projective_nonfree.2.1

lemma ideal_not_free : ¬ Module.Free R I :=
  IdempotentSpanSemiringClient.legacy_nat_product_projective_nonfree.2.2

-- Search for the existing instances on the named fibers, then check the
-- definitional reductions of the dependent family.
instance familyAddCommMonoid : ∀ i, AddCommMonoid (M i) :=
  Fin.cases (inferInstanceAs (AddCommMonoid I))
    (Fin.cases (inferInstanceAs (AddCommMonoid I))
      (fun _ => inferInstanceAs (AddCommMonoid J)))

instance familyModule : ∀ i, Module R (M i) :=
  Fin.cases (inferInstanceAs (Module R I))
    (Fin.cases (inferInstanceAs (Module R I))
      (fun _ => inferInstanceAs (Module R J)))

instance familyFinite : ∀ i, Module.Finite R (M i) :=
  Fin.cases (inferInstanceAs (Module.Finite R I))
    (Fin.cases (inferInstanceAs (Module.Finite R I))
      (fun _ => inferInstanceAs (Module.Finite R J)))

instance familyProjective : ∀ i, Module.Projective R (M i) :=
  Fin.cases (inferInstanceAs (Module.Projective R I))
    (Fin.cases (inferInstanceAs (Module.Projective R I))
      (fun _ => inferInstanceAs (Module.Projective R J)))

abbrev P := ∀ i, M i

/-- The fibers reduce to the original ideal, ideal and product carriers. -/
lemma canonical_fibers : M 0 = ↥I ∧ M 1 = ↥I ∧ M 2 = J :=
  ⟨rfl, rfl, rfl⟩

/-- Projectivity transported from the finitely supported dependent functions. -/
instance piProjective : Module.Projective R P :=
  Module.Projective.of_equiv'
    (DFinsupp.linearEquivFunOnFintype (R := R) (M := M))

/-- All pointwise additive structures are the canonical ideal/product structures. -/
lemma canonical_additive_structures :
    (inferInstance : AddCommMonoid I) = Submodule.addCommMonoid I ∧
      familyAddCommMonoid 0 = inferInstanceAs (AddCommMonoid I) ∧
      familyAddCommMonoid 1 = inferInstanceAs (AddCommMonoid I) ∧
      familyAddCommMonoid 2 = inferInstanceAs (AddCommMonoid J) ∧
      (inferInstance : AddCommMonoid P) =
        @Pi.addCommMonoid (Fin 3) M familyAddCommMonoid :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The scalar actions come from the canonical subtype, product and function modules. -/
lemma canonical_modules :
    (inferInstance : Module R I) = Submodule.module I ∧
      (inferInstance : Module R J) = Prod.instModule ∧
      familyModule 0 = Submodule.module I ∧
      familyModule 1 = Submodule.module I ∧
      familyModule 2 = Prod.instModule ∧
      (inferInstance : Module R P) = Pi.module (Fin 3) M R :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The scalar semiring and pointwise function operations are unchanged. -/
lemma canonical_pi_operations (r : R) (x y : P) (i : Fin 3) :
    (inferInstance : CommSemiring R) = inferInstanceAs (CommSemiring (ℕ × ℕ)) ∧
      (0 : P) i = 0 ∧ (x + y) i = x i + y i ∧ (r • x) i = r • x i :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The ideal, product fiber, every fiber, and the function module are finite projective. -/
lemma finite_projective_roster :
    Module.Finite R I ∧ Module.Projective R I ∧
      Module.Finite R J ∧ Module.Projective R J ∧
      (∀ i, Module.Finite R (M i)) ∧ (∀ i, Module.Projective R (M i)) ∧
      Module.Finite R P ∧ Module.Projective R P :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance⟩

lemma e_isIdempotent : IsIdempotentElem e := by
  change e * e = e
  ext <;> simp [e]

lemma e_ne_zero : e ≠ 0 := by
  intro h
  have hfst := congrArg Prod.fst h
  simp [e] at hfst

/-- The canonical generator of the ideal. -/
def v : I := ⟨e, Ideal.mem_span_singleton_self e⟩

lemma v_ne_zero : v ≠ 0 := by
  intro h
  exact e_ne_zero (congrArg (fun x : I => (x : R)) h)

instance idealNontrivial : Nontrivial I :=
  nontrivial_iff.mpr ⟨v, 0, v_ne_zero⟩

/-- The complementary scalar annihilates the ideal. -/
lemma ideal_annihilator (x : I) : ((0, 1) : R) • x = 0 := by
  apply Subtype.ext
  change ((0, 1) : R) * (x : R) = 0
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 x.property
  rw [← hr]
  ext <;> simp [e]

/-- A single supported generator detects that the function module is nonzero. -/
def w : P := LinearMap.single R M 0 v

@[simp]
lemma w_zero_coordinate : w 0 = v := by
  change Pi.single (M := M) 0 v 0 = v
  exact Pi.single_eq_same (M := M) (0 : Fin 3) v

lemma w_ne_zero : w ≠ 0 := by
  intro h
  have hzero := congrArg (fun x : P => x 0) h
  change w 0 = (0 : I) at hzero
  rw [w_zero_coordinate] at hzero
  exact v_ne_zero hzero

instance piNontrivial : Nontrivial P :=
  nontrivial_iff.mpr ⟨w, 0, w_ne_zero⟩

/-- The complementary scalar annihilates every fiber of the function module. -/
lemma pi_annihilator (x : P) : ((0, 1) : R) • x = 0 := by
  funext i
  change ((0, 1) : R) • x i = 0
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ideal_annihilator _
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact ideal_annihilator _
    · exact Prod.ext (ideal_annihilator _) (ideal_annihilator _)

/-- A nontrivial free module has faithful scalar action, unlike this function module. -/
lemma pi_not_free : ¬ Module.Free R P := by
  intro hfree
  let : Module.Free R P := hfree
  have h : ((0, 1) : R) = 0 := eq_of_smul_eq_smul fun x : P => by
    rw [pi_annihilator, zero_smul]
  have hsnd := congrArg Prod.snd h
  exact Nat.one_ne_zero hsnd

/-- The product fiber is nonfree for the same annihilator obstruction. -/
lemma product_not_free : ¬ Module.Free R J := by
  intro hfree
  let : Module.Free R J := hfree
  have h : ((0, 1) : R) = 0 := eq_of_smul_eq_smul fun x : J =>
    Prod.ext ((ideal_annihilator x.1).trans (zero_smul R x.1).symm)
      ((ideal_annihilator x.2).trans (zero_smul R x.2).symm)
  have hsnd := congrArg Prod.snd h
  exact Nat.one_ne_zero hsnd

/-- Every fiber is nonfree, not just the full function module. -/
lemma fibers_not_free : ∀ i, ¬ Module.Free R (M i) :=
  Fin.cases ideal_not_free (Fin.cases ideal_not_free (fun _ => product_not_free))

/-- Cyclicity identifies the ideal identity trace with the scalar rank-one projector trace. -/
lemma trace_ideal_id : LinearMap.traceOfFiniteProjective R I LinearMap.id = e := by
  calc
    LinearMap.traceOfFiniteProjective R I LinearMap.id =
        LinearMap.traceOfFiniteProjective R I
          ((IsIdempotentElem.spanProjection e).comp I.subtype) := by
      rw [e_isIdempotent.spanProjection_comp_subtype]
    _ = LinearMap.traceOfFiniteProjective R R
        (I.subtype.comp (IsIdempotentElem.spanProjection e)) :=
      LinearMap.traceOfFiniteProjective_comp_comm R I R
        I.subtype (IsIdempotentElem.spanProjection e)
    _ = e := by
      rw [IsIdempotentElem.subtype_comp_spanProjection]
      exact LinearMap.traceOfFiniteProjective_smulRight R R
        (LinearMap.id : R →ₗ[R] R) e

lemma trace_two_id :
    LinearMap.traceOfFiniteProjective R I ((2 : ℕ) • LinearMap.id) = ((2, 0) : R) := by
  rw [map_nsmul, trace_ideal_id]
  ext <;> simp [e]

lemma trace_three_id :
    LinearMap.traceOfFiniteProjective R I ((3 : ℕ) • LinearMap.id) = ((3, 0) : R) := by
  rw [map_nsmul, trace_ideal_id]
  ext <;> simp [e]

lemma trace_product_id :
    LinearMap.traceOfFiniteProjective R J LinearMap.id = ((2, 0) : R) := by
  have hid : (LinearMap.id : J →ₗ[R] J) =
      LinearMap.prodMap (LinearMap.id : I →ₗ[R] I) (LinearMap.id : I →ₗ[R] I) := by
    apply LinearMap.ext
    intro x
    rfl
  rw [hid, LinearMap.traceOfFiniteProjective_prodMap]
  simp only [trace_ideal_id]
  ext <;> simp [e]

-- Named codomains let synthesis use the same ideal module in both projections.
private def idealProjZero : P →ₗ[R] I :=
  LinearMap.proj (R := R) (φ := M) (0 : Fin 3)

private def idealProjOne : P →ₗ[R] I :=
  LinearMap.proj (R := R) (φ := M) (1 : Fin 3)

@[simp]
private lemma idealProjZero_apply (x : P) : idealProjZero x = x 0 := rfl

@[simp]
private lemma idealProjOne_apply (x : P) : idealProjOne x = x 1 := rfl

private lemma idealProjections_smul (r : R) (x : P) :
    idealProjZero (r • x) = r • idealProjZero x ∧
      idealProjOne (r • x) = r • idealProjOne x :=
  ⟨rfl, rfl⟩

/-- The endomorphism with nonzero cross blocks and diagonal coefficients two, three and one. -/
def F : P →ₗ[R] P :=
  LinearMap.pi (Fin.cases
    ((2 : ℕ) • idealProjZero + idealProjOne +
      (LinearMap.fst R I I).comp (LinearMap.proj (R := R) (φ := M) (2 : Fin 3)))
    (Fin.cases
      (idealProjZero + (3 : ℕ) • idealProjOne +
        (LinearMap.snd R I I).comp (LinearMap.proj (R := R) (φ := M) (2 : Fin 3)))
      (fun _ =>
        (idealProjZero + (LinearMap.fst R I I).comp
          (LinearMap.proj (R := R) (φ := M) (2 : Fin 3))).prod
          (idealProjOne + (LinearMap.snd R I I).comp
            (LinearMap.proj (R := R) (φ := M) (2 : Fin 3))))))

@[simp]
lemma F_zero (x : P) :
    F x 0 = (2 : ℕ) • idealProjZero x + idealProjOne x + (x 2).1 := rfl

@[simp]
lemma F_one (x : P) :
    F x 1 = idealProjZero x + (3 : ℕ) • idealProjOne x + (x 2).2 := rfl

@[simp]
lemma F_two (x : P) :
    F x 2 = (idealProjZero x + (x 2).1, idealProjOne x + (x 2).2) := rfl

/-- A coordinate block of this concrete endomorphism, using projection and single. -/
abbrev block (i j : Fin 3) : M j →ₗ[R] M i :=
  (LinearMap.proj (R := R) (φ := M) i).comp (F.comp (LinearMap.single R M j))

lemma block_zero_zero : block 0 0 = (2 : ℕ) • (LinearMap.id : I →ₗ[R] I) := by
  apply LinearMap.ext (M := I) (M₃ := I)
  intro x
  simp only [block]
  change (2 : ℕ) • x + (0 : I) + (0 : I) = (2 : ℕ) • x
  simp only [add_zero]

lemma block_one_one : block 1 1 = (3 : ℕ) • (LinearMap.id : I →ₗ[R] I) := by
  apply LinearMap.ext (M := I) (M₃ := I)
  intro x
  simp only [block]
  change (0 : I) + (3 : ℕ) • x + (0 : I) = (3 : ℕ) • x
  simp only [zero_add, add_zero]

lemma block_two_two : block 2 2 = (LinearMap.id : J →ₗ[R] J) := by
  apply LinearMap.ext (M := J) (M₃ := J)
  intro x
  simp only [block]
  change ((0 : I) + x.1, (0 : I) + x.2) = x
  simp only [zero_add]

lemma block_zero_one : block 0 1 = (LinearMap.id : I →ₗ[R] I) := by
  apply LinearMap.ext (M := I) (M₃ := I)
  intro x
  simp only [block]
  change (2 : ℕ) • (0 : I) + x + (0 : I) = x
  simp only [nsmul_zero, zero_add, add_zero]

lemma block_one_zero : block 1 0 = (LinearMap.id : I →ₗ[R] I) := by
  apply LinearMap.ext (M := I) (M₃ := I)
  intro x
  simp only [block]
  change x + (3 : ℕ) • (0 : I) + (0 : I) = x
  simp only [nsmul_zero, add_zero]

lemma block_zero_two : block 0 2 = LinearMap.fst R I I := by
  apply LinearMap.ext (M := J) (M₃ := I)
  intro x
  simp only [block]
  change (2 : ℕ) • (0 : I) + (0 : I) + x.1 = x.1
  simp only [nsmul_zero, zero_add]

lemma block_one_two : block 1 2 = LinearMap.snd R I I := by
  apply LinearMap.ext (M := J) (M₃ := I)
  intro x
  simp only [block]
  change (0 : I) + (3 : ℕ) • (0 : I) + x.2 = x.2
  simp only [nsmul_zero, zero_add]

lemma block_two_zero : block 2 0 = LinearMap.inl R I I := by
  apply LinearMap.ext (M := I) (M₃ := J)
  intro x
  simp only [block]
  change (x + (0 : I), (0 : I) + (0 : I)) = (x, (0 : I))
  simp only [add_zero]

lemma block_two_one : block 2 1 = LinearMap.inr R I I := by
  apply LinearMap.ext (M := I) (M₃ := J)
  intro x
  simp only [block]
  change ((0 : I) + (0 : I), x + (0 : I)) = ((0 : I), x)
  simp only [add_zero]

lemma ideal_id_ne_zero : (LinearMap.id : I →ₗ[R] I) ≠ 0 := by
  intro h
  exact v_ne_zero (by simpa using DFunLike.congr_fun h v)

lemma fst_ne_zero : LinearMap.fst R I I ≠ 0 := by
  intro h
  exact v_ne_zero (by simpa using DFunLike.congr_fun h (v, 0))

lemma snd_ne_zero : LinearMap.snd R I I ≠ 0 := by
  intro h
  exact v_ne_zero (by simpa using DFunLike.congr_fun h (0, v))

lemma inl_ne_zero : LinearMap.inl R I I ≠ 0 := by
  intro h
  have hx := congrArg Prod.fst (DFunLike.congr_fun h v)
  exact v_ne_zero (by simpa using hx)

lemma inr_ne_zero : LinearMap.inr R I I ≠ 0 := by
  intro h
  have hx := congrArg Prod.snd (DFunLike.congr_fun h v)
  exact v_ne_zero (by simpa using hx)

/-- All six cross blocks are genuinely nonzero. -/
lemma cross_blocks_nonzero :
    block 0 1 ≠ 0 ∧ block 1 0 ≠ 0 ∧ block 0 2 ≠ 0 ∧
      block 1 2 ≠ 0 ∧ block 2 0 ≠ 0 ∧ block 2 1 ≠ 0 := by
  rw [block_zero_one, block_one_zero, block_zero_two, block_one_two,
    block_two_zero, block_two_one]
  exact ⟨ideal_id_ne_zero, ideal_id_ne_zero, fst_ne_zero,
    snd_ne_zero, inl_ne_zero, inr_ne_zero⟩

lemma F_ne_zero : F ≠ 0 := by
  intro h
  apply cross_blocks_nonzero.1
  apply LinearMap.ext
  intro x
  change F (LinearMap.single R M 1 x) 0 = 0
  exact congrArg (fun f : P →ₗ[R] P => f (LinearMap.single R M 1 x) 0) h

/-- The three diagonal block traces, each computed independently of the whole trace. -/
lemma diagonal_traces :
    LinearMap.traceOfFiniteProjective R (M 0) (block 0 0) = ((2, 0) : R) ∧
      LinearMap.traceOfFiniteProjective R (M 1) (block 1 1) = ((3, 0) : R) ∧
      LinearMap.traceOfFiniteProjective R (M 2) (block 2 2) = ((2, 0) : R) := by
  rw [block_zero_zero, block_one_one, block_two_two]
  exact ⟨trace_two_id, trace_three_id, trace_product_id⟩

abbrev Q := I × (I × J)

/-- The canonical dependent function-to-product equivalences, composed. -/
def productEquiv : P ≃ₗ[R] Q :=
  (Fin.consLinearEquiv R M).symm.trans
    ((LinearEquiv.refl R I).prodCongr
      (LinearEquiv.piFinTwo R (fun i : Fin 2 => M i.succ)))

@[simp]
lemma productEquiv_apply (x : P) : productEquiv x = (x 0, (x 1, x 2)) := rfl

/-- The lower binary block of the endomorphism in product coordinates. -/
def B : (I × J) →ₗ[R] (I × J) :=
  (((3 : ℕ) • (LinearMap.id : I →ₗ[R] I)).prod (LinearMap.inr R I I)).coprod
    ((LinearMap.snd R I I).prod (LinearMap.id : J →ₗ[R] J))

/-- The same endomorphism expressed as a binary block matrix on nested products. -/
def G : Q →ₗ[R] Q :=
  (((2 : ℕ) • (LinearMap.id : I →ₗ[R] I)).prod
    ((LinearMap.id : I →ₗ[R] I).prod (LinearMap.inl R I I))).coprod
      (((LinearMap.fst R I J +
        (LinearMap.fst R I I).comp (LinearMap.snd R I J))).prod B)

lemma productEquiv_intertwines (x : P) : productEquiv (F x) = G (productEquiv x) := by
  apply Prod.ext
  · change (2 : ℕ) • idealProjZero x + idealProjOne x + (x 2).1 =
      (2 : ℕ) • idealProjZero x + (idealProjOne x + (x 2).1)
    exact add_assoc _ _ _
  · apply Prod.ext
    · change idealProjZero x + (3 : ℕ) • idealProjOne x + (x 2).2 =
        idealProjZero x + ((3 : ℕ) • idealProjOne x + (x 2).2)
      exact add_assoc _ _ _
    · apply Prod.ext
      · change idealProjZero x + (x 2).1 = idealProjZero x + (0 + (x 2).1)
        rw [zero_add]
      · change idealProjOne x + (x 2).2 = 0 + (idealProjOne x + (x 2).2)
        rw [zero_add]

lemma productEquiv_conj : productEquiv.conj F = G := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := productEquiv.surjective y
  rw [LinearEquiv.conj_apply_apply, productEquiv.symm_apply_apply]
  exact productEquiv_intertwines x

lemma trace_B : LinearMap.traceOfFiniteProjective R (I × J) B = ((5, 0) : R) := by
  rw [B, LinearMap.traceOfFiniteProjective_coprod_prod, trace_three_id, trace_product_id]
  ext <;> simp

lemma trace_G : LinearMap.traceOfFiniteProjective R Q G = ((7, 0) : R) := by
  rw [G, LinearMap.traceOfFiniteProjective_coprod_prod, trace_two_id, trace_B]
  ext <;> simp

/-- The whole trace follows from binary product blocks and conjugation invariance. -/
lemma trace_F : LinearMap.traceOfFiniteProjective R P F = ((7, 0) : R) := by
  calc
    LinearMap.traceOfFiniteProjective R P F =
        LinearMap.traceOfFiniteProjective R Q (productEquiv.conj F) :=
      (LinearMap.traceOfFiniteProjective_conj R P Q productEquiv F).symm
    _ = ((7, 0) : R) := by rw [productEquiv_conj, trace_G]

lemma trace_F_ne_zero : LinearMap.traceOfFiniteProjective R P F ≠ 0 := by
  rw [trace_F]
  intro h
  have hfst := congrArg Prod.fst h
  exact (by decide : (7 : ℕ) ≠ 0) hfst

/-- A finite projective, nonfree, nonzero function module with a nonzero endomorphism and trace. -/
lemma heterogeneous_nonfree_trace :
    ¬ Module.Free R P ∧ w ≠ 0 ∧ F ≠ 0 ∧
      LinearMap.traceOfFiniteProjective R P F = ((7, 0) : R) ∧
      LinearMap.traceOfFiniteProjective R P F ≠ 0 :=
  ⟨pi_not_free, w_ne_zero, F_ne_zero, trace_F, trace_F_ne_zero⟩

end ProjectiveModulesTests.FiniteProjectiveTracePiNonfreeClient
