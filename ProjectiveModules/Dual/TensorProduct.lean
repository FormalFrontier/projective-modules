/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Projection

/-!
# Tensor-family zero detection, dual separation and injectivity reflection

Over a commutative semiring, tensoring a jointly pair-separating family
`f i : A →ₗ[R] B i` with a projective module `P` preserves pair separation in
`P ⊗[R] A`, and by the commutor also in `A ⊗[R] P`. Only `P` is required to be
projective; the dependent target family may be indexed by an arbitrary, possibly
empty type. The premise compares all pairs in `A`, not only points with zero.

Over a commutative semiring, tensoring a jointly zero-detecting family
`h k : X →ₗ[R] Y k` with a projective module `P` preserves zero detection in
`P ⊗[R] X`, and by the commutor also in `X ⊗[R] P`. The source and dependent
targets of the family are arbitrary; they need not be projective or have
zero-separating duals. Index types may be empty and no finiteness is required.

For two jointly zero-detecting families `f i : A →ₗ[R] B i` and
`g j : C →ₗ[R] D j`, their tensor maps jointly detect zero when `C` and every
`B i` are projective. First tensor the g-family with each `B i`, then tensor
the f-family with `C`. No projectivity of `A` or `D j` is required. These
criteria concern zero detection, not separation of arbitrary pairs.

Over a commutative semiring, products of linear forms detect zero in `M ⊗[R] N`
when `M` is projective and the canonical evaluation pairing `Module.Dual.eval R N`
is left-separating. The factors may have arbitrary rank, their additive structures
need only be commutative monoids, and the scalar and carrier universes are independent.
Left separation here means detection of zero, not separation of arbitrary pairs of
points in semimodules.

Products of linear forms distinguish arbitrary tensor points when `M` is projective
and the canonical dual evaluation on `N` is injective. If both factors are projective,
Mathlib's `Module.eval_apply_injective` supplies this injectivity. Specializing the
two-projective equality criterion to comparison with zero gives the original
two-projective zero criterion by linearity. This does not replace the weaker
zero-detection hypothesis in the one-projective zero criterion.

The two-projective criterion `TensorProduct.forall_dualDistrib_apply_eq_zero_iff`
is a corollary. The scalar-submodule application
`TensorProduct.forall_dualDistrib_apply_eq_zero_iff_submodule` applies to every
`I : Submodule R R`, including ideals, without assuming projectivity of `I`.

The one-sided criterion and the dual point-equality criterion share a vector-valued
contraction argument, using Mathlib's projective splitting, finitely supported tensor
coordinates and scalar unitors. The scalar zero criterion follows from the two-family
criterion after swapping the factors; its second-factor zero-separation hypothesis
is retained.

Over a commutative semiring, the canonical map `dualTensorHom R M N` from
`Module.Dual R M ⊗[R] N` to `M →ₗ[R] N` is injective whenever the output module `N`
is projective. Both modules may be additive commutative monoids of arbitrary rank;
no projectivity of `M` or finite-generation assumption is required.

Tensoring with a module `P` with faithful scalar action reflects injectivity of
`f : M →ₗ[R] N` whenever the canonical dual evaluation on `M` is injective.
Projective domains satisfy this condition by Mathlib's `Module.eval_apply_injective`.
The coefficient module need not be flat, and the domain and codomain need not be
finitely generated. Applying this reflection to `Finsupp.linearCombination` shows
that injectivity of the tensor-valued finite-support `P`-coefficient relation map
of an arbitrary family implies its `R`-linear independence.

The reflection proof compares pairs using each dual form and the tensor right
unitor, then uses faithfulness of the scalar action. It uses no subtraction or
preservation of injectivity. Faithful action alone does not suffice for arbitrary
domains: over `ℤ`, tensoring the zero map `ZMod 2 → 0` with `ℚ` makes it injective.
Nor does faithful action imply preservation: for `P = ℤ × ZMod 2`, tensoring
multiplication by two on `ℤ` is not injective. These results are reflection only.

For a module `N` whose canonical dual evaluation is injective, tensoring with a
faithful coefficient module `P` is injective on the linear Hom space `M →ₗ[R] N`.
Here separation is required of the target, rather than of the source. Projective
targets satisfy this condition. The resulting equality criterion detects whether
an arbitrary map lands in the range of an idempotent endomorphism by testing the
corresponding tensor composition equation. These results require neither flatness
of `P` nor finite generation, additive inverses or nontriviality.

## References

- Mathlib's Contraction formalization by Oliver Nash and Antoine Labelle
  (`Mathlib.LinearAlgebra.Contraction`). The injectivity proof follows its Finsupp
  factorization, naturality and retract approach.
- Mathlib's Finsupp-Hom formalization by Johan Commelin
  (`Mathlib.RingTheory.Finiteness.Finsupp`).
- Mathlib's projective-module formalization by Kevin Buzzard and Antoine Labelle
  (`Mathlib.Algebra.Module.Projective`), used for the canonical free-module splitting.
- Mathlib's dual formalization by Johan Commelin, Fabian Glöckle and Kyle Miller
  (`Mathlib.LinearAlgebra.Dual.Lemmas`), including projective dual-evaluation injectivity.
- Mathlib's tensor maps and unitors by Kenny Lau and Mario Carneiro, and its
  Finsupp/direct-sum formalizations by Johannes Hölzl and Antoine Chambert-Loir.
  Tensor-family zero detection and dual separation use `TensorProduct.finsuppScalarLeft`
  and the canonical tensor maps and unitors. The linear-independence application uses
  `TensorProduct.finsuppScalarRight` rather than a new free-module identification.
-/

@[expose] public section

open scoped TensorProduct

universe uR uP uM uN uι uA uC uI uJ uB uD

namespace TensorProduct

/-- If dual evaluation on `N` is injective, equality after tensoring with every
point of a faithful module implies equality in `N`. No flatness or additive
inverses are required. -/
theorem eq_of_forall_tmul_eq_of_eval_injective
    {R : Type uR} {P : Type uP} {N : Type uN}
    [CommSemiring R] [AddCommMonoid P] [AddCommMonoid N]
    [Module R P] [Module R N] [FaithfulSMul R P]
    (hN : Function.Injective (Module.Dual.eval R N))
    {x y : N} (h : ∀ p : P, p ⊗ₜ[R] x = p ⊗ₜ[R] y) :
    x = y := by
  apply hN
  apply LinearMap.ext
  intro φ
  change φ x = φ y
  apply eq_of_smul_eq_smul (α := P)
  intro p
  have hφ := congrArg (fun t => TensorProduct.rid R P (φ.lTensor P t)) (h p)
  simpa only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul] using hφ

-- Vector-valued contractions distinguish pairs even if the second factor has no nonzero duals.
-- This is the single free-coordinate argument used for both zero and pair detection.
private theorem eq_of_forall_lid_rTensor_eq
    (R : Type uR) [CommSemiring R]
    (M : Type uM) (N : Type uN)
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module.Projective R M]
    (t u : M ⊗[R] N)
    (h : ∀ f : Module.Dual R M,
      TensorProduct.lid R N (f.rTensor N t) = TensorProduct.lid R N (f.rTensor N u)) :
    t = u := by
  classical
  obtain ⟨sM, hsM⟩ :=
    Module.projective_def'.mp (inferInstance : Module.Projective R M)
  have hsplit : sM.rTensor N t = sM.rTensor N u := by
    apply (TensorProduct.finsuppScalarLeft R N M).injective
    apply Finsupp.ext
    intro i
    rw [TensorProduct.finsuppScalarLeft_apply, TensorProduct.finsuppScalarLeft_apply,
      ← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply]
    exact h ((Finsupp.lapply i).comp sM)
  -- The tensor of the projective retraction returns equality in the original tensor.
  calc
    t = (Finsupp.linearCombination R (id : M → M)).rTensor N (sM.rTensor N t) := by
      rw [← LinearMap.rTensor_comp_apply, hsM, LinearMap.rTensor_id, LinearMap.id_apply]
    _ = (Finsupp.linearCombination R (id : M → M)).rTensor N (sM.rTensor N u) := by
      rw [hsplit]
    _ = u := by
      rw [← LinearMap.rTensor_comp_apply, hsM, LinearMap.rTensor_id, LinearMap.id_apply]

/-- Tensoring a jointly pair-separating family with a projective module on the left
preserves pair separation. The source, dependent targets and index type are arbitrary;
no target projectivity, finiteness or additive inverses are required. -/
theorem forall_map_id_left_apply_eq_iff_of_projective
    {R : Type uR} [CommSemiring R]
    {P : Type uP} [AddCommMonoid P] [Module R P]
    [Module.Projective R P]
    {A : Type uA} [AddCommMonoid A] [Module R A]
    {I : Type uI} {B : I → Type uB}
    [∀ i, AddCommMonoid (B i)] [∀ i, Module R (B i)]
    (f : ∀ i, A →ₗ[R] B i)
    (hf : ∀ a a' : A, (∀ i, f i a = f i a') → a = a')
    (x y : P ⊗[R] A) :
    (∀ i, TensorProduct.map (LinearMap.id : P →ₗ[R] P) (f i) x =
      TensorProduct.map (LinearMap.id : P →ₗ[R] P) (f i) y) ↔ x = y := by
  constructor
  · intro hxy
    apply eq_of_forall_lid_rTensor_eq R P A x y
    intro φ
    apply hf
    intro i
    -- Each family member commutes with the A-valued contraction by φ.
    have hnat :
        (f i).comp ((TensorProduct.lid R A).toLinearMap.comp (φ.rTensor A)) =
          (TensorProduct.lid R (B i)).toLinearMap.comp
            ((φ.rTensor (B i)).comp (TensorProduct.map LinearMap.id (f i))) := by
      apply TensorProduct.ext'
      intro p a
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
        TensorProduct.lid_tmul, TensorProduct.map_tmul, LinearMap.id_apply, map_smul]
    exact ((LinearMap.congr_fun hnat x).trans
      (congrArg (fun t => TensorProduct.lid R (B i) (φ.rTensor (B i) t)) (hxy i))).trans
        (LinearMap.congr_fun hnat y).symm
  · intro hxy i
    rw [hxy]

/-- Tensoring a jointly pair-separating family with a projective module on the right
preserves pair separation. This is the commuting orientation of the left-projective
criterion, with no projectivity assumption on any target. -/
theorem forall_map_id_right_apply_eq_iff_of_projective
    {R : Type uR} [CommSemiring R]
    {P : Type uP} [AddCommMonoid P] [Module R P]
    [Module.Projective R P]
    {A : Type uA} [AddCommMonoid A] [Module R A]
    {I : Type uI} {B : I → Type uB}
    [∀ i, AddCommMonoid (B i)] [∀ i, Module R (B i)]
    (f : ∀ i, A →ₗ[R] B i)
    (hf : ∀ a a' : A, (∀ i, f i a = f i a') → a = a')
    (x y : A ⊗[R] P) :
    (∀ i, TensorProduct.map (f i) (LinearMap.id : P →ₗ[R] P) x =
      TensorProduct.map (f i) (LinearMap.id : P →ₗ[R] P) y) ↔ x = y := by
  constructor
  · intro hxy
    apply (TensorProduct.comm R A P).injective
    apply (forall_map_id_left_apply_eq_iff_of_projective f hf
      (TensorProduct.comm R A P x) (TensorProduct.comm R A P y)).mp
    intro i
    rw [TensorProduct.map_comm, TensorProduct.map_comm, hxy i]
  · intro hxy i
    rw [hxy]

/-- Tensoring a jointly zero-detecting family with a projective module on the left
preserves zero detection. The source, dependent targets and index type are arbitrary;
no target projectivity, finiteness or additive inverses are required. -/
theorem forall_map_id_left_apply_eq_zero_iff_of_projective
    {R : Type uR} [CommSemiring R]
    (P : Type uP) [AddCommMonoid P] [Module R P] [Module.Projective R P]
    {X : Type uM} [AddCommMonoid X] [Module R X]
    {K : Type uI} {Y : K → Type uB}
    [∀ k, AddCommMonoid (Y k)] [∀ k, Module R (Y k)]
    (h : ∀ k, X →ₗ[R] Y k)
    (hh : ∀ x : X, (∀ k, h k x = 0) → x = 0)
    (s : P ⊗[R] X) :
    (∀ k, TensorProduct.map (LinearMap.id : P →ₗ[R] P) (h k) s = 0) ↔ s = 0 := by
  constructor
  · intro hs
    apply eq_of_forall_lid_rTensor_eq R P X s 0
    intro φ
    rw [map_zero, map_zero]
    apply hh
    intro k
    -- Each original test commutes with the X-valued contraction by φ.
    have hnat :
        (h k).comp ((TensorProduct.lid R X).toLinearMap.comp (φ.rTensor X)) =
          (TensorProduct.lid R (Y k)).toLinearMap.comp
            ((φ.rTensor (Y k)).comp (TensorProduct.map LinearMap.id (h k))) := by
      apply TensorProduct.ext'
      intro p x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
        TensorProduct.lid_tmul, TensorProduct.map_tmul, LinearMap.id_apply, map_smul]
    exact (LinearMap.congr_fun hnat s).trans (by
      simp only [LinearMap.comp_apply, hs k, map_zero])
  · intro hs k
    rw [hs, map_zero]

/-- Tensoring a jointly zero-detecting family with a projective module on the right
preserves zero detection. This is the commuting orientation of the left-projective
criterion, with no projectivity assumption on any target. -/
theorem forall_map_id_right_apply_eq_zero_iff_of_projective
    {R : Type uR} [CommSemiring R]
    (P : Type uP) [AddCommMonoid P] [Module R P] [Module.Projective R P]
    {X : Type uM} [AddCommMonoid X] [Module R X]
    {K : Type uI} {Y : K → Type uB}
    [∀ k, AddCommMonoid (Y k)] [∀ k, Module R (Y k)]
    (h : ∀ k, X →ₗ[R] Y k)
    (hh : ∀ x : X, (∀ k, h k x = 0) → x = 0)
    (s : X ⊗[R] P) :
    (∀ k, TensorProduct.map (h k) (LinearMap.id : P →ₗ[R] P) s = 0) ↔ s = 0 := by
  constructor
  · intro hs
    apply (TensorProduct.comm R X P).map_eq_zero_iff.mp
    apply (forall_map_id_left_apply_eq_zero_iff_of_projective P h hh
      (TensorProduct.comm R X P s)).mp
    intro k
    rw [TensorProduct.map_comm, hs k, map_zero]
  · intro hs k
    rw [hs, map_zero]

/-- Two jointly zero-detecting families detect zero after tensoring when the second
source and every target of the first family are projective. No projectivity of the
first source or the second family's targets is required, and both index types may
be empty. This is zero detection, not separation of arbitrary pairs. -/
theorem forall_map_apply_eq_zero_iff_of_projective
    {R : Type uR} [CommSemiring R]
    {A : Type uA} {C : Type uC}
    [AddCommMonoid A] [AddCommMonoid C] [Module R A] [Module R C]
    {I : Type uI} {J : Type uJ} {B : I → Type uB} {D : J → Type uD}
    [∀ i, AddCommMonoid (B i)] [∀ i, Module R (B i)]
    [∀ j, AddCommMonoid (D j)] [∀ j, Module R (D j)]
    [Module.Projective R C] [∀ i, Module.Projective R (B i)]
    (f : ∀ i, A →ₗ[R] B i) (g : ∀ j, C →ₗ[R] D j)
    (hf : ∀ a : A, (∀ i, f i a = 0) → a = 0)
    (hg : ∀ c : C, (∀ j, g j c = 0) → c = 0)
    (t : A ⊗[R] C) :
    (∀ i j, TensorProduct.map (f i) (g j) t = 0) ↔ t = 0 := by
  constructor
  · intro ht
    apply (forall_map_id_right_apply_eq_zero_iff_of_projective C f hf t).mp
    intro i
    -- First use projectivity of B i, not of any D j.
    apply (forall_map_id_left_apply_eq_zero_iff_of_projective (B i) g hg
      (TensorProduct.map (f i) LinearMap.id t)).mp
    intro j
    simpa only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id] using ht i j
  · intro ht i j
    rw [ht, map_zero]

/-- A tensor with projective first factor vanishes exactly when every rank-one product
of linear forms vanishes on it, provided the canonical dual evaluation on the second
factor detects zero. No finite-generation or second-factor projectivity is required. -/
theorem forall_dualDistrib_apply_eq_zero_iff_of_eval_separatingLeft
    (R : Type uR) [CommSemiring R]
    (M : Type uM) (N : Type uN)
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    [Module.Projective R M]
    (hN : (Module.Dual.eval R N).SeparatingLeft)
    (t : M ⊗[R] N) :
    (∀ f : Module.Dual R M, ∀ g : Module.Dual R N,
      TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) t = 0) ↔ t = 0 := by
  constructor
  · intro h
    apply (TensorProduct.comm R M N).map_eq_zero_iff.mp
    apply (forall_map_apply_eq_zero_iff_of_projective
      (fun g : Module.Dual R N => g) (fun f : Module.Dual R M => f)
      hN (fun m hm => (Module.forall_dual_apply_eq_zero_iff R m).mp hm)
      (TensorProduct.comm R M N t)).mp
    intro g f
    apply (TensorProduct.rid R R).map_eq_zero_iff.mp
    -- Swapping the factors gives the scalar product in its original order via rid.
    have hscalar : (TensorProduct.rid R R).toLinearMap.comp
        ((TensorProduct.map g f).comp (TensorProduct.comm R M N).toLinearMap) =
          TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) := by
      apply TensorProduct.ext'
      intro m n
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
        TensorProduct.map_tmul, TensorProduct.rid_tmul, smul_eq_mul,
        TensorProduct.dualDistrib_apply]
    exact (LinearMap.congr_fun hscalar t).trans (h f g)
  · intro ht f g
    rw [ht, map_zero]

/-- A tensor of two projective modules vanishes exactly when every rank-one product of
linear forms vanishes on it. No finite-generation assumption is required. -/
theorem forall_dualDistrib_apply_eq_zero_iff
    (R : Type uR) [CommSemiring R]
    (M : Type uM) (N : Type uN)
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    [Module.Projective R M] [Module.Projective R N]
    (t : M ⊗[R] N) :
    (∀ f : Module.Dual R M, ∀ g : Module.Dual R N,
      TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) t = 0) ↔ t = 0 := by
  exact forall_dualDistrib_apply_eq_zero_iff_of_eval_separatingLeft R M N
    LinearMap.SeparatingLeft.eval t

/-- Products of linear forms detect zero in the tensor product of a projective module
with any scalar submodule. No projectivity of the scalar submodule is assumed. -/
theorem forall_dualDistrib_apply_eq_zero_iff_submodule
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    [Module.Projective R M]
    (I : Submodule R R) (t : M ⊗[R] I) :
    (∀ f : Module.Dual R M, ∀ g : Module.Dual R I,
      TensorProduct.dualDistrib R M I (f ⊗ₜ[R] g) t = 0) ↔ t = 0 := by
  exact forall_dualDistrib_apply_eq_zero_iff_of_eval_separatingLeft R M I
    (fun x hx => Subtype.ext (hx I.subtype)) t

/-- Two tensors with projective first factor are equal exactly when every rank-one
product of linear forms takes equal values on them, provided the canonical dual
evaluation on the second factor is injective. Ordinary point injectivity is required,
not merely detection of zero; neither factor needs to be finitely generated. -/
theorem forall_dualDistrib_apply_eq_iff_of_eval_injective
    (R : Type uR) [CommSemiring R]
    (M : Type uM) (N : Type uN)
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    [Module.Projective R M]
    (hN : Function.Injective (Module.Dual.eval R N))
    (t u : M ⊗[R] N) :
    (∀ f : Module.Dual R M, ∀ g : Module.Dual R N,
      TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) t =
        TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) u) ↔ t = u := by
  constructor
  · intro h
    apply eq_of_forall_lid_rTensor_eq R M N t u
    intro f
    apply hN
    apply LinearMap.ext
    intro g
    change g (TensorProduct.lid R N (f.rTensor N t)) =
      g (TensorProduct.lid R N (f.rTensor N u))
    have hcoord :
        g.comp ((TensorProduct.lid R N).toLinearMap.comp (f.rTensor N)) =
          TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) := by
      apply TensorProduct.ext'
      intro m n
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
        TensorProduct.lid_tmul, map_smul, TensorProduct.dualDistrib_apply, smul_eq_mul]
    exact ((LinearMap.congr_fun hcoord t).trans (h f g)).trans
      (LinearMap.congr_fun hcoord u).symm
  · intro htu f g
    rw [htu]

/-- Two tensors of projective modules are equal exactly when every rank-one product
of linear forms takes equal values on them. The modules may have arbitrary rank
and need only have additive commutative monoid structures. -/
theorem forall_dualDistrib_apply_eq_iff
    (R : Type uR) [CommSemiring R]
    (M : Type uM) (N : Type uN)
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    [Module.Projective R M] [Module.Projective R N]
    (t u : M ⊗[R] N) :
    (∀ f : Module.Dual R M, ∀ g : Module.Dual R N,
      TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) t =
        TensorProduct.dualDistrib R M N (f ⊗ₜ[R] g) u) ↔ t = u := by
  exact forall_dualDistrib_apply_eq_iff_of_eval_injective R M N
    (Module.eval_apply_injective R (V := N)) t u

end TensorProduct

/-- Over a commutative semiring, the canonical map from `Module.Dual R M ⊗[R] N`
to `M →ₗ[R] N` is injective if the output module `N` is projective. Neither module
needs to be finitely generated, and `M` need not be projective. The proof follows
Mathlib's Finsupp factorization and output-retract approach in Contraction. -/
theorem dualTensorHom_injective_of_projective_right
    (R : Type uR) [CommSemiring R]
    (M : Type uM) (N : Type uN)
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module.Projective R N] :
    Function.Injective (dualTensorHom R M N) := by
  classical
  have hscalar : Function.Injective (dualTensorHom R M R) := by
    rw [dualTensorHom_self_right]
    exact (TensorProduct.rid R (Module.Dual R M)).injective
  -- For a free output, all three maps in the Finsupp factorization are injective.
  have hfree : Function.Injective (dualTensorHom R M (N →₀ R)) := by
    rw [dualTensorHom_finsupp, LinearMap.coe_comp, LinearMap.coe_comp]
    exact (LinearMap.finsuppLinearMap_injective (S := R) (R := R) (M := M)
      (N := R) (ι := N)).comp
        ((Finsupp.mapRange_injective _ (map_zero _) hscalar).comp
          (TensorProduct.finsuppRight R R (Module.Dual R M) R N).injective)
  obtain ⟨s, hs⟩ :=
    Module.projective_def'.mp (inferInstance : Module.Projective R N)
  -- The section of the output remains a section after tensoring with the dual.
  have hsTensor : Function.Injective (s.lTensor (Module.Dual R M)) := by
    apply LinearMap.injective_of_comp_eq_id _
      ((Finsupp.linearCombination R (id : N → N)).lTensor (Module.Dual R M))
    rw [← LinearMap.lTensor_comp, hs, LinearMap.lTensor_id]
  intro x y h
  apply hsTensor
  apply hfree
  calc
    dualTensorHom R M (N →₀ R) (s.lTensor (Module.Dual R M) x) =
        s.comp (dualTensorHom R M N x) :=
      LinearMap.congr_fun (dualTensorHom_comp_lTensor (M := M) s) x
    _ = s.comp (dualTensorHom R M N y) := congrArg (fun f => s.comp f) h
    _ = dualTensorHom R M (N →₀ R) (s.lTensor (Module.Dual R M) y) :=
      (LinearMap.congr_fun (dualTensorHom_comp_lTensor (M := M) s) y).symm

namespace LinearMap

section

variable {R : Type uR} {P : Type uP} {M : Type uM} {N : Type uN}
variable [CommSemiring R]
variable [AddCommMonoid P] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R P] [Module R M] [Module R N] [FaithfulSMul R P]

/-- Tensoring with a faithful module is injective on the linear Hom space when
canonical dual evaluation on the target is injective. The source is arbitrary. -/
theorem lTensorHom_injective_of_eval_injective
    (hN : Function.Injective (Module.Dual.eval R N)) :
    Function.Injective
      (LinearMap.lTensorHom (R := R) (N := M) (P := N) P) := by
  intro f g hfg
  ext x
  apply TensorProduct.eq_of_forall_tmul_eq_of_eval_injective (P := P) hN
  intro p
  simpa only [coe_lTensorHom, lTensor_tmul] using
    LinearMap.congr_fun hfg (p ⊗ₜ[R] x)

/-- Tensoring arbitrary maps into a dual-separated target with a faithful module
reflects their equality. -/
theorem lTensor_inj_of_eval_injective
    (hN : Function.Injective (Module.Dual.eval R N))
    {f g : M →ₗ[R] N} :
    f.lTensor P = g.lTensor P ↔ f = g := by
  rw [← coe_lTensorHom]
  exact (lTensorHom_injective_of_eval_injective hN).eq_iff

/-- Tensoring with a faithful module is injective on the linear Hom space into a
projective target, without any projectivity assumption on the source. -/
theorem lTensorHom_injective_of_projective
    [Module.Projective R N] :
    Function.Injective
      (LinearMap.lTensorHom (R := R) (N := M) (P := N) P) := by
  exact lTensorHom_injective_of_eval_injective (Module.eval_apply_injective R (V := N))

/-- A map into a dual-separated module lands in the range of an idempotent exactly
when its tensoring with a faithful module is fixed by the tensored idempotent.
The range criterion uses Mathlib's `IsIdempotentElem.comp_eq_right_iff`. -/
theorem lTensor_comp_eq_self_iff_range_le
    (hN : Function.Injective (Module.Dual.eval R N))
    {e : Module.End R N} (he : IsIdempotentElem e)
    (f : M →ₗ[R] N) :
    (e.lTensor P).comp (f.lTensor P) = f.lTensor P ↔
      LinearMap.range f ≤ LinearMap.range e := by
  rw [← lTensor_comp, lTensor_inj_of_eval_injective hN]
  exact IsIdempotentElem.comp_eq_right_iff he f

end

/-- Tensoring with a module with faithful scalar action reflects injectivity when
linear forms separate pairs of points in the domain. Neither flatness of the
coefficient module nor finite generation of any module is required. -/
theorem injective_of_lTensor_injective_of_eval_injective
    {R : Type uR} {P : Type uP} {M : Type uM} {N : Type uN}
    [CommSemiring R]
    [AddCommMonoid P] [AddCommMonoid M] [AddCommMonoid N]
    [Module R P] [Module R M] [Module R N] [FaithfulSMul R P]
    (hM : Function.Injective (Module.Dual.eval R M))
    (f : M →ₗ[R] N) (hf : Function.Injective (f.lTensor P)) :
    Function.Injective f := by
  intro x y hxy
  apply TensorProduct.eq_of_forall_tmul_eq_of_eval_injective (P := P) hM
  intro p
  apply hf
  simpa only [lTensor_tmul] using congrArg (fun n => p ⊗ₜ[R] n) hxy

/-- Tensoring with a module with faithful scalar action reflects injectivity of
maps from projective modules of arbitrary rank. The dual-separation hypothesis
is supplied by Mathlib's projective dual-evaluation injectivity theorem. -/
theorem injective_of_lTensor_injective_of_projective
    {R : Type uR} {P : Type uP} {M : Type uM} {N : Type uN}
    [CommSemiring R]
    [AddCommMonoid P] [AddCommMonoid M] [AddCommMonoid N]
    [Module R P] [Module R M] [Module R N] [FaithfulSMul R P]
    [Module.Projective R M]
    (f : M →ₗ[R] N) (hf : Function.Injective (f.lTensor P)) :
    Function.Injective f := by
  exact f.injective_of_lTensor_injective_of_eval_injective
    (Module.eval_apply_injective R (V := M)) hf

end LinearMap

/-- If the tensor-valued finite-support `P`-coefficient relation map of a family
is injective and the scalar action on `P` is faithful, the family is linearly
independent over `R`. The index type is arbitrary, and no flatness assumption
on `P` or finiteness assumption on the family is needed. -/
theorem linearIndependent_of_injective_sum_tmul
    {R : Type uR} {P : Type uP} {N : Type uN} {ι : Type uι}
    [CommSemiring R] [AddCommMonoid P] [AddCommMonoid N]
    [Module R P] [Module R N] [FaithfulSMul R P]
    (v : ι → N)
    (hv : Function.Injective
      (Finsupp.lsum R (fun i => (TensorProduct.mk R P N).flip (v i)))) :
    LinearIndependent R v := by
  classical
  let e := TensorProduct.finsuppScalarRight R R P ι
  -- Compare the relation map with tensoring the scalar linear-combination map.
  have hcomp : ((Finsupp.linearCombination R v).lTensor P).comp e.symm.toLinearMap =
      Finsupp.lsum R (fun i => (TensorProduct.mk R P N).flip (v i)) := by
    apply Finsupp.lhom_ext
    intro i p
    simp [e, Finsupp.lsum_single]
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  apply LinearMap.injective_of_lTensor_injective_of_projective (P := P)
  intro x y hxy
  apply e.injective
  apply hv
  rw [← hcomp]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using hxy
