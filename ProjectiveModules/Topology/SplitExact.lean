/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Split exact sequences of topological semimodules

An exact sequence with an embedded kernel and a continuous linear section splits
as the product of its quotient and kernel. Only the middle semimodule needs an
additive group structure. Continuity of the negative of the section replaces
continuity of negation on the entire middle semimodule.

All topologies are prescribed. The section criterion needs no topology on the
scalar semiring. For a projective quotient with its prescribed module topology,
the section and its negative are continuous by the universal property of the
module topology. Thus continuous addition and scalar multiplication on the
middle semimodule suffice for a splitting.
-/

public section

universe uR uA uB uC

namespace LinearMap

variable {R : Type uR} [Semiring R]
variable {A : Type uA} [AddCommMonoid A] [Module R A]
variable {B : Type uB} [AddCommGroup B] [Module R B]
variable {C : Type uC} [AddCommMonoid C] [Module R C]
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
variable [ContinuousAdd B]

/-- A split exact sequence of semimodules with embedded kernel is continuously
linearly equivalent to the product of its quotient and kernel. The equivalence
has quotient map as first coordinate, sends the kernel inclusion to the second
factor, and has inverse given by the section plus the kernel inclusion. -/
theorem exists_continuousLinearEquiv_prod_of_split_exact
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (s : C →ₗ[R] B)
    (hg : Continuous g) (hf : Topology.IsEmbedding f)
    (hexact : LinearMap.range f = LinearMap.ker g)
    (hsplit : g.comp s = LinearMap.id)
    (hs : Continuous s) (hneg : Continuous (fun c : C => -s c)) :
    ∃ e : B ≃L[R] C × A,
      (∀ b : B, (e b).1 = g b) ∧
      (∀ a : A, e (f a) = (0, a)) ∧
      (∀ (c : C) (a : A), e.symm (c, a) = s c + f a) := by
  classical
  have hgs (c : C) : g (s c) = c :=
    congrArg (fun k : C →ₗ[R] C => k c) hsplit
  have hs_inj : Function.Injective s := by
    intro c d h
    simpa only [hgs] using congrArg g h
  let p : B →ₗ[R] B := s.comp g
  let h : B →ₗ[R] B := LinearMap.id - p
  have hp (b : B) : p (p b) = p b := by
    change s (g (s (g b))) = s (g b)
    rw [hgs]
  -- Apply the idempotent to the residual before using injectivity of the section;
  -- subtraction need never be transported into the quotient semimodule.
  have hker (b : B) : g (h b) = 0 := by
    apply hs_inj
    change p (b - p b) = s 0
    rw [map_sub, hp, sub_self, map_zero]
  have hpre (b : B) : ∃ a : A, f a = h b := by
    have hm : h b ∈ LinearMap.ker g := hker b
    rw [← hexact] at hm
    exact hm
  let qfun : B → A := fun b => Classical.choose (hpre b)
  have hq (b : B) : f (qfun b) = h b := Classical.choose_spec (hpre b)
  let q : B →ₗ[R] A :=
    { toFun := qfun
      map_add' := by
        intro b d
        apply hf.injective
        simp only [map_add, hq]
      map_smul' := by
        intro r b
        apply hf.injective
        simp only [map_smul, hq, RingHom.id_apply] }
  have hqf (b : B) : f (q b) = h b := hq b
  have hgf (a : A) : g (f a) = 0 := by
    have hm : f a ∈ LinearMap.range f := ⟨a, rfl⟩
    rw [hexact] at hm
    exact hm
  have hq_f (a : A) : q (f a) = a := by
    apply hf.injective
    rw [hqf]
    change f a - s (g (f a)) = f a
    rw [hgf, map_zero, sub_zero]
  have hq_s (c : C) : q (s c) = 0 := by
    apply hf.injective
    rw [hqf, map_zero]
    change s c - s (g (s c)) = 0
    rw [hgs, sub_self]
  have hcont : Continuous h := by
    change Continuous (fun b : B => b - s (g b))
    apply (continuous_id.add (hneg.comp hg)).congr
    intro b
    simp only [Pi.add_apply, Function.comp_apply, id_eq, sub_eq_add_neg]
  have hqcont : Continuous q := by
    apply hf.continuous_iff.mpr
    simpa only [Function.comp_def, hqf] using hcont
  let e : B ≃L[R] C × A :=
    { toLinearEquiv :=
        { toFun := fun b => (g b, q b)
          invFun := fun z => s z.1 + f z.2
          left_inv := by
            intro b
            change s (g b) + f (q b) = b
            rw [hqf]
            change s (g b) + (b - s (g b)) = b
            rw [← add_sub_assoc, add_comm (s (g b)) b, add_sub_assoc, sub_self, add_zero]
          right_inv := by
            intro z
            apply Prod.ext
            · change g (s z.1 + f z.2) = z.1
              rw [map_add, hgs, hgf, add_zero]
            · change q (s z.1 + f z.2) = z.2
              rw [map_add, hq_s, hq_f, zero_add]
          map_add' := by
            intro b d
            exact Prod.ext (g.map_add b d) (q.map_add b d)
          map_smul' := by
            intro r b
            exact Prod.ext (g.map_smul r b) (q.map_smul r b) }
      continuous_toFun := hg.prodMk hqcont
      continuous_invFun :=
        (hs.comp continuous_fst).add (hf.continuous.comp continuous_snd) }
  refine ⟨e, fun _ => rfl, ?_, fun _ _ => rfl⟩
  intro a
  change (g (f a), q (f a)) = (0, a)
  rw [hgf, hq_f]

end LinearMap

namespace ContinuousLinearMap

variable {R : Type uR} [Semiring R] [TopologicalSpace R]
variable {A : Type uA} [AddCommMonoid A] [Module R A]
variable {B : Type uB} [AddCommGroup B] [Module R B]
variable {C : Type uC} [AddCommMonoid C] [Module R C]
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
variable [ContinuousAdd B] [ContinuousSMul R B]
variable [Module.Projective R C] [IsModuleTopology R C]

/-- An exact sequence with embedded kernel and projective quotient endowed with
its prescribed module topology splits as the product of quotient and kernel.
The equivalence has quotient map as first coordinate and sends the kernel
inclusion to the second factor. Only the middle semimodule needs continuous
addition and scalar multiplication; continuity of negation is not assumed. -/
theorem exists_continuousLinearEquiv_prod_of_projective_exact
    (f : A →L[R] B) (g : B →L[R] C)
    (hf : Topology.IsEmbedding f)
    (hexact : LinearMap.range (f : A →ₗ[R] B) = LinearMap.ker (g : B →ₗ[R] C))
    (hsurj : Function.Surjective g) :
    ∃ e : B ≃L[R] C × A,
      (∀ b : B, (e b).1 = g b) ∧
      (∀ a : A, e (f a) = (0, a)) := by
  obtain ⟨s, hsplit⟩ :=
    Module.projective_lifting_property g.toLinearMap
      (LinearMap.id : C →ₗ[R] C) hsurj
  have hs : Continuous s := IsModuleTopology.continuous_of_linearMap s
  have hneg : Continuous (fun c : C => -s c) :=
    IsModuleTopology.continuous_of_linearMap (-s)
  obtain ⟨e, hfst, hincl, _⟩ :=
    LinearMap.exists_continuousLinearEquiv_prod_of_split_exact
      f.toLinearMap g.toLinearMap s g.continuous hf hexact hsplit hs hneg
  exact ⟨e, hfst, hincl⟩

end ContinuousLinearMap
