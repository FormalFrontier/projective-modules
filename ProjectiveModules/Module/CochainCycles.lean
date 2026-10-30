/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import StableRange.Module.SplitSurjective

/-!
# Cycles of a null-homotopic cochain complex of modules

A homotopy from the identity to zero splits each term of a cochain complex into
its cycles and the cycles in the next degree. The cycles here are the linear-map
kernels of the differentials on the given modules, without a change of carriers
or scalar ring. The resulting retraction shows that finite generation and module
projectivity pass from a term to its cycles.

The splitting uses Mathlib's `lequivProdOfRightSplitExact`; its application formula
is supplied by `StableRange.Module.SplitSurjective`. No normalization of the
homotopy, such as the vanishing of its square, is required.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CochainComplex

variable {S : Type u} [Ring S] (C : CochainComplex (ModuleCat.{v} S) ℤ)

/-- The differential with codomain restricted to the kernel of the next differential. -/
def moduleToCycles (i : ℤ) :
    C.X i →ₗ[S] LinearMap.ker ((C.d (i + 1) (i + 1 + 1)).hom) :=
  (C.d i (i + 1)).hom.codRestrict _ fun x => by
    apply LinearMap.mem_ker.mpr
    have hd := congrArg
      (fun f : C.X i ⟶ C.X (i + 1 + 1) => f.hom x)
      (C.d_comp_d i (i + 1) (i + 1 + 1))
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero,
      LinearMap.comp_apply, LinearMap.zero_apply] using hd

@[simp] theorem moduleToCycles_apply_coe (i : ℤ) (x : C.X i) :
    (C.moduleToCycles i x : C.X (i + 1)) = (C.d i (i + 1)).hom x := rfl

@[simp] theorem moduleToCycles_coe (i : ℤ)
    (z : LinearMap.ker ((C.d i (i + 1)).hom)) :
    C.moduleToCycles i (z : C.X i) = 0 := by
  apply Subtype.ext
  simpa only [moduleToCycles_apply_coe, ZeroMemClass.coe_zero] using
    (LinearMap.mem_ker.mp z.property)

variable (h : Homotopy (𝟙 C) 0)

/-- The homotopy identity in degree `i + 1`, expressed on the original module maps. -/
theorem homotopy_id_next_apply (i : ℤ) (x : C.X (i + 1)) :
    (h.hom (i + 1 + 1) (i + 1)).hom ((C.d (i + 1) (i + 1 + 1)).hom x) +
      (C.d i (i + 1)).hom ((h.hom (i + 1) i).hom x) = x := by
  have he := h.comm (i + 1)
  rw [HomologicalComplex.id_f, HomologicalComplex.zero_f, add_zero,
    dNext_eq h.hom (ComplexShape.up_mk (i + 1) (i + 1 + 1) rfl),
    prevD_eq h.hom (ComplexShape.up_mk i (i + 1) rfl)] at he
  have hx := congrArg (fun f : C.X (i + 1) ⟶ C.X (i + 1) => f.hom x) he
  simpa only [ModuleCat.hom_id, ModuleCat.hom_add, ModuleCat.hom_comp,
    LinearMap.id_apply, LinearMap.add_apply, LinearMap.comp_apply] using hx.symm

/-- The homotopy restricted to the cycles in the next degree. -/
def moduleCyclesSection (i : ℤ) :
    LinearMap.ker ((C.d (i + 1) (i + 1 + 1)).hom) →ₗ[S] C.X i :=
  (h.hom (i + 1) i).hom.comp
    (LinearMap.ker ((C.d (i + 1) (i + 1 + 1)).hom)).subtype

@[simp] theorem moduleCyclesSection_apply (i : ℤ)
    (y : LinearMap.ker ((C.d (i + 1) (i + 1 + 1)).hom)) :
    C.moduleCyclesSection h i y = (h.hom (i + 1) i).hom (y : C.X (i + 1)) := rfl

/-- The differential onto the next cycles has the section supplied by the homotopy. -/
theorem moduleToCycles_comp_section (i : ℤ) :
    (C.moduleToCycles i).comp (C.moduleCyclesSection h i) = LinearMap.id := by
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  have hy : (C.d (i + 1) (i + 1 + 1)).hom (y : C.X (i + 1)) = 0 :=
    LinearMap.mem_ker.mp y.property
  simpa only [LinearMap.comp_apply, LinearMap.id_apply, moduleToCycles_apply_coe,
    moduleCyclesSection_apply, hy, map_zero, zero_add] using
    C.homotopy_id_next_apply h i (y : C.X (i + 1))

/-- The inclusion of the differential kernel has range equal to the kernel of
`moduleToCycles`. -/
theorem range_subtype_eq_ker_moduleToCycles (i : ℤ) :
    LinearMap.range (LinearMap.ker ((C.d i (i + 1)).hom)).subtype =
      LinearMap.ker (C.moduleToCycles i) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact LinearMap.mem_ker.mpr (C.moduleToCycles_coe i z)
  · intro hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    apply LinearMap.mem_ker.mpr
    have he : C.moduleToCycles i x = 0 := LinearMap.mem_ker.mp hx
    have he' := congrArg
      (fun y : LinearMap.ker ((C.d (i + 1) (i + 1 + 1)).hom) =>
        (y : C.X (i + 1))) he
    simpa only [moduleToCycles_apply_coe, ZeroMemClass.coe_zero] using he'

/-- A term of a null-homotopic cochain complex is the product of two adjacent
linear-map kernels. This is Mathlib's right-split exact-sequence equivalence. -/
noncomputable def moduleCyclesEquiv (i : ℤ) :
    (LinearMap.ker ((C.d i (i + 1)).hom) ×
      LinearMap.ker ((C.d (i + 1) (i + 1 + 1)).hom)) ≃ₗ[S] C.X i :=
  lequivProdOfRightSplitExact
    (j := (LinearMap.ker ((C.d i (i + 1)).hom)).subtype)
    (g := C.moduleToCycles i) (f := C.moduleCyclesSection h i)
    Subtype.val_injective (range_subtype_eq_ker_moduleToCycles C i)
    (C.moduleToCycles_comp_section h i)

@[simp] theorem moduleCyclesEquiv_apply (i : ℤ)
    (p : LinearMap.ker ((C.d i (i + 1)).hom) ×
      LinearMap.ker ((C.d (i + 1) (i + 1 + 1)).hom)) :
    C.moduleCyclesEquiv h i p = (p.1 : C.X i) + C.moduleCyclesSection h i p.2 := by
  exact lequivProdOfRightSplitExact_apply
    Subtype.val_injective (range_subtype_eq_ker_moduleToCycles C i)
    (C.moduleToCycles_comp_section h i) p.1 p.2

/-- The second coordinate of the splitting is the original differential. -/
@[simp] theorem moduleCyclesEquiv_symm_snd (i : ℤ) (x : C.X i) :
    ((C.moduleCyclesEquiv h i).symm x).2 = C.moduleToCycles i x := by
  have he := congrArg (C.moduleToCycles i)
    ((C.moduleCyclesEquiv h i).apply_symm_apply x)
  rw [moduleCyclesEquiv_apply, map_add, moduleToCycles_coe] at he
  have hs : C.moduleToCycles i
      (C.moduleCyclesSection h i ((C.moduleCyclesEquiv h i).symm x).2) =
        ((C.moduleCyclesEquiv h i).symm x).2 := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using congrArg
      (fun f : LinearMap.ker ((C.d (i + 1) (i + 1 + 1)).hom) →ₗ[S]
        LinearMap.ker ((C.d (i + 1) (i + 1 + 1)).hom) =>
          f ((C.moduleCyclesEquiv h i).symm x).2)
      (C.moduleToCycles_comp_section h i)
  simpa only [hs, zero_add] using he

/-- The first coordinate subtracts the section of the differential. -/
@[simp] theorem moduleCyclesEquiv_symm_fst_coe (i : ℤ) (x : C.X i) :
    (((C.moduleCyclesEquiv h i).symm x).1 : C.X i) =
      x - (h.hom (i + 1) i).hom ((C.d i (i + 1)).hom x) := by
  have he := (C.moduleCyclesEquiv h i).apply_symm_apply x
  rw [moduleCyclesEquiv_apply, moduleCyclesEquiv_symm_snd,
    moduleCyclesSection_apply, moduleToCycles_apply_coe] at he
  exact (eq_sub_iff_add_eq).mpr he

/-- The retraction of a term onto the kernel of its differential. -/
noncomputable def moduleCyclesProjection (i : ℤ) :
    C.X i →ₗ[S] LinearMap.ker ((C.d i (i + 1)).hom) :=
  (LinearMap.fst S (LinearMap.ker ((C.d i (i + 1)).hom))
    (LinearMap.ker ((C.d (i + 1) (i + 1 + 1)).hom))).comp
    (C.moduleCyclesEquiv h i).symm.toLinearMap

@[simp] theorem moduleCyclesProjection_apply_coe (i : ℤ) (x : C.X i) :
    (C.moduleCyclesProjection h i x : C.X i) =
      x - (h.hom (i + 1) i).hom ((C.d i (i + 1)).hom x) :=
  C.moduleCyclesEquiv_symm_fst_coe h i x

@[simp] theorem moduleCyclesProjection_coe (i : ℤ)
    (z : LinearMap.ker ((C.d i (i + 1)).hom)) :
    C.moduleCyclesProjection h i (z : C.X i) = z := by
  apply Subtype.ext
  have hz : (C.d i (i + 1)).hom (z : C.X i) = 0 :=
    LinearMap.mem_ker.mp z.property
  simp only [moduleCyclesProjection_apply_coe, hz, map_zero, sub_zero]

/-- The projection is a retraction of the inclusion of the differential kernel. -/
theorem moduleCyclesProjection_comp_subtype (i : ℤ) :
    (C.moduleCyclesProjection h i).comp
      (LinearMap.ker ((C.d i (i + 1)).hom)).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro z
  exact C.moduleCyclesProjection_coe h i z

/-- Cycles of a null-homotopic cochain complex are finite when their source term is finite. -/
theorem moduleFinite_cycles (h : Homotopy (𝟙 C) 0) (i : ℤ)
    [Module.Finite S (C.X i)] :
    Module.Finite S (LinearMap.ker ((C.d i (i + 1)).hom)) := by
  apply Module.Finite.of_surjective (C.moduleCyclesProjection h i)
  intro z
  exact ⟨(z : C.X i), C.moduleCyclesProjection_coe h i z⟩

/-- Cycles of a null-homotopic cochain complex are projective when their source term is
projective, by the algebraic retraction onto the differential kernel. -/
theorem moduleProjective_cycles (h : Homotopy (𝟙 C) 0) (i : ℤ)
    [Module.Projective S (C.X i)] :
    Module.Projective S (LinearMap.ker ((C.d i (i + 1)).hom)) :=
  Module.Projective.of_split
    (LinearMap.ker ((C.d i (i + 1)).hom)).subtype (C.moduleCyclesProjection h i)
    (C.moduleCyclesProjection_comp_subtype h i)

end CochainComplex
