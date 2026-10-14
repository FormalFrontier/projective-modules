/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ProjectiveModules.Module.RightProduct.Hom
import ProjectiveModules.Module.RightRegular
import Mathlib.LinearAlgebra.Prod

/-!
# An infinite-index, semiring-only client of the right-product Hom API

The coefficients and right-regular fibers are `ℕ`, indexed by `ℕ`. The action
is `Module.piRightModule`, with Mathlib's canonical right-regular factor
action. No finite-index reconstruction or Ring instance is used.

The factor map at `i` is the additive natural-number multiple `(i + 1) • id`.
We assemble it using `Module.piRightHomAddEquiv.symm`, compute a nonzero value,
and recover its components by the Hom correspondence and supported-input API.
A second assembly uses `Module.piRightEndEquiv.symm`; its square is computed
through the multiplication and inverse-evaluation API, with ordinary
endomorphism multiplication `f * g = f.comp g`.

Finally, the Hom correspondence assembles the factor inclusion
`ℕ → ℕ × ℕ` and first projection. Component composition and extensionality
prove that their assembled composite is the identity. The differently shaped
fibers use the product module with its canonical scalar action.
All declarations and imports in this test module are private.
-/

namespace ProjectiveModulesTests.RightProductHomNatClient

private abbrev natFactors : ℕ → Type := fun _ => ℕ
private abbrev pairFactors : ℕ → Type := fun _ => ℕ × ℕ

/-- Natural additive multiples of the right-linear identity need no scalar
module structure on the Hom space over the coefficient semiring. -/
private def natFactor (i : ℕ) : ℕ →ₗ[ℕᵐᵒᵖ] ℕ :=
  (i + 1) • (LinearMap.id : ℕ →ₗ[ℕᵐᵒᵖ] ℕ)

private theorem natFactor_apply (i n : ℕ) : natFactor i n = (i + 1) * n := by
  calc
    natFactor i n =
        (i + 1) • (LinearMap.evalAddMonoidHom n)
          (LinearMap.id : ℕ →ₗ[ℕᵐᵒᵖ] ℕ) :=
      map_nsmul (LinearMap.evalAddMonoidHom n) (i + 1)
        (LinearMap.id : ℕ →ₗ[ℕᵐᵒᵖ] ℕ)
    _ = (i + 1) * n := nsmul_eq_mul _ _

/-- The inverse Hom correspondence assembles the factor maps. -/
private noncomputable def assembledNat :
    @Module.End (ℕ → ℕ)ᵐᵒᵖ (ℕ → ℕ) _ _
      (Module.piRightModule natFactors natFactors) :=
  (Module.piRightHomAddEquiv natFactors natFactors natFactors).symm natFactor

private theorem assembledNat_apply (x : ℕ → ℕ) (i : ℕ) :
    assembledNat x i = (i + 1) * x i := by
  calc
    assembledNat x i = natFactor i (x i) :=
      Module.piRightHomAddEquiv_symm_apply
        natFactors natFactors natFactors natFactor x i
    _ = (i + 1) * x i := natFactor_apply i (x i)

private theorem assembledNat_one_at_two : assembledNat (fun _ => 1) 2 = 3 :=
  assembledNat_apply (fun _ => 1) 2

/-- The Hom correspondence recovers the factor family used for assembly. -/
private theorem assembledNat_components :
    Module.piRightHomAddEquiv natFactors natFactors natFactors assembledNat =
      natFactor :=
  (Module.piRightHomAddEquiv natFactors natFactors natFactors).apply_symm_apply _

/-- Supported functions are independent of the decidable equality on `ℕ`. -/
private theorem natSingle_eq_classical (i n : ℕ) :
    (Pi.single i n : ℕ → ℕ) =
      @Pi.single ℕ natFactors
        (fun _ => Nat.instAddCommMonoid.toAddZeroClass.toAddZero.toZero)
        (fun a b => Classical.propDecidable (a = b)) i n := by
  exact congrArg
    (fun d : DecidableEq ℕ =>
      @Pi.single ℕ natFactors
        (fun _ => Nat.instAddCommMonoid.toAddZeroClass.toAddZero.toZero) d i n)
    (Subsingleton.elim instDecidableEqNat
      (fun a b => Classical.propDecidable (a = b)))

/-- Compute a supported input using the component correspondence. -/
private theorem assembledNat_supported_value : assembledNat (Pi.single 2 1) 2 = 3 := by
  calc
    assembledNat (Pi.single 2 1) 2 = assembledNat
        (@Pi.single ℕ natFactors
          (fun _ => Nat.instAddCommMonoid.toAddZeroClass.toAddZero.toZero)
          (fun a b => Classical.propDecidable (a = b)) 2 1) 2 :=
      congrArg (fun x : ℕ → ℕ => assembledNat x 2) (natSingle_eq_classical 2 1)
    _ = Module.piRightHomAddEquiv natFactors natFactors natFactors assembledNat 2 1 :=
      (Module.piRightHomAddEquiv_apply
        natFactors natFactors natFactors assembledNat 2 1).symm
    _ = natFactor 2 1 :=
      congrArg (fun φ : ∀ i : ℕ, ℕ →ₗ[ℕᵐᵒᵖ] ℕ => φ 2 1) assembledNat_components
    _ = 3 := natFactor_apply 2 1

private theorem assembledNat_supported_image :
    assembledNat (Pi.single 2 1) = Pi.single 2 3 := by
  have hc :
      Module.piRightHomAddEquiv natFactors natFactors natFactors assembledNat 2 1 = 3 :=
    calc
      _ = natFactor 2 1 :=
        congrArg (fun φ : ∀ i : ℕ, ℕ →ₗ[ℕᵐᵒᵖ] ℕ => φ 2 1) assembledNat_components
      _ = 3 := natFactor_apply 2 1
  calc
    assembledNat (Pi.single 2 1) = assembledNat
        (@Pi.single ℕ natFactors
          (fun _ => Nat.instAddCommMonoid.toAddZeroClass.toAddZero.toZero)
          (fun a b => Classical.propDecidable (a = b)) 2 1) :=
      congrArg (fun x : ℕ → ℕ => assembledNat x) (natSingle_eq_classical 2 1)
    _ = @Pi.single ℕ natFactors
        (fun _ => Nat.instAddCommMonoid.toAddZeroClass.toAddZero.toZero)
        (fun a b => Classical.propDecidable (a = b)) 2
        (Module.piRightHomAddEquiv natFactors natFactors natFactors assembledNat 2 1) :=
      Module.piRightHomAddEquiv_single natFactors natFactors natFactors assembledNat 2 1
    _ = @Pi.single ℕ natFactors
        (fun _ => Nat.instAddCommMonoid.toAddZeroClass.toAddZero.toZero)
        (fun a b => Classical.propDecidable (a = b)) 2 3 :=
      congrArg (fun n : ℕ =>
        @Pi.single ℕ natFactors
          (fun _ => Nat.instAddCommMonoid.toAddZeroClass.toAddZero.toZero)
          (fun a b => Classical.propDecidable (a = b)) 2 n) hc
    _ = Pi.single 2 3 := (natSingle_eq_classical 2 3).symm

private theorem assembledNat_off_support : assembledNat (Pi.single 2 1) 5 = 0 := by
  calc
    assembledNat (Pi.single 2 1) 5 = assembledNat
        (@Pi.single ℕ natFactors
          (fun _ => Nat.instAddCommMonoid.toAddZeroClass.toAddZero.toZero)
          (fun a b => Classical.propDecidable (a = b)) 2 1) 5 :=
      congrArg (fun x : ℕ → ℕ => assembledNat x 5) (natSingle_eq_classical 2 1)
    _ = 0 :=
      Module.piRightHomAddEquiv_single_apply_of_ne
        natFactors natFactors natFactors assembledNat 2 5 (by decide) 1

/-- The inverse endomorphism semiring equivalence assembles the same factor family. -/
private noncomputable def assembledEnd :
    @Module.End (ℕ → ℕ)ᵐᵒᵖ (ℕ → ℕ) _ _
      (Module.piRightModule natFactors natFactors) :=
  (Module.piRightEndEquiv natFactors natFactors).symm natFactor

private theorem assembledEnd_components :
    Module.piRightEndEquiv natFactors natFactors assembledEnd = natFactor :=
  (Module.piRightEndEquiv natFactors natFactors).apply_symm_apply _

/-- The End API uses the same additive correspondence as the Hom API. -/
private theorem assembledEnd_hom_components :
    Module.piRightHomAddEquiv natFactors natFactors natFactors assembledEnd =
      natFactor := by
  rw [← Module.piRightEndEquiv_toAddEquiv natFactors natFactors]
  exact assembledEnd_components

private theorem hom_end_assemblies_agree : assembledNat = assembledEnd := by
  apply (Module.piRightHomAddEquiv_ext_iff
    natFactors natFactors natFactors assembledNat assembledEnd).2
  intro i n
  rw [assembledNat_components, assembledEnd_hom_components]

private noncomputable def squaredEnd :
    @Module.End (ℕ → ℕ)ᵐᵒᵖ (ℕ → ℕ) _ _
      (Module.piRightModule natFactors natFactors) := by
  letI : Module (ℕ → ℕ)ᵐᵒᵖ (ℕ → ℕ) :=
    Module.piRightModule natFactors natFactors
  exact assembledEnd * assembledEnd

/-- Multiplication of assembled endomorphisms recovers factor multiplication,
in the ordinary composition order. -/
private theorem squaredEnd_component (i : ℕ) :
    Module.piRightEndEquiv natFactors natFactors squaredEnd i =
      natFactor i * natFactor i := by
  let : Module (ℕ → ℕ)ᵐᵒᵖ (ℕ → ℕ) :=
    Module.piRightModule natFactors natFactors
  change Module.piRightEndEquiv natFactors natFactors
    (assembledEnd * assembledEnd) i = natFactor i * natFactor i
  rw [Module.piRightEndEquiv_mul, assembledEnd_components]

/-- The inverse End correspondence evaluates the square as `3 * 3 = 9`. -/
private theorem squaredEnd_one_at_two : squaredEnd (fun _ => 1) 2 = 9 := by
  calc
    squaredEnd (fun _ => 1) 2 =
        (Module.piRightEndEquiv natFactors natFactors).symm
          (Module.piRightEndEquiv natFactors natFactors squaredEnd) (fun _ => 1) 2 :=
      congrArg
        (fun f : @Module.End (ℕ → ℕ)ᵐᵒᵖ (ℕ → ℕ) _ _
          (Module.piRightModule natFactors natFactors) => f (fun _ => 1) 2)
        ((Module.piRightEndEquiv natFactors natFactors).symm_apply_apply squaredEnd).symm
    _ = Module.piRightEndEquiv natFactors natFactors squaredEnd 2 1 :=
      Module.piRightEndEquiv_symm_apply natFactors natFactors
        (Module.piRightEndEquiv natFactors natFactors squaredEnd) (fun _ => 1) 2
    _ = (natFactor 2 * natFactor 2) 1 :=
      congrArg (fun f : Module.End ℕᵐᵒᵖ ℕ => f 1) (squaredEnd_component 2)
    _ = 9 := by
      rw [Module.End.mul_apply, natFactor_apply, natFactor_apply]

/-- An assembly with source fibers `ℕ` and target fibers `ℕ × ℕ`. -/
private noncomputable def assembledInl :
    @LinearMap (ℕ → ℕ)ᵐᵒᵖ (ℕ → ℕ)ᵐᵒᵖ _ _ (RingHom.id _)
      (ℕ → ℕ) (ℕ → ℕ × ℕ) _ _
      (Module.piRightModule natFactors natFactors)
      (Module.piRightModule natFactors pairFactors) :=
  (Module.piRightHomAddEquiv natFactors natFactors pairFactors).symm
    (fun _ => LinearMap.inl ℕᵐᵒᵖ ℕ ℕ)

private theorem assembledInl_component (i : ℕ) :
    Module.piRightHomAddEquiv natFactors natFactors pairFactors assembledInl i =
      LinearMap.inl ℕᵐᵒᵖ ℕ ℕ :=
  congrFun ((Module.piRightHomAddEquiv natFactors natFactors pairFactors).apply_symm_apply
    (fun _ => LinearMap.inl ℕᵐᵒᵖ ℕ ℕ)) i

private theorem assembledInl_one_at_two :
    assembledInl (fun _ => 1) 2 = (1, 0) := by
  rw [assembledInl, Module.piRightHomAddEquiv_symm_apply, LinearMap.inl_apply]

private noncomputable def assembledFst :
    @LinearMap (ℕ → ℕ)ᵐᵒᵖ (ℕ → ℕ)ᵐᵒᵖ _ _ (RingHom.id _)
      (ℕ → ℕ × ℕ) (ℕ → ℕ) _ _
      (Module.piRightModule natFactors pairFactors)
      (Module.piRightModule natFactors natFactors) :=
  (Module.piRightHomAddEquiv natFactors pairFactors natFactors).symm
    (fun _ => LinearMap.fst ℕᵐᵒᵖ ℕ ℕ)

private theorem assembledFst_component (i : ℕ) :
    Module.piRightHomAddEquiv natFactors pairFactors natFactors assembledFst i =
      LinearMap.fst ℕᵐᵒᵖ ℕ ℕ :=
  congrFun ((Module.piRightHomAddEquiv natFactors pairFactors natFactors).apply_symm_apply
    (fun _ => LinearMap.fst ℕᵐᵒᵖ ℕ ℕ)) i

private noncomputable def assembledRetraction :
    @Module.End (ℕ → ℕ)ᵐᵒᵖ (ℕ → ℕ) _ _
      (Module.piRightModule natFactors natFactors) := by
  letI : Module (ℕ → ℕ)ᵐᵒᵖ (ℕ → ℕ) :=
    Module.piRightModule natFactors natFactors
  letI : Module (ℕ → ℕ)ᵐᵒᵖ (ℕ → ℕ × ℕ) :=
    Module.piRightModule natFactors pairFactors
  exact assembledFst.comp assembledInl

/-- Component composition, identity and extensionality prove the retraction
law for the assembled heterogeneous-fiber maps. -/
private theorem assembledRetraction_eq_id :
    assembledRetraction =
      @LinearMap.id (ℕ → ℕ)ᵐᵒᵖ (ℕ → ℕ) _ _
        (Module.piRightModule natFactors natFactors) := by
  let : Module (ℕ → ℕ)ᵐᵒᵖ (ℕ → ℕ) :=
    Module.piRightModule natFactors natFactors
  let : Module (ℕ → ℕ)ᵐᵒᵖ (ℕ → ℕ × ℕ) :=
    Module.piRightModule natFactors pairFactors
  apply (Module.piRightHomAddEquiv_ext_iff
    natFactors natFactors natFactors _ _).2
  intro i n
  change Module.piRightHomAddEquiv natFactors natFactors natFactors
    (assembledFst.comp assembledInl) i n =
      Module.piRightHomAddEquiv natFactors natFactors natFactors LinearMap.id i n
  rw [Module.piRightHomAddEquiv_comp, assembledFst_component,
    assembledInl_component, Module.piRightHomAddEquiv_id, LinearMap.fst_comp_inl]

end ProjectiveModulesTests.RightProductHomNatClient
