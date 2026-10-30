/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Prod

/-!
# Quotients by an intersection and a sum

For submodules `U` and `V` of `M`, `diagonal` sends the class of `m` modulo
`U ⊓ V` to its classes modulo `U` and `V`. The map `difference` sends a pair of
classes represented by `x` and `y` to the class of `x - y` modulo `U ⊔ V`.
Both maps use the existing quotient factor maps and product constructions.

These maps form a short exact sequence: `diagonal` is injective, `difference` is
surjective, and `exact_diagonal_difference` identifies the image of `diagonal`
with the elements killed by `difference`. The application lemmas describe both
maps on quotient representatives without unfolding their definitions.

The ring may be noncommutative or zero. The ring and module universes are independent,
and every quotient retains the given module structure.

## References

* Mathlib's submodule quotient factor maps in
  `Mathlib.LinearAlgebra.Quotient.Basic`.
* Mathlib's linear-map product and coproduct in `Mathlib.LinearAlgebra.Prod`.
-/

@[expose] public section

universe uS uM

namespace Submodule.QuotientIntersection

variable {S : Type uS} [Ring S]
variable {M : Type uM} [AddCommGroup M] [Module S M]

/-- The diagonal map from the intersection quotient to the product of the two quotients. -/
def diagonal (U V : Submodule S M) : (M ⧸ (U ⊓ V)) →ₗ[S] (M ⧸ U) × (M ⧸ V) :=
  (Submodule.factor (show U ⊓ V ≤ U from inf_le_left)).prod
    (Submodule.factor (show U ⊓ V ≤ V from inf_le_right))

/-- The difference of the two factor maps to the sum quotient, with the second factor
negated: a pair represented by `(x, y)` maps to the class of `x - y`. -/
def difference (U V : Submodule S M) : (M ⧸ U) × (M ⧸ V) →ₗ[S] M ⧸ (U ⊔ V) :=
  (Submodule.factor (show U ≤ U ⊔ V from le_sup_left)).coprod
    (-(Submodule.factor (show V ≤ U ⊔ V from le_sup_right)))

/-- The first component of the diagonal is the factor map to the quotient by `U`. -/
@[simp]
theorem diagonal_fst (U V : Submodule S M) (q : M ⧸ (U ⊓ V)) :
    (diagonal U V q).1 = Submodule.factor (show U ⊓ V ≤ U from inf_le_left) q := rfl

/-- The second component of the diagonal is the factor map to the quotient by `V`. -/
@[simp]
theorem diagonal_snd (U V : Submodule S M) (q : M ⧸ (U ⊓ V)) :
    (diagonal U V q).2 = Submodule.factor (show U ⊓ V ≤ V from inf_le_right) q := rfl

/-- The diagonal sends a quotient-map image to its two quotient-map images. -/
theorem diagonal_mkQ (U V : Submodule S M) (x : M) :
    diagonal U V ((U ⊓ V).mkQ x) = (U.mkQ x, V.mkQ x) := by
  simp [diagonal]

/-- The diagonal sends a representative to its two quotient classes. -/
@[simp]
theorem diagonal_mk (U V : Submodule S M) (x : M) :
    diagonal U V (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x, Submodule.Quotient.mk x) := diagonal_mkQ U V x

/-- The difference map subtracts the two images in the sum quotient. -/
theorem difference_apply (U V : Submodule S M) (q : (M ⧸ U) × (M ⧸ V)) :
    difference U V q =
      Submodule.factor (show U ≤ U ⊔ V from le_sup_left) q.1 -
        Submodule.factor (show V ≤ U ⊔ V from le_sup_right) q.2 := by
  simp [difference, sub_eq_add_neg]

/-- The difference of quotient-map images is the quotient-map image of the difference. -/
theorem difference_mkQ (U V : Submodule S M) (x y : M) :
    difference U V (U.mkQ x, V.mkQ y) = (U ⊔ V).mkQ (x - y) := by
  simp [difference_apply, map_sub]

/-- On representatives the difference map sends `(x, y)` to the class of `x - y`. -/
@[simp]
theorem difference_mk (U V : Submodule S M) (x y : M) :
    difference U V (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x - y) := difference_mkQ U V x y

/-- Every element in the diagonal image is killed by the difference map. -/
@[simp]
theorem difference_diagonal (U V : Submodule S M) (q : M ⧸ (U ⊓ V)) :
    difference U V (diagonal U V q) = 0 := by
  obtain ⟨x, rfl⟩ := (U ⊓ V).mkQ_surjective q
  simp only [diagonal_mkQ, difference_mkQ, sub_self, map_zero]

/-- A class modulo the intersection is determined by its two quotient classes. -/
theorem diagonal_injective (U V : Submodule S M) : Function.Injective (diagonal U V) := by
  intro a b h
  obtain ⟨x, rfl⟩ := (U ⊓ V).mkQ_surjective a
  obtain ⟨y, rfl⟩ := (U ⊓ V).mkQ_surjective b
  have h' : (U.mkQ x, V.mkQ x) = (U.mkQ y, V.mkQ y) := by
    simpa only [diagonal_mkQ] using h
  apply (Submodule.Quotient.eq (U ⊓ V)).mpr
  exact ⟨(Submodule.Quotient.eq U).mp (congrArg Prod.fst h'),
    (Submodule.Quotient.eq V).mp (congrArg Prod.snd h')⟩

/-- Every class modulo the sum is the difference of two quotient classes. -/
theorem difference_surjective (U V : Submodule S M) :
    Function.Surjective (difference U V) := by
  intro q
  obtain ⟨x, rfl⟩ := (U ⊔ V).mkQ_surjective q
  refine ⟨(U.mkQ x, V.mkQ 0), ?_⟩
  rw [difference_mkQ, sub_zero]

/-- The diagonal image consists exactly of the pairs killed by the difference map. -/
theorem exact_diagonal_difference (U V : Submodule S M) :
    Function.Exact (diagonal U V) (difference U V) := by
  intro q
  rcases q with ⟨a, b⟩
  obtain ⟨x, rfl⟩ := U.mkQ_surjective a
  obtain ⟨y, rfl⟩ := V.mkQ_surjective b
  constructor
  · intro h
    have hxy : x - y ∈ U ⊔ V := by
      rw [difference_mkQ] at h
      exact (Submodule.Quotient.mk_eq_zero (U ⊔ V)).mp h
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hxy
    have hu0 : U.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hu
    have hv0 : V.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero V).mpr hv
    have hz : x - u = y + v := by
      rw [sub_eq_iff_eq_add]
      calc
        x = (x - y) + y := (sub_add_cancel x y).symm
        _ = (u + v) + y := by rw [huv]
        _ = (y + v) + u := by ac_rfl
    refine ⟨(U ⊓ V).mkQ (x - u), ?_⟩
    rw [diagonal_mkQ]
    apply Prod.ext
    · simp only [map_sub, hu0, sub_zero]
    · simp only [hz, map_add, hv0, add_zero]
  · rintro ⟨z, hz⟩
    rw [← hz]
    exact difference_diagonal U V z

end Submodule.QuotientIntersection
