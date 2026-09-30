# Generated API reference

This is a **historical native display**, not an exhaustive current-release API.
Doc-gen4 on original source `5d1b1b276d4a11ee6ce9ae238c9511de8dbec1e9`
selected 43 modules and displayed 469 named sites, with 477 database name rows
(eight non-displayed private names) and 47 module-documentation positions.
The released tree contains 44 Lean files: the later
`ProjectiveModules/Module/CountablyGenerated/Noetherian.lean` is guide-only in
[this documentation](NoetherianSubmodule.md), **outside** the 43-module run.
Neither the displayed sites nor the historical manifest field
`public_display_names` constitute an exported-declaration census: displayed
names include local instances. The example and private regression clients do
not export their private declarations.

Headers below reproduce historical native *display* signatures, including
visible modifiers and implicit parameters, except for the two explicitly
marked source-inspected `[Finite I]` amendments. Relative source links point
into this checkout; corrected `ComponentwiseFree` and `RightExtension` ranges
may differ from parenthetical historical native database ranges. The
[manifest](api-manifest.json) remains bound to the original source and native
records, not these later source-inspected edits. No new native output, current
all-files census, proof audit or source-coverage certification is asserted.
Headers are not proof bodies; pretty-printing can suppress inferable types.
Consult the linked source for elaboration context.
[Generation and limits](README.md) · [Credits](CREDITS.md) ·
[source and tool manifest](api-manifest.json).

Missing source docstrings are explicitly marked; no authored notes are passed off as native docs.

## ProjectiveModules

Scope: aggregate public-import root.

No native public display sites in this module.

## ProjectiveModules.Category.FiniteProjective

Scope: mathematical library leaf.

### ModuleCat.isFiniteProjective

```lean
def ModuleCat.isFiniteProjective (R : Type uR) [Ring R] : CategoryTheory.ObjectProperty (ModuleCat R)
```

The property of a module being both finitely generated and projective.

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L36-L38) (native database range lines 36–38).

### ModuleCat.isFiniteProjective_iff

```lean
theorem ModuleCat.isFiniteProjective_iff {R : Type uR} [Ring R] (P : ModuleCat R) : isFiniteProjective R P ↔ Module.Finite R ↑P ∧ Module.Projective R ↑P
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L41-L43) (native database range lines 41–43).

### ModuleCat.FiniteProjective

```lean
abbrev ModuleCat.FiniteProjective (R : Type uR) [Ring R] : Type (max (uM + 1) uR)
```

The full subcategory of finitely generated projective `R`-modules.

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L45-L46) (native database range lines 45–46).

### ModuleCat.FiniteProjective.carrier

```lean
def ModuleCat.FiniteProjective.carrier {R : Type uR} [Ring R] (M : FiniteProjective R) : Type uM
```

The underlying type of a finite projective module.

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L51-L53) (native database range lines 51–53).

### ModuleCat.FiniteProjective.instCoeSortType

```lean
instance ModuleCat.FiniteProjective.instCoeSortType (R : Type uR) [Ring R] : CoeSort (FiniteProjective R) (Type uM)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L55-L56) (native database range lines 55–56).

### ModuleCat.FiniteProjective.obj_carrier

```lean
theorem ModuleCat.FiniteProjective.obj_carrier (R : Type uR) [Ring R] (M : FiniteProjective R) : ↑M.obj = ↑M
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L60-L61) (native database range lines 60–61).

### ModuleCat.FiniteProjective.instFiniteCarrier

```lean
instance ModuleCat.FiniteProjective.instFiniteCarrier (R : Type uR) [Ring R] (M : FiniteProjective R) : Module.Finite R ↑M
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L63-L64) (native database range lines 63–64).

### ModuleCat.FiniteProjective.instProjectiveCarrier

```lean
instance ModuleCat.FiniteProjective.instProjectiveCarrier (R : Type uR) [Ring R] (M : FiniteProjective R) : Module.Projective R ↑M
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L66-L67) (native database range lines 66–67).

### ModuleCat.FiniteProjective.of

```lean
abbrev ModuleCat.FiniteProjective.of (R : Type uR) [Ring R] (M : Type uM) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] : FiniteProjective R
```

Bundle an unbundled finite projective module.

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L69-L72) (native database range lines 69–72).

### ModuleCat.FiniteProjective.of_carrier

```lean
theorem ModuleCat.FiniteProjective.of_carrier (R : Type uR) [Ring R] (M : Type uM) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] : ↑(of R M) = M
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L74-L77) (native database range lines 74–77).

### ModuleCat.FiniteProjective.ofHom

```lean
abbrev ModuleCat.FiniteProjective.ofHom (R : Type uR) [Ring R] {M N : Type uM} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N] (f : M →ₗ[R] N) : of R M ⟶ of R N
```

Bundle a linear map between finite projective modules.

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L79-L85) (native database range lines 79–85).

### ModuleCat.FiniteProjective.hom_ext

```lean
theorem ModuleCat.FiniteProjective.hom_ext (R : Type uR) [Ring R] {X Y : FiniteProjective R} {f g : X ⟶ Y} (h : Hom.hom f.hom = Hom.hom g.hom) : f = g
```

Two morphisms of finite projective modules are equal when their underlying
linear maps are equal.

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L87-L92) (native database range lines 87–92).

### ModuleCat.FiniteProjective.hom_ext_iff

```lean
theorem ModuleCat.FiniteProjective.hom_ext_iff {R : Type uR} [Ring R] {X Y : FiniteProjective R} {f g : X ⟶ Y} : f = g ↔ Hom.hom f.hom = Hom.hom g.hom
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L89-L89) (native database range lines 89–89).

### ModuleCat.FiniteProjective.homLinearEquiv

```lean
def ModuleCat.FiniteProjective.homLinearEquiv (R : Type uR) [Ring R] (X Y : FiniteProjective R) : (X ⟶ Y) ≃ (↑X →ₗ[R] ↑Y)
```

Morphisms in `ModuleCat.FiniteProjective R` are the underlying linear maps.

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L94-L97) (native database range lines 94–97).

### ModuleCat.finiteProjective_prod

```lean
theorem ModuleCat.finiteProjective_prod (R : Type uR) [Ring R] {P Q : Type uM} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (hP : Module.Finite R P ∧ Module.Projective R P) (hQ : Module.Finite R Q ∧ Module.Projective R Q) : Module.Finite R (P × Q) ∧ Module.Projective R (P × Q)
```

The product of two finite projective modules is finite projective.

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L101-L112) (native database range lines 101–112).

### ModuleCat.isFiniteProjectiveIsClosedUnderIsomorphisms

```lean
instance ModuleCat.isFiniteProjectiveIsClosedUnderIsomorphisms (R : Type uR) [Ring R] : (isFiniteProjective R).IsClosedUnderIsomorphisms
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L114-L120) (native database range lines 114–120).

### ModuleCat.isFiniteProjectiveContainsZero

```lean
instance ModuleCat.isFiniteProjectiveContainsZero (R : Type uR) [Ring R] : (isFiniteProjective R).ContainsZero
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L122-L127) (native database range lines 122–127).

### ModuleCat.isFiniteProjectiveIsClosedUnderBinaryProducts

```lean
instance ModuleCat.isFiniteProjectiveIsClosedUnderBinaryProducts (R : Type uR) [Ring R] : (isFiniteProjective R).IsClosedUnderBinaryProducts
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L129-L144) (native database range lines 129–144).

### ModuleCat.isFiniteProjectiveIsClosedUnderFiniteProducts

```lean
instance ModuleCat.isFiniteProjectiveIsClosedUnderFiniteProducts (R : Type uR) [Ring R] : (isFiniteProjective R).IsClosedUnderFiniteProducts
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L146-L148) (native database range lines 146–148).

### ModuleCat.finiteProjectiveHasFiniteBiproducts

```lean
instance ModuleCat.finiteProjectiveHasFiniteBiproducts (R : Type uR) [Ring R] : CategoryTheory.Limits.HasFiniteBiproducts (FiniteProjective R)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/FiniteProjective.lean#L150-L152) (native database range lines 150–152).

## ProjectiveModules.Category.Stable

Scope: mathematical library leaf.

### ModuleCat.FactorsThroughProjective

```lean
def ModuleCat.FactorsThroughProjective (R : Type uR) [Ring R] {M N : ModuleCat R} (f : M ⟶ N) : Prop
```

A module morphism factors through a projective module.

[Source](../ProjectiveModules/Category/Stable.lean#L37-L40) (native database range lines 37–40).

### ModuleCat.FactorsThroughProjective.zero

```lean
theorem ModuleCat.FactorsThroughProjective.zero {R : Type uR} [Ring R] {M N : ModuleCat R} : FactorsThroughProjective R 0
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/Stable.lean#L46-L49) (native database range lines 46–49).

### ModuleCat.FactorsThroughProjective.add

```lean
theorem ModuleCat.FactorsThroughProjective.add {R : Type uR} [Ring R] {M N : ModuleCat R} {f g : M ⟶ N} (hf : FactorsThroughProjective R f) (hg : FactorsThroughProjective R g) : FactorsThroughProjective R (f + g)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/Stable.lean#L51-L59) (native database range lines 51–59).

### ModuleCat.FactorsThroughProjective.neg

```lean
theorem ModuleCat.FactorsThroughProjective.neg {R : Type uR} [Ring R] {M N : ModuleCat R} {f : M ⟶ N} (hf : FactorsThroughProjective R f) : FactorsThroughProjective R (-f)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/Stable.lean#L61-L65) (native database range lines 61–65).

### ModuleCat.FactorsThroughProjective.sub

```lean
theorem ModuleCat.FactorsThroughProjective.sub {R : Type uR} [Ring R] {M N : ModuleCat R} {f g : M ⟶ N} (hf : FactorsThroughProjective R f) (hg : FactorsThroughProjective R g) : FactorsThroughProjective R (f - g)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/Stable.lean#L67-L71) (native database range lines 67–71).

### ModuleCat.FactorsThroughProjective.precomp

```lean
theorem ModuleCat.FactorsThroughProjective.precomp {R : Type uR} [Ring R] {L M N : ModuleCat R} (e : L ⟶ M) {f : M ⟶ N} (hf : FactorsThroughProjective R f) : FactorsThroughProjective R (CategoryTheory.CategoryStruct.comp e f)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/Stable.lean#L73-L77) (native database range lines 73–77).

### ModuleCat.FactorsThroughProjective.postcomp

```lean
theorem ModuleCat.FactorsThroughProjective.postcomp {R : Type uR} [Ring R] {M N L : ModuleCat R} {f : M ⟶ N} (e : N ⟶ L) (hf : FactorsThroughProjective R f) : FactorsThroughProjective R (CategoryTheory.CategoryStruct.comp f e)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/Stable.lean#L79-L83) (native database range lines 79–83).

### ModuleCat.FactorsThroughProjective.of_projective_source

```lean
theorem ModuleCat.FactorsThroughProjective.of_projective_source {R : Type uR} [Ring R] {M N : ModuleCat R} [CategoryTheory.Projective M] (f : M ⟶ N) : FactorsThroughProjective R f
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/Stable.lean#L85-L87) (native database range lines 85–87).

### ModuleCat.FactorsThroughProjective.of_projective_target

```lean
theorem ModuleCat.FactorsThroughProjective.of_projective_target {R : Type uR} [Ring R] {M N : ModuleCat R} [CategoryTheory.Projective N] (f : M ⟶ N) : FactorsThroughProjective R f
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/Stable.lean#L89-L91) (native database range lines 89–91).

### ModuleCat.stableHomRel

```lean
def ModuleCat.stableHomRel (R : Type uR) [Ring R] : HomRel (ModuleCat R)
```

The congruence on module morphisms whose differences factor through projective modules.

[Source](../ProjectiveModules/Category/Stable.lean#L95-L97) (native database range lines 95–97).

### ModuleCat.stableHomRel.instCongruence

```lean
instance ModuleCat.stableHomRel.instCongruence {R : Type uR} [Ring R] : CategoryTheory.Congruence (stableHomRel R)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/Stable.lean#L103-L125) (native database range lines 103–125).

### ModuleCat.stableHomRel.add

```lean
theorem ModuleCat.stableHomRel.add {R : Type uR} [Ring R] {M N : ModuleCat R} (f₁ f₂ g₁ g₂ : M ⟶ N) (hf : stableHomRel R f₁ f₂) (hg : stableHomRel R g₁ g₂) : stableHomRel R (f₁ + g₁) (f₂ + g₂)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/Stable.lean#L127-L132) (native database range lines 127–132).

### ModuleCat.Stable

```lean
abbrev ModuleCat.Stable (R : Type uR) [Ring R] : Type (max (uM + 1) uR)
```

The stable category of left `R`-modules, modulo maps through projective modules.

[Source](../ProjectiveModules/Category/Stable.lean#L136-L137) (native database range lines 136–137).

### ModuleCat.Stable.stablePreadditive

```lean
instance ModuleCat.Stable.stablePreadditive (R : Type uR) [Ring R] : CategoryTheory.Preadditive (Stable R)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/Stable.lean#L141-L144) (native database range lines 141–144).

### ModuleCat.Stable.quotient

```lean
abbrev ModuleCat.Stable.quotient (R : Type uR) [Ring R] : CategoryTheory.Functor (ModuleCat R) (Stable R)
```

The additive quotient functor from modules to their stable category.

[Source](../ProjectiveModules/Category/Stable.lean#L146-L148) (native database range lines 146–148).

### ModuleCat.Stable.instAdditiveQuotient

```lean
instance ModuleCat.Stable.instAdditiveQuotient (R : Type uR) [Ring R] : (quotient R).Additive
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/Stable.lean#L150-L152) (native database range lines 150–152).

### ModuleCat.Stable.quotient_map_eq_iff

```lean
theorem ModuleCat.Stable.quotient_map_eq_iff {R : Type uR} [Ring R] {M N : ModuleCat R} (f g : M ⟶ N) : (quotient R).map f = (quotient R).map g ↔ FactorsThroughProjective R (f - g)
```

Equality in the stable category is exactly equality modulo a map through a projective.

[Source](../ProjectiveModules/Category/Stable.lean#L156-L160) (native database range lines 156–160).

### ModuleCat.Stable.quotient_map_eq_zero_iff

```lean
theorem ModuleCat.Stable.quotient_map_eq_zero_iff {R : Type uR} [Ring R] {M N : ModuleCat R} (f : M ⟶ N) : (quotient R).map f = 0 ↔ FactorsThroughProjective R f
```

A map through a projective module is zero in the stable category.

[Source](../ProjectiveModules/Category/Stable.lean#L162-L166) (native database range lines 162–166).

### ModuleCat.Stable.quotient_map_fst_comp_inl

```lean
theorem ModuleCat.Stable.quotient_map_fst_comp_inl {R : Type uR} [Ring R] (M P : ModuleCat R) [CategoryTheory.Projective P] : (quotient R).map (CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.fst CategoryTheory.Limits.biprod.inl) = CategoryTheory.CategoryStruct.id ((quotient R).obj (M ⊞ P))
```

The projector onto a summand complementary to a projective module is the identity in the
stable category.

[Source](../ProjectiveModules/Category/Stable.lean#L168-L177) (native database range lines 168–177).

### ModuleCat.Stable.addProjectiveIso

```lean
noncomputable def ModuleCat.Stable.addProjectiveIso {R : Type uR} [Ring R] (M P : ModuleCat R) [CategoryTheory.Projective P] : (quotient R).obj M ≅ (quotient R).obj (M ⊞ P)
```

Adjoining a projective direct summand does not change a module in the stable category.

[Source](../ProjectiveModules/Category/Stable.lean#L179-L189) (native database range lines 179–189).

### ModuleCat.Stable.addProjectiveIso_hom

```lean
theorem ModuleCat.Stable.addProjectiveIso_hom {R : Type uR} [Ring R] (M P : ModuleCat R) [CategoryTheory.Projective P] : (addProjectiveIso M P).hom = (quotient R).map CategoryTheory.Limits.biprod.inl
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/Stable.lean#L180-L180) (native database range lines 180–180).

### ModuleCat.Stable.addProjectiveIso_inv

```lean
theorem ModuleCat.Stable.addProjectiveIso_inv {R : Type uR} [Ring R] (M P : ModuleCat R) [CategoryTheory.Projective P] : (addProjectiveIso M P).inv = (quotient R).map CategoryTheory.Limits.biprod.fst
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Category/Stable.lean#L180-L180) (native database range lines 180–180).

### ModuleCat.Stable.quotient_map_of_projective_source

```lean
theorem ModuleCat.Stable.quotient_map_of_projective_source {R : Type uR} [Ring R] {M N : ModuleCat R} [CategoryTheory.Projective M] (f : M ⟶ N) : (quotient R).map f = 0
```

Every morphism with projective source is zero in the stable category.

[Source](../ProjectiveModules/Category/Stable.lean#L191-L196) (native database range lines 191–196).

### ModuleCat.Stable.quotient_map_of_projective_target

```lean
theorem ModuleCat.Stable.quotient_map_of_projective_target {R : Type uR} [Ring R] {M N : ModuleCat R} [CategoryTheory.Projective N] (f : M ⟶ N) : (quotient R).map f = 0
```

Every morphism with projective target is zero in the stable category.

[Source](../ProjectiveModules/Category/Stable.lean#L198-L203) (native database range lines 198–203).

### ModuleCat.FactorsThroughProjective.iff_ext_one_precomp_eq_zero

```lean
theorem ModuleCat.FactorsThroughProjective.iff_ext_one_precomp_eq_zero {R : Type uR} [Ring R] [Small.{uM, uR} R] {M N : ModuleCat R} (f : M ⟶ N) : FactorsThroughProjective R f ↔ ∀ (A : ModuleCat R), (CategoryTheory.Abelian.Ext.mk₀ f).precomp A ⋯ = 0
```

A morphism factors through a projective module exactly when it acts by zero on every first
`Ext` group by precomposition.

[Source](../ProjectiveModules/Category/Stable.lean#L211-L239) (native database range lines 211–239).

### ModuleCat.FactorsThroughProjective.sub_iff_ext_one_precomp_eq

```lean
theorem ModuleCat.FactorsThroughProjective.sub_iff_ext_one_precomp_eq {R : Type uR} [Ring R] [Small.{uM, uR} R] {M N : ModuleCat R} (f g : M ⟶ N) : FactorsThroughProjective R (f - g) ↔ ∀ (A : ModuleCat R), (CategoryTheory.Abelian.Ext.mk₀ f).precomp A ⋯ = (CategoryTheory.Abelian.Ext.mk₀ g).precomp A ⋯
```

Two module morphisms have the same effect by precomposition on all first `Ext` groups exactly
when their difference factors through a projective module.

[Source](../ProjectiveModules/Category/Stable.lean#L241-L265) (native database range lines 241–265).

## ProjectiveModules.Contraction.BaseChange

Scope: mathematical library leaf.

### IsBaseChange.contractBaseChangeEquivOfProjective

```lean
noncomputable def IsBaseChange.contractBaseChangeEquivOfProjective {R : Type u_1} [CommRing R] {V : Type u_2} [AddCommGroup V] [Module R V] {W : Type u_3} [AddCommGroup W] [Module R W] {A : Type u_4} [CommRing A] [Algebra R A] [Module A W] [IsScalarTower R A W] {j : V →ₗ[R] W} (ibc : IsBaseChange A j) [Module.Finite R V] [Module.Projective R V] : TensorProduct R A (TensorProduct R (Module.Dual R V) V) ≃ₗ[A] TensorProduct A (Module.Dual A W) W
```

Scalar extension of `Dual R V ⊗[R] V` is canonically equivalent to
`Dual A W ⊗[A] W` when `W` is a supplied scalar extension of the finite
projective module `V`.

[Source](../ProjectiveModules/Contraction/BaseChange.lean#L34-L42) (native database range lines 34–42).

### IsBaseChange.toContractBaseChangeOfProjective

```lean
noncomputable def IsBaseChange.toContractBaseChangeOfProjective {R : Type u_1} [CommRing R] {V : Type u_2} [AddCommGroup V] [Module R V] {W : Type u_3} [AddCommGroup W] [Module R W] {A : Type u_4} [CommRing A] [Algebra R A] [Module A W] [IsScalarTower R A W] {j : V →ₗ[R] W} (ibc : IsBaseChange A j) [Module.Finite R V] [Module.Projective R V] : TensorProduct R (Module.Dual R V) V →ₗ[R] TensorProduct A (Module.Dual A W) W
```

The canonical map from the domain of evaluation to its supplied scalar
extension.

[Source](../ProjectiveModules/Contraction/BaseChange.lean#L44-L49) (native database range lines 44–49).

### IsBaseChange.toContractBaseChangeOfProjective_tmul

```lean
theorem IsBaseChange.toContractBaseChangeOfProjective_tmul {R : Type u_1} [CommRing R] {V : Type u_2} [AddCommGroup V] [Module R V] {W : Type u_3} [AddCommGroup W] [Module R W] {A : Type u_4} [CommRing A] [Algebra R A] [Module A W] [IsScalarTower R A W] {j : V →ₗ[R] W} (ibc : IsBaseChange A j) [Module.Finite R V] [Module.Projective R V] (f : Module.Dual R V) (v : V) : ibc.toContractBaseChangeOfProjective (f ⊗ₜ[R] v) = ibc.toDual f ⊗ₜ[A] j v
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Contraction/BaseChange.lean#L51-L56) (native database range lines 51–56).

### IsBaseChange.contract_of_projective

```lean
theorem IsBaseChange.contract_of_projective {R : Type u_1} [CommRing R] {V : Type u_2} [AddCommGroup V] [Module R V] {W : Type u_3} [AddCommGroup W] [Module R W] {A : Type u_4} [CommRing A] [Algebra R A] [Module A W] [IsScalarTower R A W] {j : V →ₗ[R] W} (ibc : IsBaseChange A j) [Module.Finite R V] [Module.Projective R V] : IsBaseChange A ibc.toContractBaseChangeOfProjective
```

The tensor product of a finite projective module with its dual commutes
with scalar extension, using the canonical maps on both factors.

[Source](../ProjectiveModules/Contraction/BaseChange.lean#L58-L64) (native database range lines 58–64).

### IsBaseChange.contractLeft_comp_toContractBaseChangeOfProjective

```lean
theorem IsBaseChange.contractLeft_comp_toContractBaseChangeOfProjective {R : Type u_1} [CommRing R] {V : Type u_2} [AddCommGroup V] [Module R V] {W : Type u_3} [AddCommGroup W] [Module R W] {A : Type u_4} [CommRing A] [Algebra R A] [Module A W] [IsScalarTower R A W] {j : V →ₗ[R] W} (ibc : IsBaseChange A j) [Module.Finite R V] [Module.Projective R V] : ↑R (contractLeft A W) ∘ₗ ibc.toContractBaseChangeOfProjective = Algebra.linearMap R A ∘ₗ contractLeft R V
```

The canonical evaluation pairing is compatible with finite-projective
base change.

[Source](../ProjectiveModules/Contraction/BaseChange.lean#L66-L73) (native database range lines 66–73).

## ProjectiveModules.Dual.BaseChange

Scope: mathematical library leaf.

### IsBaseChange.toDualBaseChangeOfProjective

```lean
noncomputable def IsBaseChange.toDualBaseChangeOfProjective {R : Type u_1} [CommSemiring R] {V : Type u_2} [AddCommMonoid V] [Module R V] {W : Type u_3} [AddCommMonoid W] [Module R W] {A : Type u_4} [CommSemiring A] [Algebra R A] [Module A W] [IsScalarTower R A W] {j : V →ₗ[R] W} (ibc : IsBaseChange A j) [Module.Finite R V] [Module.Projective R V] : TensorProduct R A (Module.Dual R V) ≃ₗ[A] Module.Dual A W
```

For a finite projective module, the canonical scalar extension of its dual
is linearly equivalent to the dual of any supplied scalar extension.

[Source](../ProjectiveModules/Dual/BaseChange.lean#L85-L90) (native database range lines 85–90).

### IsBaseChange.toDualBaseChangeOfProjective_tmul

```lean
theorem IsBaseChange.toDualBaseChangeOfProjective_tmul {R : Type u_1} [CommSemiring R] {V : Type u_2} [AddCommMonoid V] [Module R V] {W : Type u_3} [AddCommMonoid W] [Module R W] {A : Type u_4} [CommSemiring A] [Algebra R A] [Module A W] [IsScalarTower R A W] {j : V →ₗ[R] W} (ibc : IsBaseChange A j) [Module.Finite R V] [Module.Projective R V] (a : A) (f : Module.Dual R V) (v : V) : (ibc.toDualBaseChangeOfProjective (a ⊗ₜ[R] f)) (j v) = a * (algebraMap R A) (f v)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Dual/BaseChange.lean#L94-L98) (native database range lines 94–98).

### IsBaseChange.toDualBaseChangeOfProjective_one_tmul

```lean
theorem IsBaseChange.toDualBaseChangeOfProjective_one_tmul {R : Type u_1} [CommSemiring R] {V : Type u_2} [AddCommMonoid V] [Module R V] {W : Type u_3} [AddCommMonoid W] [Module R W] {A : Type u_4} [CommSemiring A] [Algebra R A] [Module A W] [IsScalarTower R A W] {j : V →ₗ[R] W} (ibc : IsBaseChange A j) [Module.Finite R V] [Module.Projective R V] (f : Module.Dual R V) : ibc.toDualBaseChangeOfProjective (1 ⊗ₜ[R] f) = ibc.toDual f
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Dual/BaseChange.lean#L100-L107) (native database range lines 100–107).

### IsBaseChange.dual_of_projective

```lean
theorem IsBaseChange.dual_of_projective {R : Type u_1} [CommSemiring R] {V : Type u_2} [AddCommMonoid V] [Module R V] {W : Type u_3} [AddCommMonoid W] [Module R W] {A : Type u_4} [CommSemiring A] [Algebra R A] [Module A W] [IsScalarTower R A W] {j : V →ₗ[R] W} (ibc : IsBaseChange A j) [Module.Finite R V] [Module.Projective R V] : IsBaseChange A ibc.toDual
```

Taking the dual of a finite projective module commutes with arbitrary
scalar extension.

[Source](../ProjectiveModules/Dual/BaseChange.lean#L109-L114) (native database range lines 109–114).

## ProjectiveModules.ExteriorAlgebra.BaseChange

Scope: mathematical library leaf.

### ExteriorAlgebra.toBaseChange

```lean
noncomputable def ExteriorAlgebra.toBaseChange {R : Type uR} {S : Type uS} {M : Type uM} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] : ExteriorAlgebra S (TensorProduct R S M) →ₐ[S] TensorProduct R S (ExteriorAlgebra R M)
```

The canonical map from the exterior algebra after extending scalars to the scalar extension
of the original exterior algebra.

[Source](../ProjectiveModules/ExteriorAlgebra/BaseChange.lean#L70-L74) (native database range lines 70–74).

### ExteriorAlgebra.ofBaseChange

```lean
noncomputable def ExteriorAlgebra.ofBaseChange {R : Type uR} {S : Type uS} {M : Type uM} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] : TensorProduct R S (ExteriorAlgebra R M) →ₐ[S] ExteriorAlgebra S (TensorProduct R S M)
```

The canonical map from the scalar extension of an exterior algebra to the exterior algebra
after extending scalars.

[Source](../ProjectiveModules/ExteriorAlgebra/BaseChange.lean#L82-L87) (native database range lines 82–87).

### ExteriorAlgebra.ofBaseChange_tmul_ι

```lean
theorem ExteriorAlgebra.ofBaseChange_tmul_ι {R : Type uR} {S : Type uS} {M : Type uM} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] (s : S) (m : M) : ofBaseChange (s ⊗ₜ[R] (ι R) m) = (ι S) (s ⊗ₜ[R] m)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/ExteriorAlgebra/BaseChange.lean#L89-L98) (native database range lines 89–98).

### ExteriorAlgebra.toBaseChange_ι_tmul

```lean
theorem ExteriorAlgebra.toBaseChange_ι_tmul {R : Type uR} {S : Type uS} {M : Type uM} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] (s : S) (m : M) : toBaseChange ((ι S) (s ⊗ₜ[R] m)) = s ⊗ₜ[R] (ι R) m
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/ExteriorAlgebra/BaseChange.lean#L105-L109) (native database range lines 105–109).

### ExteriorAlgebra.equivBaseChange

```lean
noncomputable def ExteriorAlgebra.equivBaseChange {R : Type uR} {S : Type uS} {M : Type uM} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] : ExteriorAlgebra S (TensorProduct R S M) ≃ₐ[S] TensorProduct R S (ExteriorAlgebra R M)
```

Extending scalars in an exterior algebra agrees with taking the exterior algebra after
extending scalars. This equivalence is valid without assuming that two is invertible.

[Source](../ProjectiveModules/ExteriorAlgebra/BaseChange.lean#L129-L136) (native database range lines 129–136).

### ExteriorAlgebra.equivBaseChange_apply_ι_tmul

```lean
theorem ExteriorAlgebra.equivBaseChange_apply_ι_tmul {R : Type uR} {S : Type uS} {M : Type uM} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] (s : S) (m : M) : equivBaseChange ((ι S) (s ⊗ₜ[R] m)) = s ⊗ₜ[R] (ι R) m
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/ExteriorAlgebra/BaseChange.lean#L138-L142) (native database range lines 138–142).

### ExteriorAlgebra.equivBaseChange_symm_apply_tmul_ι

```lean
theorem ExteriorAlgebra.equivBaseChange_symm_apply_tmul_ι {R : Type uR} {S : Type uS} {M : Type uM} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] (s : S) (m : M) : equivBaseChange.symm (s ⊗ₜ[R] (ι R) m) = (ι S) (s ⊗ₜ[R] m)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/ExteriorAlgebra/BaseChange.lean#L144-L148) (native database range lines 144–148).

## ProjectiveModules.ExteriorPower.Determinant

Scope: mathematical library leaf.

### exteriorPower.mapEndomorphismMonoidHom

```lean
noncomputable def exteriorPower.mapEndomorphismMonoidHom (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) : Module.End R M →* Module.End R ↥(⋀[R]^n M)
```

Functoriality packages the `n`th exterior-power map as a monoid
homomorphism on module endomorphisms.

[Source](../ProjectiveModules/ExteriorPower/Determinant.lean#L34-L44) (native database range lines 34–44).

### exteriorPower.determinant

```lean
noncomputable def exteriorPower.determinant (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) [Module.Invertible R ↥(⋀[R]^n M)] : Module.End R M →* R
```

The determinant scalar obtained from the induced action on an invertible
exterior power.

[Source](../ProjectiveModules/ExteriorPower/Determinant.lean#L46-L51) (native database range lines 46–51).

### exteriorPower.determinant_apply

```lean
theorem exteriorPower.determinant_apply (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) [Module.Invertible R ↥(⋀[R]^n M)] (f : Module.End R M) : (determinant R M n) f = (Module.Invertible.toModuleEndRingEquiv R ↥(⋀[R]^n M)).symm (map n f)
```

The determinant is the scalar corresponding to the induced exterior-power
endomorphism.

[Source](../ProjectiveModules/ExteriorPower/Determinant.lean#L53-L59) (native database range lines 53–59).

### exteriorPower.map_eq_smul_determinant

```lean
theorem exteriorPower.map_eq_smul_determinant (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) [Module.Invertible R ↥(⋀[R]^n M)] (f : Module.End R M) (x : ↥(⋀[R]^n M)) : (map n f) x = (determinant R M n) f • x
```

The induced exterior-power endomorphism is scalar multiplication by its
determinant.

[Source](../ProjectiveModules/ExteriorPower/Determinant.lean#L61-L68) (native database range lines 61–68).

### exteriorPower.determinant_eq_iff_map_eq_smul

```lean
theorem exteriorPower.determinant_eq_iff_map_eq_smul (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) [Module.Invertible R ↥(⋀[R]^n M)] (f : Module.End R M) (r : R) : (determinant R M n) f = r ↔ ∀ (x : ↥(⋀[R]^n M)), (map n f) x = r • x
```

A scalar is the determinant exactly when it induces the exterior-power
map.

[Source](../ProjectiveModules/ExteriorPower/Determinant.lean#L70-L85) (native database range lines 70–85).

### exteriorPower.determinant_id

```lean
theorem exteriorPower.determinant_id (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) [Module.Invertible R ↥(⋀[R]^n M)] : (determinant R M n) LinearMap.id = 1
```

The determinant of the identity endomorphism is one.

[Source](../ProjectiveModules/ExteriorPower/Determinant.lean#L87-L90) (native database range lines 87–90).

### exteriorPower.determinant_comp

```lean
theorem exteriorPower.determinant_comp (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) [Module.Invertible R ↥(⋀[R]^n M)] (f g : Module.End R M) : (determinant R M n) (f ∘ₗ g) = (determinant R M n) f * (determinant R M n) g
```

Determinants multiply under composition.

[Source](../ProjectiveModules/ExteriorPower/Determinant.lean#L92-L97) (native database range lines 92–97).

## ProjectiveModules.ExteriorPower.DirectSum

Scope: mathematical library leaf.

### exteriorPower.prodEquivDirectSum

```lean
noncomputable def exteriorPower.prodEquivDirectSum (R : Type u) [CommRing R] (P : Type v) (Q : Type w) [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (k : ℕ) : ↥(⋀[R]^k (P × Q)) ≃ₗ[R] DirectSum (Fin (k + 1)) fun (i : Fin (k + 1)) => TensorProduct R ↥(⋀[R]^↑i P) ↥(⋀[R]^(k - ↑i) Q)
```

The degree-`k` exterior power of a binary direct sum is the direct sum of the tensor products
of exterior powers whose degrees add to `k`.

The inverse uses the ordered convention: the `P` block is wedged before the `Q` block. No
finiteness, projectivity, flatness, or nontriviality assumption is needed.

[Source](../ProjectiveModules/ExteriorPower/DirectSum.lean#L372-L381) (native database range lines 372–381).

### exteriorPower.coe_prodEquivDirectSum_symm_of_tmul

```lean
theorem exteriorPower.coe_prodEquivDirectSum_symm_of_tmul (R : Type u) [CommRing R] (P : Type v) (Q : Type w) [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (k : ℕ) (i : Fin (k + 1)) (a : ↥(⋀[R]^↑i P)) (b : ↥(⋀[R]^(k - ↑i) Q)) : ↑((prodEquivDirectSum R P Q k).symm ((DirectSum.of (fun (j : Fin (k + 1)) => TensorProduct R ↥(⋀[R]^↑j P) ↥(⋀[R]^(k - ↑j) Q)) i) (a ⊗ₜ[R] b))) = (ExteriorAlgebra.map (LinearMap.inl R P Q)) ↑a * (ExteriorAlgebra.map (LinearMap.inr R P Q)) ↑b
```

The inverse of `prodEquivDirectSum` sends a pure tensor in the `i`th summand to exterior
multiplication after the two canonical inclusions, with the `P` factor first.

[Source](../ProjectiveModules/ExteriorPower/DirectSum.lean#L383-L398) (native database range lines 383–398).

### exteriorPower.coe_prodEquivDirectSum_symm_of_tmul_ιMulti

```lean
theorem exteriorPower.coe_prodEquivDirectSum_symm_of_tmul_ιMulti (R : Type u) [CommRing R] (P : Type v) (Q : Type w) [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (k : ℕ) (i : Fin (k + 1)) (p : Fin ↑i → P) (q : Fin (k - ↑i) → Q) : ↑((prodEquivDirectSum R P Q k).symm ((DirectSum.of (fun (j : Fin (k + 1)) => TensorProduct R ↥(⋀[R]^↑j P) ↥(⋀[R]^(k - ↑j) Q)) i) ((ιMulti R ↑i) p ⊗ₜ[R] (ιMulti R (k - ↑i)) q))) = (ExteriorAlgebra.ιMulti R (↑i + (k - ↑i))) (Fin.append (⇑(LinearMap.inl R P Q) ∘ p) (⇑(LinearMap.inr R P Q) ∘ q))
```

On pure exterior products, the inverse concatenates the `P` entries and then the `Q`
entries. The right side is written in the full exterior algebra, avoiding any index casts.

[Source](../ProjectiveModules/ExteriorPower/DirectSum.lean#L400-L413) (native database range lines 400–413).

### exteriorPower.prodDirectSumMap

```lean
noncomputable def exteriorPower.prodDirectSumMap (R : Type u) [CommRing R] (P : Type v) (Q : Type w) [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] {P' : Type v'} {Q' : Type w'} [AddCommGroup P'] [Module R P'] [AddCommGroup Q'] [Module R Q'] (k : ℕ) (f : P →ₗ[R] P') (g : Q →ₗ[R] Q') : (DirectSum (Fin (k + 1)) fun (i : Fin (k + 1)) => TensorProduct R ↥(⋀[R]^↑i P) ↥(⋀[R]^(k - ↑i) Q)) →ₗ[R] DirectSum (Fin (k + 1)) fun (i : Fin (k + 1)) => TensorProduct R ↥(⋀[R]^↑i P') ↥(⋀[R]^(k - ↑i) Q')
```

The summandwise map on the direct-sum side induced by a pair of linear maps.

[Source](../ProjectiveModules/ExteriorPower/DirectSum.lean#L420-L425) (native database range lines 420–425).

### exteriorPower.prodEquivDirectSum_symm_naturality

```lean
theorem exteriorPower.prodEquivDirectSum_symm_naturality (R : Type u) [CommRing R] (P : Type v) (Q : Type w) [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] {P' : Type v'} {Q' : Type w'} [AddCommGroup P'] [Module R P'] [AddCommGroup Q'] [Module R Q'] (k : ℕ) (f : P →ₗ[R] P') (g : Q →ₗ[R] Q') : map k (f.prodMap g) ∘ₗ ↑(prodEquivDirectSum R P Q k).symm = ↑(prodEquivDirectSum R P' Q' k).symm ∘ₗ prodDirectSumMap R P Q k f g
```

Naturality of the inverse fixed-degree decomposition for arbitrary module maps over `R`.

[Source](../ProjectiveModules/ExteriorPower/DirectSum.lean#L427-L472) (native database range lines 427–472).

### exteriorPower.prodEquivDirectSum_naturality

```lean
theorem exteriorPower.prodEquivDirectSum_naturality (R : Type u) [CommRing R] (P : Type v) (Q : Type w) [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] {P' : Type v'} {Q' : Type w'} [AddCommGroup P'] [Module R P'] [AddCommGroup Q'] [Module R Q'] (k : ℕ) (f : P →ₗ[R] P') (g : Q →ₗ[R] Q') : ↑(prodEquivDirectSum R P' Q' k) ∘ₗ map k (f.prodMap g) = prodDirectSumMap R P Q k f g ∘ₗ ↑(prodEquivDirectSum R P Q k)
```

Naturality of `prodEquivDirectSum` for arbitrary module maps over the fixed base ring.

[Source](../ProjectiveModules/ExteriorPower/DirectSum.lean#L474-L498) (native database range lines 474–498).

## ProjectiveModules.ExteriorPower.Projective

Scope: mathematical library leaf.

### exteriorPower.instProjective

```lean
instance exteriorPower.instProjective (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) [Module.Projective R M] : Module.Projective R ↥(⋀[R]^n M)
```

Every exterior power of a projective module is projective.

[Source](../ProjectiveModules/ExteriorPower/Projective.lean#L29-L36) (native database range lines 29–36).

## ProjectiveModules.ExteriorPower.Top

Scope: mathematical library leaf.

### Module.Basis.topExteriorWedge

```lean
noncomputable def Module.Basis.topExteriorWedge {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (b : Basis (Fin n) R M) : ↥(⋀[R]^n M)
```

The ordered exterior product of a basis indexed by `Fin n`.

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L38-L40) (native database range lines 38–40).

### Module.Basis.topExteriorCoordinate

```lean
noncomputable def Module.Basis.topExteriorCoordinate {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (b : Basis (Fin n) R M) : ↥(⋀[R]^n M) →ₗ[R] R
```

The determinant coordinate on the top exterior power.

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L42-L44) (native database range lines 42–44).

### Module.Basis.topExteriorCoordinate_wedge

```lean
theorem Module.Basis.topExteriorCoordinate_wedge {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (b : Basis (Fin n) R M) : b.topExteriorCoordinate b.topExteriorWedge = 1
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L46-L51) (native database range lines 46–51).

### Module.Basis.topExteriorInverse

```lean
noncomputable def Module.Basis.topExteriorInverse {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (b : Basis (Fin n) R M) : R →ₗ[R] ↥(⋀[R]^n M)
```

Multiply the ordered top wedge by a scalar.

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L53-L55) (native database range lines 53–55).

### Module.Basis.iMulti_eq_det_smul_topExteriorWedge

```lean
theorem Module.Basis.iMulti_eq_det_smul_topExteriorWedge {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (b : Basis (Fin n) R M) (x : Fin n → M) : (exteriorPower.ιMulti R n) x = b.det x • b.topExteriorWedge
```

Every top exterior product is its determinant times the ordered basis wedge.

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L57-L68) (native database range lines 57–68).

### Module.Basis.topExteriorInverse_comp_coordinate

```lean
theorem Module.Basis.topExteriorInverse_comp_coordinate {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (b : Basis (Fin n) R M) : b.topExteriorInverse ∘ₗ b.topExteriorCoordinate = LinearMap.id
```

Multiplying the top wedge is a left inverse to taking its determinant coordinate.

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L70-L80) (native database range lines 70–80).

### Module.Basis.topExteriorCoordinate_comp_inverse

```lean
theorem Module.Basis.topExteriorCoordinate_comp_inverse {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (b : Basis (Fin n) R M) : b.topExteriorCoordinate ∘ₗ b.topExteriorInverse = LinearMap.id
```

Taking the determinant coordinate is a left inverse to multiplying the top wedge.

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L82-L88) (native database range lines 82–88).

### Module.Basis.topExteriorEquiv

```lean
noncomputable def Module.Basis.topExteriorEquiv {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (b : Basis (Fin n) R M) : ↥(⋀[R]^n M) ≃ₗ[R] R
```

A basis indexed by `Fin n` identifies its `n`th exterior power with the ring.

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L90-L93) (native database range lines 90–93).

### Module.Basis.topExteriorEquiv_apply

```lean
theorem Module.Basis.topExteriorEquiv_apply {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (b : Basis (Fin n) R M) (x : ↥(⋀[R]^n M)) : b.topExteriorEquiv x = b.topExteriorCoordinate x
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L95-L98) (native database range lines 95–98).

### Module.Basis.topExteriorEquiv_wedge

```lean
theorem Module.Basis.topExteriorEquiv_wedge {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (b : Basis (Fin n) R M) : b.topExteriorEquiv b.topExteriorWedge = 1
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L100-L103) (native database range lines 100–103).

### Module.Basis.topExteriorEquiv_symm_apply

```lean
theorem Module.Basis.topExteriorEquiv_symm_apply {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (b : Basis (Fin n) R M) (r : R) : b.topExteriorEquiv.symm r = r • b.topExteriorWedge
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L105-L108) (native database range lines 105–108).

### Module.Basis.topExteriorEquiv_map

```lean
theorem Module.Basis.topExteriorEquiv_map {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (b : Basis (Fin n) R M) (f : End R M) (x : ↥(⋀[R]^n M)) : b.topExteriorEquiv ((exteriorPower.map n f) x) = LinearMap.det f * b.topExteriorEquiv x
```

The top exterior coordinate intertwines an endomorphism with its determinant.

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L110-L125) (native database range lines 110–125).

### Module.Basis.topExteriorInvertible

```lean
theorem Module.Basis.topExteriorInvertible {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (b : Basis (Fin n) R M) : Module.Invertible R ↥(⋀[R]^n M)
```

A basis indexed by `Fin n` proves that the top exterior power is invertible.

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L127-L130) (native database range lines 127–130).

### Module.Basis.exteriorPower_determinant_eq_det

```lean
theorem Module.Basis.exteriorPower_determinant_eq_det {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (b : Basis (Fin n) R M) [Module.Invertible R ↥(⋀[R]^n M)] (f : End R M) : (exteriorPower.determinant R M n) f = LinearMap.det f
```

The determinant defined through an invertible top exterior power agrees
with the ordinary finite-free determinant.

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L132-L141) (native database range lines 132–141).

### exteriorPower.standardTopEquiv

```lean
noncomputable def exteriorPower.standardTopEquiv (R : Type u) [CommRing R] (n : ℕ) : ↥(⋀[R]^n (Fin n → R)) ≃ₗ[R] R
```

The standard coordinate equivalence on the top exterior power of `R^n`.

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L149-L151) (native database range lines 149–151).

### exteriorPower.instInvertiblePiTop

```lean
instance exteriorPower.instInvertiblePiTop (R : Type u) [CommRing R] (n : ℕ) : Module.Invertible R ↥(⋀[R]^n (Fin n → R))
```

The standard top exterior power of `R^n` is invertible.

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L153-L156) (native database range lines 153–156).

### exteriorPower.standardTopEquiv_map

```lean
theorem exteriorPower.standardTopEquiv_map (R : Type u) [CommRing R] (n : ℕ) (f : Module.End R (Fin n → R)) (x : ↥(⋀[R]^n (Fin n → R))) : (standardTopEquiv R n) ((map n f) x) = LinearMap.det f * (standardTopEquiv R n) x
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L158-L163) (native database range lines 158–163).

### exteriorPower.determinant_pi_eq_det

```lean
theorem exteriorPower.determinant_pi_eq_det (R : Type u) [CommRing R] (n : ℕ) (f : Module.End R (Fin n → R)) : (determinant R (Fin n → R) n) f = LinearMap.det f
```

On the standard free module, the exterior-power determinant is
`LinearMap.det`.

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L165-L169) (native database range lines 165–169).

### exteriorPower.determinant_toLin'

```lean
theorem exteriorPower.determinant_toLin' (R : Type u) [CommRing R] (n : ℕ) (g : Matrix (Fin n) (Fin n) R) : (determinant R (Fin n → R) n) (Matrix.toLin' g) = g.det
```

On a matrix endomorphism, the exterior-power determinant is `Matrix.det`.

[Source](../ProjectiveModules/ExteriorPower/Top.lean#L171-L174) (native database range lines 171–174).

## ProjectiveModules.Free.CountableAbsorption

Scope: mathematical library leaf.

### Module.Free.endomorphismsInto

```lean
def Module.Free.endomorphismsInto (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] (p : Submodule R M) : Submodule (End R M)ᵐᵒᵖ (End R M)
```

The right ideal of endomorphisms whose ranges lie in `p`.

Right ideals of `Module.End R M` are represented as submodules over the
opposite endomorphism ring, so scalar multiplication is right multiplication.

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L35-L50) (native database range lines 35–50).

### Module.Free.mem_endomorphismsInto_iff_range_le

```lean
theorem Module.Free.mem_endomorphismsInto_iff_range_le (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] (p : Submodule R M) (f : End R M) : f ∈ endomorphismsInto R M p ↔ LinearMap.range f ≤ p
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L52-L61) (native database range lines 52–61).

### Module.Free.isCompl_endomorphismsInto

```lean
theorem Module.Free.isCompl_endomorphismsInto (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] {p q : Submodule R M} (h : IsCompl p q) : IsCompl (endomorphismsInto R M p) (endomorphismsInto R M q)
```

Complementary submodules give complementary right ideals consisting of
endomorphisms with range in the respective submodule.

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L63-L90) (native database range lines 63–90).

### Module.Free.finsuppProdLEquiv

```lean
noncomputable def Module.Free.finsuppProdLEquiv (R : Type u) [Ring R] (V : Type v) (W : Type w) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] : (ℕ →₀ V × W) ≃ₗ[R] (ℕ →₀ V) × (ℕ →₀ W)
```

A finitely supported sequence of pairs is the product of two finitely
supported sequences.

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L92-L110) (native database range lines 92–110).

### Module.Free.prodFinsuppNatEquiv

```lean
noncomputable def Module.Free.prodFinsuppNatEquiv (R : Type u) [Ring R] (V : Type v) [AddCommGroup V] [Module R V] : (V × (ℕ →₀ V)) ≃ₗ[R] ℕ →₀ V
```

One copy of a module is absorbed by its countable direct sum.

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L112-L120) (native database range lines 112–120).

### Module.Free.prodEquivOfCountableSelfSum

```lean
noncomputable def Module.Free.prodEquivOfCountableSelfSum (R : Type u) [Ring R] (M : Type v) (V : Type w) (W : Type u_1) [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] (countableSelfSum : M ≃ₗ[R] ℕ →₀ M) (split : M ≃ₗ[R] V × W) : (V × M) ≃ₗ[R] M
```

If `M` is equivalent to a countable direct sum of itself, every chosen
direct summand of `M` is absorbed by `M`.

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L122-L139) (native database range lines 122–139).

### Module.Free.natFinsuppCountableSelfSum

```lean
noncomputable def Module.Free.natFinsuppCountableSelfSum (R : Type u) [Ring R] : (ℕ →₀ R) ≃ₗ[R] ℕ →₀ ℕ →₀ R
```

Pairing natural coordinates identifies `ℕ →₀ R` with a countable direct
sum of copies of itself.

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L141-L149) (native database range lines 141–149).

### Module.Free.prodNatFinsuppEquivOfSplit

```lean
noncomputable def Module.Free.prodNatFinsuppEquivOfSplit (R : Type u) [Ring R] (V : Type v) (W : Type w) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] (split : (ℕ →₀ R) ≃ₗ[R] V × W) : (V × (ℕ →₀ R)) ≃ₗ[R] ℕ →₀ R
```

Every chosen direct summand of `ℕ →₀ R` is absorbed by `ℕ →₀ R`.

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L151-L159) (native database range lines 151–159).

### LinearMap.instModuleMulOppositeEnd

```lean
instance LinearMap.instModuleMulOppositeEnd (R : Type u) [Ring R] (M : Type v) (V : Type w) [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V] : Module (Module.End R M)ᵐᵒᵖ (M →ₗ[R] V)
```

Precomposition is the natural right action of `End_R(M)` on linear maps
out of `M`. The low priority leaves the regular-module instance in control when
the codomain is definitionally `M`.

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L167-L186) (native database range lines 167–186).

### Module.Free.linearMapProdEndEquiv

```lean
def Module.Free.linearMapProdEndEquiv (R : Type u) [Ring R] (M : Type v) (V : Type w) [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V] (absorb : (V × M) ≃ₗ[R] M) : ((M →ₗ[R] V) × End R M) ≃ₗ[(End R M)ᵐᵒᵖ] End R M
```

Postcomposition with an equivalence `V × M ≃ M` identifies
`Hom_R(M,V) × End_R(M)` with `End_R(M)` as right `End_R(M)`-modules.

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L194-L217) (native database range lines 194–217).

### Module.Free.rightIdealProjection

```lean
noncomputable def Module.Free.rightIdealProjection (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] {I J : Submodule (End R M)ᵐᵒᵖ (End R M)} (h : IsCompl I J) : End R M
```

The idempotent obtained by projecting the identity onto a complemented
right ideal of an endomorphism ring.

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L219-L225) (native database range lines 219–225).

### Module.Free.rightIdealProjection_mem

```lean
theorem Module.Free.rightIdealProjection_mem (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] {I J : Submodule (End R M)ᵐᵒᵖ (End R M)} (h : IsCompl I J) : rightIdealProjection R M h ∈ I
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L227-L231) (native database range lines 227–231).

### Module.Free.rightIdealProjection_isIdempotent

```lean
theorem Module.Free.rightIdealProjection_isIdempotent (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] {I J : Submodule (End R M)ᵐᵒᵖ (End R M)} (h : IsCompl I J) : IsIdempotentElem (rightIdealProjection R M h)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L233-L244) (native database range lines 233–244).

### Module.Free.coe_eq_rightIdealProjection_mul

```lean
theorem Module.Free.coe_eq_rightIdealProjection_mul (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] {I J : Submodule (End R M)ᵐᵒᵖ (End R M)} (h : IsCompl I J) (f : ↥I) : ↑f = rightIdealProjection R M h * ↑f
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L246-L259) (native database range lines 246–259).

### Module.Free.rightIdealAction

```lean
def Module.Free.rightIdealAction (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] (I : Submodule (End R M)ᵐᵒᵖ (End R M)) : Submodule R M
```

The submodule generated by the values of all endomorphisms in a right
ideal. For a complemented right ideal, this is the range of its projection
idempotent.

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L261-L267) (native database range lines 261–267).

### Module.Free.rightIdealAction_eq_range_rightIdealProjection

```lean
theorem Module.Free.rightIdealAction_eq_range_rightIdealProjection (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] {I J : Submodule (End R M)ᵐᵒᵖ (End R M)} (h : IsCompl I J) : rightIdealAction R M I = LinearMap.range (rightIdealProjection R M h)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L269-L278) (native database range lines 269–278).

### Module.Free.rightIdealEquivRange

```lean
noncomputable def Module.Free.rightIdealEquivRange (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] {I J : Submodule (End R M)ᵐᵒᵖ (End R M)} (h : IsCompl I J) : ↥I ≃ₗ[(End R M)ᵐᵒᵖ] M →ₗ[R] ↥(LinearMap.range (rightIdealProjection R M h))
```

A complemented right ideal of `End_R(M)` is the right module of maps from
`M` into the range of its projection idempotent.

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L280-L322) (native database range lines 280–322).

### Module.Free.isCompl_range_rightIdealProjection

```lean
theorem Module.Free.isCompl_range_rightIdealProjection (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] {I J : Submodule (End R M)ᵐᵒᵖ (End R M)} (h : IsCompl I J) : IsCompl (LinearMap.range (rightIdealProjection R M h)) (LinearMap.range (rightIdealProjection R M ⋯))
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L324-L337) (native database range lines 324–337).

### Module.Free.isCompl_rightIdealAction

```lean
theorem Module.Free.isCompl_rightIdealAction (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] {I J : Submodule (End R M)ᵐᵒᵖ (End R M)} (h : IsCompl I J) : IsCompl (rightIdealAction R M I) (rightIdealAction R M J)
```

Complementary right ideals of an endomorphism ring give complementary
submodules after evaluation on the underlying module.

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L339-L347) (native database range lines 339–347).

### Module.Free.rightIdealProdEndNatFinsuppEquiv

```lean
noncomputable def Module.Free.rightIdealProdEndNatFinsuppEquiv (R : Type u) [Ring R] {I J : Submodule (End R (ℕ →₀ R))ᵐᵒᵖ (End R (ℕ →₀ R))} (h : IsCompl I J) : (↥I × End R (ℕ →₀ R)) ≃ₗ[(End R (ℕ →₀ R))ᵐᵒᵖ] End R (ℕ →₀ R)
```

Every complemented right ideal of the endomorphism ring of `ℕ →₀ R` is
absorbed by that endomorphism ring.

[Source](../ProjectiveModules/Free/CountableAbsorption.lean#L349-L365) (native database range lines 349–365).

## ProjectiveModules.Free.CountableCancellation

Scope: mathematical library leaf.

### Module.Free.CountableFree

```lean
abbrev Module.Free.CountableFree (R : Type u) [Ring R] : Type u
```

The countable coordinate module used by the cancellation interface.

[Source](../ProjectiveModules/Free/CountableCancellation.lean#L34-L35) (native database range lines 34–35).

### Module.Free.FiniteFree

```lean
abbrev Module.Free.FiniteFree (R : Type u) [Ring R] (m : ℕ) : Type u
```

The finite coordinate module used by the cancellation interface.

[Source](../ProjectiveModules/Free/CountableCancellation.lean#L36-L37) (native database range lines 36–37).

### Module.Free.natFinsuppEquivOfProdFinFinsuppEquiv

```lean
noncomputable def Module.Free.natFinsuppEquivOfProdFinFinsuppEquiv (R : Type u) [Ring R] {P : Type v} [AddCommGroup P] [Module R P] (m : ℕ) (h : (P × FiniteFree R m) ≃ₗ[R] CountableFree R) : P ≃ₗ[R] CountableFree R
```

Removing a finite-coordinate free summand from a module equivalent to the
countable free module does not change the module's isomorphism type.

[Source](../ProjectiveModules/Free/CountableCancellation.lean#L313-L336) (native database range lines 313–336).

### Module.Free.natFinsuppEquivOfProdFinEquiv

```lean
noncomputable def Module.Free.natFinsuppEquivOfProdFinEquiv (R : Type u) [Ring R] {P : Type v} [AddCommGroup P] [Module R P] (m : ℕ) (h : (P × (Fin m → R)) ≃ₗ[R] ℕ →₀ R) : P ≃ₗ[R] ℕ →₀ R
```

Removing a standard finite coordinate module from a module equivalent to
the countable free module does not change the module's isomorphism type.

[Source](../ProjectiveModules/Free/CountableCancellation.lean#L338-L346) (native database range lines 338–346).

### Module.Free.countableFinsuppEquivOfProdFiniteFinsuppEquiv

```lean
noncomputable def Module.Free.countableFinsuppEquivOfProdFiniteFinsuppEquiv (R : Type u) [Ring R] {P : Type v} [AddCommGroup P] [Module R P] {ι : Type w} [Finite ι] {κ : Type x} [Countable κ] [Infinite κ] (e : (P × (ι →₀ R)) ≃ₗ[R] κ →₀ R) : P ≃ₗ[R] κ →₀ R
```

A version of `natFinsuppEquivOfProdFinFinsuppEquiv` for arbitrary finite
and countably infinite coordinate types.

[Source](../ProjectiveModules/Free/CountableCancellation.lean#L348-L368) (native database range lines 348–368).

## ProjectiveModules.Free.Semisimple

Scope: mathematical library leaf.

### Module.free_of_finite_isStablyFree_of_isSemisimpleRing

```lean
theorem Module.free_of_finite_isStablyFree_of_isSemisimpleRing (R : Type u) [Ring R] [IsSemisimpleRing R] (P : Type v) [AddCommGroup P] [Module R P] [IsStablyFree R P] [Module.Finite R P] : Free R P
```

A finite stably free module over a semisimple ring is free.

This applies to arbitrary left modules over possibly noncommutative rings and
also covers the zero ring and zero module.

[Source](../ProjectiveModules/Free/Semisimple.lean#L66-L102) (native database range lines 66–102).

## ProjectiveModules.Invertible.Endomorphism

Scope: mathematical library leaf.

### Module.Invertible.toModuleEndRingEquiv

```lean
noncomputable def Module.Invertible.toModuleEndRingEquiv (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Invertible R M] : R ≃+* End R M
```

Scalar multiplication identifies the base ring with the endomorphism ring
of an invertible module.

[Source](../ProjectiveModules/Invertible/Endomorphism.lean#L29-L34) (native database range lines 29–34).

### Module.Invertible.toModuleEndRingEquiv_apply

```lean
theorem Module.Invertible.toModuleEndRingEquiv_apply (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Invertible R M] (r : R) (m : M) : ((toModuleEndRingEquiv R M) r) m = r • m
```

The forward map of `toModuleEndRingEquiv` is scalar multiplication.

[Source](../ProjectiveModules/Invertible/Endomorphism.lean#L36-L40) (native database range lines 36–40).

### Module.Invertible.existsUnique_eq_smul

```lean
theorem Module.Invertible.existsUnique_eq_smul (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Invertible R M] (f : End R M) : ∃! r : R, ∀ (m : M), f m = r • m
```

Every endomorphism of an invertible module is multiplication by a unique
scalar.

[Source](../ProjectiveModules/Invertible/Endomorphism.lean#L42-L54) (native database range lines 42–54).

## ProjectiveModules.Invertible.OfRankOne

Scope: mathematical library leaf.

### Module.invertible_of_rankAtStalk_eq_one

```lean
theorem Module.invertible_of_rankAtStalk_eq_one {R : Type u_1} {M : Type u_2} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] (h : rankAtStalk M = 1) : Module.Invertible R M
```

A finite projective module of constant stalk rank one is invertible.

[Source](../ProjectiveModules/Invertible/OfRankOne.lean#L29-L60) (native database range lines 29–60).

### Module.invertible_iff_finite_projective_rankAtStalk_eq_one

```lean
theorem Module.invertible_iff_finite_projective_rankAtStalk_eq_one {R : Type u_1} {M : Type u_2} [CommRing R] [AddCommGroup M] [Module R M] : Module.Invertible R M ↔ Module.Finite R M ∧ Projective R M ∧ rankAtStalk M = 1
```

A module over a commutative ring is invertible if and only if it is finite
projective and has constant stalk rank one.

[Source](../ProjectiveModules/Invertible/OfRankOne.lean#L62-L77) (native database range lines 62–77).

## ProjectiveModules.Invertible.StableCancellation

Scope: mathematical library leaf.

### Module.Invertible.tensorFinStabilization

```lean
noncomputable def Module.Invertible.tensorFinStabilization {R : Type u} [CommRing R] {L : Type v} {L' : Type w} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L'] [Module.Invertible R L'] (n : ℕ) (e : (L × (Fin n → R)) ≃ₗ[R] L' × (Fin n → R)) : (TensorProduct R L (Dual R L') × TensorProduct R (Fin n → R) (Dual R L')) ≃ₗ[R] R × TensorProduct R (Fin n → R) (Dual R L')
```

Tensoring a finite-free stabilization by the dual of `L'` reduces it to a
stabilization of `L ⊗ (L')ᵛ` by the same finite projective module.

[Source](../ProjectiveModules/Invertible/StableCancellation.lean#L41-L52) (native database range lines 41–52).

### Module.Invertible.nonempty_linearEquiv_of_fin_stabilization

```lean
theorem Module.Invertible.nonempty_linearEquiv_of_fin_stabilization {R : Type u} [CommRing R] {L : Type v} {L' : Type w} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L'] [Module.Invertible R L] [Module.Invertible R L'] (n : ℕ) (e : (L × (Fin n → R)) ≃ₗ[R] L' × (Fin n → R)) : Nonempty (L ≃ₗ[R] L')
```

A common finite free summand can be cancelled from two invertible modules.

[Source](../ProjectiveModules/Invertible/StableCancellation.lean#L54-L87) (native database range lines 54–87).

## ProjectiveModules.Module.ArbitraryLocalProjectiveFree

Scope: mathematical library leaf.

### Module.Projective.free_of_isUnit_compl_arbitraryRank

```lean
theorem Module.Projective.free_of_isUnit_compl_arbitraryRank {R : Type uR} [Ring R] {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P] [Projective Rᵐᵒᵖ P] (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r) : Free Rᵐᵒᵖ P
```

Every arbitrary-rank projective right module over a possibly
noncommutative ring with a proper two-sided ideal whose complement consists of
units is free.

[Source](../ProjectiveModules/Module/ArbitraryLocalProjectiveFree.lean#L36-L93) (native database range lines 36–93).

## ProjectiveModules.Module.BalancedTensorExact

Scope: mathematical library leaf.

### BalancedTensorProduct.mapLeft

```lean
def BalancedTensorProduct.mapLeft {R : Type uR} [Ring R] {M : Type uM} {M' : Type uM'} {N : Type uN} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ M'] [Module R N] (f : M →ₗ[Rᵐᵒᵖ] M') : BalancedTensorProduct R M N →+ BalancedTensorProduct R M' N
```

The additive map on balanced tensor products induced by a right-linear map
in the first variable.

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L37-L47) (native database range lines 37–47).

### BalancedTensorProduct.mapRight

```lean
def BalancedTensorProduct.mapRight {R : Type uR} [Ring R] {M : Type uM} {N : Type uN} {N' : Type uN'} [AddCommGroup M] [AddCommGroup N] [AddCommGroup N'] [Module Rᵐᵒᵖ M] [Module R N] [Module R N'] (g : N →ₗ[R] N') : BalancedTensorProduct R M N →+ BalancedTensorProduct R M N'
```

The additive map on balanced tensor products induced by a left-linear map
in the second variable.

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L49-L59) (native database range lines 49–59).

### BalancedTensorProduct.mapLeft_tmul

```lean
theorem BalancedTensorProduct.mapLeft_tmul {R : Type uR} [Ring R] {M : Type uM} {M' : Type uM'} {N : Type uN} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ M'] [Module R N] (f : M →ₗ[Rᵐᵒᵖ] M') (m : M) (n : N) : (mapLeft f) (tmul m n) = tmul (f m) n
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L61-L64) (native database range lines 61–64).

### BalancedTensorProduct.mapRight_tmul

```lean
theorem BalancedTensorProduct.mapRight_tmul {R : Type uR} [Ring R] {M : Type uM} {N : Type uN} {N' : Type uN'} [AddCommGroup M] [AddCommGroup N] [AddCommGroup N'] [Module Rᵐᵒᵖ M] [Module R N] [Module R N'] (g : N →ₗ[R] N') (m : M) (n : N) : (mapRight g) (tmul m n) = tmul m (g n)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L66-L69) (native database range lines 66–69).

### BalancedTensorProduct.mapLeft_id

```lean
theorem BalancedTensorProduct.mapLeft_id {R : Type uR} [Ring R] {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] : mapLeft LinearMap.id = AddMonoidHom.id (BalancedTensorProduct R M N)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L71-L76) (native database range lines 71–76).

### BalancedTensorProduct.mapRight_id

```lean
theorem BalancedTensorProduct.mapRight_id {R : Type uR} [Ring R] {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] : mapRight LinearMap.id = AddMonoidHom.id (BalancedTensorProduct R M N)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L78-L83) (native database range lines 78–83).

### BalancedTensorProduct.mapLeft_comp

```lean
theorem BalancedTensorProduct.mapLeft_comp {R : Type uR} [Ring R] {M : Type uM} {M' : Type uM'} {M'' : Type uM''} {N : Type uN} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M''] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ M'] [Module Rᵐᵒᵖ M''] [Module R N] (f : M →ₗ[Rᵐᵒᵖ] M') (g : M' →ₗ[Rᵐᵒᵖ] M'') : mapLeft (g ∘ₗ f) = (mapLeft g).comp (mapLeft f)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L85-L91) (native database range lines 85–91).

### BalancedTensorProduct.mapRight_comp

```lean
theorem BalancedTensorProduct.mapRight_comp {R : Type uR} [Ring R] {M : Type uM} {N : Type uN} {N' : Type uN'} {N'' : Type uN''} [AddCommGroup M] [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module Rᵐᵒᵖ M] [Module R N] [Module R N'] [Module R N''] (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') : mapRight (g ∘ₗ f) = (mapRight g).comp (mapRight f)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L93-L99) (native database range lines 93–99).

### BalancedTensorProduct.mapLeft_mapLeft

```lean
theorem BalancedTensorProduct.mapLeft_mapLeft {R : Type uR} [Ring R] {M : Type uM} {M' : Type uM'} {M'' : Type uM''} {N : Type uN} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M''] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ M'] [Module Rᵐᵒᵖ M''] [Module R N] (f : M →ₗ[Rᵐᵒᵖ] M') (g : M' →ₗ[Rᵐᵒᵖ] M'') (z : BalancedTensorProduct R M N) : (mapLeft g) ((mapLeft f) z) = (mapLeft (g ∘ₗ f)) z
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L101-L106) (native database range lines 101–106).

### BalancedTensorProduct.mapRight_mapRight

```lean
theorem BalancedTensorProduct.mapRight_mapRight {R : Type uR} [Ring R] {M : Type uM} {N : Type uN} {N' : Type uN'} {N'' : Type uN''} [AddCommGroup M] [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module Rᵐᵒᵖ M] [Module R N] [Module R N'] [Module R N''] (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') (z : BalancedTensorProduct R M N) : (mapRight g) ((mapRight f) z) = (mapRight (g ∘ₗ f)) z
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L108-L113) (native database range lines 108–113).

### BalancedTensorProduct.mapLeft_mapRight

```lean
theorem BalancedTensorProduct.mapLeft_mapRight {R : Type uR} [Ring R] {M : Type uM} {M' : Type uM'} {N : Type uN} {N' : Type uN'} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N'] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ M'] [Module R N] [Module R N'] (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') : (mapLeft f).comp (mapRight g) = (mapRight g).comp (mapLeft f)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L115-L120) (native database range lines 115–120).

### BalancedTensorProduct.mapLeft_mapRight_apply

```lean
theorem BalancedTensorProduct.mapLeft_mapRight_apply {R : Type uR} [Ring R] {M : Type uM} {M' : Type uM'} {N : Type uN} {N' : Type uN'} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N'] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ M'] [Module R N] [Module R N'] (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') (z : BalancedTensorProduct R M N) : (mapLeft f) ((mapRight g) z) = (mapRight g) ((mapLeft f) z)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L122-L126) (native database range lines 122–126).

### BalancedTensorProduct.mapLeft_zero

```lean
theorem BalancedTensorProduct.mapLeft_zero {R : Type uR} [Ring R] {M : Type uM} {M' : Type uM'} {N : Type uN} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ M'] [Module R N] : mapLeft 0 = 0
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L128-L132) (native database range lines 128–132).

### BalancedTensorProduct.mapRight_zero

```lean
theorem BalancedTensorProduct.mapRight_zero {R : Type uR} [Ring R] {M : Type uM} {N : Type uN} {N' : Type uN'} [AddCommGroup M] [AddCommGroup N] [AddCommGroup N'] [Module Rᵐᵒᵖ M] [Module R N] [Module R N'] : mapRight 0 = 0
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L134-L138) (native database range lines 134–138).

### BalancedTensorProduct.mapLeft_add

```lean
theorem BalancedTensorProduct.mapLeft_add {R : Type uR} [Ring R] {M : Type uM} {M' : Type uM'} {N : Type uN} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ M'] [Module R N] (f g : M →ₗ[Rᵐᵒᵖ] M') : mapLeft (f + g) = mapLeft f + mapLeft g
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L140-L145) (native database range lines 140–145).

### BalancedTensorProduct.mapRight_add

```lean
theorem BalancedTensorProduct.mapRight_add {R : Type uR} [Ring R] {M : Type uM} {N : Type uN} {N' : Type uN'} [AddCommGroup M] [AddCommGroup N] [AddCommGroup N'] [Module Rᵐᵒᵖ M] [Module R N] [Module R N'] (f g : N →ₗ[R] N') : mapRight (f + g) = mapRight f + mapRight g
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L147-L152) (native database range lines 147–152).

### BalancedTensorProduct.freeCoefficient

```lean
noncomputable def BalancedTensorProduct.freeCoefficient {R : Type uR} [Ring R] {N : Type uN} [AddCommGroup N] [Module R N] {ι : Type uI} (i : ι) (n : N) : Rᵐᵒᵖ →+ ι →₀ N
```

The coefficient map used to evaluate balanced tensors with a free first
factor. This is an implementation detail of `freeToFinsupp`.

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L158-L163) (native database range lines 158–163).

### BalancedTensorProduct.freeBalancedMap

```lean
noncomputable def BalancedTensorProduct.freeBalancedMap {R : Type uR} [Ring R] {N : Type uN} [AddCommGroup N] [Module R N] {ι : Type uI} : BalancedMap (ι →₀ N)
```

The balanced map used by `freeToFinsupp`.

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L165-L180) (native database range lines 165–180).

### BalancedTensorProduct.freeToFinsupp

```lean
noncomputable def BalancedTensorProduct.freeToFinsupp {R : Type uR} [Ring R] {N : Type uN} [AddCommGroup N] [Module R N] {ι : Type uI} : BalancedTensorProduct R (ι →₀ Rᵐᵒᵖ) N →+ ι →₀ N
```

A balanced tensor with a free right module, evaluated coordinatewise.

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L182-L185) (native database range lines 182–185).

### BalancedTensorProduct.freeToFinsupp_tmul

```lean
theorem BalancedTensorProduct.freeToFinsupp_tmul {R : Type uR} [Ring R] {N : Type uN} [AddCommGroup N] [Module R N] {ι : Type uI} (x : ι →₀ Rᵐᵒᵖ) (n : N) : freeToFinsupp (tmul x n) = (Finsupp.liftAddHom fun (i : ι) => freeCoefficient i n) x
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L187-L191) (native database range lines 187–191).

### BalancedTensorProduct.freeToFinsupp_single_tmul

```lean
theorem BalancedTensorProduct.freeToFinsupp_single_tmul {R : Type uR} [Ring R] {N : Type uN} [AddCommGroup N] [Module R N] {ι : Type uI} (i : ι) (r : Rᵐᵒᵖ) (n : N) : freeToFinsupp (tmul (Finsupp.single i r) n) = Finsupp.single i (MulOpposite.unop r • n)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L193-L197) (native database range lines 193–197).

### BalancedTensorProduct.freeSingle

```lean
noncomputable def BalancedTensorProduct.freeSingle {R : Type uR} [Ring R] {N : Type uN} [AddCommGroup N] [Module R N] {ι : Type uI} (i : ι) : N →+ BalancedTensorProduct R (ι →₀ Rᵐᵒᵖ) N
```

The single-coordinate map used by `finsuppToFree`.

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L199-L204) (native database range lines 199–204).

### BalancedTensorProduct.finsuppToFree

```lean
noncomputable def BalancedTensorProduct.finsuppToFree {R : Type uR} [Ring R] {N : Type uN} [AddCommGroup N] [Module R N] {ι : Type uI} : (ι →₀ N) →+ BalancedTensorProduct R (ι →₀ Rᵐᵒᵖ) N
```

Reassemble a finitely supported family as a sum of elementary balanced
tensors.

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L206-L210) (native database range lines 206–210).

### BalancedTensorProduct.finsuppToFree_single

```lean
theorem BalancedTensorProduct.finsuppToFree_single {R : Type uR} [Ring R] {N : Type uN} [AddCommGroup N] [Module R N] {ι : Type uI} (i : ι) (n : N) : finsuppToFree (Finsupp.single i n) = tmul (Finsupp.single i 1) n
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L212-L216) (native database range lines 212–216).

### BalancedTensorProduct.freeAddEquiv

```lean
noncomputable def BalancedTensorProduct.freeAddEquiv {R : Type uR} [Ring R] {N : Type uN} [AddCommGroup N] [Module R N] {ι : Type uI} : BalancedTensorProduct R (ι →₀ Rᵐᵒᵖ) N ≃+ (ι →₀ N)
```

A balanced tensor with a free right module is the finitely supported
family of its coordinates.

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L231-L249) (native database range lines 231–249).

### BalancedTensorProduct.freeAddEquiv_tmul

```lean
theorem BalancedTensorProduct.freeAddEquiv_tmul {R : Type uR} [Ring R] {N : Type uN} [AddCommGroup N] [Module R N] {ι : Type uI} (x : ι →₀ Rᵐᵒᵖ) (n : N) : freeAddEquiv (tmul x n) = (Finsupp.liftAddHom fun (i : ι) => freeCoefficient i n) x
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L251-L255) (native database range lines 251–255).

### BalancedTensorProduct.freeAddEquiv_symm_single

```lean
theorem BalancedTensorProduct.freeAddEquiv_symm_single {R : Type uR} [Ring R] {N : Type uN} [AddCommGroup N] [Module R N] {ι : Type uI} (i : ι) (n : N) : freeAddEquiv.symm (Finsupp.single i n) = tmul (Finsupp.single i 1) n
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L257-L261) (native database range lines 257–261).

### BalancedTensorProduct.freeAddEquiv_mapRight

```lean
theorem BalancedTensorProduct.freeAddEquiv_mapRight {R : Type uR} [Ring R] {N : Type uN} {N' : Type uN'} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N'] {ι : Type uI} (g : N →ₗ[R] N') (z : BalancedTensorProduct R (ι →₀ Rᵐᵒᵖ) N) : freeAddEquiv ((mapRight g) z) = (Finsupp.mapRange.linearMap g) (freeAddEquiv z)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L263-L281) (native database range lines 263–281).

### BalancedTensorProduct.mapRight_injective_free

```lean
theorem BalancedTensorProduct.mapRight_injective_free {R : Type uR} [Ring R] {N : Type uN} {N' : Type uN'} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N'] {ι : Type uI} (g : N →ₗ[R] N') (hg : Function.Injective ⇑g) : Function.Injective ⇑(mapRight g)
```

Tensoring a free right module with an injective map in the second variable
is injective.

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L283-L292) (native database range lines 283–292).

### BalancedTensorProduct.exact_mapRight_free

```lean
theorem BalancedTensorProduct.exact_mapRight_free {R : Type uR} [Ring R] {N : Type uN} {N' : Type uN'} {N'' : Type uN''} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] [Module R N''] {ι : Type uI} (i : N →ₗ[R] N') (p : N' →ₗ[R] N'') (hi : Function.Injective ⇑i) (h : Function.Exact ⇑i ⇑p) : Function.Exact ⇑(mapRight i) ⇑(mapRight p)
```

Tensoring a free right module preserves an exact pair in the second
variable when the first map is injective.

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L294-L325) (native database range lines 294–325).

### BalancedTensorProduct.mapRight_surjective

```lean
theorem BalancedTensorProduct.mapRight_surjective {R : Type uR} [Ring R] {M : Type uM} {N : Type uN} {N' : Type uN'} [AddCommGroup M] [AddCommGroup N] [AddCommGroup N'] [Module Rᵐᵒᵖ M] [Module R N] [Module R N'] (g : N →ₗ[R] N') (hg : Function.Surjective ⇑g) : Function.Surjective ⇑(mapRight g)
```

A surjective map in the second variable induces a surjective map of
balanced tensor products.

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L329-L345) (native database range lines 329–345).

### Module.Projective.balancedTensor_injective

```lean
theorem Module.Projective.balancedTensor_injective {R : Type uR} [Ring R] {P : Type uP} {L : Type uL} {M : Type uM} [AddCommGroup P] [AddCommGroup L] [AddCommGroup M] [Module Rᵐᵒᵖ P] [Module R L] [Module R M] [Projective Rᵐᵒᵖ P] (i : L →ₗ[R] M) (hi : Function.Injective ⇑i) : Function.Injective ⇑(BalancedTensorProduct.mapRight i)
```

Tensoring with a projective right module preserves injective maps in the
left-module variable.

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L356-L370) (native database range lines 356–370).

### Module.Projective.balancedTensor_exact

```lean
theorem Module.Projective.balancedTensor_exact {R : Type uR} [Ring R] {P : Type uP} {L : Type uL} {M : Type uM} {N : Type uN} [AddCommGroup P] [AddCommGroup L] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ P] [Module R L] [Module R M] [Module R N] [Projective Rᵐᵒᵖ P] (i : L →ₗ[R] M) (p : M →ₗ[R] N) (hi : Function.Injective ⇑i) (h : Function.Exact ⇑i ⇑p) : Function.Exact ⇑(BalancedTensorProduct.mapRight i) ⇑(BalancedTensorProduct.mapRight p)
```

Tensoring with a projective right module preserves an exact pair in the
left-module variable when the first map is injective.

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L372-L396) (native database range lines 372–396).

### Module.Projective.balancedTensor_short_exact

```lean
theorem Module.Projective.balancedTensor_short_exact {R : Type uR} [Ring R] {P : Type uP} {L : Type uL} {M : Type uM} {N : Type uN} [AddCommGroup P] [AddCommGroup L] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ P] [Module R L] [Module R M] [Module R N] [Projective Rᵐᵒᵖ P] (i : L →ₗ[R] M) (p : M →ₗ[R] N) (hi : Function.Injective ⇑i) (h : Function.Exact ⇑i ⇑p) (hp : Function.Surjective ⇑p) : Function.Injective ⇑(BalancedTensorProduct.mapRight i) ∧ Function.Exact ⇑(BalancedTensorProduct.mapRight i) ⇑(BalancedTensorProduct.mapRight p) ∧ Function.Surjective ⇑(BalancedTensorProduct.mapRight p)
```

Applying balanced tensor with a projective right module to an
injective/exact/surjective pair preserves all three properties.

[Source](../ProjectiveModules/Module/BalancedTensorExact.lean#L398-L409) (native database range lines 398–409).

## ProjectiveModules.Module.BalancedTensorProduct

Scope: mathematical library leaf.

### BalancedTensorProduct.Free

```lean
abbrev BalancedTensorProduct.Free (M : Type uM) (N : Type uN) : Type (max uN uM)
```

The free additive commutative group used in the quotient construction.

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L34-L35) (native database range lines 34–35).

### BalancedTensorProduct.Relation

```lean
inductive BalancedTensorProduct.Relation (R : Type uR) (M : Type uM) (N : Type uN) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] : Free M N → Prop
```

The elementary relations defining the tensor product of a right module
and a left module over an arbitrary ring.

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L37-L50) (native database range lines 37–50).

### BalancedTensorProduct.Relation.zero_left

```lean
constructor BalancedTensorProduct.Relation.zero_left {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] (n : N) : Relation R M N (FreeAbelianGroup.of (0, n))
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L40-L40) (native database range lines 40–40).

### BalancedTensorProduct.Relation.zero_right

```lean
constructor BalancedTensorProduct.Relation.zero_right {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] (m : M) : Relation R M N (FreeAbelianGroup.of (m, 0))
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L41-L41) (native database range lines 41–41).

### BalancedTensorProduct.Relation.add_left

```lean
constructor BalancedTensorProduct.Relation.add_left {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] (m₁ m₂ : M) (n : N) : Relation R M N (FreeAbelianGroup.of (m₁ + m₂, n) - FreeAbelianGroup.of (m₁, n) - FreeAbelianGroup.of (m₂, n))
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L42-L44) (native database range lines 42–44).

### BalancedTensorProduct.Relation.add_right

```lean
constructor BalancedTensorProduct.Relation.add_right {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] (m : M) (n₁ n₂ : N) : Relation R M N (FreeAbelianGroup.of (m, n₁ + n₂) - FreeAbelianGroup.of (m, n₁) - FreeAbelianGroup.of (m, n₂))
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L45-L47) (native database range lines 45–47).

### BalancedTensorProduct.Relation.balance

```lean
constructor BalancedTensorProduct.Relation.balance {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] (r : R) (m : M) (n : N) : Relation R M N (FreeAbelianGroup.of (MulOpposite.op r • m, n) - FreeAbelianGroup.of (m, r • n))
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L48-L50) (native database range lines 48–50).

### BalancedTensorProduct.relations

```lean
def BalancedTensorProduct.relations (R : Type uR) (M : Type uM) (N : Type uN) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] : AddSubgroup (Free M N)
```

The additive subgroup generated by the elementary balanced tensor
relations.

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L52-L55) (native database range lines 52–55).

### BalancedTensorProduct

```lean
abbrev BalancedTensorProduct (R : Type uR) (M : Type uM) (N : Type uN) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] : Type (max uM uN)
```

The tensor product of a right `R`-module and a left `R`-module over a
possibly noncommutative ring.

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L59-L64) (native database range lines 59–64).

### BalancedTensorProduct.instAddCommGroup

```lean
instance BalancedTensorProduct.instAddCommGroup {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] : AddCommGroup (BalancedTensorProduct R M N)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L72-L73) (native database range lines 72–73).

### BalancedTensorProduct.tmul

```lean
def BalancedTensorProduct.tmul {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] (m : M) (n : N) : BalancedTensorProduct R M N
```

The canonical pure tensor.

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L75-L77) (native database range lines 75–77).

### BalancedTensorProduct.«term_⊗ᵇ[_]_»

```lean
def BalancedTensorProduct.«term_⊗ᵇ[_]_» : Lean.TrailingParserDescr
```

The canonical pure tensor.

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L79-L79) (native database range lines 79–79).

### BalancedTensorProduct.zero_tmul

```lean
theorem BalancedTensorProduct.zero_tmul {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] (n : N) : tmul 0 n = 0
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L86-L88) (native database range lines 86–88).

### BalancedTensorProduct.tmul_zero

```lean
theorem BalancedTensorProduct.tmul_zero {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] (m : M) : tmul m 0 = 0
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L90-L92) (native database range lines 90–92).

### BalancedTensorProduct.add_tmul

```lean
theorem BalancedTensorProduct.add_tmul {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] (m₁ m₂ : M) (n : N) : tmul (m₁ + m₂) n = tmul m₁ n + tmul m₂ n
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L94-L101) (native database range lines 94–101).

### BalancedTensorProduct.tmul_add

```lean
theorem BalancedTensorProduct.tmul_add {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] (m : M) (n₁ n₂ : N) : tmul m (n₁ + n₂) = tmul m n₁ + tmul m n₂
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L103-L110) (native database range lines 103–110).

### BalancedTensorProduct.smul_tmul

```lean
theorem BalancedTensorProduct.smul_tmul {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] (r : R) (m : M) (n : N) : tmul (MulOpposite.op r • m) n = tmul m (r • n)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L112-L119) (native database range lines 112–119).

### BalancedTensorProduct.BalancedMap

```lean
structure BalancedTensorProduct.BalancedMap {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] (A : Type uA) [AddCommGroup A] : Type (max (max uA uM) uN)
```

A biadditive map which is balanced over `R`.

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L121-L128) (native database range lines 121–128).

### BalancedTensorProduct.BalancedMap.mk

```lean
constructor BalancedTensorProduct.BalancedMap.mk : {R : Type uR} → {M : Type uM} → {N : Type uN} → [inst : Ring R] → [inst_1 : AddCommGroup M] → [inst_2 : AddCommGroup N] → [inst_3 : Module Rᵐᵒᵖ M] → [inst_4 : Module R N] → {A : Type uA} → [inst_5 : AddCommGroup A] → (toFun : M → N → A) → (∀ (n : N), toFun 0 n = 0) → (∀ (m₁ m₂ : M) (n : N), toFun (m₁ + m₂) n = toFun m₁ n + toFun m₂ n) → (∀ (m : M), toFun m 0 = 0) → (∀ (m : M) (n₁ n₂ : N), toFun m (n₁ + n₂) = toFun m n₁ + toFun m n₂) → (∀ (r : R) (m : M) (n : N), toFun (MulOpposite.op r • m) n = toFun m (r • n)) → BalancedTensorProduct.BalancedMap A
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L121-L128) (native database range lines 121–128).

### BalancedTensorProduct.BalancedMap.toFun

```lean
abbrev BalancedTensorProduct.BalancedMap.toFun {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {A : Type uA} [AddCommGroup A] (self : BalancedMap A) : M → N → A
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L123-L123) (native database range lines 123–123).

### BalancedTensorProduct.BalancedMap.map_zero_left

```lean
theorem BalancedTensorProduct.BalancedMap.map_zero_left {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {A : Type uA} [AddCommGroup A] (self : BalancedMap A) (n : N) : self.toFun 0 n = 0
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L124-L124) (native database range lines 124–124).

### BalancedTensorProduct.BalancedMap.map_add_left

```lean
theorem BalancedTensorProduct.BalancedMap.map_add_left {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {A : Type uA} [AddCommGroup A] (self : BalancedMap A) (m₁ m₂ : M) (n : N) : self.toFun (m₁ + m₂) n = self.toFun m₁ n + self.toFun m₂ n
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L125-L125) (native database range lines 125–125).

### BalancedTensorProduct.BalancedMap.map_zero_right

```lean
theorem BalancedTensorProduct.BalancedMap.map_zero_right {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {A : Type uA} [AddCommGroup A] (self : BalancedMap A) (m : M) : self.toFun m 0 = 0
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L126-L126) (native database range lines 126–126).

### BalancedTensorProduct.BalancedMap.map_add_right

```lean
theorem BalancedTensorProduct.BalancedMap.map_add_right {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {A : Type uA} [AddCommGroup A] (self : BalancedMap A) (m : M) (n₁ n₂ : N) : self.toFun m (n₁ + n₂) = self.toFun m n₁ + self.toFun m n₂
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L127-L127) (native database range lines 127–127).

### BalancedTensorProduct.BalancedMap.balance

```lean
theorem BalancedTensorProduct.BalancedMap.balance {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {A : Type uA} [AddCommGroup A] (self : BalancedMap A) (r : R) (m : M) (n : N) : self.toFun (MulOpposite.op r • m) n = self.toFun m (r • n)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L128-L128) (native database range lines 128–128).

### BalancedTensorProduct.BalancedMap.instCoeFunForallForall

```lean
instance BalancedTensorProduct.BalancedMap.instCoeFunForallForall {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {A : Type uA} [AddCommGroup A] : CoeFun (BalancedMap A) fun (x : BalancedMap A) => M → N → A
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L134-L135) (native database range lines 134–135).

### BalancedTensorProduct.BalancedMap.freeLift

```lean
def BalancedTensorProduct.BalancedMap.freeLift {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {A : Type uA} [AddCommGroup A] (b : BalancedMap A) : Free M N →+ A
```

The homomorphism from the free additive group induced by a balanced map.
This is an implementation detail of `BalancedTensorProduct.lift`.

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L137-L140) (native database range lines 137–140).

### BalancedTensorProduct.BalancedMap.relations_le_ker

```lean
theorem BalancedTensorProduct.BalancedMap.relations_le_ker {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {A : Type uA} [AddCommGroup A] (b : BalancedMap A) : relations R M N ≤ b.freeLift.ker
```

The defining relations lie in the kernel of `BalancedMap.freeLift`.
This is an implementation detail of `BalancedTensorProduct.lift`.

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L142-L161) (native database range lines 142–161).

### BalancedTensorProduct.lift

```lean
def BalancedTensorProduct.lift {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {A : Type uA} [AddCommGroup A] (b : BalancedMap A) : BalancedTensorProduct R M N →+ A
```

Lift a balanced biadditive map to an additive homomorphism from the
balanced tensor product.

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L165-L171) (native database range lines 165–171).

### BalancedTensorProduct.lift_tmul

```lean
theorem BalancedTensorProduct.lift_tmul {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {A : Type uA} [AddCommGroup A] (b : BalancedMap A) (m : M) (n : N) : (lift b) (tmul m n) = b.toFun m n
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L173-L177) (native database range lines 173–177).

### BalancedTensorProduct.induction_on

```lean
theorem BalancedTensorProduct.induction_on {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {C : BalancedTensorProduct R M N → Prop} (x : BalancedTensorProduct R M N) (zero : C 0) (pure : ∀ (m : M) (n : N), C (tmul m n)) (neg : ∀ (x : BalancedTensorProduct R M N), C x → C (-x)) (add : ∀ (x y : BalancedTensorProduct R M N), C x → C y → C (x + y)) : C x
```

Induction on a balanced tensor product by zero, pure tensors, negation,
and addition.

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L179-L193) (native database range lines 179–193).

### BalancedTensorProduct.hom_ext

```lean
theorem BalancedTensorProduct.hom_ext {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {A : Type uA} [AddCommGroup A] {g h : BalancedTensorProduct R M N →+ A} (H : ∀ (m : M) (n : N), g (tmul m n) = h (tmul m n)) : g = h
```

Additive maps from a balanced tensor product are determined by their
values on pure tensors.

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L195-L209) (native database range lines 195–209).

### BalancedTensorProduct.hom_ext_iff

```lean
theorem BalancedTensorProduct.hom_ext_iff {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {A : Type uA} [AddCommGroup A] {g h : BalancedTensorProduct R M N →+ A} : g = h ↔ ∀ (m : M) (n : N), g (tmul m n) = h (tmul m n)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L197-L197) (native database range lines 197–197).

### BalancedTensorProduct.smulBalancedMap

```lean
def BalancedTensorProduct.smulBalancedMap {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {S : Type uS} [Ring S] [Module Sᵐᵒᵖ N] [SMulCommClass R Sᵐᵒᵖ N] (s : Sᵐᵒᵖ) : BalancedMap (BalancedTensorProduct R M N)
```

The balanced map used to define a compatible right action on the tensor
product. This is an implementation detail of `BalancedTensorProduct.smulAddHom`.

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L217-L226) (native database range lines 217–226).

### BalancedTensorProduct.smulAddHom

```lean
def BalancedTensorProduct.smulAddHom {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {S : Type uS} [Ring S] [Module Sᵐᵒᵖ N] [SMulCommClass R Sᵐᵒᵖ N] (s : Sᵐᵒᵖ) : BalancedTensorProduct R M N →+ BalancedTensorProduct R M N
```

The action on a balanced tensor product induced by a compatible right
action on the second factor.

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L228-L232) (native database range lines 228–232).

### BalancedTensorProduct.rightSMul

```lean
instance BalancedTensorProduct.rightSMul {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {S : Type uS} [Ring S] [Module Sᵐᵒᵖ N] [SMulCommClass R Sᵐᵒᵖ N] : SMul Sᵐᵒᵖ (BalancedTensorProduct R M N)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L234-L235) (native database range lines 234–235).

### BalancedTensorProduct.smul_tmul_right

```lean
theorem BalancedTensorProduct.smul_tmul_right {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {S : Type uS} [Ring S] [Module Sᵐᵒᵖ N] [SMulCommClass R Sᵐᵒᵖ N] (s : Sᵐᵒᵖ) (m : M) (n : N) : s • tmul m n = tmul m (s • n)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L237-L240) (native database range lines 237–240).

### BalancedTensorProduct.rightDistribMulAction

```lean
instance BalancedTensorProduct.rightDistribMulAction {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {S : Type uS} [Ring S] [Module Sᵐᵒᵖ N] [SMulCommClass R Sᵐᵒᵖ N] : DistribMulAction Sᵐᵒᵖ (BalancedTensorProduct R M N)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L242-L254) (native database range lines 242–254).

### BalancedTensorProduct.rightModule

```lean
instance BalancedTensorProduct.rightModule {R : Type uR} {M : Type uM} {N : Type uN} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module Rᵐᵒᵖ M] [Module R N] {S : Type uS} [Ring S] [Module Sᵐᵒᵖ N] [SMulCommClass R Sᵐᵒᵖ N] : Module Sᵐᵒᵖ (BalancedTensorProduct R M N)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/BalancedTensorProduct.lean#L256-L266) (native database range lines 256–266).

## ProjectiveModules.Module.ComponentwiseFree

Scope: mathematical library leaf.

### Module.ComponentwiseFreeModel

```lean
abbrev Module.ComponentwiseFreeModel {R : Type u} [CommRing R] {I : Type u_1} (e : I → R) (n : I → ℕ) : Type (max u u_1)
```

The module which is free of rank `n i` on the component cut out by `e i`.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L39-L41) (native database range lines 39–41).

### Module.ComponentwiseFree

```lean
def Module.ComponentwiseFree (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] : Prop
```

A module is componentwise free if it is isomorphic to an explicit model
for some finite complete orthogonal family of idempotents.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L43-L48) (native database range lines 43–48).

### Module.spanFamilyEquiv

```lean
noncomputable def Module.spanFamilyEquiv {R : Type u} [CommRing R] {I : Type u_1} [Fintype I] (g : I → R) (e : R) (hg : OrthogonalIdempotents g) (hsum : ∑ i : I, g i = e) : ↥(Ideal.span {e}) ≃ₗ[R] (i : I) → ↥(Ideal.span {g i})
```

A finite orthogonal family whose sum is `e` decomposes the ideal generated
by `e` into the product of the ideals generated by its members.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L50-L104) (native database range lines 50–104).

### Module.componentwiseFreeModel_finite

```lean
theorem Module.componentwiseFreeModel_finite {R : Type u} [CommRing R] {I : Type u_1} [Finite I] (e : I → R) (n : I → ℕ) : Module.Finite R (ComponentwiseFreeModel e n)
```

*Source-inspected amendment at `1762876`: `[Finite I]` replaces the historical
native `[Fintype I]`; the native range below remains historical.*

The explicit component model is finitely generated.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L106-L113) (native database range lines 106–112).

### Module.componentwiseFreeModel_projective

```lean
theorem Module.componentwiseFreeModel_projective {R : Type u} [CommRing R] {I : Type u_1} [Finite I] (e : I → R) (n : I → ℕ) (he : ∀ (i : I), IsIdempotentElem (e i)) : Projective R (ComponentwiseFreeModel e n)
```

*Source-inspected amendment at `1762876`: `[Finite I]` replaces the historical
native `[Fintype I]`; the native range below remains historical.*

The explicit component model is projective when its component generators
are idempotent.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L115-L128) (native database range lines 114–126).

### Module.ComponentwiseFree.equiv

```lean
theorem Module.ComponentwiseFree.equiv {R : Type u} [CommRing R] {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (hM : ComponentwiseFree R M) (E : N ≃ₗ[R] M) : ComponentwiseFree R N
```

Componentwise freeness is invariant under linear equivalence.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L130-L136) (native database range lines 128–134).

### Module.componentwiseFree_of_model

```lean
theorem Module.componentwiseFree_of_model {R : Type u} [CommRing R] {I : Type u_1} [Fintype I] {M : Type v} [AddCommGroup M] [Module R M] (e : I → R) (n : I → ℕ) (he : CompleteOrthogonalIdempotents e) (E : Nonempty (M ≃ₗ[R] ComponentwiseFreeModel e n)) : ComponentwiseFree R M
```

An explicit model indexed by any finite type gives componentwise freeness;
the witness is reindexed by a finite ordinal only to match the predicate's
small, concrete existential interface.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L138-L152) (native database range lines 136–150).

### Module.ComponentwiseFree.finite

```lean
theorem Module.ComponentwiseFree.finite {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (hM : ComponentwiseFree R M) : Module.Finite R M
```

A componentwise-free module is finitely generated.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L154-L160) (native database range lines 152–158).

### Module.ComponentwiseFree.projective

```lean
theorem Module.ComponentwiseFree.projective {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (hM : ComponentwiseFree R M) : Projective R M
```

A componentwise-free module is projective.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L162-L168) (native database range lines 160–166).

### Module.rankAtStalk_componentwiseFreeModel_of_notMem

```lean
theorem Module.rankAtStalk_componentwiseFreeModel_of_notMem {R : Type u} [CommRing R] {I : Type u_1} [Fintype I] (e : I → R) (n : I → ℕ) (he : CompleteOrthogonalIdempotents e) (i : I) (p : PrimeSpectrum R) (hi : e i ∉ p.asIdeal) : rankAtStalk (ComponentwiseFreeModel e n) p = n i
```

At a prime avoiding a member of a complete orthogonal family, the explicit
component model has the displayed rank of that member.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L170-L211) (native database range lines 168–209).

### Module.componentwiseFreeModelRank

```lean
noncomputable def Module.componentwiseFreeModelRank {R : Type u} [CommRing R] {I : Type u_1} [Fintype I] (e : I → R) (n : I → ℕ) (p : PrimeSpectrum R) : ℕ
```

The numerical rank prescribed by an explicit component model at a prime.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L213-L217) (native database range lines 211–215).

### Module.rankAtStalk_componentwiseFreeModel

```lean
theorem Module.rankAtStalk_componentwiseFreeModel {R : Type u} [CommRing R] {I : Type u_1} [Fintype I] (e : I → R) (n : I → ℕ) (he : CompleteOrthogonalIdempotents e) (p : PrimeSpectrum R) : rankAtStalk (ComponentwiseFreeModel e n) p = componentwiseFreeModelRank e n p
```

The exact stalk-rank formula for an explicit component model.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L219-L244) (native database range lines 217–242).

### Module.orthogonalIdempotents_mul_right

```lean
theorem Module.orthogonalIdempotents_mul_right {R : Type u} [CommRing R] {I : Type u_1} {e : I → R} {d : R} (he : OrthogonalIdempotents e) (hd : IsIdempotentElem d) : OrthogonalIdempotents fun (i : I) => e i * d
```

Multiplying a finite orthogonal family by an idempotent preserves
orthogonality.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L246-L260) (native database range lines 244–258).

### Module.orthogonalIdempotents_mul_left

```lean
theorem Module.orthogonalIdempotents_mul_left {R : Type u} [CommRing R] {I : Type u_1} {e : I → R} {d : R} (he : OrthogonalIdempotents e) (hd : IsIdempotentElem d) : OrthogonalIdempotents fun (i : I) => d * e i
```

Multiplying an orthogonal family on the left by an idempotent also
preserves orthogonality.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L262-L267) (native database range lines 260–265).

### Module.componentwiseFreeModelRefineRightEquiv

```lean
noncomputable def Module.componentwiseFreeModelRefineRightEquiv {R : Type u} [CommRing R] {I : Type u_1} {J : Type u_2} [Fintype I] [Fintype J] (e : I → R) (n : I → ℕ) (d : J → R) (he : CompleteOrthogonalIdempotents e) (hd : CompleteOrthogonalIdempotents d) : ComponentwiseFreeModel e n ≃ₗ[R] (i : I) → Fin (n i) → (j : J) → ↥(Ideal.span {e i * d j})
```

Refining the components `e i` by a second complete orthogonal family
`d j` does not change the explicit model.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L269-L281) (native database range lines 267–279).

### Module.componentwiseFreeModelRefineLeftEquiv

```lean
noncomputable def Module.componentwiseFreeModelRefineLeftEquiv {R : Type u} [CommRing R] {I : Type u_1} {J : Type u_2} [Fintype I] [Fintype J] (e : I → R) (d : J → R) (m : J → ℕ) (he : CompleteOrthogonalIdempotents e) (hd : CompleteOrthogonalIdempotents d) : ComponentwiseFreeModel d m ≃ₗ[R] (j : J) → Fin (m j) → (i : I) → ↥(Ideal.span {e i * d j})
```

Reassembly in the other order: the family `e i * d j` also refines
`d j`.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L283-L295) (native database range lines 281–293).

### Module.componentBlockEquiv

```lean
noncomputable def Module.componentBlockEquiv {R : Type u} [CommRing R] {I : Type u_1} {J : Type u_2} [Fintype I] [Fintype J] (e : I → R) (n : I → ℕ) (d : J → R) (m : J → ℕ) (hrank : ∀ (i : I) (j : J), e i * d j ≠ 0 → n i = m j) (i : I) (j : J) : (Fin (n i) → ↥(Ideal.span {e i * d j})) ≃ₗ[R] Fin (m j) → ↥(Ideal.span {e i * d j})
```

On a nonzero common idempotent corner, equal stalk ranks identify the
two displayed finite ranks; on the zero corner both blocks are zero.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L297-L312) (native database range lines 295–310).

### Module.componentRefinementComparisonEquiv

```lean
noncomputable def Module.componentRefinementComparisonEquiv {R : Type u} [CommRing R] {I : Type u_1} {J : Type u_2} [Fintype I] [Fintype J] (e : I → R) (n : I → ℕ) (d : J → R) (m : J → ℕ) (hrank : ∀ (i : I) (j : J), e i * d j ≠ 0 → n i = m j) : ((i : I) → Fin (n i) → (j : J) → ↥(Ideal.span {e i * d j})) ≃ₗ[R] (j : J) → Fin (m j) → (i : I) → ↥(Ideal.span {e i * d j})
```

Compare the two orderings of a common orthogonal refinement.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L314-L339) (native database range lines 312–337).

### Module.componentwiseFreeModelEquivOfRankAtStalkEq

```lean
noncomputable def Module.componentwiseFreeModelEquivOfRankAtStalkEq {R : Type u} [CommRing R] {I : Type u_1} {J : Type u_2} [Fintype I] [Fintype J] (e : I → R) (n : I → ℕ) (he : CompleteOrthogonalIdempotents e) (d : J → R) (m : J → ℕ) (hd : CompleteOrthogonalIdempotents d) (hrank : rankAtStalk (ComponentwiseFreeModel e n) = rankAtStalk (ComponentwiseFreeModel d m)) : ComponentwiseFreeModel e n ≃ₗ[R] ComponentwiseFreeModel d m
```

Explicit component models with equal stalk-rank functions are linearly
equivalent.  The proof refines both decompositions by the products `e i * d j`
and handles zero corners separately.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L341-L376) (native database range lines 339–374).

### Module.locallyConstantRankFiberIndex

```lean
abbrev Module.locallyConstantRankFiberIndex {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) : Type u
```

The nonempty rank fibers of a prescribed locally constant rank, using its
canonical threshold-ideal realization.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L380-L384) (native database range lines 378–382).

### Module.locallyConstantRankFiberIdempotent

```lean
noncomputable abbrev Module.locallyConstantRankFiberIdempotent {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) (j : locallyConstantRankFiberIndex f) : R
```

The idempotent cutting out a nonempty rank fiber of the canonical
realization of `f`.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L386-L391) (native database range lines 384–389).

### Module.locallyConstantRankFiberRank

```lean
noncomputable abbrev Module.locallyConstantRankFiberRank {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) (j : locallyConstantRankFiberIndex f) : ℕ
```

The value of the rank on a nonempty rank fiber of the canonical
realization of `f`.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L393-L398) (native database range lines 391–396).

### Module.locallyConstantRankFiberRank_le_rankBound

```lean
theorem Module.locallyConstantRankFiberRank_le_rankBound {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) (j : locallyConstantRankFiberIndex f) : locallyConstantRankFiberRank f j ≤ ModuleCat.FiniteProjective.rankBound f
```

The value on a rank fiber is bounded by the global bound used in the
threshold construction.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L400-L424) (native database range lines 398–422).

### Module.rankIdempotent_mul_locallyConstantRankFiberIdempotent

```lean
theorem Module.rankIdempotent_mul_locallyConstantRankFiberIdempotent {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) (i : Fin (ModuleCat.FiniteProjective.rankBound f)) (j : locallyConstantRankFiberIndex f) : ModuleCat.FiniteProjective.rankIdempotent f i * locallyConstantRankFiberIdempotent f j = if ↑i < locallyConstantRankFiberRank f j then locallyConstantRankFiberIdempotent f j else 0
```

On a rank fiber, a threshold idempotent is either one or zero.  This is
the key finite orthogonal comparison behind the explicit component model.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L426-L475) (native database range lines 424–473).

### Module.rankIdempotent_eq_sum_locallyConstantRankFiberIdempotent

```lean
theorem Module.rankIdempotent_eq_sum_locallyConstantRankFiberIdempotent {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) (i : Fin (ModuleCat.FiniteProjective.rankBound f)) : ModuleCat.FiniteProjective.rankIdempotent f i = ∑ j : locallyConstantRankFiberIndex f, if ↑i < locallyConstantRankFiberRank f j then locallyConstantRankFiberIdempotent f j else 0
```

The threshold idempotent is the sum of the rank-fiber idempotents on
which its threshold is active.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L477-L499) (native database range lines 475–497).

### Module.rankModuleEquivComponentwiseFreeModel

```lean
noncomputable def Module.rankModuleEquivComponentwiseFreeModel {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) : ModuleCat.FiniteProjective.rankModule R f ≃ₗ[R] ComponentwiseFreeModel (locallyConstantRankFiberIdempotent f) (locallyConstantRankFiberRank f)
```

The threshold-ideal realization is linearly equivalent to its explicit
complete-orthogonal-idempotent component model.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L501-L591) (native database range lines 499–589).

### Module.componentwiseFree_ofLocallyConstantRank

```lean
theorem Module.componentwiseFree_ofLocallyConstantRank {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) : ComponentwiseFree R ↑(ModuleCat.FiniteProjective.ofLocallyConstantRank R f)
```

The accepted canonical realization of any locally constant rank is
componentwise free in the explicit complete-orthogonal-idempotent sense.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L593-L604) (native database range lines 591–602).

### Module.ComponentwiseFree.nonempty_linearEquiv_of_rankAtStalk_eq

```lean
theorem Module.ComponentwiseFree.nonempty_linearEquiv_of_rankAtStalk_eq {R : Type u} [CommRing R] {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (hM : ComponentwiseFree R M) (hN : ComponentwiseFree R N) (hrank : rankAtStalk M = rankAtStalk N) : Nonempty (M ≃ₗ[R] N)
```

Componentwise-free modules in independent universes with the same stalk
rank are nonemptily linearly equivalent.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L608-L620) (native database range lines 606–618).

### Module.ComponentwiseFree.iff_nonempty_linearEquiv_ofLocallyConstantRank

```lean
theorem Module.ComponentwiseFree.iff_nonempty_linearEquiv_ofLocallyConstantRank {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] : ComponentwiseFree R M ↔ Nonempty (M ≃ₗ[R] ↑(ModuleCat.FiniteProjective.ofLocallyConstantRank R (rankLocallyConstant R M)))
```

A finite projective module is componentwise free exactly when it is
linearly equivalent to the canonical realization of its stalk-rank function.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L622-L639) (native database range lines 620–637).

### ModuleCat.isComponentwiseFree

```lean
def ModuleCat.isComponentwiseFree (R : Type u) [CommRing R] : CategoryTheory.ObjectProperty (FiniteProjective R)
```

The object property of a finite projective module being componentwise
free.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L647-L651) (native database range lines 645–649).

### ModuleCat.ComponentwiseFreeFiniteProjective

```lean
abbrev ModuleCat.ComponentwiseFreeFiniteProjective (R : Type u) [CommRing R] : Type (u + 1)
```

The full subcategory of finite projective modules which admit an explicit
finite complete-orthogonal-idempotent component model.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L653-L656) (native database range lines 651–654).

### ModuleCat.ComponentwiseFreeFiniteProjective.isoToLinearEquiv

```lean
noncomputable def ModuleCat.ComponentwiseFreeFiniteProjective.isoToLinearEquiv {R : Type u} [CommRing R] {X Y : ComponentwiseFreeFiniteProjective R} (e : X ≅ Y) : ↑X.obj ≃ₗ[R] ↑Y.obj
```

An isomorphism in the componentwise-free full subcategory induces the
underlying linear equivalence.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L662-L668) (native database range lines 660–666).

### ModuleCat.ComponentwiseFreeFiniteProjective.isoOfLinearEquiv

```lean
noncomputable def ModuleCat.ComponentwiseFreeFiniteProjective.isoOfLinearEquiv {R : Type u} [CommRing R] {X Y : ComponentwiseFreeFiniteProjective R} (e : ↑X.obj ≃ₗ[R] ↑Y.obj) : X ≅ Y
```

A linear equivalence between the underlying modules lifts to an
isomorphism in the componentwise-free full subcategory.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L670-L675) (native database range lines 668–673).

### ModuleCat.componentwiseFreeSkeletonRank

```lean
noncomputable def ModuleCat.componentwiseFreeSkeletonRank (R : Type u) [CommRing R] : CategoryTheory.Skeleton (ComponentwiseFreeFiniteProjective R) → LocallyConstant (PrimeSpectrum R) ℕ
```

The locally constant stalk-rank function represented by an object of the
skeleton of componentwise-free finite projectives.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L679-L685) (native database range lines 677–683).

### ModuleCat.componentwiseFreeSkeletonEquiv

```lean
noncomputable def ModuleCat.componentwiseFreeSkeletonEquiv (R : Type u) [CommRing R] : CategoryTheory.Skeleton (ComponentwiseFreeFiniteProjective R) ≃ LocallyConstant (PrimeSpectrum R) ℕ
```

The skeleton of componentwise-free finite projective modules is
classified by locally constant natural-valued rank functions.

[Source](../ProjectiveModules/Module/ComponentwiseFree.lean#L687-L722) (native database range lines 685–720).

## ProjectiveModules.Module.ComponentwiseFreeExamples

Scope: eight private example checks.

No native public display sites in this module.

## ProjectiveModules.Module.CountableCoordinateClosure

Scope: mathematical library leaf.

### LinearMap.exists_countable_invariant_supported

```lean
theorem LinearMap.exists_countable_invariant_supported {R : Type uR} [Semiring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) {s : Set ι} (hs : s.Countable) : ∃ (t : Set ι), s ⊆ t ∧ t.Countable ∧ Finsupp.supported R R t ≤ Submodule.comap p (Finsupp.supported R R t)
```

A countable set of coordinates in a standard free module is contained in
a countable coordinate set whose supported submodule is preserved by a chosen
linear endomorphism.

[Source](../ProjectiveModules/Module/CountableCoordinateClosure.lean#L78-L98) (native database range lines 78–98).

## ProjectiveModules.Module.CountableLocalProjective

Scope: mathematical library leaf.

### Module.Projective.exists_fin_rightFree_biorthogonal_exhaustion

```lean
theorem Module.Projective.exists_fin_rightFree_biorthogonal_exhaustion {R : Type uR} [Ring R] {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P] [Projective Rᵐᵒᵖ P] (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r) (x : ℕ → P) : ∃ (k : ℕ → ℕ) (f : (n : ℕ) → (Fin (k n) → R) →ₗ[Rᵐᵒᵖ] P) (g : (n : ℕ) → P →ₗ[Rᵐᵒᵖ] Fin (k n) → R), (∀ (n : ℕ), g n ∘ₗ f n = LinearMap.id) ∧ (∀ (m n : ℕ), m ≠ n → g m ∘ₗ f n = 0) ∧ ∀ (n : ℕ), x n = ∑ i : Fin (n + 1), (f ↑i) ((g ↑i) (x n))
```

A sequence in a projective right module over a possibly noncommutative
local ring admits coherent finite standard-free split components.  The
components are pairwise biorthogonal, and the `n`th vector is reconstructed by
the first `n + 1` components.

[Source](../ProjectiveModules/Module/CountableLocalProjective.lean#L369-L420) (native database range lines 369–420).

### Module.Projective.exists_fin_rightFree_biorthogonal_exhaustion_of_countablyGenerated

```lean
theorem Module.Projective.exists_fin_rightFree_biorthogonal_exhaustion_of_countablyGenerated {R : Type uR} [Ring R] {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P] [Projective Rᵐᵒᵖ P] (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r) (hP : CountablyGenerated Rᵐᵒᵖ P) : ∃ (x : ℕ → P) (k : ℕ → ℕ) (f : (n : ℕ) → (Fin (k n) → R) →ₗ[Rᵐᵒᵖ] P) (g : (n : ℕ) → P →ₗ[Rᵐᵒᵖ] Fin (k n) → R), Submodule.span Rᵐᵒᵖ (Set.range x) = ⊤ ∧ (∀ (n : ℕ), g n ∘ₗ f n = LinearMap.id) ∧ (∀ (m n : ℕ), m ≠ n → g m ∘ₗ f n = 0) ∧ ∀ (n : ℕ), x n = ∑ i : Fin (n + 1), (f ↑i) ((g ↑i) (x n))
```

A countably generated projective right module over a possibly
noncommutative local ring has a spanning sequence equipped with coherent finite
standard-free split components.

[Source](../ProjectiveModules/Module/CountableLocalProjective.lean#L422-L438) (native database range lines 422–438).

## ProjectiveModules.Module.CountableLocalProjectiveFree

Scope: mathematical library leaf.

### Module.Projective.exists_sigma_fin_rightBasis_of_countablyGenerated

```lean
theorem Module.Projective.exists_sigma_fin_rightBasis_of_countablyGenerated {R : Type uR} [Ring R] {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P] [Projective Rᵐᵒᵖ P] (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r) (hP : CountablyGenerated Rᵐᵒᵖ P) : ∃ (k : ℕ → ℕ), Nonempty (Basis ((n : ℕ) × Fin (k n)) Rᵐᵒᵖ P)
```

A countably generated projective right module over a possibly
noncommutative ring with a proper two-sided ideal whose complement consists of
units has a basis indexed by a countable disjoint union of finite types.

[Source](../ProjectiveModules/Module/CountableLocalProjectiveFree.lean#L119-L135) (native database range lines 119–135).

### Module.Projective.free_of_countablyGenerated

```lean
theorem Module.Projective.free_of_countablyGenerated {R : Type uR} [Ring R] {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P] [Projective Rᵐᵒᵖ P] (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r) (hP : CountablyGenerated Rᵐᵒᵖ P) : Free Rᵐᵒᵖ P
```

Every countably generated projective right module over a possibly
noncommutative ring with a proper two-sided ideal whose complement consists of
units is free.

[Source](../ProjectiveModules/Module/CountableLocalProjectiveFree.lean#L137-L147) (native database range lines 137–147).

## ProjectiveModules.Module.CountablyGenerated

Scope: mathematical library leaf.

### Module.CountablyGenerated

```lean
def Module.CountablyGenerated (R : Type uR) (M : Type uM) [Semiring R] [AddCommMonoid M] [Module R M] : Prop
```

A module is countably generated if the range of some sequence spans it.

[Source](../ProjectiveModules/Module/CountablyGenerated.lean#L31-L33) (native database range lines 31–33).

### Module.CountablyGenerated.of_finite

```lean
theorem Module.CountablyGenerated.of_finite {R : Type uR} {M : Type uM} [Semiring R] [AddCommMonoid M] [Module R M] [Module.Finite R M] : CountablyGenerated R M
```

A finite module is countably generated.

[Source](../ProjectiveModules/Module/CountablyGenerated.lean#L39-L48) (native database range lines 39–48).

### Module.CountablyGenerated.of_surjective

```lean
theorem Module.CountablyGenerated.of_surjective {R : Type uR} {M : Type uM} [Semiring R] [AddCommMonoid M] [Module R M] {N : Type uN} [AddCommMonoid N] [Module R N] (hM : CountablyGenerated R M) (f : M →ₗ[R] N) (hf : Function.Surjective ⇑f) : CountablyGenerated R N
```

A surjective linear image of a countably generated module is countably
generated.

[Source](../ProjectiveModules/Module/CountablyGenerated.lean#L52-L69) (native database range lines 52–69).

### Module.CountablyGenerated.equiv

```lean
theorem Module.CountablyGenerated.equiv {R : Type uR} {M : Type uM} [Semiring R] [AddCommMonoid M] [Module R M] {N : Type uN} [AddCommMonoid N] [Module R N] (hM : CountablyGenerated R M) (e : M ≃ₗ[R] N) : CountablyGenerated R N
```

A module linearly equivalent to a countably generated module is countably
generated.

[Source](../ProjectiveModules/Module/CountablyGenerated.lean#L71-L75) (native database range lines 71–75).

### Module.CountablyGenerated.equiv_iff

```lean
theorem Module.CountablyGenerated.equiv_iff {R : Type uR} {M : Type uM} [Semiring R] [AddCommMonoid M] [Module R M] {N : Type uN} [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N) : CountablyGenerated R M ↔ CountablyGenerated R N
```

Linearly equivalent modules are countably generated simultaneously.

[Source](../ProjectiveModules/Module/CountablyGenerated.lean#L77-L84) (native database range lines 77–84).

### Module.CountablyGenerated.finsupp

```lean
theorem Module.CountablyGenerated.finsupp {R : Type uR} [Semiring R] (ι : Type u_1) [Countable ι] : CountablyGenerated R (ι →₀ R)
```

A standard free module on a countable index type is countably generated.

[Source](../ProjectiveModules/Module/CountablyGenerated.lean#L86-L111) (native database range lines 86–111).

### Module.CountablyGenerated.supported

```lean
theorem Module.CountablyGenerated.supported {R : Type uR} [Semiring R] {ι : Type u_1} (s : Set ι) (hs : s.Countable) : CountablyGenerated R ↥(Finsupp.supported R R s)
```

The submodule of finitely supported functions on a countable coordinate
set is countably generated.

[Source](../ProjectiveModules/Module/CountablyGenerated.lean#L113-L119) (native database range lines 113–119).

## ProjectiveModules.Module.HomExact

Scope: mathematical library leaf.

### LinearMap.postcomp

```lean
def LinearMap.postcomp {R : Type uR} [Semiring R] {P : Type uP} {M : Type uM} {N : Type uN} [AddCommMonoid P] [AddCommMonoid M] [AddCommMonoid N] [Module R P] [Module R M] [Module R N] (f : M →ₗ[R] N) : (P →ₗ[R] M) →+ P →ₗ[R] N
```

Postcomposition by a linear map, as an additive homomorphism on a linear
Hom space.

[Source](../ProjectiveModules/Module/HomExact.lean#L36-L41) (native database range lines 36–41).

### LinearMap.postcomp_apply

```lean
theorem LinearMap.postcomp_apply {R : Type uR} [Semiring R] {P : Type uP} {M : Type uM} {N : Type uN} [AddCommMonoid P] [AddCommMonoid M] [AddCommMonoid N] [Module R P] [Module R M] [Module R N] (f : M →ₗ[R] N) (g : P →ₗ[R] M) : f.postcomp g = f ∘ₗ g
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/HomExact.lean#L43-L46) (native database range lines 43–46).

### LinearMap.postcomp_injective

```lean
theorem LinearMap.postcomp_injective {R : Type uR} [Semiring R] {P : Type uP} {L : Type uL} {M : Type uM} [AddCommMonoid P] [AddCommMonoid L] [AddCommMonoid M] [Module R P] [Module R L] [Module R M] (i : L →ₗ[R] M) (hi : Function.Injective ⇑i) : Function.Injective ⇑i.postcomp
```

Postcomposition with an injective linear map is injective.

[Source](../ProjectiveModules/Module/HomExact.lean#L48-L51) (native database range lines 48–51).

### LinearMap.exact_postcomp

```lean
theorem LinearMap.exact_postcomp {R : Type uR} [Semiring R] {P : Type uP} {L : Type uL} {M : Type uM} {N : Type uN} [AddCommMonoid P] [AddCommMonoid L] [AddCommMonoid M] [AddCommMonoid N] [Module R P] [Module R L] [Module R M] [Module R N] (i : L →ₗ[R] M) (p : M →ₗ[R] N) (hi : Function.Injective ⇑i) (h : Function.Exact ⇑i ⇑p) : Function.Exact ⇑i.postcomp ⇑p.postcomp
```

Postcomposition preserves exactness at the middle Hom space when the
first map of the original exact pair is injective.

[Source](../ProjectiveModules/Module/HomExact.lean#L53-L75) (native database range lines 53–75).

### Module.Projective.postcomp_surjective

```lean
theorem Module.Projective.postcomp_surjective {R : Type uR} [Semiring R] {P : Type uP} {M : Type uM} {N : Type uN} [AddCommMonoid P] [AddCommMonoid M] [AddCommMonoid N] [Module R P] [Module R M] [Module R N] [Projective R P] (p : M →ₗ[R] N) (hp : Function.Surjective ⇑p) : Function.Surjective ⇑p.postcomp
```

If `P` is projective, postcomposition with a surjective linear map is
surjective on linear maps out of `P`.

[Source](../ProjectiveModules/Module/HomExact.lean#L86-L92) (native database range lines 86–92).

### Module.Projective.hom_short_exact

```lean
theorem Module.Projective.hom_short_exact {R : Type uR} [Semiring R] {P : Type uP} {L : Type uL} {M : Type uM} {N : Type uN} [AddCommMonoid P] [AddCommMonoid L] [AddCommMonoid M] [AddCommMonoid N] [Module R P] [Module R L] [Module R M] [Module R N] [Projective R P] (i : L →ₗ[R] M) (p : M →ₗ[R] N) (hi : Function.Injective ⇑i) (h : Function.Exact ⇑i ⇑p) (hp : Function.Surjective ⇑p) : Function.Injective ⇑i.postcomp ∧ Function.Exact ⇑i.postcomp ⇑p.postcomp ∧ Function.Surjective ⇑p.postcomp
```

Applying `Hom(P, -)` to an injective/exact/surjective pair preserves all
three properties when `P` is projective.

[Source](../ProjectiveModules/Module/HomExact.lean#L94-L105) (native database range lines 94–105).

## ProjectiveModules.Module.InvariantSupportedProjection

Scope: mathematical library leaf.

### LinearMap.supportedRange

```lean
noncomputable def LinearMap.supportedRange {R : Type uR} [Ring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) (s : Set ι) : Submodule R (ι →₀ R)
```

The elements in the range of `p` whose coordinates are supported on `s`.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L38-L41) (native database range lines 38–41).

### LinearMap.supportedRange_mono

```lean
theorem LinearMap.supportedRange_mono {R : Type uR} [Ring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) {s t : Set ι} (hst : s ⊆ t) : p.supportedRange s ≤ p.supportedRange t
```

Supported range pieces are monotone in their coordinate set.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L43-L47) (native database range lines 43–47).

### LinearMap.supportedRangeInclusion

```lean
noncomputable def LinearMap.supportedRangeInclusion {R : Type uR} [Ring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) {s t : Set ι} (hst : s ⊆ t) : ↥(p.supportedRange s) →ₗ[R] ↥(p.supportedRange t)
```

The natural inclusion between nested supported range pieces.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L49-L53) (native database range lines 49–53).

### LinearMap.supportedRangeProjection

```lean
noncomputable def LinearMap.supportedRangeProjection {R : Type uR} [Ring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) (s : Set ι) (hinv : Finsupp.supported R R s ≤ Submodule.comap p (Finsupp.supported R R s)) : ↥(Finsupp.supported R R s) →ₗ[R] ↥(p.supportedRange s)
```

On an invariant coordinate set, applying `p` lands in its supported
range.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L55-L64) (native database range lines 55–64).

### LinearMap.supportedRangeToSupported

```lean
noncomputable def LinearMap.supportedRangeToSupported {R : Type uR} [Ring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) (s : Set ι) : ↥(p.supportedRange s) →ₗ[R] ↥(Finsupp.supported R R s)
```

The supported range piece includes into its supported standard free
module.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L66-L71) (native database range lines 66–71).

### LinearMap.supportedRangeProjection_comp_toSupported

```lean
theorem LinearMap.supportedRangeProjection_comp_toSupported {R : Type uR} [Ring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) (hp : IsIdempotentElem p) (s : Set ι) (hinv : Finsupp.supported R R s ≤ Submodule.comap p (Finsupp.supported R R s)) : p.supportedRangeProjection s hinv ∘ₗ p.supportedRangeToSupported s = id
```

For an idempotent endomorphism, supported range projection retracts the
natural inclusion.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L73-L85) (native database range lines 73–85).

### LinearMap.supportedRange_projective

```lean
theorem LinearMap.supportedRange_projective {R : Type uR} [Ring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) (hp : IsIdempotentElem p) (s : Set ι) (hinv : Finsupp.supported R R s ≤ Submodule.comap p (Finsupp.supported R R s)) : Module.Projective R ↥(p.supportedRange s)
```

An invariant supported piece of the range of an idempotent endomorphism
is projective.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L87-L101) (native database range lines 87–101).

### LinearMap.supportedRangeRetraction

```lean
noncomputable def LinearMap.supportedRangeRetraction {R : Type uR} [Ring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) (s t : Set ι) (hinv : Finsupp.supported R R s ≤ Submodule.comap p (Finsupp.supported R R s)) : ↥(p.supportedRange t) →ₗ[R] ↥(p.supportedRange s)
```

Restriction to `s`, followed by `p`, retracts a later supported range piece
onto the earlier one.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L103-L113) (native database range lines 103–113).

### LinearMap.supportedRangeRetraction_comp_inclusion

```lean
theorem LinearMap.supportedRangeRetraction_comp_inclusion {R : Type uR} [Ring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) (hp : IsIdempotentElem p) {s t : Set ι} (hst : s ⊆ t) (hinv : Finsupp.supported R R s ≤ Submodule.comap p (Finsupp.supported R R s)) : p.supportedRangeRetraction s t hinv ∘ₗ p.supportedRangeInclusion hst = id
```

The retraction of a nested supported range piece is a right inverse to its
natural inclusion.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L115-L133) (native database range lines 115–133).

### LinearMap.supportedRangeProdComplementEquiv

```lean
noncomputable def LinearMap.supportedRangeProdComplementEquiv {R : Type uR} [Ring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) (hp : IsIdempotentElem p) {s t : Set ι} (hst : s ⊆ t) (hinv : Finsupp.supported R R s ≤ Submodule.comap p (Finsupp.supported R R s)) : (↥(p.supportedRangeRetraction s t hinv).ker × ↥(p.supportedRange s)) ≃ₗ[R] ↥(p.supportedRange t)
```

A later supported range piece is the product of an earlier piece and the
kernel of the canonical retraction.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L135-L160) (native database range lines 135–160).

### LinearMap.splitKernelProjection

```lean
def LinearMap.splitKernelProjection {R : Type uR} [Ring R] {A : Type u_1} {M : Type u_2} [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M] (i : A →ₗ[R] M) (r : M →ₗ[R] A) (h : r ∘ₗ i = id) : M →ₗ[R] ↥r.ker
```

Projection from a split module onto the kernel of its retraction.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L162-L172) (native database range lines 162–172).

### LinearMap.splitKernelProjection_comp_subtype

```lean
theorem LinearMap.splitKernelProjection_comp_subtype {R : Type uR} [Ring R] {A : Type u_1} {M : Type u_2} [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M] (i : A →ₗ[R] M) (r : M →ₗ[R] A) (h : r ∘ₗ i = id) : i.splitKernelProjection r h ∘ₗ r.ker.subtype = id
```

The split-kernel projection retracts the kernel subtype.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L174-L185) (native database range lines 174–185).

### LinearMap.projective_splitKernel

```lean
theorem LinearMap.projective_splitKernel {R : Type uR} [Ring R] {A : Type u_1} {M : Type u_2} [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M] [Module.Projective R M] (i : A →ₗ[R] M) (r : M →ₗ[R] A) (h : r ∘ₗ i = id) : Module.Projective R ↥r.ker
```

The kernel of a retraction from a projective module is projective.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L187-L196) (native database range lines 187–196).

### LinearMap.supportedRangeComplement_projective

```lean
theorem LinearMap.supportedRangeComplement_projective {R : Type uR} [Ring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) (hp : IsIdempotentElem p) {s t : Set ι} (hst : s ⊆ t) (hs : Finsupp.supported R R s ≤ Submodule.comap p (Finsupp.supported R R s)) (ht : Finsupp.supported R R t ≤ Submodule.comap p (Finsupp.supported R R t)) : Module.Projective R ↥(p.supportedRangeRetraction s t hs).ker
```

The complement of an earlier invariant supported range piece in a later
one is projective.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L198-L219) (native database range lines 198–219).

### LinearMap.supportedDifferenceToComplement

```lean
noncomputable def LinearMap.supportedDifferenceToComplement {R : Type uR} [Ring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) (hp : IsIdempotentElem p) {s t : Set ι} (hst : s ⊆ t) (hs : Finsupp.supported R R s ≤ Submodule.comap p (Finsupp.supported R R s)) (ht : Finsupp.supported R R t ≤ Submodule.comap p (Finsupp.supported R R t)) : ↥(Finsupp.supported R R (t \ s)) →ₗ[R] ↥(p.supportedRangeRetraction s t hs).ker
```

The coordinate difference maps onto the complement of an earlier
invariant supported range piece.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L234-L251) (native database range lines 234–251).

### LinearMap.supportedDifferenceToComplement_surjective

```lean
theorem LinearMap.supportedDifferenceToComplement_surjective {R : Type uR} [Ring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) (hp : IsIdempotentElem p) {s t : Set ι} (hst : s ⊆ t) (hs : Finsupp.supported R R s ≤ Submodule.comap p (Finsupp.supported R R s)) (ht : Finsupp.supported R R t ≤ Submodule.comap p (Finsupp.supported R R t)) : Function.Surjective ⇑(p.supportedDifferenceToComplement hp hst hs ht)
```

The coordinate-difference map onto the split complement is surjective.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L253-L320) (native database range lines 253–320).

### LinearMap.supportedRangeComplement_countablyGenerated

```lean
theorem LinearMap.supportedRangeComplement_countablyGenerated {R : Type uR} [Ring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) (hp : IsIdempotentElem p) {s t : Set ι} (hst : s ⊆ t) (hs : Finsupp.supported R R s ≤ Submodule.comap p (Finsupp.supported R R s)) (ht : Finsupp.supported R R t ≤ Submodule.comap p (Finsupp.supported R R t)) (hcount : (t \ s).Countable) : Module.CountablyGenerated R ↥(p.supportedRangeRetraction s t hs).ker
```

If the coordinate increment is countable, the complement of the earlier
supported range piece is countably generated.

[Source](../ProjectiveModules/Module/InvariantSupportedProjection.lean#L322-L336) (native database range lines 322–336).

## ProjectiveModules.Module.LaurentPolynomial

Scope: mathematical library leaf.

### LaurentPolynomial.instIsPrincipalIdealRingOfField

```lean
instance LaurentPolynomial.instIsPrincipalIdealRingOfField (F : Type uF) [Field F] : IsPrincipalIdealRing (LaurentPolynomial F)
```

The one-variable Laurent polynomial ring over a field is a principal ideal
ring.

[Source](../ProjectiveModules/Module/LaurentPolynomial.lean#L34-L45) (native database range lines 34–45).

### LaurentPolynomial.instIsPrincipalIdealRingOppositeOfField

```lean
instance LaurentPolynomial.instIsPrincipalIdealRingOppositeOfField (F : Type uF) [Field F] : IsPrincipalIdealRing (LaurentPolynomial F)ᵐᵒᵖ
```

The opposite of a one-variable Laurent polynomial ring over a field is a
principal ideal ring.  This is the scalar ring for literal right modules.

[Source](../ProjectiveModules/Module/LaurentPolynomial.lean#L47-L52) (native database range lines 47–52).

### LaurentPolynomial.module_free_of_finite_projective

```lean
theorem LaurentPolynomial.module_free_of_finite_projective (F : Type uF) (P : Type uP) [Field F] [AddCommGroup P] [Module (LaurentPolynomial F) P] [Module.Finite (LaurentPolynomial F) P] [Module.Projective (LaurentPolynomial F) P] : Module.Free (LaurentPolynomial F) P
```

A finitely generated projective module over the one-variable Laurent
polynomial ring over a field is free.

[Source](../ProjectiveModules/Module/LaurentPolynomial.lean#L54-L62) (native database range lines 54–62).

### LaurentPolynomial.op_module_free_of_finite_projective

```lean
theorem LaurentPolynomial.op_module_free_of_finite_projective (F : Type uF) (P : Type uP) [Field F] [AddCommGroup P] [Module (LaurentPolynomial F)ᵐᵒᵖ P] [Module.Finite (LaurentPolynomial F)ᵐᵒᵖ P] [Module.Projective (LaurentPolynomial F)ᵐᵒᵖ P] : Module.Free (LaurentPolynomial F)ᵐᵒᵖ P
```

A finitely generated projective right module over the one-variable Laurent
polynomial ring over a field is free, with the right action represented as a
left action of the opposite ring.

[Source](../ProjectiveModules/Module/LaurentPolynomial.lean#L64-L73) (native database range lines 64–73).

## ProjectiveModules.Module.LocalProjective

Scope: mathematical library leaf.

### Module.Projective.exists_rightFreeLinearEquiv_of_isUnit_compl

```lean
theorem Module.Projective.exists_rightFreeLinearEquiv_of_isUnit_compl {R : Type uR} [Ring R] {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P] [Module.Finite Rᵐᵒᵖ P] [Projective Rᵐᵒᵖ P] (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ x ∉ I, IsUnit x) : have x := ⋯; let x := I.quotientDivisionRing hI hunit; have x_1 := ⋯; ∃ (e : (Fin (finrank (R ⧸ TwoSidedIdeal.asIdeal I)ᵐᵒᵖ (ModuleCat.RightExtension.IdealQuotient (TwoSidedIdeal.asIdeal I))) → R) ≃ₗ[Rᵐᵒᵖ] P), ∀ (i : Fin (finrank (R ⧸ TwoSidedIdeal.asIdeal I)ᵐᵒᵖ (ModuleCat.RightExtension.IdealQuotient (TwoSidedIdeal.asIdeal I)))), Submodule.Quotient.mk (e (Pi.single i 1)) = (finBasis (R ⧸ TwoSidedIdeal.asIdeal I)ᵐᵒᵖ (ModuleCat.RightExtension.IdealQuotient (TwoSidedIdeal.asIdeal I))) i
```

A finite projective right module over a ring with a proper two-sided ideal
whose complement consists of units has a finite standard-coordinate
equivalence.  The standard basis reduces to the canonical basis of the
quotient module, so the rank is exactly its residue-module finrank.

[Source](../ProjectiveModules/Module/LocalProjective.lean#L42-L391) (native database range lines 42–391).

### Module.Projective.free_of_isUnit_compl

```lean
theorem Module.Projective.free_of_isUnit_compl {R : Type uR} [Ring R] {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P] [Module.Finite Rᵐᵒᵖ P] [Projective Rᵐᵒᵖ P] (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ x ∉ I, IsUnit x) : Free Rᵐᵒᵖ P
```

Every finitely generated projective right module over a ring with a proper
two-sided ideal whose complement consists of units is free.

[Source](../ProjectiveModules/Module/LocalProjective.lean#L393-L414) (native database range lines 393–414).

## ProjectiveModules.Module.LocalProjectiveElement

Scope: mathematical library leaf.

### Module.Projective.exists_fin_rightFree_split_containing

```lean
theorem Module.Projective.exists_fin_rightFree_split_containing {R : Type uR} [Ring R] {P : Type uP} [AddCommGroup P] [Module Rᵐᵒᵖ P] [Projective Rᵐᵒᵖ P] (I : TwoSidedIdeal R) (hI : I ≠ ⊤) (hunit : ∀ r ∉ I, IsUnit r) (x : P) : ∃ (n : ℕ) (f : (Fin n → R) →ₗ[Rᵐᵒᵖ] P) (g : P →ₗ[Rᵐᵒᵖ] Fin n → R), g ∘ₗ f = LinearMap.id ∧ x ∈ f.range
```

Every element of a projective right module over a ring with a proper
two-sided ideal whose complement consists of units lies in a finite free direct
summand.  The maps `f` and `g` exhibit the range of `f` as that summand.

[Source](../ProjectiveModules/Module/LocalProjectiveElement.lean#L31-L163) (native database range lines 31–163).

## ProjectiveModules.Module.LocallyConstantRank

Scope: mathematical library leaf.

### IsIdempotentElem.spanProjection

```lean
noncomputable def IsIdempotentElem.spanProjection {R : Type u} [CommRing R] (e : R) : R →ₗ[R] ↥(Ideal.span {e})
```

Multiplication by `e`, regarded as a projection onto the principal ideal
generated by `e`.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L38-L44) (native database range lines 38–44).

### IsIdempotentElem.spanProjection_comp_subtype

```lean
theorem IsIdempotentElem.spanProjection_comp_subtype {R : Type u} [CommRing R] {e : R} (he : IsIdempotentElem e) : spanProjection e ∘ₗ Submodule.subtype (Ideal.span {e}) = LinearMap.id
```

The idempotent-span projection retracts the inclusion into the base ring.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L46-L53) (native database range lines 46–53).

### IsIdempotentElem.projective_span

```lean
theorem IsIdempotentElem.projective_span {R : Type u} [CommRing R] {e : R} (he : IsIdempotentElem e) : Module.Projective R ↥(Ideal.span {e})
```

The principal ideal generated by an idempotent is projective.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L55-L59) (native database range lines 55–59).

### IsIdempotentElem.spanProdEquiv

```lean
noncomputable def IsIdempotentElem.spanProdEquiv {R : Type u} [CommRing R] {e : R} (he : IsIdempotentElem e) : (↥(Ideal.span {e}) × ↥(Ideal.span {1 - e})) ≃ₗ[R] R
```

The two ideals cut out by an idempotent are complementary.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L61-L85) (native database range lines 61–85).

### IsIdempotentElem.rankAtStalk_span_eq_zero

```lean
theorem IsIdempotentElem.rankAtStalk_span_eq_zero {R : Type u} [CommRing R] {e : R} (he : IsIdempotentElem e) (p : PrimeSpectrum R) (hp : e ∈ p.asIdeal) : Module.rankAtStalk (↥(Ideal.span {e})) p = 0
```

The ideal generated by an idempotent has stalk rank zero at a prime
containing the idempotent.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L87-L108) (native database range lines 87–108).

### IsIdempotentElem.rankAtStalk_span_eq_one

```lean
theorem IsIdempotentElem.rankAtStalk_span_eq_one {R : Type u} [CommRing R] {e : R} (he : IsIdempotentElem e) (p : PrimeSpectrum R) (hp : e ∉ p.asIdeal) : Module.rankAtStalk (↥(Ideal.span {e})) p = 1
```

The ideal generated by an idempotent has stalk rank one at a prime not
containing the idempotent.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L110-L137) (native database range lines 110–137).

### ModuleCat.FiniteProjective.rankBound

```lean
noncomputable def ModuleCat.FiniteProjective.rankBound {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) : ℕ
```

A finite upper bound for a locally constant natural-valued function on a
prime spectrum.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L145-L148) (native database range lines 145–148).

### ModuleCat.FiniteProjective.le_rankBound

```lean
theorem ModuleCat.FiniteProjective.le_rankBound {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) (p : PrimeSpectrum R) : f p ≤ rankBound f
```

Every value of `f` is at most `rankBound f`.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L150-L155) (native database range lines 150–155).

### ModuleCat.FiniteProjective.rankClopen

```lean
def ModuleCat.FiniteProjective.rankClopen {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) (i : Fin (rankBound f)) : TopologicalSpace.Clopens (PrimeSpectrum R)
```

The clopen threshold set on which the prescribed rank is greater than `i`.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L157-L160) (native database range lines 157–160).

### ModuleCat.FiniteProjective.rankIdempotent

```lean
noncomputable def ModuleCat.FiniteProjective.rankIdempotent {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) (i : Fin (rankBound f)) : R
```

The idempotent cutting out the threshold set `rankClopen f i`.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L162-L165) (native database range lines 162–165).

### ModuleCat.FiniteProjective.rankIdempotent_isIdempotent

```lean
theorem ModuleCat.FiniteProjective.rankIdempotent_isIdempotent {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) (i : Fin (rankBound f)) : IsIdempotentElem (rankIdempotent f i)
```

A threshold idempotent is idempotent.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L167-L171) (native database range lines 167–171).

### ModuleCat.FiniteProjective.rankIdempotent_notMem_iff

```lean
theorem ModuleCat.FiniteProjective.rankIdempotent_notMem_iff {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) (i : Fin (rankBound f)) (p : PrimeSpectrum R) : rankIdempotent f i ∉ p.asIdeal ↔ ↑i < f p
```

A threshold idempotent avoids precisely the primes where the rank is
strictly larger than its index.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L173-L181) (native database range lines 173–181).

### ModuleCat.FiniteProjective.rankModule

```lean
abbrev ModuleCat.FiniteProjective.rankModule (R : Type u) [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) : Type u
```

The explicit threshold-ideal module underlying
`ofLocallyConstantRank`.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L183-L187) (native database range lines 183–187).

### ModuleCat.FiniteProjective.rankModuleFinite

```lean
theorem ModuleCat.FiniteProjective.rankModuleFinite {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) : Module.Finite R (rankModule R f)
```

The explicit threshold-ideal module is finitely generated.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L193-L200) (native database range lines 193–200).

### ModuleCat.FiniteProjective.rankModuleProjective

```lean
theorem ModuleCat.FiniteProjective.rankModuleProjective {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) : Module.Projective R (rankModule R f)
```

The explicit threshold-ideal module is projective.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L202-L209) (native database range lines 202–209).

### ModuleCat.FiniteProjective.ofLocallyConstantRank

```lean
noncomputable def ModuleCat.FiniteProjective.ofLocallyConstantRank (R : Type u) [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) : FiniteProjective R
```

A finite projective module realizing a locally constant stalk-rank function.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L228-L233) (native database range lines 228–233).

### ModuleCat.FiniteProjective.complementOfLocallyConstantRank

```lean
noncomputable def ModuleCat.FiniteProjective.complementOfLocallyConstantRank (R : Type u) [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) : FiniteProjective R
```

The complementary finite projective module in the finite-free realization
of a locally constant stalk-rank function.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L235-L241) (native database range lines 235–241).

### ModuleCat.FiniteProjective.prodComplementEquiv

```lean
noncomputable def ModuleCat.FiniteProjective.prodComplementEquiv (R : Type u) [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) : (↑(ofLocallyConstantRank R f) × ↑(complementOfLocallyConstantRank R f)) ≃ₗ[R] Fin (rankBound f) → R
```

The realizing module and its componentwise complement sum to a finite
standard free module.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L254-L265) (native database range lines 254–265).

### ModuleCat.FiniteProjective.rankAtStalk_ofLocallyConstantRank

```lean
theorem ModuleCat.FiniteProjective.rankAtStalk_ofLocallyConstantRank {R : Type u} [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) : Module.rankAtStalk ↑(ofLocallyConstantRank R f) = ⇑f
```

The module constructed by `ofLocallyConstantRank` has the prescribed
stalk-rank function at every prime.

[Source](../ProjectiveModules/Module/LocallyConstantRank.lean#L267-L296) (native database range lines 267–296).

## ProjectiveModules.Module.MinimalSupport

Scope: mathematical library leaf.

### Module.Basis.HasMinimalSupport

```lean
def Module.Basis.HasMinimalSupport {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module R M] {ι : Type uι} (b : Basis ι R M) (x : M) : Prop
```

A basis has minimal support for `x` if no basis with the same index type
expresses `x` using fewer nonzero coordinates.

[Source](../ProjectiveModules/Module/MinimalSupport.lean#L30-L33) (native database range lines 30–33).

### Module.Basis.exists_hasMinimalSupport

```lean
theorem Module.Basis.exists_hasMinimalSupport {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module R M] {ι : Type uι} (b₀ : Basis ι R M) (x : M) : ∃ (b : Basis ι R M), b.HasMinimalSupport x
```

Every vector admits a basis of minimal support among bases with a fixed
index type, provided one such basis exists.

[Source](../ProjectiveModules/Module/MinimalSupport.lean#L35-L45) (native database range lines 35–45).

### Module.Basis.HasMinimalSupport.coord_ne_apply_of_apply_eq_zero

```lean
theorem Module.Basis.HasMinimalSupport.coord_ne_apply_of_apply_eq_zero {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module R M] {ι : Type uι} {b : Basis ι R M} {x : M} (hb : b.HasMinimalSupport x) {j : ι} (hj : j ∈ (b.repr x).support) (φ : M →ₗ[R] R) (hφj : φ (b j) = 0) : (b.repr x) j ≠ φ x
```

In a minimal-support basis, a nonzero coordinate cannot be recovered by a
linear functional that vanishes on the corresponding basis vector.

The elementary change of basis is the transvection
`z ↦ z + φ z • b j`. If `φ (b j) = 0` and the `j`th coordinate of `x` equals
`φ x`, then the inverse transvection erases exactly that coordinate and leaves
all others unchanged, contradicting minimality.

[Source](../ProjectiveModules/Module/MinimalSupport.lean#L47-L73) (native database range lines 47–73).

### Module.Basis.HasMinimalSupport.coord_ne_sum_mul

```lean
theorem Module.Basis.HasMinimalSupport.coord_ne_sum_mul {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module R M] {ι : Type uι} [DecidableEq ι] {b : Basis ι R M} {x : M} (hb : b.HasMinimalSupport x) {j : ι} (hj : j ∈ (b.repr x).support) (c : ι → R) : (b.repr x) j ≠ ∑ i ∈ (b.repr x).support.erase j, (b.repr x) i * c i
```

A nonzero coordinate in a minimal-support basis is not a right-linear
combination of the remaining coordinates. For a module over `Rᵐᵒᵖ`, this is
exactly the left-ideal coefficient orientation for a right `R`-module.

[Source](../ProjectiveModules/Module/MinimalSupport.lean#L75-L101) (native database range lines 75–101).

### Module.Basis.HasMinimalSupport.not_isUnit_coord_comp_apply_of_ne

```lean
theorem Module.Basis.HasMinimalSupport.not_isUnit_coord_comp_apply_of_ne {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module R M] {ι : Type uι} {b : Basis ι R M} {x : M} (hb : b.HasMinimalSupport x) (e : M →ₗ[R] M) (hex : e x = x) {i j : ι} (hi : i ∈ (b.repr x).support) (hij : i ≠ j) : ¬IsUnit ((b.coord j) (e (b i)))
```

An off-diagonal coefficient of a projection fixing `x`, measured in a
minimal-support basis and between two coordinates in the support of `x`, cannot
be a unit.

[Source](../ProjectiveModules/Module/MinimalSupport.lean#L103-L127) (native database range lines 103–127).

### Module.Basis.HasMinimalSupport.not_isUnit_one_sub_coord_comp_apply

```lean
theorem Module.Basis.HasMinimalSupport.not_isUnit_one_sub_coord_comp_apply {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module R M] {ι : Type uι} {b : Basis ι R M} {x : M} (hb : b.HasMinimalSupport x) (e : M →ₗ[R] M) (hex : e x = x) {j : ι} (hj : j ∈ (b.repr x).support) : ¬IsUnit (1 - (b.coord j) (e (b j)))
```

The complement of a diagonal coefficient of a projection fixing `x`, in a
minimal-support coordinate of `x`, cannot be a unit.

[Source](../ProjectiveModules/Module/MinimalSupport.lean#L129-L151) (native database range lines 129–151).

## ProjectiveModules.Module.PID

Scope: mathematical library leaf.

### Submodule.PIDFree.instLinearOrder_projectiveModules

```lean
noncomputable def Submodule.PIDFree.instLinearOrder_projectiveModules {ι : Type w} : LinearOrder ι
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/PID.lean#L55-L55) (native database range lines 55–55).

### Submodule.PIDFree.instWellFoundedLT_projectiveModules

```lean
theorem Submodule.PIDFree.instWellFoundedLT_projectiveModules {ι : Type w} : WellFoundedLT ι
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/PID.lean#L56-L56) (native database range lines 56–56).

### Submodule.free_of_pid_of_free

```lean
theorem Submodule.free_of_pid_of_free {R : Type u} {M : Type v} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] [Module.Free R M] (N : Submodule R M) : Module.Free R ↥N
```

Every submodule of an arbitrary-rank free module over a commutative PID is free.

[Source](../ProjectiveModules/Module/PID.lean#L257-L260) (native database range lines 257–260).

### Module.Projective.free_of_pid

```lean
theorem Module.Projective.free_of_pid (R : Type u) (P : Type v) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup P] [Module R P] [Projective R P] : Free R P
```

An arbitrary-rank projective module over a commutative PID is free.

[Source](../ProjectiveModules/Module/PID.lean#L272-L283) (native database range lines 272–283).

## ProjectiveModules.Module.ProjectiveComplement

Scope: mathematical library leaf.

### Module.Projective.prodKerEquivOfSurjective

```lean
noncomputable def Module.Projective.prodKerEquivOfSurjective {R : Type uR} [Ring R] {F : Type uF} [AddCommGroup F] [Module R F] {P : Type uP} [AddCommGroup P] [Module R P] [Projective R P] (f : F →ₗ[R] P) (hf : Function.Surjective ⇑f) : (P × ↥f.ker) ≃ₗ[R] F
```

A surjection onto a projective module identifies its domain with the
product of the target and its kernel.

[Source](../ProjectiveModules/Module/ProjectiveComplement.lean#L37-L49) (native database range lines 37–49).

### Module.Projective.exists_surjective_iff_exists_prod_equiv

```lean
theorem Module.Projective.exists_surjective_iff_exists_prod_equiv {R : Type uR} [Ring R] {F : Type uF} [AddCommGroup F] [Module R F] {P : Type uP} [AddCommGroup P] [Module R P] [Projective R P] : (∃ (f : F →ₗ[R] P), Function.Surjective ⇑f) ↔ ∃ (Q : Type uF) (x : AddCommGroup Q) (x_1 : Module R Q), Nonempty ((P × Q) ≃ₗ[R] F)
```

A projective module is a quotient of `F` exactly when it is a direct
summand of `F`.

[Source](../ProjectiveModules/Module/ProjectiveComplement.lean#L51-L65) (native database range lines 51–65).

### Module.Projective.exists_fin_generating_family_iff_exists_prod_equiv

```lean
theorem Module.Projective.exists_fin_generating_family_iff_exists_prod_equiv {R : Type uR} [Ring R] {P : Type uP} [AddCommGroup P] [Module R P] [Projective R P] (n : ℕ) : (∃ (v : Fin n → P), Submodule.span R (Set.range v) = ⊤) ↔ ∃ (Q : Type uR) (x : AddCommGroup Q) (x_1 : Module R Q), Nonempty ((P × Q) ≃ₗ[R] Fin n → R)
```

A projective module has an `n`-element spanning family exactly when it is
a direct summand of the standard free module of rank `n`.

[Source](../ProjectiveModules/Module/ProjectiveComplement.lean#L67-L92) (native database range lines 67–92).

### Module.Projective.exists_finite_complement_linearEquiv

```lean
theorem Module.Projective.exists_finite_complement_linearEquiv {R : Type uR} [Ring R] {P : Type uP} [AddCommGroup P] [Module R P] [Module.Finite R P] [Projective R P] : ∃ (n : ℕ) (Q : Type uR) (x : AddCommGroup Q) (x_1 : Module R Q), Module.Finite R Q ∧ Nonempty ((P × Q) ≃ₗ[R] Fin n → R)
```

A finite projective module has a finite complement whose product with it
is explicitly equivalent to a finite standard free module.

[Source](../ProjectiveModules/Module/ProjectiveComplement.lean#L94-L108) (native database range lines 94–108).

### Module.exists_finite_free_product_of_finite_projective

```lean
theorem Module.exists_finite_free_product_of_finite_projective {R : Type uR} [Ring R] {B : Type uP} [AddCommGroup B] [Module R B] [Module.Finite R B] [Projective R B] : ∃ (Q : Type uR) (x : AddCommGroup Q) (x_1 : Module R Q), Module.Finite R Q ∧ Module.Finite R (B × Q) ∧ Free R (B × Q)
```

A finite projective module has a finite complement whose product with the
module is finite free.

[Source](../ProjectiveModules/Module/ProjectiveComplement.lean#L116-L132) (native database range lines 116–132).

## ProjectiveModules.Module.RankFiberDecomposition

Scope: mathematical library leaf.

### Module.rankLocallyConstant

```lean
noncomputable def Module.rankLocallyConstant (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] : LocallyConstant (PrimeSpectrum R) ℕ
```

The stalk-rank function of a finite projective module, bundled as a locally
constant function.

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L35-L40) (native database range lines 35–40).

### Module.rankLocallyConstant_apply

```lean
theorem Module.rankLocallyConstant_apply (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] (p : PrimeSpectrum R) : (rankLocallyConstant R M) p = rankAtStalk M p
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L42-L45) (native database range lines 42–45).

### Module.rankFiberIndex

```lean
abbrev Module.rankFiberIndex (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] : Type u
```

The finite type of nonempty fibers of the stalk-rank function.

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L47-L48) (native database range lines 47–48).

### Module.rankFiberIndexFintype

```lean
noncomputable instance Module.rankFiberIndexFintype (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] : Fintype (rankFiberIndex R M)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L50-L51) (native database range lines 50–51).

### Module.rankFiberClopen

```lean
def Module.rankFiberClopen (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] (i : rankFiberIndex R M) : TopologicalSpace.Clopens (PrimeSpectrum R)
```

The clopen subset of the prime spectrum underlying a rank fiber.

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L53-L58) (native database range lines 53–58).

### Module.rankFiberRank

```lean
noncomputable def Module.rankFiberRank (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] (i : rankFiberIndex R M) : ℕ
```

The common stalk rank on a rank fiber.

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L60-L62) (native database range lines 60–62).

### Module.rankFiberIdempotent

```lean
noncomputable def Module.rankFiberIdempotent (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] (i : rankFiberIndex R M) : R
```

The idempotent corresponding to a rank fiber.

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L64-L67) (native database range lines 64–67).

### Module.rankFiberIdempotent_isIdempotent

```lean
theorem Module.rankFiberIdempotent_isIdempotent (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] (i : rankFiberIndex R M) : IsIdempotentElem (rankFiberIdempotent R M i)
```

A rank-fiber idempotent is idempotent.

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L69-L73) (native database range lines 69–73).

### Module.rankFiberIdempotent_notMem_iff

```lean
theorem Module.rankFiberIdempotent_notMem_iff (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] (i : rankFiberIndex R M) (p : PrimeSpectrum R) : rankFiberIdempotent R M i ∉ p.asIdeal ↔ p ∈ ↑i
```

A rank-fiber idempotent avoids exactly the primes in its fiber.

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L75-L82) (native database range lines 75–82).

### Module.rankAtStalk_eq_rankFiberRank_of_mem

```lean
theorem Module.rankAtStalk_eq_rankFiberRank_of_mem (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] (i : rankFiberIndex R M) (p : PrimeSpectrum R) (hp : p ∈ ↑i) : rankAtStalk M p = rankFiberRank R M i
```

Membership in a rank fiber computes the stalk rank as that fiber's
displayed rank.

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L84-L89) (native database range lines 84–89).

### Module.rankFiberIdempotents_complete

```lean
theorem Module.rankFiberIdempotents_complete (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] : CompleteOrthogonalIdempotents (rankFiberIdempotent R M)
```

The idempotents attached to the nonempty rank fibers form a complete
orthogonal family.

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L114-L143) (native database range lines 114–143).

### Module.rankFiberRing

```lean
abbrev Module.rankFiberRing (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] (i : rankFiberIndex R M) : Type u
```

The component ring supported on a rank fiber.

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L145-L147) (native database range lines 145–147).

### Module.rankFiberModule

```lean
abbrev Module.rankFiberModule (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] (i : rankFiberIndex R M) : Type (max u v)
```

Base change of the module to a rank-fiber component ring.

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L149-L151) (native database range lines 149–151).

### Module.rankFiberModuleFinite

```lean
instance Module.rankFiberModuleFinite (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] (i : rankFiberIndex R M) : Module.Finite (rankFiberRing R M i) (rankFiberModule R M i)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L153-L155) (native database range lines 153–155).

### Module.rankFiberModuleProjective

```lean
instance Module.rankFiberModuleProjective (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] (i : rankFiberIndex R M) : Projective (rankFiberRing R M i) (rankFiberModule R M i)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L157-L159) (native database range lines 157–159).

### Module.rankFiberRingEquiv

```lean
noncomputable def Module.rankFiberRingEquiv (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] : R ≃ₐ[R] (i : rankFiberIndex R M) → rankFiberRing R M i
```

The base ring is the product of its rank-fiber component rings.

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L161-L166) (native database range lines 161–166).

### Module.rankAtStalk_rankFiberModule

```lean
theorem Module.rankAtStalk_rankFiberModule (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] (i : rankFiberIndex R M) (p : PrimeSpectrum (rankFiberRing R M i)) : rankAtStalk (rankFiberModule R M i) p = rankFiberRank R M i
```

On a rank-fiber component, the base-changed module has the fiber's
constant stalk rank.

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L168-L186) (native database range lines 168–186).

### Module.rankFiberLinearEquiv

```lean
noncomputable def Module.rankFiberLinearEquiv (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Projective R M] : M ≃ₗ[R] (i : rankFiberIndex R M) → rankFiberModule R M i
```

Reconstruct a finite projective module from its rank-fiber base changes,
viewed by restriction of scalars to the original ring.

[Source](../ProjectiveModules/Module/RankFiberDecomposition.lean#L188-L196) (native database range lines 188–196).

## ProjectiveModules.Module.RightEndomorphismMatrix

Scope: mathematical library leaf.

### Module.rightEndomorphismMatrixEquiv

```lean
noncomputable def Module.rightEndomorphismMatrixEquiv (R : Type uR) [Ring R] (ι : Type uι) [Fintype ι] [DecidableEq ι] : End Rᵐᵒᵖ (ι → R) ≃+* Matrix ι ι R
```

The ring equivalence from endomorphisms of the finite free right
`R`-module to matrices over `R`.

The first equivalence makes a matrix of endomorphisms of one copy of `R`; the
second evaluates each such right-linear endomorphism at `1`.

[Source](../ProjectiveModules/Module/RightEndomorphismMatrix.lean#L41-L49) (native database range lines 41–49).

### Module.rightEndomorphismMatrixEquiv_apply

```lean
theorem Module.rightEndomorphismMatrixEquiv_apply (R : Type uR) [Ring R] (ι : Type uι) [Fintype ι] [DecidableEq ι] (f : End Rᵐᵒᵖ (ι → R)) (i j : ι) : (rightEndomorphismMatrixEquiv R ι) f i j = f (Pi.single j 1) i
```

The `j`th column of the right-endomorphism matrix is the image of the
`j`th standard basis vector.

[Source](../ProjectiveModules/Module/RightEndomorphismMatrix.lean#L51-L57) (native database range lines 51–57).

### Module.rightEndomorphismMatrixEquiv_mulVec

```lean
theorem Module.rightEndomorphismMatrixEquiv_mulVec (R : Type uR) [Ring R] (ι : Type uι) [Fintype ι] [DecidableEq ι] (f : End Rᵐᵒᵖ (ι → R)) (x : ι → R) : ((rightEndomorphismMatrixEquiv R ι) f).mulVec x = f x
```

The right-endomorphism matrix acts on column vectors exactly as the
endomorphism does.

[Source](../ProjectiveModules/Module/RightEndomorphismMatrix.lean#L59-L75) (native database range lines 59–75).

### Module.rightEndomorphismMatrixEquiv_comp

```lean
theorem Module.rightEndomorphismMatrixEquiv_comp (R : Type uR) [Ring R] (ι : Type uι) [Fintype ι] [DecidableEq ι] (f g : End Rᵐᵒᵖ (ι → R)) : (rightEndomorphismMatrixEquiv R ι) (f ∘ₗ g) = (rightEndomorphismMatrixEquiv R ι) f * (rightEndomorphismMatrixEquiv R ι) g
```

Composition of right-linear endomorphisms is represented by matrix
multiplication in the same order.

[Source](../ProjectiveModules/Module/RightEndomorphismMatrix.lean#L77-L85) (native database range lines 77–85).

### Module.isUnit_rightEndomorphismMatrixEquiv_iff

```lean
theorem Module.isUnit_rightEndomorphismMatrixEquiv_iff (R : Type uR) [Ring R] (ι : Type uι) [Fintype ι] [DecidableEq ι] (f : End Rᵐᵒᵖ (ι → R)) : IsUnit ((rightEndomorphismMatrixEquiv R ι) f) ↔ Function.Bijective ⇑f
```

A finite free right-module endomorphism is bijective exactly when its
coefficient matrix is a unit.

[Source](../ProjectiveModules/Module/RightEndomorphismMatrix.lean#L87-L97) (native database range lines 87–97).

### Module.rightEndomorphism_bijective_of_mapMatrix_quotient_isUnit

```lean
theorem Module.rightEndomorphism_bijective_of_mapMatrix_quotient_isUnit (R : Type uR) [Ring R] (ι : Type uι) [Fintype ι] [DecidableEq ι] (I : TwoSidedIdeal R) (hI : I.IsQuasiregular) (f : End Rᵐᵒᵖ (ι → R)) (hf : IsUnit ((Ideal.Quotient.mk (TwoSidedIdeal.asIdeal I)).mapMatrix ((rightEndomorphismMatrixEquiv R ι) f))) : Function.Bijective ⇑f
```

If the coefficient matrix of a specified finite free right-module
endomorphism is invertible modulo a quasi-regular two-sided ideal, then the
endomorphism is bijective.

[Source](../ProjectiveModules/Module/RightEndomorphismMatrix.lean#L99-L109) (native database range lines 99–109).

### Module.rightEndomorphismScalarExtension

```lean
noncomputable def Module.rightEndomorphismScalarExtension (R : Type uR) [Ring R] (ι : Type uι) [Fintype ι] [DecidableEq ι] {S : Type u_1} [Ring S] (f : R →+* S) (g : End Rᵐᵒᵖ (ι → R)) : End Sᵐᵒᵖ (ι → S)
```

Scalar extension of an endomorphism of a finite free right module,
transported across the canonical coordinate equivalences.

[Source](../ProjectiveModules/Module/RightEndomorphismMatrix.lean#L111-L119) (native database range lines 111–119).

### Module.rightEndomorphismScalarExtension_single

```lean
theorem Module.rightEndomorphismScalarExtension_single (R : Type uR) [Ring R] (ι : Type uι) [Fintype ι] [DecidableEq ι] {S : Type u_1} [Ring S] (f : R →+* S) (g : End Rᵐᵒᵖ (ι → R)) (j : ι) : (rightEndomorphismScalarExtension R ι f g) (Pi.single j 1) = fun (i : ι) => f (g (Pi.single j 1) i)
```

Scalar extension of a finite free right-module endomorphism acts on a
standard basis vector by applying the coefficient homomorphism coordinatewise.

[Source](../ProjectiveModules/Module/RightEndomorphismMatrix.lean#L121-L133) (native database range lines 121–133).

### Module.rightEndomorphismMatrixEquiv_scalarExtension

```lean
theorem Module.rightEndomorphismMatrixEquiv_scalarExtension (R : Type uR) [Ring R] (ι : Type uι) [Fintype ι] [DecidableEq ι] {S : Type u_1} [Ring S] (f : R →+* S) (g : End Rᵐᵒᵖ (ι → R)) : f.mapMatrix ((rightEndomorphismMatrixEquiv R ι) g) = (rightEndomorphismMatrixEquiv S ι) (rightEndomorphismScalarExtension R ι f g)
```

The matrix of a scalar-extended finite free right-module endomorphism is
obtained by applying the coefficient homomorphism entrywise.

[Source](../ProjectiveModules/Module/RightEndomorphismMatrix.lean#L135-L144) (native database range lines 135–144).

### Module.rightEndomorphism_bijective_of_quotientScalarExtension_bijective

```lean
theorem Module.rightEndomorphism_bijective_of_quotientScalarExtension_bijective (R : Type uR) [Ring R] (ι : Type uι) [Fintype ι] [DecidableEq ι] (I : TwoSidedIdeal R) (hI : I.IsQuasiregular) (g : End Rᵐᵒᵖ (ι → R)) (hg : Function.Bijective ⇑(rightEndomorphismScalarExtension R ι (Ideal.Quotient.mk (TwoSidedIdeal.asIdeal I)) g)) : Function.Bijective ⇑g
```

Bijectivity of a finite free right-module endomorphism is reflected from
its scalar extension to a quasi-regular quotient.

[Source](../ProjectiveModules/Module/RightEndomorphismMatrix.lean#L146-L157) (native database range lines 146–157).

### Module.rightEndomorphismLinearEquivOfMapMatrixQuotientIsUnit

```lean
noncomputable def Module.rightEndomorphismLinearEquivOfMapMatrixQuotientIsUnit (R : Type uR) [Ring R] (ι : Type uι) [Fintype ι] [DecidableEq ι] (I : TwoSidedIdeal R) (hI : I.IsQuasiregular) (f : End Rᵐᵒᵖ (ι → R)) (hf : IsUnit ((Ideal.Quotient.mk (TwoSidedIdeal.asIdeal I)).mapMatrix ((rightEndomorphismMatrixEquiv R ι) f))) : (ι → R) ≃ₗ[Rᵐᵒᵖ] ι → R
```

The linear self-equivalence induced by reflection of a specified finite
free right-module endomorphism through a quasi-regular quotient.

[Source](../ProjectiveModules/Module/RightEndomorphismMatrix.lean#L159-L168) (native database range lines 159–168).

### Module.rightEndomorphismLinearEquivOfMapMatrixQuotientIsUnit_apply

```lean
theorem Module.rightEndomorphismLinearEquivOfMapMatrixQuotientIsUnit_apply (R : Type uR) [Ring R] (ι : Type uι) [Fintype ι] [DecidableEq ι] (I : TwoSidedIdeal R) (hI : I.IsQuasiregular) (f : End Rᵐᵒᵖ (ι → R)) (hf : IsUnit ((Ideal.Quotient.mk (TwoSidedIdeal.asIdeal I)).mapMatrix ((rightEndomorphismMatrixEquiv R ι) f))) (x : ι → R) : (rightEndomorphismLinearEquivOfMapMatrixQuotientIsUnit R ι I hI f hf) x = f x
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightEndomorphismMatrix.lean#L170-L178) (native database range lines 170–178).

## ProjectiveModules.Module.RightExtension

Scope: mathematical library leaf.

### ModuleCat.RightExtension.smulCommClass

```lean
theorem ModuleCat.RightExtension.smulCommClass {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) : have x := f.toModule; SMulCommClass R Sᵐᵒᵖ S
```

The left `R`-action and right `S`-action on `S` induced by a ring
homomorphism commute.

[Source](../ProjectiveModules/Module/RightExtension.lean#L33-L42) (native database range lines 33–42).

### ModuleCat.RightExtension.Obj

```lean
abbrev ModuleCat.RightExtension.Obj {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M] : Type (max uM uS)
```

Extension of a right module along a homomorphism of arbitrary rings.

[Source](../ProjectiveModules/Module/RightExtension.lean#L44-L47) (native database range lines 44–47).

### ModuleCat.RightExtension.instAddCommGroupObj

```lean
instance ModuleCat.RightExtension.instAddCommGroupObj {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] : AddCommGroup (Obj f M)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtension.lean#L55-L57) (native database range lines 55–57).

### ModuleCat.RightExtension.instModuleMulOppositeObj

```lean
instance ModuleCat.RightExtension.instModuleMulOppositeObj {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] : Module Sᵐᵒᵖ (Obj f M)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtension.lean#L59-L62) (native database range lines 59–62).

### ModuleCat.RightExtension.tmul

```lean
def ModuleCat.RightExtension.tmul {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (m : M) (s : S) : Obj f M
```

The canonical pure tensor in a right-module extension of scalars.

[Source](../ProjectiveModules/Module/RightExtension.lean#L64-L67) (native database range lines 64–67).

### ModuleCat.RightExtension.tmul_smul

```lean
theorem ModuleCat.RightExtension.tmul_smul {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (m : M) (s : S) (t : Sᵐᵒᵖ) : t • tmul f m s = tmul f m (t • s)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtension.lean#L69-L74) (native database range lines 69–74).

### ModuleCat.RightExtension.smul_tmul

```lean
theorem ModuleCat.RightExtension.smul_tmul {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (r : R) (m : M) (s : S) : tmul f (MulOpposite.op r • m) s = tmul f m (f r * s)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtension.lean#L76-L80) (native database range lines 76–80).

### ModuleCat.RightExtension.mapAddHom

```lean
def ModuleCat.RightExtension.mapAddHom {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (g : M →ₗ[Rᵐᵒᵖ] N) : Obj f M →+ Obj f N
```

The additive homomorphism underlying scalar extension of a morphism. This
is an implementation detail of `ModuleCat.RightExtension.map`.

[Source](../ProjectiveModules/Module/RightExtension.lean#L82-L95) (native database range lines 82–95).

### ModuleCat.RightExtension.map

```lean
def ModuleCat.RightExtension.map {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (g : M →ₗ[Rᵐᵒᵖ] N) : Obj f M →ₗ[Sᵐᵒᵖ] Obj f N
```

Extension of scalars on a morphism of right modules.

[Source](../ProjectiveModules/Module/RightExtension.lean#L97-L109) (native database range lines 97–109).

### ModuleCat.RightExtension.map_tmul

```lean
theorem ModuleCat.RightExtension.map_tmul {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (g : M →ₗ[Rᵐᵒᵖ] N) (m : M) (s : S) : (map f g) (tmul f m s) = tmul f (g m) s
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtension.lean#L111-L115) (native database range lines 111–115).

### ModuleCat.RightExtension.linearMap_ext

```lean
theorem ModuleCat.RightExtension.linearMap_ext {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] {X : Type u_1} [AddCommGroup X] [Module Sᵐᵒᵖ X] {g h : Obj f M →ₗ[Sᵐᵒᵖ] X} (H : ∀ (m : M) (s : S), g (tmul f m s) = h (tmul f m s)) : g = h
```

Two right-linear maps from an extension of scalars are equal if they agree
on pure tensors.

[Source](../ProjectiveModules/Module/RightExtension.lean#L117-L127) (native database range lines 117–127).

### ModuleCat.RightExtension.map_id

```lean
theorem ModuleCat.RightExtension.map_id {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] : map f LinearMap.id = LinearMap.id
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtension.lean#L129-L133) (native database range lines 129–133).

### ModuleCat.RightExtension.map_comp

```lean
theorem ModuleCat.RightExtension.map_comp {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] {P : Type u_1} [AddCommGroup P] [Module Rᵐᵒᵖ P] (g : M →ₗ[Rᵐᵒᵖ] N) (h : N →ₗ[Rᵐᵒᵖ] P) : map f (h ∘ₗ g) = map f h ∘ₗ map f g
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtension.lean#L135-L141) (native database range lines 135–141).

### ModuleCat.RightExtension.map_add

```lean
theorem ModuleCat.RightExtension.map_add {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (g h : M →ₗ[Rᵐᵒᵖ] N) : map f (g + h) = map f g + map f h
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtension.lean#L143-L149) (native database range lines 143–149).

### ModuleCat.RightExtension.functor

```lean
abbrev ModuleCat.RightExtension.functor {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) : CategoryTheory.Functor (ModuleCat Rᵐᵒᵖ) (ModuleCat Sᵐᵒᵖ)
```

Extension of scalars along a homomorphism of arbitrary rings, as a functor
between categories of right modules.

[Source](../ProjectiveModules/Module/RightExtension.lean#L151-L162) (native database range lines 151–162).

### ModuleCat.RightExtension.functorAdditive

```lean
instance ModuleCat.RightExtension.functorAdditive {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) : (functor f).Additive
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtension.lean#L164-L167) (native database range lines 164–167).

### ModuleCat.RightExtension.toSemilinear

```lean
def ModuleCat.RightExtension.toSemilinear {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] {X : Type uX} [AddCommGroup X] [Module Sᵐᵒᵖ X] (g : Obj f M →ₗ[Sᵐᵒᵖ] X) : M →ₛₗ[RingHom.op f] X
```

Restrict a right-linear map out of an extension of scalars to tensors with
second factor `1`.

[Source](../ProjectiveModules/Module/RightExtension.lean#L175-L191) (native database range lines 175–191).

### ModuleCat.RightExtension.toSemilinear_apply

```lean
theorem ModuleCat.RightExtension.toSemilinear_apply {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] {X : Type uX} [AddCommGroup X] [Module Sᵐᵒᵖ X] (g : Obj f M →ₗ[Sᵐᵒᵖ] X) (m : M) : (toSemilinear f g) m = g (tmul f m 1)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtension.lean#L193-L196) (native database range lines 193–196).

### ModuleCat.RightExtension.tmulOne

```lean
def ModuleCat.RightExtension.tmulOne {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] : M →ₛₗ[RingHom.op f] Obj f M
```

The canonical semilinear map from a right module to its extension of
scalars, sending `m` to `m ⊗ 1`.

[Source](../ProjectiveModules/Module/RightExtension.lean#L198-L201) (native database range lines 198–201).

### ModuleCat.RightExtension.tmulOne_apply

```lean
theorem ModuleCat.RightExtension.tmulOne_apply {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (m : M) : (tmulOne f) m = tmul f m 1
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtension.lean#L203-L205) (native database range lines 203–205).

### ModuleCat.RightExtension.tmulOne_surjective

```lean
theorem ModuleCat.RightExtension.tmulOne_surjective {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (hf : Function.Surjective ⇑f) : Function.Surjective ⇑(tmulOne f)
```

The canonical map to a right-module extension of scalars is surjective
when the ring homomorphism is surjective.

[Source](../ProjectiveModules/Module/RightExtension.lean#L207-L225) (native database range lines 207–225).

### ModuleCat.RightExtension.fromSemilinearAddHom

```lean
def ModuleCat.RightExtension.fromSemilinearAddHom {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] {X : Type uX} [AddCommGroup X] [Module Sᵐᵒᵖ X] (h : M →ₛₗ[RingHom.op f] X) : Obj f M →+ X
```

The additive homomorphism induced by a semilinear map from the original
right module. This is an implementation detail of `fromSemilinear`.

[Source](../ProjectiveModules/Module/RightExtension.lean#L227-L245) (native database range lines 227–245).

### ModuleCat.RightExtension.fromSemilinear

```lean
def ModuleCat.RightExtension.fromSemilinear {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] {X : Type uX} [AddCommGroup X] [Module Sᵐᵒᵖ X] (h : M →ₛₗ[RingHom.op f] X) : Obj f M →ₗ[Sᵐᵒᵖ] X
```

Extend a semilinear map from the original right module to a right-linear
map from its extension of scalars.

[Source](../ProjectiveModules/Module/RightExtension.lean#L247-L268) (native database range lines 247–265).

### ModuleCat.RightExtension.fromSemilinear_tmul

```lean
theorem ModuleCat.RightExtension.fromSemilinear_tmul {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] {X : Type uX} [AddCommGroup X] [Module Sᵐᵒᵖ X] (h : M →ₛₗ[RingHom.op f] X) (m : M) (s : S) : (fromSemilinear f h) (tmul f m s) = MulOpposite.op s • h m
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtension.lean#L270-L275) (native database range lines 267–272).

### ModuleCat.RightExtension.linearMapEquiv

```lean
def ModuleCat.RightExtension.linearMapEquiv {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] {X : Type uX} [AddCommGroup X] [Module Sᵐᵒᵖ X] : (Obj f M →ₗ[Sᵐᵒᵖ] X) ≃ (M →ₛₗ[RingHom.op f] X)
```

The extension/restriction correspondence for linear and semilinear maps
over arbitrary, possibly noncommutative rings.

[Source](../ProjectiveModules/Module/RightExtension.lean#L277-L295) (native database range lines 274–292).

### ModuleCat.RightExtension.linearMapAddEquiv

```lean
def ModuleCat.RightExtension.linearMapAddEquiv {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] {X : Type uX} [AddCommGroup X] [Module Sᵐᵒᵖ X] : (Obj f M →ₗ[Sᵐᵒᵖ] X) ≃+ (M →ₛₗ[RingHom.op f] X)
```

The additive extension/restriction correspondence for right modules over
arbitrary, possibly noncommutative rings.

[Source](../ProjectiveModules/Module/RightExtension.lean#L297-L304) (native database range lines 294–301).

### ModuleCat.RightExtension.HomEquiv.toRestriction

```lean
noncomputable def ModuleCat.RightExtension.HomEquiv.toRestriction {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (M' : ModuleCat Rᵐᵒᵖ) (X : ModuleCat Sᵐᵒᵖ) (g : (functor f).obj M' ⟶ X) : M' ⟶ (restrictScalars (RingHom.op f)).obj X
```

Send a map out of an extension of scalars to its value on tensors with
second factor `1`.

[Source](../ProjectiveModules/Module/RightExtension.lean#L314-L335) (native database range lines 311–332).

### ModuleCat.RightExtension.HomEquiv.toRestriction_apply

```lean
theorem ModuleCat.RightExtension.HomEquiv.toRestriction_apply {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (M' : ModuleCat Rᵐᵒᵖ) (X : ModuleCat Sᵐᵒᵖ) (g : (functor f).obj M' ⟶ X) (m : ↑M') : (CategoryTheory.ConcreteCategory.hom (toRestriction f M' X g)) m = (CategoryTheory.ConcreteCategory.hom g) (tmul f m 1)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtension.lean#L337-L340) (native database range lines 334–337).

### ModuleCat.RightExtension.HomEquiv.fromRestrictionAddHom

```lean
noncomputable def ModuleCat.RightExtension.HomEquiv.fromRestrictionAddHom {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (M' : ModuleCat Rᵐᵒᵖ) (X : ModuleCat Sᵐᵒᵖ) (h : M' ⟶ (restrictScalars (RingHom.op f)).obj X) : Obj f ↑M' →+ ↑X
```

The additive homomorphism induced by a map to a restricted right module.
This is an implementation detail of `ModuleCat.RightExtension.HomEquiv.fromRestriction`.

[Source](../ProjectiveModules/Module/RightExtension.lean#L342-L368) (native database range lines 339–365).

### ModuleCat.RightExtension.HomEquiv.fromRestriction

```lean
noncomputable def ModuleCat.RightExtension.HomEquiv.fromRestriction {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (M' : ModuleCat Rᵐᵒᵖ) (X : ModuleCat Sᵐᵒᵖ) (h : M' ⟶ (restrictScalars (RingHom.op f)).obj X) : (functor f).obj M' ⟶ X
```

Send a map to a restricted right module to the corresponding map from the
extension of scalars.

[Source](../ProjectiveModules/Module/RightExtension.lean#L370-L394) (native database range lines 367–391).

### ModuleCat.RightExtension.HomEquiv.fromRestriction_tmul

```lean
theorem ModuleCat.RightExtension.HomEquiv.fromRestriction_tmul {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (M' : ModuleCat Rᵐᵒᵖ) (X : ModuleCat Sᵐᵒᵖ) (h : M' ⟶ (restrictScalars (RingHom.op f)).obj X) (m : ↑M') (s : S) : (CategoryTheory.ConcreteCategory.hom (fromRestriction f M' X h)) (tmul f m s) = MulOpposite.op s • (CategoryTheory.ConcreteCategory.hom h) m
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtension.lean#L396-L403) (native database range lines 393–400).

### ModuleCat.RightExtension.HomEquiv.homEquiv

```lean
noncomputable def ModuleCat.RightExtension.HomEquiv.homEquiv {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (M' : ModuleCat Rᵐᵒᵖ) (X : ModuleCat Sᵐᵒᵖ) : ((functor f).obj M' ⟶ X) ≃ (M' ⟶ (restrictScalars (RingHom.op f)).obj X)
```

The extension/restriction adjunction for right modules over arbitrary
possibly noncommutative rings.

[Source](../ProjectiveModules/Module/RightExtension.lean#L405-L427) (native database range lines 402–424).

### ModuleCat.RightExtension.adjunction

```lean
noncomputable def ModuleCat.RightExtension.adjunction {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) : functor f ⊣ restrictScalars (RingHom.op f)
```

Extension of scalars for right modules over arbitrary rings is left
adjoint to restriction of scalars.

[Source](../ProjectiveModules/Module/RightExtension.lean#L431-L449) (native database range lines 428–446).

### ModuleCat.RightExtension.instProjective

```lean
instance ModuleCat.RightExtension.instProjective {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] : Module.Projective Sᵐᵒᵖ (Obj f M)
```

Extension of scalars along a homomorphism of arbitrary rings preserves
projective right modules.

[Source](../ProjectiveModules/Module/RightExtension.lean#L451-L481) (native database range lines 448–478).

### ModuleCat.RightExtension.instFinite

```lean
instance ModuleCat.RightExtension.instFinite {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ M] : Module.Finite Sᵐᵒᵖ (Obj f M)
```

Extension of scalars along a homomorphism of arbitrary rings preserves
finite generation of right modules.

[Source](../ProjectiveModules/Module/RightExtension.lean#L483-L540) (native database range lines 480–537).

## ProjectiveModules.Module.RightExtensionFiniteResidue

Scope: mathematical library leaf.

### ModuleCat.RightExtension.map_zero

```lean
theorem ModuleCat.RightExtension.map_zero {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] : map f 0 = 0
```

Extension of scalars sends the zero right-linear map to zero.

[Source](../ProjectiveModules/Module/RightExtensionFiniteResidue.lean#L37-L45) (native database range lines 37–45).

### ModuleCat.RightExtension.mapLinearEquiv

```lean
def ModuleCat.RightExtension.mapLinearEquiv {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (e : M ≃ₗ[Rᵐᵒᵖ] N) : Obj f M ≃ₗ[Sᵐᵒᵖ] Obj f N
```

Extension of scalars carries a right-linear equivalence to a
right-linear equivalence.

[Source](../ProjectiveModules/Module/RightExtensionFiniteResidue.lean#L47-L59) (native database range lines 47–59).

### ModuleCat.RightExtension.mapLinearEquiv_tmul

```lean
theorem ModuleCat.RightExtension.mapLinearEquiv_tmul {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (e : M ≃ₗ[Rᵐᵒᵖ] N) (m : M) (s : S) : (mapLinearEquiv f e) (tmul f m s) = tmul f (e m) s
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionFiniteResidue.lean#L61-L64) (native database range lines 61–64).

### ModuleCat.RightExtension.prodLinearEquiv

```lean
def ModuleCat.RightExtension.prodLinearEquiv {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] : Obj f (M × N) ≃ₗ[Sᵐᵒᵖ] Obj f M × Obj f N
```

Extension of scalars commutes with a binary product of right modules.

[Source](../ProjectiveModules/Module/RightExtensionFiniteResidue.lean#L66-L109) (native database range lines 66–109).

### ModuleCat.RightExtension.prodLinearEquiv_tmul

```lean
theorem ModuleCat.RightExtension.prodLinearEquiv_tmul {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (m : M) (n : N) (s : S) : (prodLinearEquiv f) (tmul f (m, n) s) = (tmul f m s, tmul f n s)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionFiniteResidue.lean#L111-L115) (native database range lines 111–115).

### ModuleCat.RightExtension.idealQuotientMapLinearEquiv

```lean
def ModuleCat.RightExtension.idealQuotientMapLinearEquiv {R : Type uR} [Ring R] {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (I : Ideal R) [I.IsTwoSided] (e : M ≃ₗ[Rᵐᵒᵖ] N) : IdealQuotient I ≃ₗ[(R ⧸ I)ᵐᵒᵖ] IdealQuotient I
```

A right-linear equivalence descends to the quotients by the action of a
two-sided ideal.

[Source](../ProjectiveModules/Module/RightExtensionFiniteResidue.lean#L124-L132) (native database range lines 124–132).

### ModuleCat.RightExtension.idealQuotientMapLinearEquiv_mk

```lean
theorem ModuleCat.RightExtension.idealQuotientMapLinearEquiv_mk {R : Type uR} [Ring R] {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (I : Ideal R) [I.IsTwoSided] (e : M ≃ₗ[Rᵐᵒᵖ] N) (m : M) : (idealQuotientMapLinearEquiv I e) (Submodule.Quotient.mk m) = Submodule.Quotient.mk (e m)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionFiniteResidue.lean#L134-L140) (native database range lines 134–140).

### ModuleCat.RightExtension.idealQuotientProdLinearEquiv

```lean
def ModuleCat.RightExtension.idealQuotientProdLinearEquiv {R : Type uR} [Ring R] {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (I : Ideal R) [I.IsTwoSided] : IdealQuotient I ≃ₗ[(R ⧸ I)ᵐᵒᵖ] IdealQuotient I × IdealQuotient I
```

Quotienting a product of right modules by the action of a two-sided ideal
is the product of the corresponding quotient modules.

[Source](../ProjectiveModules/Module/RightExtensionFiniteResidue.lean#L142-L150) (native database range lines 142–150).

### ModuleCat.RightExtension.idealQuotientProdLinearEquiv_mk

```lean
theorem ModuleCat.RightExtension.idealQuotientProdLinearEquiv_mk {R : Type uR} [Ring R] {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (I : Ideal R) [I.IsTwoSided] (m : M) (n : N) : (idealQuotientProdLinearEquiv I) (Submodule.Quotient.mk (m, n)) = (Submodule.Quotient.mk m, Submodule.Quotient.mk n)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionFiniteResidue.lean#L152-L160) (native database range lines 152–160).

### ModuleCat.RightExtension.idealQuotientFinite

```lean
instance ModuleCat.RightExtension.idealQuotientFinite {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] [Module.Finite Rᵐᵒᵖ M] : Module.Finite (R ⧸ I)ᵐᵒᵖ (IdealQuotient I)
```

A finitely generated right module has a finitely generated quotient by
the action of a two-sided ideal.

[Source](../ProjectiveModules/Module/RightExtensionFiniteResidue.lean#L162-L167) (native database range lines 162–167).

### ModuleCat.RightExtension.idealQuotientFree

```lean
theorem ModuleCat.RightExtension.idealQuotientFree {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] [Module.Free (R ⧸ I)ᵐᵒᵖ (Obj (Ideal.Quotient.mk I) M)] : Module.Free (R ⧸ I)ᵐᵒᵖ (IdealQuotient I)
```

Freeness of the extension of scalars transfers to the quotient by the
action of a two-sided ideal.

[Source](../ProjectiveModules/Module/RightExtensionFiniteResidue.lean#L169-L174) (native database range lines 169–174).

### ModuleCat.RightExtension.idealQuotientFree_of_isMaximal

```lean
theorem ModuleCat.RightExtension.idealQuotientFree_of_isMaximal {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] [I.IsMaximal] : Module.Free (R ⧸ I)ᵐᵒᵖ (IdealQuotient I)
```

The quotient of a right module by the action of a two-sided maximal ideal
is free over the resulting division ring.

[Source](../ProjectiveModules/Module/RightExtensionFiniteResidue.lean#L176-L184) (native database range lines 176–184).

### ModuleCat.RightExtension.finrank_idealQuotient_prod

```lean
theorem ModuleCat.RightExtension.finrank_idealQuotient_prod {R : Type uR} [Ring R] {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (I : Ideal R) [I.IsTwoSided] [StrongRankCondition (R ⧸ I)ᵐᵒᵖ] [Module.Free (R ⧸ I)ᵐᵒᵖ (IdealQuotient I)] [Module.Free (R ⧸ I)ᵐᵒᵖ (IdealQuotient I)] [Module.Finite Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ N] : Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient I) = Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient I) + Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient I)
```

The dimension of the quotient of a product is the sum of the dimensions
of the two quotient modules whenever dimension is available over the quotient
scalar ring.

[Source](../ProjectiveModules/Module/RightExtensionFiniteResidue.lean#L186-L198) (native database range lines 186–198).

### ModuleCat.RightExtension.finrank_idealQuotient_prod_of_isMaximal

```lean
theorem ModuleCat.RightExtension.finrank_idealQuotient_prod_of_isMaximal {R : Type uR} [Ring R] {M : Type uM} {N : Type uN} [AddCommGroup M] [Module Rᵐᵒᵖ M] [AddCommGroup N] [Module Rᵐᵒᵖ N] (I : Ideal R) [I.IsTwoSided] [I.IsMaximal] [Module.Finite Rᵐᵒᵖ M] [Module.Finite Rᵐᵒᵖ N] : Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient I) = Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient I) + Module.finrank (R ⧸ I)ᵐᵒᵖ (IdealQuotient I)
```

Modulo a two-sided maximal ideal, the dimension of the quotient of a product
is the sum of the dimensions of the two quotient modules.

[Source](../ProjectiveModules/Module/RightExtensionFiniteResidue.lean#L200-L213) (native database range lines 200–213).

## ProjectiveModules.Module.RightExtensionFree

Scope: mathematical library leaf.

### Module.rightFreeCoordEquiv

```lean
noncomputable def Module.rightFreeCoordEquiv (R : Type uR) [Ring R] (ι : Type uι) : (ι → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] ι → R
```

The standard free module over `Rᵐᵒᵖ`, written with coordinates in `R`.

[Source](../ProjectiveModules/Module/RightExtensionFree.lean#L30-L34) (native database range lines 30–34).

### Module.rightFreeCoordEquiv_apply

```lean
theorem Module.rightFreeCoordEquiv_apply (R : Type uR) [Ring R] (ι : Type uι) (x : ι → Rᵐᵒᵖ) (i : ι) : (rightFreeCoordEquiv R ι) x i = MulOpposite.unop (x i)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionFree.lean#L36-L39) (native database range lines 36–39).

### Module.rightFreeCoordEquiv_symm_apply

```lean
theorem Module.rightFreeCoordEquiv_symm_apply (R : Type uR) [Ring R] (ι : Type uι) (x : ι → R) (i : ι) : (rightFreeCoordEquiv R ι).symm x i = MulOpposite.op (x i)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionFree.lean#L41-L44) (native database range lines 41–44).

### ModuleCat.RightExtension.rightFreeToSemilinear

```lean
def ModuleCat.RightExtension.rightFreeToSemilinear {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (ι : Type uι) : (ι → R) →ₛₗ[RingHom.op f] ι → S
```

Coordinatewise scalar extension on a finite canonical right-free module.

[Source](../ProjectiveModules/Module/RightExtensionFree.lean#L54-L65) (native database range lines 54–65).

### ModuleCat.RightExtension.rightFreeTo

```lean
def ModuleCat.RightExtension.rightFreeTo {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (ι : Type uι) : Obj f (ι → R) →ₗ[Sᵐᵒᵖ] ι → S
```

The forward map from scalar extension of a finite canonical right-free
module to the corresponding right-free module over the target ring.

[Source](../ProjectiveModules/Module/RightExtensionFree.lean#L67-L71) (native database range lines 67–71).

### ModuleCat.RightExtension.rightFreeTo_tmul

```lean
theorem ModuleCat.RightExtension.rightFreeTo_tmul {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (ι : Type uι) (x : ι → R) (s : S) : (rightFreeTo f ι) (tmul f x s) = fun (i : ι) => f (x i) * s
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionFree.lean#L74-L79) (native database range lines 74–79).

### ModuleCat.RightExtension.rightFreeFrom

```lean
noncomputable def ModuleCat.RightExtension.rightFreeFrom {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (ι : Type uι) [Fintype ι] [DecidableEq ι] : (ι → S) →ₗ[Sᵐᵒᵖ] Obj f (ι → R)
```

The inverse to `rightFreeTo`, given by the target coefficients of the
scalar-extended standard basis.

[Source](../ProjectiveModules/Module/RightExtensionFree.lean#L81-L87) (native database range lines 81–87).

### ModuleCat.RightExtension.rightFreeFrom_apply

```lean
theorem ModuleCat.RightExtension.rightFreeFrom_apply {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (ι : Type uι) [Fintype ι] [DecidableEq ι] (x : ι → S) : (rightFreeFrom f ι) x = ∑ i : ι, tmul f (Pi.single i 1) (x i)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionFree.lean#L89-L92) (native database range lines 89–92).

### ModuleCat.RightExtension.rightFreeTo_rightFreeFrom

```lean
theorem ModuleCat.RightExtension.rightFreeTo_rightFreeFrom {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (ι : Type uι) [Fintype ι] [DecidableEq ι] (x : ι → S) : (rightFreeTo f ι) ((rightFreeFrom f ι) x) = x
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionFree.lean#L94-L99) (native database range lines 94–99).

### ModuleCat.RightExtension.rightFreeFrom_rightFreeTo

```lean
theorem ModuleCat.RightExtension.rightFreeFrom_rightFreeTo {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (ι : Type uι) [Fintype ι] [DecidableEq ι] (z : Obj f (ι → R)) : (rightFreeFrom f ι) ((rightFreeTo f ι) z) = z
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionFree.lean#L101-L127) (native database range lines 101–127).

### ModuleCat.RightExtension.rightFreeLinearEquiv

```lean
noncomputable def ModuleCat.RightExtension.rightFreeLinearEquiv {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (ι : Type uι) [Fintype ι] [DecidableEq ι] : Obj f (ι → R) ≃ₗ[Sᵐᵒᵖ] ι → S
```

Scalar extension of a finite canonical right-free module is the canonical
right-free module over the target ring.

[Source](../ProjectiveModules/Module/RightExtensionFree.lean#L129-L141) (native database range lines 129–141).

### ModuleCat.RightExtension.rightFreeLinearEquiv_tmul

```lean
theorem ModuleCat.RightExtension.rightFreeLinearEquiv_tmul {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) (ι : Type uι) [Fintype ι] [DecidableEq ι] (x : ι → R) (s : S) : (rightFreeLinearEquiv f ι) (tmul f x s) = fun (i : ι) => f (x i) * s
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionFree.lean#L143-L146) (native database range lines 143–146).

### ModuleCat.RightExtension.idealQuotientRightFreeLinearEquiv

```lean
noncomputable def ModuleCat.RightExtension.idealQuotientRightFreeLinearEquiv (ι : Type uι) [Fintype ι] [DecidableEq ι] {R : Type uR} [Ring R] (I : Ideal R) [I.IsTwoSided] : IdealQuotient I ≃ₗ[(R ⧸ I)ᵐᵒᵖ] ι → R ⧸ I
```

The quotient by the right action of a two-sided ideal on a finite
canonical right-free module is coordinatewise ring quotient.

[Source](../ProjectiveModules/Module/RightExtensionFree.lean#L152-L158) (native database range lines 152–158).

### ModuleCat.RightExtension.idealQuotientRightFreeLinearEquiv_mk

```lean
theorem ModuleCat.RightExtension.idealQuotientRightFreeLinearEquiv_mk (ι : Type uι) [Fintype ι] [DecidableEq ι] {R : Type uR} [Ring R] (I : Ideal R) [I.IsTwoSided] (x : ι → R) : (idealQuotientRightFreeLinearEquiv ι I) (Submodule.Quotient.mk x) = fun (i : ι) => (Ideal.Quotient.mk I) (x i)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionFree.lean#L160-L167) (native database range lines 160–167).

## ProjectiveModules.Module.RightExtensionQuotient

Scope: mathematical library leaf.

### ModuleCat.RightExtension.oppositeIdeal

```lean
abbrev ModuleCat.RightExtension.oppositeIdeal {R : Type uR} [Ring R] (I : Ideal R) [I.IsTwoSided] : Ideal Rᵐᵒᵖ
```

A two-sided ideal of `R`, regarded as an ideal of the opposite ring.

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L32-L34) (native database range lines 32–34).

### ModuleCat.RightExtension.quotientOppositeHom

```lean
def ModuleCat.RightExtension.quotientOppositeHom {R : Type uR} [Ring R] (I : Ideal R) [I.IsTwoSided] : (R ⧸ I)ᵐᵒᵖ →+* Rᵐᵒᵖ ⧸ oppositeIdeal I
```

The canonical homomorphism from the opposite of a quotient ring to the
quotient of the opposite ring.

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L36-L56) (native database range lines 36–56).

### ModuleCat.RightExtension.quotientOppositeHom_mk

```lean
theorem ModuleCat.RightExtension.quotientOppositeHom_mk {R : Type uR} [Ring R] (I : Ideal R) [I.IsTwoSided] (r : R) : (quotientOppositeHom I) (MulOpposite.op ((Ideal.Quotient.mk I) r)) = (Ideal.Quotient.mk (oppositeIdeal I)) (MulOpposite.op r)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L58-L62) (native database range lines 58–62).

### ModuleCat.RightExtension.mem_oppositeIdeal_iff

```lean
theorem ModuleCat.RightExtension.mem_oppositeIdeal_iff {R : Type uR} [Ring R] (I : Ideal R) [I.IsTwoSided] (r : R) : MulOpposite.op r ∈ oppositeIdeal I ↔ r ∈ I
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L64-L69) (native database range lines 64–69).

### ModuleCat.RightExtension.idealSubmodule

```lean
abbrev ModuleCat.RightExtension.idealSubmodule {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] : Submodule Rᵐᵒᵖ M
```

The submodule generated by the right action of a two-sided ideal.

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L75-L77) (native database range lines 75–77).

### ModuleCat.RightExtension.IdealQuotient

```lean
abbrev ModuleCat.RightExtension.IdealQuotient {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] : Type uM
```

A right module modulo the right action of a two-sided ideal.

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L79-L81) (native database range lines 79–81).

### ModuleCat.RightExtension.idealQuotientModule

```lean
instance ModuleCat.RightExtension.idealQuotientModule {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] : Module (R ⧸ I)ᵐᵒᵖ (IdealQuotient I)
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L83-L89) (native database range lines 83–89).

### ModuleCat.RightExtension.idealQuotientMk

```lean
def ModuleCat.RightExtension.idealQuotientMk {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] : M →ₛₗ[RingHom.op (Ideal.Quotient.mk I)] IdealQuotient I
```

The canonical semilinear map from a right module to its quotient by the
right action of a two-sided ideal.

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L91-L107) (native database range lines 91–107).

### ModuleCat.RightExtension.idealQuotientMk_apply

```lean
theorem ModuleCat.RightExtension.idealQuotientMk_apply {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] (m : M) : (idealQuotientMk I) m = Submodule.Quotient.mk m
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L109-L113) (native database range lines 109–113).

### ModuleCat.RightExtension.toIdealQuotient

```lean
def ModuleCat.RightExtension.toIdealQuotient {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] : Obj (Ideal.Quotient.mk I) M →ₗ[(R ⧸ I)ᵐᵒᵖ] IdealQuotient I
```

The quotient map induces a map from extension of scalars to the quotient
module.

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L115-L119) (native database range lines 115–119).

### ModuleCat.RightExtension.toIdealQuotient_tmul

```lean
theorem ModuleCat.RightExtension.toIdealQuotient_tmul {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] (m : M) (s : R ⧸ I) : (toIdealQuotient I) (tmul (Ideal.Quotient.mk I) m s) = MulOpposite.op s • Submodule.Quotient.mk m
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L121-L127) (native database range lines 121–127).

### ModuleCat.RightExtension.idealSubmodule_le_tmulOne_ker

```lean
theorem ModuleCat.RightExtension.idealSubmodule_le_tmulOne_ker {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] : idealSubmodule I ≤ (tmulOne (Ideal.Quotient.mk I)).ker
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L129-L143) (native database range lines 129–143).

### ModuleCat.RightExtension.fromIdealQuotientSemilinear

```lean
def ModuleCat.RightExtension.fromIdealQuotientSemilinear {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] : IdealQuotient I →ₛₗ[RingHom.op (Ideal.Quotient.mk I)] Obj (Ideal.Quotient.mk I) M
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L145-L150) (native database range lines 145–150).

### ModuleCat.RightExtension.fromIdealQuotientSemilinear_mk

```lean
theorem ModuleCat.RightExtension.fromIdealQuotientSemilinear_mk {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] (m : M) : (fromIdealQuotientSemilinear I) (Submodule.Quotient.mk m) = tmul (Ideal.Quotient.mk I) m 1
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L152-L158) (native database range lines 152–158).

### ModuleCat.RightExtension.fromIdealQuotient

```lean
def ModuleCat.RightExtension.fromIdealQuotient {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] : IdealQuotient I →ₗ[(R ⧸ I)ᵐᵒᵖ] Obj (Ideal.Quotient.mk I) M
```

The map induced by `m ↦ m ⊗ 1` from the quotient module to extension of
scalars.

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L160-L183) (native database range lines 160–183).

### ModuleCat.RightExtension.fromIdealQuotient_mk

```lean
theorem ModuleCat.RightExtension.fromIdealQuotient_mk {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] (m : M) : (fromIdealQuotient I) (Submodule.Quotient.mk m) = tmul (Ideal.Quotient.mk I) m 1
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L185-L190) (native database range lines 185–190).

### ModuleCat.RightExtension.fromIdealQuotient_comp_toIdealQuotient

```lean
theorem ModuleCat.RightExtension.fromIdealQuotient_comp_toIdealQuotient {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] : fromIdealQuotient I ∘ₗ toIdealQuotient I = LinearMap.id
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L192-L200) (native database range lines 192–200).

### ModuleCat.RightExtension.toIdealQuotient_comp_fromIdealQuotient

```lean
theorem ModuleCat.RightExtension.toIdealQuotient_comp_fromIdealQuotient {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] : toIdealQuotient I ∘ₗ fromIdealQuotient I = LinearMap.id
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L202-L211) (native database range lines 202–211).

### ModuleCat.RightExtension.idealQuotientLinearEquiv

```lean
def ModuleCat.RightExtension.idealQuotientLinearEquiv {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] : Obj (Ideal.Quotient.mk I) M ≃ₗ[(R ⧸ I)ᵐᵒᵖ] IdealQuotient I
```

Extension of scalars along `R → R ⧸ I` is canonically the quotient by
the right action of `I`.

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L213-L220) (native database range lines 213–220).

### ModuleCat.RightExtension.idealQuotientLinearEquiv_tmul

```lean
theorem ModuleCat.RightExtension.idealQuotientLinearEquiv_tmul {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] (m : M) (s : R ⧸ I) : (idealQuotientLinearEquiv I) (tmul (Ideal.Quotient.mk I) m s) = MulOpposite.op s • Submodule.Quotient.mk m
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L222-L229) (native database range lines 222–229).

### ModuleCat.RightExtension.idealQuotientLinearEquiv_symm_mk

```lean
theorem ModuleCat.RightExtension.idealQuotientLinearEquiv_symm_mk {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] (m : M) : (idealQuotientLinearEquiv I).symm (Submodule.Quotient.mk m) = tmul (Ideal.Quotient.mk I) m 1
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L231-L237) (native database range lines 231–237).

### ModuleCat.RightExtension.tmulOne_ker_quotient_mk

```lean
theorem ModuleCat.RightExtension.tmulOne_ker_quotient_mk {R : Type uR} [Ring R] {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M] (I : Ideal R) [I.IsTwoSided] : (tmulOne (Ideal.Quotient.mk I)).ker = idealSubmodule I
```

The kernel of the canonical map to extension along `R → R ⧸ I` is the
submodule generated by the right action of `I`.

[Source](../ProjectiveModules/Module/RightExtensionQuotient.lean#L239-L252) (native database range lines 239–252).

## ProjectiveModules.Module.TransfiniteCoordinateFiltration

Scope: mathematical library leaf.

### LinearMap.CountableInvariantCoordinateFiltration

```lean
structure LinearMap.CountableInvariantCoordinateFiltration {R : Type uR} [Semiring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) : Type uI
```

A well-ordered family of countable coordinate sets, each containing its
index and each supporting a submodule preserved by `p`.  The sets may overlap;
their well-ordered unions form the associated filtration.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L38-L56) (native database range lines 38–56).

### LinearMap.CountableInvariantCoordinateFiltration.mk

```lean
constructor LinearMap.CountableInvariantCoordinateFiltration.mk : {R : Type uR} → [inst : Semiring R] → {ι : Type uI} → {p : (ι →₀ R) →ₗ[R] ι →₀ R} → (r : ι → ι → Prop) → IsWellOrder ι r → (block : ι → Set ι) → (∀ (i : ι), i ∈ block i) → (∀ (i : ι), (block i).Countable) → (∀ (i : ι), Finsupp.supported R R (block i) ≤ Submodule.comap p (Finsupp.supported R R (block i))) → p.CountableInvariantCoordinateFiltration
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L38-L56) (native database range lines 38–56).

### LinearMap.CountableInvariantCoordinateFiltration.r

```lean
abbrev LinearMap.CountableInvariantCoordinateFiltration.r {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (self : p.CountableInvariantCoordinateFiltration) : ι → ι → Prop
```

The well-order used to assemble the filtration.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L44-L44) (native database range lines 44–44).

### LinearMap.CountableInvariantCoordinateFiltration.isWellOrder

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.isWellOrder {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (self : p.CountableInvariantCoordinateFiltration) : IsWellOrder ι self.r
```

The chosen relation is a well-order.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L46-L46) (native database range lines 46–46).

### LinearMap.CountableInvariantCoordinateFiltration.block

```lean
abbrev LinearMap.CountableInvariantCoordinateFiltration.block {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (self : p.CountableInvariantCoordinateFiltration) : ι → Set ι
```

A countable invariant coordinate closure around each index.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L48-L48) (native database range lines 48–48).

### LinearMap.CountableInvariantCoordinateFiltration.mem_block

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.mem_block {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (self : p.CountableInvariantCoordinateFiltration) (i : ι) : i ∈ self.block i
```

Each index belongs to its chosen closure.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L50-L50) (native database range lines 50–50).

### LinearMap.CountableInvariantCoordinateFiltration.block_countable

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.block_countable {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (self : p.CountableInvariantCoordinateFiltration) (i : ι) : (self.block i).Countable
```

Every chosen closure is countable.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L52-L52) (native database range lines 52–52).

### LinearMap.CountableInvariantCoordinateFiltration.block_invariant

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.block_invariant {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (self : p.CountableInvariantCoordinateFiltration) (i : ι) : Finsupp.supported R R (self.block i) ≤ Submodule.comap p (Finsupp.supported R R (self.block i))
```

Every chosen closure supports a submodule preserved by `p`.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L54-L54) (native database range lines 54–54).

### LinearMap.CountableInvariantCoordinateFiltration.before

```lean
def LinearMap.CountableInvariantCoordinateFiltration.before {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (F : p.CountableInvariantCoordinateFiltration) (i : ι) : Set ι
```

The coordinates strictly before `i` in the filtration.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L62-L64) (native database range lines 62–64).

### LinearMap.CountableInvariantCoordinateFiltration.through

```lean
def LinearMap.CountableInvariantCoordinateFiltration.through {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (F : p.CountableInvariantCoordinateFiltration) (i : ι) : Set ι
```

The coordinates through `i` in the filtration.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L66-L68) (native database range lines 66–68).

### LinearMap.CountableInvariantCoordinateFiltration.before_invariant

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.before_invariant {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (F : p.CountableInvariantCoordinateFiltration) (i : ι) : Finsupp.supported R R (F.before i) ≤ Submodule.comap p (Finsupp.supported R R (F.before i))
```

The submodule supported on the coordinates before a stage is preserved by
the endomorphism.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L70-L84) (native database range lines 70–84).

### LinearMap.CountableInvariantCoordinateFiltration.through_invariant

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.through_invariant {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (F : p.CountableInvariantCoordinateFiltration) (i : ι) : Finsupp.supported R R (F.through i) ≤ Submodule.comap p (Finsupp.supported R R (F.through i))
```

The submodule supported on the coordinates through a stage is preserved by
the endomorphism.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L86-L95) (native database range lines 86–95).

### LinearMap.CountableInvariantCoordinateFiltration.mem_through

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.mem_through {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (F : p.CountableInvariantCoordinateFiltration) (i : ι) : i ∈ F.through i
```

Every stage contains its indexing coordinate.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L97-L100) (native database range lines 97–100).

### LinearMap.CountableInvariantCoordinateFiltration.before_subset_through

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.before_subset_through {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (F : p.CountableInvariantCoordinateFiltration) (i : ι) : F.before i ⊆ F.through i
```

The coordinates before a stage are contained in the coordinates through
that stage.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L102-L107) (native database range lines 102–107).

### LinearMap.CountableInvariantCoordinateFiltration.increment_countable

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.increment_countable {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (F : p.CountableInvariantCoordinateFiltration) (i : ι) : (F.through i \ F.before i).Countable
```

The new coordinates at each stage form a countable set.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L109-L116) (native database range lines 109–116).

### LinearMap.CountableInvariantCoordinateFiltration.through_subset_before_of_rel

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.through_subset_before_of_rel {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (F : p.CountableInvariantCoordinateFiltration) {i j : ι} (hij : F.r i j) : F.through i ⊆ F.before j
```

A completed stage lies in the coordinates before every later stage.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L118-L131) (native database range lines 118–131).

### LinearMap.CountableInvariantCoordinateFiltration.before_subset_before_of_rel

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.before_subset_before_of_rel {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (F : p.CountableInvariantCoordinateFiltration) {i j : ι} (hij : F.r i j) : F.before i ⊆ F.before j
```

Earlier open stages are contained in later open stages.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L133-L137) (native database range lines 133–137).

### LinearMap.CountableInvariantCoordinateFiltration.through_subset_through_of_rel

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.through_subset_through_of_rel {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (F : p.CountableInvariantCoordinateFiltration) {i j : ι} (hij : F.r i j) : F.through i ⊆ F.through j
```

Earlier completed stages are contained in later completed stages.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L139-L143) (native database range lines 139–143).

### LinearMap.CountableInvariantCoordinateFiltration.before_eq_iUnion_through

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.before_eq_iUnion_through {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (F : p.CountableInvariantCoordinateFiltration) (i : ι) : F.before i = ⋃ (j : ι), ⋃ (_ : F.r j i), F.through j
```

The coordinates before a stage are exactly the union of all completed
earlier stages.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L145-L162) (native database range lines 145–162).

### LinearMap.CountableInvariantCoordinateFiltration.iUnion_through

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.iUnion_through {R : Type uR} [Semiring R] {ι : Type uI} {p : (ι →₀ R) →ₗ[R] ι →₀ R} (F : p.CountableInvariantCoordinateFiltration) : ⋃ (i : ι), F.through i = Set.univ
```

The completed stages cover all coordinates.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L164-L169) (native database range lines 164–169).

### LinearMap.exists_countable_invariant_coordinate_filtration

```lean
theorem LinearMap.exists_countable_invariant_coordinate_filtration {R : Type uR} [Semiring R] {ι : Type uI} (p : (ι →₀ R) →ₗ[R] ι →₀ R) : Nonempty p.CountableInvariantCoordinateFiltration
```

Every endomorphism of an arbitrary standard free module admits a
well-ordered invariant coordinate filtration with countable increments.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L173-L192) (native database range lines 173–192).

### LinearMap.CountableInvariantCoordinateFiltration.beforeProdIncrementEquiv

```lean
noncomputable def LinearMap.CountableInvariantCoordinateFiltration.beforeProdIncrementEquiv {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (hq : IsIdempotentElem q) (i : κ) : (↥(q.supportedRangeRetraction (F.before i) (F.through i) ⋯).ker × ↥(q.supportedRange (F.before i))) ≃ₗ[S] ↥(q.supportedRange (F.through i))
```

For an idempotent endomorphism, a completed filtration stage is the
product of its open stage and the kernel of the canonical retraction.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L201-L211) (native database range lines 201–211).

### LinearMap.CountableInvariantCoordinateFiltration.increment_projective

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.increment_projective {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (hq : IsIdempotentElem q) (i : κ) : Module.Projective S ↥(q.supportedRangeRetraction (F.before i) (F.through i) ⋯).ker
```

The split increment between the open and completed parts of every
filtration stage is projective.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L213-L222) (native database range lines 213–222).

### LinearMap.CountableInvariantCoordinateFiltration.increment_countablyGenerated

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.increment_countablyGenerated {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (hq : IsIdempotentElem q) (i : κ) : Module.CountablyGenerated S ↥(q.supportedRangeRetraction (F.before i) (F.through i) ⋯).ker
```

Every split increment in the filtration of an idempotent endomorphism is
countably generated.

[Source](../ProjectiveModules/Module/TransfiniteCoordinateFiltration.lean#L224-L233) (native database range lines 224–233).

## ProjectiveModules.Module.TransfiniteRangeBasis

Scope: mathematical library leaf.

### LinearMap.CountableInvariantCoordinateFiltration.increment

```lean
noncomputable abbrev LinearMap.CountableInvariantCoordinateFiltration.increment {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (i : κ) : Submodule S ↥(q.supportedRange (F.through i))
```

The canonical split increment at a filtration stage.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L37-L41) (native database range lines 37–41).

### LinearMap.CountableInvariantCoordinateFiltration.incrementToRange

```lean
def LinearMap.CountableInvariantCoordinateFiltration.incrementToRange {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (i : κ) : ↥(F.increment i) →ₗ[S] ↥q.range
```

A split increment, included in the full range of the idempotent.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L43-L49) (native database range lines 43–49).

### LinearMap.CountableInvariantCoordinateFiltration.incrementToRange_injective

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.incrementToRange_injective {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (i : κ) : Function.Injective ⇑(F.incrementToRange i)
```

Inclusion of a split increment in the full range is injective.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L51-L59) (native database range lines 51–59).

### LinearMap.CountableInvariantCoordinateFiltration.incrementInRange

```lean
noncomputable def LinearMap.CountableInvariantCoordinateFiltration.incrementInRange {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (i : κ) : Submodule S ↥q.range
```

The copy of a split increment inside the full range of the idempotent.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L61-L65) (native database range lines 61–65).

### LinearMap.CountableInvariantCoordinateFiltration.incrementEquivInRange

```lean
noncomputable def LinearMap.CountableInvariantCoordinateFiltration.incrementEquivInRange {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (i : κ) : ↥(F.increment i) ≃ₗ[S] ↥(F.incrementInRange i)
```

A split increment is linearly equivalent to its copy in the full range.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L67-L72) (native database range lines 67–72).

### LinearMap.CountableInvariantCoordinateFiltration.rangeSupported

```lean
noncomputable def LinearMap.CountableInvariantCoordinateFiltration.rangeSupported {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (_F : q.CountableInvariantCoordinateFiltration) (s : Set κ) : Submodule S ↥q.range
```

Elements of the full range supported on a chosen coordinate set.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L74-L78) (native database range lines 74–78).

### LinearMap.CountableInvariantCoordinateFiltration.mem_rangeSupported

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.mem_rangeSupported {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (s : Set κ) (x : ↥q.range) : x ∈ F.rangeSupported s ↔ ↑x ∈ Finsupp.supported S S s
```

*No source docstring is attached to this native display.*

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L80-L85) (native database range lines 80–85).

### LinearMap.CountableInvariantCoordinateFiltration.rangeSupported_mono

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.rangeSupported_mono {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) {s t : Set κ} (hst : s ⊆ t) : F.rangeSupported s ≤ F.rangeSupported t
```

Supported pieces of the full range are monotone in the coordinate set.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L87-L92) (native database range lines 87–92).

### LinearMap.CountableInvariantCoordinateFiltration.incrementInRange_le_rangeSupported_through

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.incrementInRange_le_rangeSupported_through {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (i : κ) : F.incrementInRange i ≤ F.rangeSupported (F.through i)
```

Every increment is supported on its completed filtration stage.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L94-L99) (native database range lines 94–99).

### LinearMap.CountableInvariantCoordinateFiltration.incrementInRange_le_rangeSupported_before_of_rel

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.incrementInRange_le_rangeSupported_before_of_rel {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) {i j : κ} (hji : F.r j i) : F.incrementInRange j ≤ F.rangeSupported (F.before i)
```

An earlier increment is supported before every later stage.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L101-L107) (native database range lines 101–107).

### LinearMap.CountableInvariantCoordinateFiltration.disjoint_incrementInRange_rangeSupported_before

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.disjoint_incrementInRange_rangeSupported_before {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (hq : IsIdempotentElem q) (i : κ) : Disjoint (F.incrementInRange i) (F.rangeSupported (F.before i))
```

A split increment meets the preceding supported range only in zero.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L109-L134) (native database range lines 109–134).

### LinearMap.CountableInvariantCoordinateFiltration.incrementInRange_free

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.incrementInRange_free {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (i : κ) (hfree : Module.Free S ↥(F.increment i)) : Module.Free S ↥(F.incrementInRange i)
```

Freeness of an increment passes to its copy in the full range.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L136-L141) (native database range lines 136–141).

### LinearMap.CountableInvariantCoordinateFiltration.incrementInRange_iSupIndep

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.incrementInRange_iSupIndep {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (hq : IsIdempotentElem q) : iSupIndep F.incrementInRange
```

The split increments form an independent family inside the full range.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L143-L191) (native database range lines 143–191).

### LinearMap.CountableInvariantCoordinateFiltration.eq_zero_or_exists_rel_mem_rangeSupported_through

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.eq_zero_or_exists_rel_mem_rangeSupported_through {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (i : κ) (x : ↥q.range) (hx : x ∈ F.rangeSupported (F.before i)) : x = 0 ∨ ∃ (j : κ), F.r j i ∧ x ∈ F.rangeSupported (F.through j)
```

A nonzero range element supported before a stage is already supported
through one strictly earlier stage.  Finite coordinate support is essential
here: it lets us take the greatest of the finitely many witness stages.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L193-L236) (native database range lines 193–236).

### LinearMap.CountableInvariantCoordinateFiltration.rangeSupported_through_le_iSup_incrementInRange

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.rangeSupported_through_le_iSup_incrementInRange {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (hq : IsIdempotentElem q) (i : κ) : F.rangeSupported (F.through i) ≤ ⨆ (j : κ), F.incrementInRange j
```

Every completed supported range stage is generated by the split
increments up to that stage.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L238-L286) (native database range lines 238–286).

### LinearMap.CountableInvariantCoordinateFiltration.iSup_incrementInRange_eq_top

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.iSup_incrementInRange_eq_top {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (hq : IsIdempotentElem q) : ⨆ (i : κ), F.incrementInRange i = ⊤
```

The split increments span the full range of the idempotent.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L288-L310) (native database range lines 288–310).

### LinearMap.CountableInvariantCoordinateFiltration.range_free_of_free_increments

```lean
theorem LinearMap.CountableInvariantCoordinateFiltration.range_free_of_free_increments {S : Type uS} [Ring S] {κ : Type uJ} {q : (κ →₀ S) →ₗ[S] κ →₀ S} (F : q.CountableInvariantCoordinateFiltration) (hq : IsIdempotentElem q) (hfree : ∀ (i : κ), Module.Free S ↥(F.increment i)) : Module.Free S ↥q.range
```

The range of an idempotent endomorphism is free when every split
increment in an invariant coordinate filtration is free.

[Source](../ProjectiveModules/Module/TransfiniteRangeBasis.lean#L312-L331) (native database range lines 312–331).

## PublicAPIClient

Scope: private regression client (not exported by the library).

No native public display sites in this module.
