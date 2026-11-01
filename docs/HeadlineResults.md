# Projective Modules: detailed headline results

[Library README](../README.md) · [Headline results](../README.md#headline-results) · [Module map](../README.md#module-map)

## Navigation

- [Quotients, kernels and presentations](#quotients-kernels-and-presentations)
- [Freeness, cancellation and free words](#freeness-cancellation-and-free-words)
- [Idempotents and projections](#idempotents-and-projections)
- [Exterior algebra and contraction](#exterior-algebra-and-contraction)
- [Symmetric powers](#symmetric-powers): [binomial decomposition](#symmetric-binomial-decomposition), [plethysm](#plethysm-and-flattening), [base change](#symmetric-power-base-change)
- [Determinants](#determinants)
- [Duality, Hom and tensor tests](#duality-hom-and-tensor-tests)
- [Traces](#traces)
- [Topology](#topology)
- [Coefficient products and right extension](#coefficient-products-and-right-extension)
- [Categories, size and length](#categories-size-and-length)
- [Right classes and K0 structures](#right-classes-and-k0-structures)
- [K0 calculations and simple types](#k0-calculations-and-simple-types)
- [Stalk rank and component models](#stalk-rank-and-component-models)
- [Tensor families and finite residue rank](#tensor-families-and-finite-residue-rank)

[Use](../README.md#use) · [Mathematical scope](../README.md#mathematical-scope) · [Build](../README.md#build) · [Documentation limits](../README.md#documentation-limits) · [References](../README.md#references) · [License and credit](../README.md#license-and-credit)

The [mathematical overview](../docs/Overview.md) gives detailed results, formulas,
examples and qualifications; links below go to the corresponding result families.

## Quotients, kernels and presentations

### Quotients by an intersection and a sum

- **[Quotients by an intersection and a sum](../ProjectiveModules/Module/QuotientIntersection.lean).**
  For submodules `U,V` of a module `M` over any ring `S`, `diagonal` maps
  `M ⧸ (U ⊓ V)` to `(M ⧸ U) × (M ⧸ V)` by the two quotient factor maps, and
  `difference` maps a pair represented by `(x,y)` to `[x-y]` modulo `U ⊔ V`.
  The diagonal–difference sequence is short exact. If the sum quotient is projective,
  the [splitting criteria](../ProjectiveModules/Module/QuotientIntersectionSplitting.lean)
  `finite_iff` and `projective_iff` characterize finite generation and projectivity of
  the intersection quotient by the corresponding property of both individual quotients.
  The [right-module K₀ theorem](../ProjectiveModules/KTheory/QuotientIntersection.lean)
  `KTheory.K0.of_quotientInf_add_quotientSup` derives finite generation and projectivity
  of the intersection quotient, finite generation of the sum quotient, and the equality
  `[M ⧸ (U ⊓ V)] + [M ⧸ (U ⊔ V)] = [M ⧸ U] + [M ⧸ V]` in `KTheory.K0 R`.
  Its only property premises are finite generation and projectivity of each individual
  quotient and projectivity of the sum quotient over `Rᵐᵒᵖ`.
  No finiteness or projectivity of `M` is required. Scalar and module
  universes are independent, with noncommutative and zero rings allowed.

### Diagonal quotients of module products

- **[Diagonal quotients of module products](../ProjectiveModules/Module/DiagonalQuotient.lean).**
  For linear maps `f : X →ₗ[S] M` and `g : X →ₗ[S] N` over any ring `S`, the
  canonical map from `(M × N) ⧸ range (f.prod g)` onto
  `(M ⧸ range f) × (N ⧸ range g)` has kernel the image of `x ↦ [(f x, 0)]`.
  The latter map has kernel `ker f ⊔ ker g`, giving the canonical linear
  equivalence from `X ⧸ (ker f ⊔ ker g)` to the projection kernel. Scalar and
  module universes are independent; noncommutative and zero rings are allowed,
  with no finiteness or projectivity premise. For two identity maps, the left
  map is bijective and the class of `(x, y)` is represented by `x - y`. Commuting
  squares induce maps on both quotient constructions, compatible with the left maps
  and projections and respecting identities and composition. Surjective coordinate
  maps induce surjective quotient maps. With a surjective common-source map,
  injective or bijective coordinate maps induce injective or bijective maps,
  respectively.
  Coordinate linear equivalences carrying the relation range onto the target range
  induce an equivalence of presentations, with componentwise forward and inverse
  formulas. It agrees with the induced quotient map for commuting squares; a
  surjective common-source map supplies the relation-range equality.
  Arbitrary commuting squares also induce `quotientKerMap` on the source kernel-sum
  quotients and `kerMap` on the projection kernels. Their characteristic formulas
  `quotientKerMap_mk` and `kerMap_coe`, together with `quotientKerMap_unique` and
  `kerMap_unique`, determine them by quotient composition and ambient inclusion.
  The canonical kernel equivalence is natural for these maps:
  `kerMap_comp_quotientKerEquiv` is an equality of linear maps, proved through the
  characteristic API, with no injectivity or surjectivity assumption.
  If the product of the two range quotients is projective,
  [projective splitting](../ProjectiveModules/Module/DiagonalQuotientSplitting.lean) gives
  `exists_section` and `exists_equiv_prod`: the diagonal quotient splits as the product
  of `X ⧸ (ker f ⊔ ker g)` and the two range quotients, with both the projection and
  canonical kernel inclusion respected. The same hypothesis gives `projective_iff`,
  relating projectivity of the diagonal quotient to that of the source kernel-sum quotient,
  and `finite_iff`, characterizing finite generation by finite generation of both product
  factors.
  For right-linear maps, [K₀ additivity](../ProjectiveModules/KTheory/DiagonalQuotient.lean)
  is proved by `KTheory.K0.of_diagonalQuotient`:
  `[D] = ([K] + [M ⧸ range f]) + [N ⧸ range g]`, where
  `D = (M × N) ⧸ range (f.prod g)` and `K = X ⧸ (ker f ⊔ ker g)`. Only the three
  right-hand modules need be finitely generated and projective over `Rᵐᵒᵖ`; no such
  hypothesis on `X`, `M`, `N`, or `D` is required. The ring may be noncommutative or zero,
  and the four carrier universes are independent. The proof uses short-exact additivity
  for the canonical projection and for the product of cokernels.
  All these results are exported by `import ProjectiveModules`.

### Kernel row of a lifted coproduct

- **[Kernel row of a lifted coproduct](../ProjectiveModules/Module/KernelCoprod.lean).**
  For a supplied lift `ell` with `j.comp ell = p''` and `j.comp i = 0`, the
  kernel of `(i.comp p').coprod ell` lies in a canonical row from `ker p'` to
  `ker p''`. Over any semiring and additive commutative monoids, its first map
  is injective and the row is exact if `i` is injective. If the source of `p'`
  has additive inverses, bottom exactness and surjectivity of `p'` make the
  kernel projection onto. For injective `i`, a supplied section gives a product
  linear equivalence without bottom exactness or cover surjectivity;
  projectivity of `ker p''` supplies such a section when the projection is onto.
  Neither cover source needs to be projective, and the right source and all
  targets may be nongroups.
  Import `ProjectiveModules.Module.KernelCoprod` directly.

### Schanuel kernel comparison

- **[Schanuel kernel comparison](../ProjectiveModules/Module/KernelComparison.lean).**
  Over any semiring, supplied lifts between two linear maps from additive
  commutative groups to a common additive commutative monoid give
  `(ker p × Q) ≃ₗ[R] (ker q × P)`, with formulas retaining both lifts.
  The core needs neither surjectivity nor projectivity. For surjections from
  projective source modules, the
  [projective presentation theorem](../ProjectiveModules/Module/ProjectiveKernelComparison.lean)
  obtains such an equivalence from the projective lifting property.
  The common target needs no additive inverses; all universes are independent.

### Intrinsic Euler classes

- **[Intrinsic Euler classes](../ProjectiveModules/KTheory/Presentation.lean).**
  `KTheory.K0.eulerClass` assigns an intrinsic K₀ class to a finitely presented right
  module over any ring when some finite-free cover has projective kernel.
  Every surjection from a finite projective module then has finite projective kernel
  and computes the class as source minus kernel. Finite projective modules recover
  their existing K₀ classes;
  zero and same-scalar linear equivalence are respected. Finite generators-and-relations
  presentations with projective kernel supply the construction without independent
  relations or a free-kernel assumption. Targets need not be projective, scalar and
  carrier universes are independent, and zero rings are allowed.
  In a short exact sequence with finitely presented endpoints admitting such
  covers, `KTheory.K0.exists_eulerClass_eq_add_of_exact` derives finite presentation
  and cover eligibility of the original middle module, together with
  `χ(M₂) = χ(M₁) + χ(M₃)`. The separate closure theorem
  `KTheory.K0.finitePresentation_and_exists_projective_ker_free_cover_of_exact`
  exposes the middle certificates. The sequence need not split and none of the
  three targets is assumed projective; their original additive-monoid and module
  structures are retained.

### Stable presentations and kernels

- **[Stable presentations and kernels](../docs/Overview.md#stable-presentations-and-split-kernels):**
  over rings, finite stable presentations mean finite and stably free; IBN semirings
  give cross-sum/integer-difference invariance. Split kernels over semirings require
  an additive-group source, additive-monoid target and a specified section; finite
  generation and projectivity follow independently from the corresponding source
  property. A surjection from a stably free source to a finite stably free target has stably free kernel.

## Freeness, cancellation and free words

### Noetherian and PID freeness

- **[Noetherian and PID freeness](../docs/Overview.md#noetherian-submodules-and-pid-freeness):**
  over a left-Noetherian, possibly noncommutative ring, submodules of sequence-spanned
  modules are sequence-spanned, with independent universes and no ambient Noetherian,
  free, projective or finite premise. Commutative PID freeness covers arbitrary-rank projectives
  and submodules of arbitrary-rank free modules, not general Noetherian submodules.

### Local freeness

- **[Local freeness](../docs/Overview.md#local-freeness):** every projective right module
  is free over a ring with a proper two-sided ideal and unit complement, with no
  generation bound. The `IsLocalRing` form permits noncommutative rings and independent
  universes; split-range assembly itself requires explicitly free increments.

### Stabilization and dimension

- **[Stabilization and dimension](../docs/Overview.md#stabilization-and-finite-dimension):**
  over arbitrary rings a finite-projective common stabilizer can be replaced by a
  standard finite free one, without hypotheses on the two modules. Finite free
  categorical objects are classified by finite rank over strong-rank-condition rings;
  division rings supply freeness, not rank classification for all projectives.

### Free modules and summands

- **[Free modules and summands](../docs/Overview.md#free-modules-and-finite-summands):** Hom from finite free
  semiring sources to targets with commuting actions is free/finite when the target is, independently.
  Countably free modules absorb summands and cancel finite coordinates; semisimple
  freeness needs finite stably-free modules, and Laurent freeness is one-variable
  over a field. Finite-summand cancellation needs Dedekind/stable finiteness;
  finite-free rank bounds need rank condition, not arbitrary cancellation.

### Right inverses and coordinates

- **[Right inverses and coordinates](../docs/Overview.md#right-inverses-and-infinite-coordinates):**
  over any ring, `x * y = 1` splits the right regular module by the `1 - y * x`
  defect; the defect vanishes iff `y * x = 1`. Over nontrivial semirings, infinite
  basis index cardinals agree across universes without IBN or rank condition;
  infinite coordinate equivalence excludes finite targets, not finite-rank uniqueness.

### Rank conditions and free words

- **[Rank conditions and free words](../docs/Overview.md#rank-conditions-free-words-and-cyclic-traces):**
  rank condition and IBN pull back separately along any semiring homomorphism.
  Arbitrary semiring free words have left-linear independent letters with right
  suffixes; two distinct letters give a strong-rank obstruction. The augmentation-kernel
  range description includes trivial coefficients and empty/infinite alphabets. A cyclic additive map
  with injective natural multiples of its unit value gives semiring IBN.

## Idempotents and projections

[Stalk rank and component models](#stalk-rank-and-component-models)

### Idempotents and principal ideals

- **[Idempotents and principal ideals](../docs/Overview.md#idempotents-and-principal-right-ideals):**
  idempotent left ideals are projective over semirings; complements split over rings.
  For commutative semirings, an idempotent ideal is free iff its generator is zero or
  one. Right-ideal extension along any ring map is regular when the generator maps
  to one; image-zero annihilation requires idempotence, but image-one does not.

### Commuting idempotent refinements

- **[Commuting idempotent refinements](../ProjectiveModules/Module/ComponentwiseFree.lean):**
  over any semiring, two finite complete orthogonal idempotent families whose entries
  commute across the families have a complete orthogonal Cartesian product family.
  All pairs are retained, including zero products; the two index universes are independent,
  and empty families and zero semirings are allowed.

### Commuting idempotent endomorphisms

- **[Commuting idempotent endomorphisms](../ProjectiveModules/Module/CommutingIdempotents.lean):**
  over any semiring `R`, two commuting idempotent endomorphisms `p`, `q` of an
  `R`-module `M` whose addition is a commutative group give
  `LinearMap.commutingIdempotentsEquiv`, an `R`-linear equivalence from `M` to
  the product of `p.range ⊓ q.range`, `p.range ⊓ q.ker`, `p.ker ⊓ q.range` and
  `p.ker ⊓ q.ker`, in that order. Scalar and carrier universes are independent.

### Inclusion-exclusion for commuting ranges

- **[Inclusion-exclusion for commuting ranges](../ProjectiveModules/KTheory/CommutingIdempotents.lean):**
  over an arbitrary ring, commuting idempotents on a finite projective right module
  have finite projective ranges, intersection and sum. Their original `K₀` classes
  satisfy `[range e] + [range f] = [range e ⊓ range f] + [range e ⊔ range f]`.
  The ambient additive monoid and scalar action are retained; no group or extra
  finite-projectivity premise is supplied. The underlying range identities and
  projectivity results hold over semiring scalars, with an additive group required
  for the results about the sum.

### Finite intersections of idempotent ranges

- **[Finite intersections of idempotent ranges](../ProjectiveModules/Module/FiniteRangeIntersections.lean):**
  over any semiring `R`, a finite pairwise commuting family of idempotent endomorphisms
  of an additive-commutative-monoid `R`-module `M` has a finitely generated intersection
  of ranges when `M` is finitely generated
  (`Module.Finite.iInf_range_of_commuting_idempotents`), and a projective intersection
  when `M` is projective (`Module.Projective.iInf_range_of_commuting_idempotents`).
  Neither conclusion requires the other ambient hypothesis. `LinearMap.range_noncommProd`
  identifies the range of the finite product with the intersection. The original module
  and action are retained, scalar, carrier and index universes are independent, and the
  empty intersection is `⊤`.

### Finite simultaneous decomposition

- **[Finite simultaneous decomposition](../ProjectiveModules/Module/CommutingProjections.lean):**
  for any semiring `R`, additive commutative group `M` with an `R`-module structure,
  finite index type `I`, and supplied pairwise commuting idempotent endomorphisms
  `p : I → Module.End R M`, `LinearMap.commutingIdempotentsPiEquiv` identifies the
  original `M` with the product of all Boolean-selected intersections of the original
  ranges and kernels. Its components are the commuting products of `p i` or `1 - p i`,
  and its inverse sums the block inclusions. Zero blocks and the empty constraint
  family are retained; scalar, module and index universes are independent. No freeness,
  finite generation, finite dimension or commutativity of `R` is assumed.

## Exterior algebra and contraction

### Exterior constructions

- **[Exterior constructions](../docs/Overview.md#exterior-constructions):** full exterior
  algebra commutes with arbitrary scalar extension, and its equivalence identifies
  homogeneous submodule images in every degree, without asserting a general tensor
  equivalence of fixed-degree carriers. The fixed-ring binary fixed-degree Sum Formula
  is natural for module maps; projective exterior powers and determinants are also
  provided. The top exterior power of a finite projective module of constant stalk
  rank is invertible, including degree zero and the zero ring.
  The determinant pairing identifies exterior powers of the dual of a finite projective
  module with duals of its exterior powers, in every degree over any commutative ring.
  This identification is natural for ordinary module maps and also gives a canonical
  equivalence with alternating scalar-valued forms.
  For a finite flat module, an exterior power vanishes when its degree strictly
  exceeds every stalk rank, without assuming global projectivity.

### Symmetric powers

- **[Symmetric powers](../ProjectiveModules/Module/SymmetricPower.lean).**
  Finitely indexed symmetric powers over a commutative semiring preserve
  finite generation, freeness and projectivity separately. An arbitrary
  supplied basis gives a monomial basis indexed by multiplicity vectors
  of total slot count. Projectivity requires no finite generation.
  For arbitrary label types,
  [concatenation](../ProjectiveModules/Module/SymmetricPower/Tensor.lean) is a
  surjective linear map from the tensor product of the two symmetric powers
  to the symmetric power on the disjoint union. It is characterized on all
  labelled generator tensors and is natural under linear maps.
  Neither the labels nor the semimodule need be finite; this is a surjection,
  not generally an equivalence.

The following finite-degree interfaces use `ULift.{uR} (Fin n)` as labels when
`R : Type uR`. Write `Sym_R^n M` for that symmetric power. The semimodules
are additive commutative monoids with their given module structures; scalar
and carrier universes are independent. All natural-number degrees, including
zero, are allowed. None of these constructions requires factorials to be
invertible, a characteristic restriction, additive inverses, or a nonzero base.

#### Symmetric binomial decomposition

For a commutative semiring `R` and arbitrary `R`-semimodules `M` and `N`,
[`SymmetricPower.binomialEquiv`](../ProjectiveModules/Module/SymmetricPower/Prod.lean)
is an `R`-linear equivalence

`Sym_R^n (M × N) ≃ₗ[R] ⨁ j : Fin (n + 1), Sym_R^j M ⊗[R] Sym_R^(n - j) N`.

Here `j` in a degree means `j.val`; the target is the algebraic direct sum
of the `n + 1` complementary-degree tensor factors, in increasing `j` order.
The two carrier universes are independent, with no finite-generation,
freeness, flatness or projectivity assumption.

For a labelled family `x` in `M × N`, `binomialEquiv_tprod_component` gives
its degree-`j` component as the sum over all subsets of the lifted `Fin n`
labels of cardinality `j`: take the first coordinates on the subset and
the second coordinates on its complement, form their symmetric tensors,
and tensor the two results. Each **labelled subset** occurs with coefficient
one. The formula accepts arbitrary enumerations of each subset and its
complement; it is not a division by factorials or a claim about coefficients
after equal monomials are collected. `binomialEquiv_tprod_sum` packages these
components using `DirectSum.lof`.

The inverse formula `binomialEquiv_symm_lof_tprod` inserts the two blocks as
`(m, 0)` and `(0, z)` and concatenates them using any bijection from the
sum of the lifted block labels to the lifted `Fin n` labels.
`binomialEquiv_natural` intertwines `LinearMap.prodMap f g` with the direct
sum of the tensor maps on complementary degrees, for arbitrary linear maps
`f` and `g` between independently sized carriers. Thus both the equivalence
and its inverse are natural in both modules.

`binomialTargetZeroEquiv` identifies the target in degree zero with `R`;
`binomialEquiv_symm_zero` compares the inverse with the empty-label scalar
identification and preserves the scalar unit. In degree one,
`binomialTargetOneEquiv` identifies the target with **`N × M`**, not `M × N`:
the degree-zero block comes first. Its block formulas send the `N` and `M`
generators to `(z, 0)` and `(0, m)`. Accordingly,
`binomialEquiv_symm_one` says that the normalized inverse swaps coordinates.

#### Plethysm and flattening

Over a commutative semiring `R : Type uR`, take label types `I, J : Type uR`
with **`Finite I`**, but no finiteness assumption on `J`, and an arbitrary
`R`-semimodule `M` in an independent universe.
[`SymmetricPower.flatten`](../ProjectiveModules/Module/SymmetricPower/Plethysm.lean)
maps `SymmetricPower R I (SymmetricPower R J M)` linearly onto
`SymmetricPower R (I × J) M`. For every independently labelled grid
`x : I → J → M`, it sends the symmetric tensor of the row tensors to the
single symmetric tensor with entry `x i j` at `(i, j)`, with coefficient one.
`flatten_unique`, `flatten_surjective` and `flatten_natural` give its
characterization, surjectivity and naturality under every module map.

For any `p q : ℕ`, `SymmetricPower.plethysm` specializes this construction to
`Sym_R^p (Sym_R^q M) →ₗ[R] Sym_R^(p * q) M`. `plethysm_tprod` gives the
coefficient-one grid formula for **any** bijection from the product of the
lifted degree labels to the lifted `Fin (p * q)` labels; `plethysm_unique`
characterizes it by these formulas. It is natural and surjective in every
degree, without finiteness, freeness, flatness or projectivity of `M`.
These assertions do not claim general injectivity or an isomorphism.

The singleton comparisons `plethysm_one_left` and `plethysm_one_right`
agree, after the stated reindexing, with the singleton-label equivalence
and its image under the symmetric-power map, respectively, for every other
degree, including zero. Under the empty-label scalar identifications,
`plethysm_zero_left` is the identity on `R`; `plethysm_zero_right` sends a
labelled tensor of degree-zero scalars to their product, with the empty
product equal to one. These are scalar-unit formulas, not vanishing claims.

If `Module.Projective R M`, `plethysm_exists_section` supplies a linear map
back whose composite with plethysm is the identity on `Sym_R^(p * q) M`.
No finite-generation hypothesis is needed, and `p` and `q` may be zero.
The assertion is existence of a linear section, **not** a canonical or
natural choice of sections.

#### Symmetric-power base change

Let `R : Type uR` and `S : Type uS` be commutative semirings with
`Algebra R S`, and let `M : Type uM` be an additive commutative monoid with
`Module R M`. For every `n : ℕ`,
[`SymmetricPower.baseChangeEquiv`](../ProjectiveModules/Module/SymmetricPower/BaseChange.lean)
is the `S`-linear equivalence

`S ⊗[R] Sym_R^n M ≃ₗ[S] Sym_S^n (S ⊗[R] M)`.

The three universes are independent. Labels are lifted `Fin n` in the
respective scalar universes, with the canonical bijection between the lifts.
The tensors are **scalar-first**: their `S`-action is on the first factor;
restriction of scalars uses the given algebra structure and its canonical
tower actions. No `S`-action on the original `M` is assumed. There is no
flatness, freeness, finite-generation or projectivity hypothesis on `M` or
the scalar extension.

Suppressing only these canonical label lifts, the forward formula is
`s ⊗ tprod_R (x_i) ↦ s • tprod_S (1 ⊗ x_i)`; the inverse formula is
`tprod_S (s_i ⊗ x_i) ↦ (∏ i, s_i) ⊗ tprod_R (x_i)`.
The declarations `baseChangeEquiv_tmul_tprod` and
`baseChangeEquiv_symm_tprod_tmul` state them on labelled pure tensors.
`baseChange_eq` and `baseChangeInverse_unique` characterize the two maps;
their composition identities give the equivalence. For every `R`-linear
map `f : M →ₗ[R] N`, with an independently sized carrier `N`,
`baseChangeEquiv_natural` compares its scalar-extended symmetric-power map
with the symmetric-power map of `f.baseChange S`. The inverse comparison
is natural as well. In degree zero, `baseChangeEquiv_zero_unit` and
`baseChangeEquiv_symm_zero_unit` identify both directions with the scalar-unit
comparison `S ⊗[R] R ≃ₗ[S] S`, not with a zero module.

The mathematical references are Weibel's *The K-book* for symmetric powers
and the binomial decomposition, and Bourbaki's *Algebra I*, Chapters 1–3,
as cited by the base-change module. The construction extends Kenny Lau's
Mathlib symmetric tensor powers and uses Mathlib's tensor, multilinear,
basis and projective-splitting APIs; see the [references and credits](../README.md#references).

### Exterior contractions

- **[Exterior contractions](../ProjectiveModules/ExteriorPower/Contraction.lean):** over any
  commutative ring, contraction by a linear functional restricts to consecutive exterior
  powers and is natural under every module map, with pullback of the functional.
  The [contraction calculus](../ProjectiveModules/ExteriorAlgebra/Contraction.lean) includes
  uniqueness, the product rule twisted by the grade involution, and Cartan's identity.
  A vector and functional pairing to one give a contracting identity.

### Unimodular contraction

- **[Unimodular contraction](../ProjectiveModules/ExteriorAlgebra/ContractionExactness.lean):**
  for every quadratic form over a commutative ring, contraction by a surjective covector
  has range equal to its kernel. A vector pairing to one gives a
  [linear splitting](../ProjectiveModules/ExteriorAlgebra/ContractionSplitting.lean) into two
  copies of that kernel, with explicit forward and inverse formulas. Left multiplication
  squares to the quadratic value, not necessarily to zero; no invertibility of two,
  finiteness or freeness is required.

### Naturality of cycle splittings

- **[Naturality of cycle splittings](../ProjectiveModules/ExteriorAlgebra/ContractionNaturality.lean):**
  a quadratic-form-preserving linear map restricts to contraction kernels. Pulling back
  the covector and mapping the unit-pairing vector makes the splitting commute with
  the Clifford map, using the same induced cycle map on both product factors.
  No injectivity is needed; for zero quadratic forms every linear map qualifies.

### Right modules over contraction cycles

- **[Right modules over contraction cycles](../ProjectiveModules/ExteriorAlgebra/ContractionRightModule.lean):**
  for any covector the contraction kernel is a unital subalgebra `B`.
  A vector paired to one upgrades the same cycle-product splitting to `Bᵐᵒᵖ`-linearity
  for right multiplication, preserving the coordinates, inverse and base-ring action.

## Determinants

### Determinant lines

- **[Determinant lines](../docs/Overview.md#determinant-lines):** for finite projective
  modules over arbitrary commutative rings, the dependent product of top exterior
  powers over attained stalk-rank fibers is invertible. Rank zero, zero rings and
  independent universes are included. Isomorphism invariance, rank-fiber recovery,
  zero-module and invertible-module normalizations assert existence of linear
  isomorphisms, not a chosen coherent family of maps. For any commutative
  `R`-algebra `S` supported on a rank fiber, the scalar-extended line is isomorphic
  to the homogeneous exterior power of `S ⊗[R] P` in that fiber's rank.
  The tensor product of the determinant lines of two finite projective modules
  is isomorphic to the determinant line of their product.

### Determinant classes under scalar extension

- **[Determinant classes under scalar extension](../ProjectiveModules/ExteriorPower/DeterminantLineBaseChange.lean):**
  for arbitrary commutative rings `R`, `S`, a homomorphism `f : R →+* S` and a
  finite projective right `R`-module `P`,
  `ModuleCat.RightExtension.determinantLine_mk` identifies the Picard class over
  `Sᵐᵒᵖ` of the determinant line of `ModuleCat.RightExtension.Obj f P` with
  `CommRing.Pic.mapRingHom f.op` applied to the determinant class of `P` over
  `Rᵐᵒᵖ`. Coefficient and carrier universes are independent; variable local rank,
  rank zero and zero rings are allowed, with no flatness assumption on `S`.

### K0 determinant

- **[K₀ determinant](../ProjectiveModules/KTheory/Determinant.lean):** for every
  commutative ring `R`, `KTheory.K0.determinantHom R` is the surjective additive
  homomorphism from right-module K₀ to the additively written Picard group.
  Its value on a finite projective module is its determinant-line class,
  transported from `Rᵐᵒᵖ` to `R`. This normalization determines it uniquely;
  carrier universes are independent and the zero ring is included.

### K0 determinant naturality

- **[K₀ determinant naturality](../ProjectiveModules/KTheory/DeterminantNaturality.lean):**
  for every unital homomorphism `f : R →+* S` of commutative rings in independent
  universes, the additive determinant `K₀(R) → Additive (Pic R)` commutes with
  K₀ scalar extension and Picard base change. This includes zero rings and
  nonflat maps, with no constant-rank assumption.

## Duality, Hom and tensor tests

### Duality and trace

- **[Duality and trace](../docs/Overview.md#duality-biduality-and-trace):** finite-projective
  dual/evaluation base change; rank-one invertibles including zero rings; cancellation
  only of common finite free summands. Finite-projective left-module biduality uses ordinary coefficients
  over arbitrary semirings; finite-projective contraction trace, cyclicity, dual,
  product, tensor and finite dependent-product laws use commutative semirings.
  Contraction trace also commutes with arbitrary scalar extension between commutative
  semirings, with no freeness or flatness assumption; on finite free modules over
  commutative rings it agrees with Mathlib's scalar-extension trace formula.
  Biduality and trace allow additive monoids; the commutator corollary needs additive groups.

### Tensor-family zero detection

- **[Tensor-family zero detection](../ProjectiveModules/Dual/TensorProduct.lean):** over a
  commutative semiring, tensoring a jointly zero-detecting family with a projective
  module on either side preserves zero detection. The family's source and dependent
  targets are arbitrary additive commutative monoids. For two jointly zero-detecting
  families `f i : A →ₗ[R] B i` and `g j : C →ₗ[R] D j`, the maps `f i ⊗ g j`
  jointly detect zero when `C` and every `B i` are projective; no projectivity of
  `A` or `D j` is required. Universes are independent, index types may be empty,
  and no finite-generation assumption is needed. This is zero detection, not
  separation of arbitrary pairs.

### Tensor dual separation

- **[Tensor dual separation](../ProjectiveModules/Dual/TensorProduct.lean):** over a
  commutative semiring, products of linear forms detect zero in `M ⊗[R] N` when
  `M` is projective and the canonical dual evaluation on `N` is left-separating
  (detects zero). Additive commutative monoids and independent scalar/carrier
  universes suffice, without finite generation. The two-projective criterion is
  a corollary; any scalar submodule, including any ideal, can be the second factor
  without a projectivity assumption on it.

### Tensor equality from linear forms

- **[Tensor equality from linear forms](../ProjectiveModules/Dual/TensorProduct.lean):**
  over a commutative semiring `R`, two tensors in `M ⊗[R] N` are equal iff
  every product of linear forms takes equal values on them, when `M` is
  projective and the canonical dual evaluation `Module.Dual.eval R N` is
  injective. In particular, both modules being projective suffices. Additive
  commutative monoids, independent scalar/carrier universes and arbitrary rank
  are allowed; ordinary point injectivity on `N`, not merely zero detection,
  is the hypothesis of the general criterion.

### Faithful tensor injectivity reflection

- **[Faithful tensor injectivity reflection](../ProjectiveModules/Dual/TensorProduct.lean):**
  over a commutative semiring `R`, tensoring with a module `P` with faithful scalar
  action reflects injectivity of maps `M →ₗ[R] N` when `Module.Dual.eval R M` is
  injective, in particular when `M` is projective. The additive structures may be
  commutative monoids, all scalar/carrier universes are independent, and no module
  needs finite generation. Neither flatness of `P` nor any condition on `N` is
  required. For any indexed family `v : ι → N`, injectivity of the finite-support
  relation map `a ↦ a.sum (fun i p => p ⊗ₜ[R] v i)` with coefficients in such a `P` implies
  `LinearIndependent R v`. This is reflection only, not preservation of injectivity.

### Canonical tensor-Hom injectivity

- **[Canonical tensor–Hom injectivity](../ProjectiveModules/Dual/TensorProduct.lean):** over a
  commutative semiring `R`, the canonical map `Module.Dual R M ⊗[R] N →ₗ[R] M →ₗ[R] N`
  is injective when the output `N` is projective. Both modules are additive commutative
  monoids with independent scalar and carrier universes; neither needs finite generation,
  and no projectivity of `M` is assumed.

### Tensoring semilinear Hom

- **[Tensoring semilinear Hom](../ProjectiveModules/TensorProduct/Hom.lean):** for a
  homomorphism `σ : R →+* S` of commutative semirings, the canonical map
  `(L →ₛₗ[σ] M) ⊗[S] N →ₗ[S] (L →ₛₗ[σ] (M ⊗[S] N))` is bijective when `L`
  is finite projective over `R`, with arbitrary `N`. The finite-projective-source
  equivalence has this canonical forward map and agrees with the linear
  equivalence for identity scalars. For a projective `S`-module `N`, the same
  map is injective for arbitrary `L`, and bijective if either `L` is finitely
  generated over `R` or `N` is finitely generated over `S`. Finite-source
  bijectivity thus needs neither projectivity of `L` nor finite generation of `N`.
  All modules are additive
  commutative monoids, their carrier universes are independent, and `σ` is
  arbitrary. Naturality in all three modules needs no finiteness or projectivity;
  the left unitor identifies the dual specialization with `dualTensorHom`.

The [general-source comparison](../ProjectiveModules/TensorProduct/SemilinearHomProjective.lean)
`TensorProduct.semilinearHomTensorMap` also allows an arbitrary, possibly
noncommutative semiring `R`, a commutative semiring `S` and any `σ : R →+* S`.
For a finite projective `R`-module `M`, its canonical map
`(M →ₛₗ[σ] N) ⊗[S] P →ₗ[S] (M →ₛₗ[σ] (N ⊗[S] P))` is bijective.
The additive commutative monoids `N` and `P` are arbitrary `S`-modules,
without finiteness, projectivity or flatness assumptions; scalar and carrier
universes are independent.

For any possibly noncommutative `S`-algebra `T`,
[`TensorProduct.semilinearHomCoeffEquiv`](../ProjectiveModules/TensorProduct/SemilinearHomCoefficient.lean)
gives the corresponding **`T`-linear** coefficient-extension equivalence
from `(M →ₛₗ[σ] N) ⊗[S] T` to the maps
`M →ₛₗ[(algebraMap S T).comp σ] (N ⊗[S] T)`.
Both tensor products use the explicitly chosen **right-factor** `T`-action,
`t • (n ⊗ u) = n ⊗ (t * u)`; the map space has the induced pointwise action.
It sends `f ⊗ t` to `m ↦ f m ⊗ t`. The source `M` is finite projective over
`R`; no flatness or finiteness of `T`, or finiteness of `N`, is required.
The ordinary linear specialization is `TensorProduct.homCoeffEquiv`.
These comparisons reuse Mathlib's semilinear-map, tensor, basis and projective
splitting APIs; their linear mathematical background is Chapter 17 of
J. P. May's *A Concise Course in Algebraic Topology*.

### Flat tensor-Hom comparison

- **[Flat tensor–Hom comparison](../ProjectiveModules/TensorProduct/Hom.lean):** for
  a flat `R`-module `N`, the canonical map
  `(L →ₗ[R] M) ⊗[R] N →ₗ[R] (L →ₗ[R] M ⊗[R] N)` is injective when `L` is
  finitely generated over a commutative semiring `R`, and bijective when `L` is
  finitely presented over a commutative ring `R`. All three modules are additive
  commutative monoids, with four independent scalar and carrier universes;
  `M` is arbitrary, and neither `L` nor `N` need be projective.

### Finite-projective Hom

- **[Finite-projective Hom](../ProjectiveModules/Module/FiniteProjectiveHom.lean).**
  For arbitrary semirings `R`, `S`, `T`, a finite projective `R`-module `M`
  and `σ : R →+* S`, let `N` be both an `S`-module and a `T`-module.
  Semilinear maps carry the
  [canonical pointwise `T`-module structure](../ProjectiveModules/LinearMap/ChangeOfScalars.lean)
  when the `T`-action on `N` commutes with the image of `σ`. They are
  projective over `T` if `N` is projective over `T`, and finitely generated
  over `T` if `N` is finitely generated over `T`, independently. No `T`-action
  on `M` or commutation with all of `S` is required.

### Duals and Hom

- **[Duals and Hom](../docs/Overview.md#categorical-duals-and-hom-modules):** right categorical
  duals use arbitrary rings. For a finite-projective source over a semiring and
  commuting target actions, Hom is independently projective or finite over the outer
  semiring when the target is. Quotient Hom is a restriction kernel for group modules
  over a ring, with commuting outer semiring action; no finite/projective premise.

## Traces

[Trace modulo additive commutators](#trace-modulo-additive-commutators) · [Duality and trace](#duality-and-trace)

### Partial trace

- **[Partial trace](../ProjectiveModules/Module/Trace/Partial.lean):** over a commutative
  semiring `R`, contraction in a finite-projective tensor factor `M` defines an
  `R`-linear operator from maps `M ⊗[R] N →ₗ[R] M ⊗[R] P` to maps `N →ₗ[R] P`.
  The untraced semimodules `N` and `P` are arbitrary, with independent universes.
  On `TensorProduct.map a b`, its value is `tr_M(a) • b`.
  Precomposition by `b.lTensor M` and postcomposition by `c.lTensor M` commute
  with contraction, separately and together, for every input map and arbitrary
  `b : N' →ₗ[R] N`, `c : P →ₗ[R] P'`. These are stock `TensorProduct.map` maps
  with identity on `M`; all untraced factors are arbitrary, with independent scalar/carrier universes.
  For two finite-projective traced factors `M` and `N`, contraction over `M ⊗[R] N`
  agrees with successive contractions, first over `M` and then over `N`, after
  inverse-associator input and forward-associator output transport. The remaining
  input and output semimodules are arbitrary, with independent universes.

### Trace under scalar restriction

- **[Trace under scalar restriction](../ProjectiveModules/Module/Trace/ScalarRestriction.lean):**
  for a commutative-semiring algebra `R → A`, with `A` finite projective over
  `R` and an additive-commutative-monoid module `M` finite projective over `A`,
  every `A`-linear endomorphism `f` satisfies
  `tr_R(f.restrictScalars R) = tr_R(Algebra.lmul R A (tr_A f))`, where `tr`
  is the finite-projective contraction trace. The given `R`-action on `M`
  must be compatible with the tower; scalar and carrier universes are independent,
  without freeness or additive inverses. On successive finite free extensions
  `R → A → T` of commutative rings, the multiplication-map specialization is
  equivalent to `Algebra.trace R T x = Algebra.trace R A (Algebra.trace A T x)`,
  the symmetric form of Mathlib's `Algebra.trace_trace`.

### Rectangular product trace

- **[Rectangular product trace](../ProjectiveModules/Module/Trace/Pi.lean):** for maps in
  opposite directions between two finite dependent products of additive-commutative-monoid
  modules over a commutative semiring, the trace of `g.comp f` is the sum of its
  returning coordinate-path traces. Only the source factors must be finitely generated
  and projective; the intermediate factors need neither property. Scalar, both index
  and both carrier universes are independent.

### K0 trace naturality

- **[K₀ trace naturality](../ProjectiveModules/KTheory/TraceNaturality.lean):**
  for arbitrary rings `R`, `S` in independent universes and every unital
  `f : R →+* S`, `KTheory.K0.traceModCommutators_map` identifies trace after
  right extension of scalars `K0.map f` with the induced additive map on
  commutator quotients applied to the source trace. No commutativity, flatness,
  injectivity or nontriviality hypothesis is required.

## Trace modulo additive commutators

This is the endomorphism-level Hattori–Stallings trace described in Weibel,
*The K-book*, §II.2, “Hattori–Stallings trace map”. Its finite-dual-family
formula is a coordinate expression of the finite-complement construction.

[The additive trace construction](../ProjectiveModules/Module/Trace/CommutatorQuotient.lean)
uses a finite complement of a finite projective right module over an arbitrary
ring `R`. Right modules are left `Rᵐᵒᵖ`-modules; no extra `R`-action or basis is
assumed. The result `LinearMap.traceModCommutators R M` is an `AddMonoidHom`
from `Module.End Rᵐᵒᵖ M` to `R ⧸ Ring.additiveCommutators R`, the additive-group
quotient by the subgroup generated by `a*b - b*a`. This is not an ideal quotient
and no scalar-linearity into the quotient is asserted.

For any finite dual family satisfying `∑ i, φ i m • x i = m`, the characteristic
formula states that the value at `F` is the quotient class of
`∑ i, MulOpposite.unop (φ i (F (x i)))`. This formula is the evaluation and
choice-independence interface, including empty families. The other characteristic
statements compare with finite-free column-matrix trace, normalize left
multiplication on the ordinary right regular carrier, give rectangular
cyclicity and, for commutative rings, compare with contraction trace on the
same `Rᵐᵒᵖ`-module followed by `unop` and the quotient map. Unlike the
commutative-semiring contraction construction, the additive-quotient construction
requires additive inverses but not commutative multiplication.

[Identity trace on classes and K₀](../ProjectiveModules/KTheory/Trace.lean) descends
the identity endomorphism trace through `ProjectiveClass.lift` and extends it
through `K0.lift`, giving additive maps from `KTheory.ProjectiveClass R` and
`KTheory.K0 R` to the same additive quotient. These types already use the right
`R`-module convention. The ordinary right regular module has value the class
of `1`; no cancellation or injectivity of the completion map is assumed.
[Naturality on K₀](../ProjectiveModules/KTheory/TraceNaturality.lean) identifies,
for every unital `f : R →+* S`, the trace after right extension of scalars with
Mathlib's additive quotient map induced by `f`. The rings and their universe
levels are independent.

The construction reuses Mathlib's finite/projective, opposite, linear-map and
additive-quotient APIs; General Linear Groups' additive-commutator and rectangular
trace formalization; and Projective Modules' contraction, complement/retract
and right-matrix formalizations. Their contributors and the motivating Weibel
reference for the existing right-matrix convention are credited in the module.

## Topology

### Kernel families

- **Kernel families.** Over an arbitrary semiring, two supplied split linear
  retractions with a common section into a fixed module with a topological
  additive-group structure have homeomorphic total kernel spaces whenever their
  ambient projection difference is jointly continuous. The section-domain modules
  may vary and need no topology. Both total spaces retain their subspace topologies
  in the parameter–ambient product. Writing `Δ = Γr - Γq`, transport is
  `(t,a) ↦ (t,a + Δ(t,a))`, with inverse `(t,a) ↦ (t,a - Δ(t,a))`.

  [`LinearMap.kerFamilyHomeomorphOfCommonRightInverse`](../ProjectiveModules/Topology/KernelComparison.lean)
  supplies this homeomorphism for an arbitrary topological parameter space and
  varying additive commutative target monoids with their module structures.
  No individual continuity of the retractions or common section is assumed.
  Its fibrewise algebraic core is
  [`LinearMap.kerEquivOfCommonRightInverse`](../ProjectiveModules/Module/KernelComparison.lean).

### Kernels with a common section

- **[Kernels with a common section](../ProjectiveModules/Topology/KernelComparison.lean).**
  Over a semiring, continuous linear maps `r, s : A →L[K] H` sharing a right inverse
  `Γ : H →L[K] A` have canonically continuously linearly equivalent kernels, via
  `a ↦ a - Γ (s a)`. Here `H` is an additive commutative monoid with a module
  structure and a given topology, and `A` is an additive commutative group with a
  module structure and a given topological additive group topology. The comparison
  uses the induced kernel topologies and satisfies identity, inverse and composition
  laws; no topology on the scalar semiring or separation axiom is required.

### Continuous kernel-product splitting

- **Continuous kernel-product splitting.**
  [`ContinuousLinearMap.exists_equiv_ker_prod`](../ProjectiveModules/Topology/Splitting.lean)
  splits a surjective continuous linear map as `M ≃L[R] (f.ker × N)`, with `f` as
  its second coordinate. The scalar semiring has a given topology; the source is
  an additive commutative group with continuous addition and scalar multiplication.
  The target is an additive commutative monoid, projective with its given module
  topology. No continuity assumptions on the target's operations are needed.

### Continuous projective lifting

- **[Continuous projective lifting](../ProjectiveModules/Topology/Projective.lean):**
  continuous linear maps from a projective module carrying its module topology
  lift through surjective continuous linear maps over a semiring with a scalar
  topology. The target of the lift has continuous addition and scalar
  multiplication; the common codomain needs no continuity of its operations.
  Conversely, testing all such continuous liftings detects algebraic projectivity
  for any fixed source topology; with its given module topology this is an iff.

### Topologies on invertible modules

- **[Topologies on invertible modules](../ProjectiveModules/Invertible/Topology.lean):**
  a Hausdorff invertible topological vector space over a nontrivially normed field
  has the module topology on its given space. No completeness of the field or
  norm on the vector space is assumed; scalar and carrier universes are independent.
  Scalar multiplication gives `ContinuousLinearMap.scalarEndEquiv`, a continuous
  linear equivalence from the field to its continuous endomorphisms with bounded
  convergence. Its inverse is the canonical algebraic scalar, with action and
  algebraic-comparison laws; no input vector, frame or inverse is required.

## Coefficient products and right extension

### Coefficient products

- **[Coefficient products](../docs/Overview.md#coefficient-products):** finite products of
  arbitrary rings reconstruct right modules and split finite-projective classes and K₀.
  For arbitrary families of rings, `ProjectiveClass.piMap` is injective; its image
  consists exactly of families admitting projective-class complements to finite free
  classes with one common number of generators.
  Coordinate recovery also allows infinite indices; binary universes are independent,
  empty families and zero rings are included, and no class cancellation is assumed.
  Finite families of left modules over semirings are finitely generated or projective
  over the coefficient product when the factors are, with the canonical pointwise action.

### Right-free transport

- **[Right-free transport](../docs/Overview.md#right-free-coefficient-transport):** arbitrary
  semiring homomorphisms transport supplied right-linear coordinate maps with finite
  source and arbitrary target index; supplied equivalences require both indices finite.
  Coefficients multiply on the left and scalars on the right, with independent universes;
  Ring tensor bridges require both indices finite, not IBN or equal prescribed ranks.

### Right extension comparisons

- **[Right extension comparisons](../docs/Overview.md#right-scalar-extension-comparisons):**
  arbitrary ring maps admit identity, composition and unit-semiconjugacy comparisons
  for all right modules, with independent universes and no finiteness. Ordered unit
  and associativity laws are pointwise, not categorical coherence. Tensor comparison
  needs a commutative source ring; the scalar-first form also needs a commutative target.

### Pointwise right tensor base change

- **[Pointwise right tensor base change](../ProjectiveModules/Module/RightExtensionTensorProduct.lean):**
  for homomorphisms of commutative rings, including zero rings,
  `oppositeScalarEquiv` compares right extension with opposite-base scalar extension,
  and `tensorBaseChangeEquiv` distributes it over tensors of arbitrary right modules.
  Both are linear over the target opposite ring and have forward and inverse
  pure-tensor formulas, with independent scalar and module universes.

### Surjective right extension

- **[Surjective right extension](../ProjectiveModules/Module/RightExtensionQuotient.lean):**
  for a surjection of arbitrary rings and any right module, the kernel of
  `m ↦ m ⊗ 1` is the submodule generated by the right action of the ring-map kernel.
  The zero and fiber criteria require no commutativity or finiteness assumptions.

## Categories, size and length

### Finite projectives and injectivity

- **[Finite projectives and injectivity](../ProjectiveModules/Module/Injective.lean):**
  `Module.injective_of_finite_projective` shows that a finitely generated projective
  left module over an arbitrary left self-injective ring is injective, with
  independent scalar and carrier universes.
  [Morita invariance of self-injectivity](../ProjectiveModules/Category/ModuleEquivalence.lean)
  states that for rings `R : Type uR`, `S : Type uS` and any given equivalence
  `e : ModuleCat.{max uR vR} R ≌ ModuleCat.{max uS vS} S`,
  `ModuleCat.selfInjective_iff_of_equivalence` gives
  `Module.Injective R R ↔ Module.Injective S S`. The ring and carrier universes
  are independent; no identification of the two regular-module images is assumed.

### Categories and restriction

- **[Categories and restriction](../docs/Overview.md#categories-scalar-restriction-and-size):**
  arbitrary-ring module-category equivalences preserve/reflect finite generation.
  For rings `R : Type uR` and `S : Type uS`,
  `ModuleCat.finitePresentation_of_equivalence` states that, for
  `e : ModuleCat.{vR} R ≌ ModuleCat.{max uS vS} S` and `X : ModuleCat.{vR} R`,
  finite presentation over `R` implies finite presentation of `e.functor.obj X`
  over `S`, with unrestricted source carrier universe. With both carriers at
  `max uR vR` and `max uS vS`, respectively,
  `ModuleCat.finitePresentation_iff_of_equivalence` gives
  `Module.FinitePresentation S (e.functor.obj X) ↔ Module.FinitePresentation R X`.
  Here `Module.FinitePresentation` means finite generation with finitely
  generated relations, without a projectivity or freeness assumption. These
  maximum universe bounds are standard sufficient choices, not necessary
  conditions for every ring or equivalence.
  Finite-projective preservation needs the target carrier at its scalar/carrier maximum;
  reflection needs both carriers there. Semiring towers preserve projectivity with
  projective coefficients; ring-map finite-projective restriction needs its canonical
  coefficient finite projective, separately on each side. Representatives allow independent carriers.

### Noetherian modules and rings under equivalence

- **Noetherian modules and rings under equivalence:** For rings `R : Type uR`
  and `S : Type uS`, the [Noetherian interface](../ProjectiveModules/Category/Noetherian.lean)
  identifies `CategoryTheory.IsNoetherianObject X` with `IsNoetherian R X`:
  the ascending chain condition on all submodules, equivalently finite
  generation of every submodule. A given equivalence
  `ModuleCat.{vR} R ≌ ModuleCat.{vS} S` preserves and reflects this module
  property, with independent scalar and carrier universes. This uses the
  general preservation and reflection of Noetherian objects under category
  equivalences, with independent object and morphism universes.
  For the ring implication `IsNoetherianRing R → IsNoetherianRing S`,
  `ModuleCat.{vR} R ≌ ModuleCat.{max uS vS} S` suffices: the source
  carrier universe is unrestricted. An equivalence
  `ModuleCat.{max uR vR} R ≌ ModuleCat.{max uS vS} S` gives
  `IsNoetherianRing R ↔ IsNoetherianRing S`. Here `IsNoetherianRing` means
  **left** Noetherian; neither commutative rings nor a linearity assumption
  on the equivalence is required.

### Submodule lattices and length

- **[Submodule lattices and length](../ProjectiveModules/Category/Length.lean):**
  ordinary equivalences `e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S` over arbitrary
  rings give the canonical order isomorphism
  `ModuleCat.submoduleOrderIsoOfEquivalence e X` on all submodules. For every
  module `X`, `ModuleCat.length_eq_of_equivalence e X` gives
  `Module.length S (e.functor.obj X) = Module.length R X` in `ℕ∞`, including `⊤`;
  `ModuleCat.isFiniteLength_iff_of_equivalence e X` preserves and reflects the
  proposition `IsFiniteLength`. Scalar and carrier universes are independent,
  with no maximum-universe or finite-generation hypothesis. This compares a
  module with its image, not the two regular modules: the matrix equivalence
  sends `ℚ` to the simple column module `Fin 2 → ℚ` of length 1 over
  `Matrix (Fin 2) (Fin 2) ℚ`, whose left regular module instead has length 2.

### Stable categories and rank

- **[Stable categories and rank](../docs/Overview.md#stable-categories-and-stalk-rank):**
  the ring-module stable quotient is preadditive; Ext¹ detection needs `Small.{uM} R`.
  For commutative rings, finite projectives realize locally constant natural stalk
  ranks and decompose by rank fibers; classification is only for componentwise-free models.

## Right classes and K0 structures

### Finite free K0 denominators

- **[Finite free K₀ denominators](../ProjectiveModules/KTheory/FiniteFree.lean):** over any
  ring `R`, the finite free right-module classes `[Fin n → Rᵐᵒᵖ]` are cofinal under
  addition in `ProjectiveClass R`. Every element of `K0 R` is the class of a finite
  projective right module minus one of these finite free classes. Zero rings are
  included; neither cancellation nor invariant basis number is assumed.

### Euler characteristics

- **[Euler characteristics](../ProjectiveModules/KTheory/CochainEulerCharacteristic.lean):**
  finite alternating sums of finite-projective right-module classes in the existing
  `K0 R` are independent of the finite support, and additive on degreewise products.
  For finitely supported acyclic cochain complexes, the even and odd term-class
  sums agree already in `ProjectiveClass R`, giving zero Euler characteristic.
  Supports mean that the original modules vanish outside the chosen finite set;
  arbitrary finite truncations need not be supports. Arbitrary rings, including
  noncommutative rings and zero rings, are allowed; no cancellation is assumed.

### Reduced K0 and stable freeness

- **[Reduced K₀ and stable freeness](../ProjectiveModules/KTheory/Reduced.lean):** over any
  ring `R`, the additive quotient of `K0 R` by integer multiples of the regular
  right-module class has the universal property for additive maps killing that class.
  Every reduced class has a finite projective representative. A finite projective
  right module has zero reduced class exactly when it becomes finite free after
  adding a finite free module, with independent carrier universes and no rank or
  invariant basis number assumption. This is an additive quotient, not a quotient ring.

### Right classes and K0

- **[Right classes and K₀](../docs/Overview.md#right-module-classes-and-k₀):** over any ring,
  including zero rings, ring-sized classes use arbitrary-carrier finite projectives;
  K₀ is their group completion, with finite-projective/finite-free common stabilization
  and additive scalar-extension maps. Division-ring classes and K₀ are ℕ and ℤ;
  division-ring extension maps are bijective, and maps from a division-ring source
  to any ring are independent of the scalar homomorphism. Zero-ring objects collapse.
  Isomorphism-invariant functions descend to class functions, and preservation of zero
  and direct sum bundles this descent as an additive map.

### Invariant basis number and the regular K0 class

- **[Invariant basis number and the regular K₀ class](../ProjectiveModules/KTheory/InvariantBasisNumber.lean):**
  for any ring `R`, possibly noncommutative and including zero rings,
  `InvariantBasisNumber R` holds iff the integer orbit
  `z ↦ z • K0.of R Rᵐᵒᵖ` is injective, equivalently the regular class has
  infinite additive order: `addOrderOf (K0.of R Rᵐᵒᵖ) = 0`.
  Here the regular right module has both scalar ring and carrier `Rᵐᵒᵖ`;
  this is a condition on that single class, not torsion-freeness of all of `K0 R`.

### Tensor semiring of projective classes

- **[Tensor semiring of projective classes](../ProjectiveModules/KTheory/TensorProduct.lean):**
  for every commutative ring `R`, `ProjectiveClass R` has a canonical `CommSemiring`
  instance with direct-sum addition and tensor multiplication. On finite projective
  right modules in independent carrier universes, multiplication gives the class of
  `M ⊗[Rᵐᵒᵖ] N`. Right actions are represented by left `Rᵐᵒᵖ`-module structures;
  the unit is the regular right-module class `of R Rᵐᵒᵖ`, and natural-number casts
  use the direct-sum monoid's scaling of that unit. This is the class-semiring
  construction of Weibel, *The K-book*, II §2, extended to include the zero ring.

### Tensor-product ring on K0

- **[Tensor-product ring on K₀](../ProjectiveModules/KTheory/Ring.lean):** for every
  commutative ring `R`, including the zero ring, the additive Grothendieck group
  `K0 R` has the commutative-ring structure supplied by Group Theory's generic
  completion API. Its additive group and whole `K0.ofClass` map are retained.
  `K0.ofClassRingHom` bundles the class map; the unit is the regular right-module
  generator, and multiplication of module generators computes `M ⊗[Rᵐᵒᵖ] N`,
  with independent module-carrier universes. The generic ring lift and
  extensionality APIs apply to any target ring in an independent universe,
  including noncommutative and zero targets.

### Scalar extension on tensor semirings

- **[Scalar extension on tensor semirings](../ProjectiveModules/KTheory/RingScalarExtension.lean):**
  for any unital homomorphism of commutative rings, including zero rings,
  `KTheory.ProjectiveClass.mapRingHom` enriches the additive class map to a semiring
  homomorphism, with the same whole underlying additive map. It sends arbitrary-carrier
  finite projective right-module classes to their right extensions and respects identity
  and composition; scalar and carrier universes are independent.

### Ring compatibility of the K0 product comparison

- **[Ring compatibility of the K₀ product comparison](../ProjectiveModules/KTheory/ProductRing.lean):**
  for any family of commutative rings, the original additive `KTheory.K0.piMap`
  preserves the tensor unit and multiplication. Index and scalar universes are
  independent; empty families and zero factors are allowed. The regular
  right-module formula holds for arbitrary unital rings. Over `Bool → ℤ`,
  the product of free factor modules of ranks one and zero is not free;
  its K₀ class is idempotent and is the inverse image of the coordinate
  idempotent under `KTheory.K0.piEquiv`.

### K0 bijectivity from projective classes

- **[K₀ bijectivity from projective classes](../ProjectiveModules/KTheory/ScalarExtension.lean):**
  for arbitrary rings `R` and `S` in independent universes and any `f : R →+* S`,
  bijectivity of the scalar-extension class map `ProjectiveClass.map f` implies
  bijectivity of `K0.map f`, by
  `KTheory.K0.map_bijective_of_projectiveClass_map_bijective`. This conditional
  group-completion result assumes neither cancellation nor nontrivial rings.

### Nilpotent-kernel invariance

- **[Nilpotent-kernel invariance](../ProjectiveModules/KTheory/Nilpotent.lean):**
  for a surjective unital homomorphism of arbitrary, possibly noncommutative rings
  with uniformly nilpotent two-sided kernel ideal, the scalar-extension maps on
  finite-projective right-module isomorphism-class monoids and on K₀
  are additive equivalences.

### Opposite-ring duality

- **[Opposite-ring duality](../docs/Overview.md#right-module-classes-and-k₀):** for any
  ring `R`, dualizing finite-projective right modules gives canonical additive
  equivalences of class monoids `ProjectiveClass R ≃+ ProjectiveClass Rᵐᵒᵖ`
  and their group completions `K0 R ≃+ K0 Rᵐᵒᵖ`
  ([duality maps](../ProjectiveModules/KTheory/Dual.lean)). The inverse uses canonical
  double-opposite scalar transport; module-carrier universes are independent.

### Morita invariance

- **[Morita invariance](../docs/Overview.md#right-module-classes-and-k₀):** ordinary
  equivalences of right-module categories over arbitrary rings induce additive
  equivalences of finite-projective classes and K₀, with four independent universe
  parameters and category carriers at their scalar/carrier maxima; no functor linearity
  or additivity premise.

### Matrix rings

- **[Matrix rings](../docs/Overview.md#right-module-classes-and-k₀):** over arbitrary
  rings, finite nonempty indices with `Fintype` and `DecidableEq` give canonical
  additive equivalences on finite-projective right-module classes and K₀.
  Forward generators are right rows; the inverse regular matrix generator is
  `[ι → R]`, not generally `[R]`.

## K0 calculations and simple types

### Integer-rank ring equivalences

- **[Integer-rank ring equivalences](../ProjectiveModules/KTheory/Rank.lean):** for
  fields, commutative local rings and commutative principal ideal domains,
  `KTheory.K0.finrankRingEquiv`, `localRingEquivInt` and `pidRingEquivInt` identify
  the tensor-product K₀ ring with `ℤ`. Their entire underlying additive
  equivalences are the existing dimension equivalences. Local dimension uses
  the Jacobson residue field, and PID dimension uses the fraction field and
  agrees with source-module finrank on finite projectives. Each inverse is the
  canonical integer cast, equivalently `z ↦ z • [R]`. These hypotheses exclude
  zero rings; the general K₀ ring construction above remains zero-inclusive.

### Product comparisons and uniform rank bounds

- **[Product comparisons and uniform rank bounds](../ProjectiveModules/KTheory/RankBound.lean):**
  the [canonical additive comparison](../ProjectiveModules/KTheory/Product.lean) maps
  K₀ of any product of rings to the product of their K₀ groups. For a family of
  possibly noncommutative division rings, it is injective and its image consists
  exactly of families whose integer ranks have one uniform absolute bound.
  More generally, every K₀ element of an arbitrary ring `R` has uniformly bounded
  absolute integer ranks under any indexed family of unital maps `R →+* D i` to
  division rings. For an infinite product of division rings, the comparison is
  not surjective.

### Local and PID K0 calculations

- **[Local and PID K₀ calculations](../ProjectiveModules/KTheory/Rank.lean):** for a
  possibly noncommutative local ring, `KTheory.K0.localEquivInt` identifies K₀ with ℤ
  by canonical Jacobson-residue dimension. For a commutative PID,
  `KTheory.K0.pidEquivInt` uses fraction-field dimension, agreeing with source-module
  finrank on finite projectives. Both send the regular class to one, with inverse
  `z ↦ z • [R]` for every integer. Any unital map to a division ring also gives an
  explicit integer retraction, without a surjectivity hypothesis.

### Scalar-matrix K0 maps

- **[Scalar-matrix K₀ maps](../ProjectiveModules/KTheory/Matrix.lean):** for a finite
  nonempty index of cardinality `n` over a division ring, scalar extension has
  coordinate multiplication by `n` under the Morita/dimension identification. Its
  image is generated by the regular matrix-module class and has index `n`; for
  `n > 1` the scalar-extension map has no additive left inverse. The empty-index
  matrix ring is zero and its regular-class subgroup has index one. These coordinate
  formulas do not assert an identification with intrinsic module length.

### Finite matrix families

- **[Finite matrix families](../ProjectiveModules/KTheory/Semisimple.lean):** for a finite
  family of finite nonempty matrix blocks over division rings, finite-projective
  classes have natural-number coordinates and K₀ has integer coordinates.
  The coordinate basis consists of the classes of supported right rows, which
  uniquely classify simple right modules in arbitrary carrier universes. The
  regular module has coordinate `card (κ i)` at each block, not its square.
  Empty outer families are included.

### Semisimple rings

- **[Semisimple rings](../ProjectiveModules/KTheory/SemisimpleEquivalence.lean):** for
  a ring `R` with `IsSemisimpleRing R`, a chosen Wedderburn–Artin decomposition
  gives natural coordinates on finite-projective right-module classes and
  integer coordinates on K₀. Its transported supported right rows uniquely
  classify simple right modules in arbitrary carrier universes; their classes
  are the coordinate units and their K₀ generators form the integer basis.
  Each row's endomorphism ring is isomorphic to its coefficient division ring,
  not its opposite. The regular coordinates are the block sizes, not their
  squares. Empty outer families include zero rings. The chosen-decomposition
  API also allows independent ring, coefficient and index universes; its row
  construction works over coefficient rings, and the endomorphism statement
  only requires the selected matrix index to be nonempty. No commutativity or
  `Small` hypothesis is imposed.

### Simple multiplicities

- **[Simple multiplicities](../docs/Overview.md#simple-multiplicities-and-matrix-rows):**
  arbitrary-ring semisimple modules isotypic of a fixed simple type have Hom-dimension
  multiplicity, invariant under compatible chosen-ring semilinear equivalences.
  Right matrix rows over division rings with finite nonempty indices are simple
  and decompose every right module. Scalar-rank formulas require compatible actions,
  strong rank condition and a simple type free over the scalar semiring; no generation bound.

## Stalk rank and component models

[Stable categories and rank](#stable-categories-and-rank)

### Locally constant module rank

- **[Locally constant module rank](../ProjectiveModules/Module/RankLocallyConstant.lean):**
  `Module.rankLocallyConstant R M` assigns a locally constant natural-valued
  function on `Spec R` to each finite projective left module over a commutative
  ring. It is invariant under linear isomorphism, sends subsingleton modules to
  zero and the regular module to one, adds under finite dependent products and
  binary products, and multiplies under tensor products. Arbitrary commutative
  algebra base change pulls this function back along the induced map on prime
  spectra. Scalar, module and index universes are independent; empty products
  and zero rings are included. These are module-level laws, not a class or K₀ map.

### Finite generation from rank-one residue fibers

- **[Finite generation from rank-one residue fibers](../ProjectiveModules/Module/FiniteOfFiberRank.lean).**
  An arbitrary projective module over a commutative ring is finitely generated when
  every maximal residue tensor fiber has cardinal rank one. No finite generation,
  finite presentation or Noetherian hypothesis is assumed, and scalar and carrier
  universes are independent. The supporting results separate nonzero-fiber saturation
  of dual evaluations from functional proportionality under the weaker rank-at-most-one
  condition, which also allows zero fibers. The rank is a cardinal, not natural-number
  `finrank`; the zero ring is allowed.

## Tensor families and finite residue rank

### Tensor products and products

Tensoring over a commutative semiring with a projective factor preserves joint pair
injectivity of arbitrary dependent families. The canonical comparison
`P ⊗[R] (∀ i, B i) → ∀ i, P ⊗[R] B i` is injective, but is not generally surjective;
see [tensor products and products](../ProjectiveModules/TensorProduct/Pi.lean).

### Finite generation from constant finite residue rank

- **[Finite generation from constant finite residue rank](../ProjectiveModules/Module/FiniteOfFiberRank.lean).**
  A projective module over a commutative ring whose maximal residue tensor fibers all
  have cardinal rank `r : ℕ` is finitely generated, without assuming finite generation
  or presentation.
  The result includes rank zero and the zero ring, and preserves independent scalar
  and carrier universes. In rank zero the module is
  [subsingleton](../ProjectiveModules/Module/ZeroOfFiberRank.lean). Degreewise exterior
  base change and finite support reduce the argument to rank-one finiteness and
  surjectivity over maximal localizations.

### Finite generation from locally constant finite residue rank

- **[Finite generation from locally constant finite residue rank](../ProjectiveModules/Module/FiniteOfLocallyConstantRank.lean).**
  A projective module over a commutative ring is finitely generated exactly when
  its residue-field tensor ranks are finite cardinals and their Cardinal-valued
  function on the prime spectrum is locally constant. The finite ranks may vary
  between components; no common rank value, finite-generation premise or
  nontrivial-ring hypothesis is needed for the finiteness implication.
  [Residue rank base change](../ProjectiveModules/Module/ResidueRank.lean) identifies
  the Cardinal ranks of `κ(q) ⊗[S] (S ⊗[R] M)` and `κ(f⁻¹(q)) ⊗[R] M`
  for every homomorphism `f : R →+* S` of commutative rings, arbitrary `R`-module
  `M`, and prime `q` of `S`, with cardinal lifts for independent universes.
  This includes infinite-dimensional fibers, without finite-generation, flatness
  or projectivity hypotheses. The maximal-ideal quotient comparison for an algebra
  also allows the contracted prime to be nonmaximal.

### Residue ranks of cyclic quotients

- **[Residue ranks of cyclic quotients](../ProjectiveModules/Module/QuotientResidueRankLocus.lean).**
  For a commutative ring `R` and any ideal `I`, the Cardinal-valued residue-field
  tensor rank of `R/I` is one at primes containing `I` and zero elsewhere.
  This function is locally constant exactly when `V(I)` is clopen, without a
  finite-generation assumption on `I`. A nonzero proper ideal in a domain
  gives non-local constancy; in particular, `ℤ/(2)` is not projective as a
  `ℤ`-module. The ranks are also [compatible with pullback along ring
  homomorphisms](../ProjectiveModules/Module/QuotientResidueRankMap.lean), with
  cardinal lifts accommodating independent universes.

### Tensor and direct-sum residue ranks

- **[Tensor and direct-sum residue ranks](../ProjectiveModules/Module/ResidueRankOperations.lean).**
  For arbitrary modules over a commutative ring, the cardinal residue-field rank of
  a tensor product is the product of the ranks of its two fibres, with lifts for
  independent universes. The rank of an arbitrary algebraic direct sum is the
  cardinal sum of the fibre ranks. No finite generation, flatness or projectivity
  hypothesis is required, and the index and module universes are independent.

### Finite-source tensor-Hom surjectivity

- **[Tensoring semilinear Hom](../ProjectiveModules/TensorProduct/Hom.lean):** for a
  homomorphism `σ : R →+* S` of commutative semirings, the canonical map
  `(L →ₛₗ[σ] M) ⊗[S] N →ₗ[S] (L →ₛₗ[σ] (M ⊗[S] N))` is bijective when `N`
  is finite projective over `S`, with arbitrary source `L`. It is also surjective
  when `L` is finitely generated over `R` and `N` is projective over `S`, without
  projectivity of `L` or finite generation of `N`. All modules are additive
  commutative monoids, their carrier universes are independent, and `σ` is
  arbitrary. Naturality in all three modules needs no finiteness or projectivity;
  the left unitor identifies the dual specialization with `dualTensorHom`.

### Tensor-image membership

- **[Tensor-image membership](../ProjectiveModules/TensorProduct/Submodule.lean):** over a
  commutative ring, if `W ≤ V` has projective quotient, any jointly zero-detecting
  family `f i : A →ₗ[R] B i` detects membership in the image of
  `W ⊗[R] A → V ⊗[R] A`. This image equals the infimum of the comaps of the
  corresponding images in `V ⊗[R] B i`. The source and dependent targets are
  arbitrary modules, and the index type may be infinite or empty.
