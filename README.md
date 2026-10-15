# Projective Modules

A reusable Lean library for projective and free modules, scalar extension,
exterior algebra, cancellation, local freeness, stable categories, right-module
K₀ and rank. Hypotheses vary by result; see the linked guides and declarations.
Maintained by the Formal Frontier source-maintainer team.

## Headline results

The [mathematical overview](docs/Overview.md) gives detailed results, formulas,
examples and qualifications; links below go to the corresponding result families.

- **[Coefficient products](docs/Overview.md#coefficient-products):** finite products of
  arbitrary rings reconstruct right modules and split finite-projective classes and K₀.
  Coordinate recovery also allows infinite indices; binary universes are independent,
  empty families and zero rings are included, and no class cancellation is assumed.
- **[Noetherian and PID freeness](docs/Overview.md#noetherian-submodules-and-pid-freeness):**
  over a left-Noetherian, possibly noncommutative ring, submodules of sequence-spanned
  modules are sequence-spanned, with independent universes and no ambient Noetherian,
  free, projective or finite premise. Commutative PID freeness covers arbitrary-rank projectives
  and submodules of arbitrary-rank free modules, not general Noetherian submodules.
- **[Idempotents and principal ideals](docs/Overview.md#idempotents-and-principal-right-ideals):**
  idempotent left ideals are projective over semirings; complements split over rings.
  For commutative semirings, an idempotent ideal is free iff its generator is zero or
  one. Right-ideal extension along any ring map is regular when the generator maps
  to one; image-zero annihilation requires idempotence, but image-one does not.
- **[Exterior constructions](docs/Overview.md#exterior-constructions):** full exterior
  algebra commutes with arbitrary scalar extension. The separate fixed-ring binary
  fixed-degree Sum Formula is natural for module maps; projective exterior powers
  and determinants are also provided, not fixed-degree scalar extension.
- **[Duality and trace](docs/Overview.md#duality-biduality-and-trace):** finite-projective
  dual/evaluation base change; rank-one invertibles including zero rings; cancellation
  only of common finite free summands. Finite-projective left-module biduality uses ordinary coefficients
  over arbitrary semirings; finite-projective contraction trace, cyclicity, dual,
  product, tensor and finite dependent-product laws use commutative semirings.
  Contraction trace also commutes with arbitrary scalar extension between commutative
  semirings, with no freeness or flatness assumption; on finite free modules over
  commutative rings it agrees with Mathlib's scalar-extension trace formula.
  Biduality and trace allow additive monoids; the commutator corollary needs additive groups.
- **[Trace under scalar restriction](ProjectiveModules/Module/Trace/ScalarRestriction.lean):**
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
- **[Rectangular product trace](ProjectiveModules/Module/Trace/Pi.lean):** for maps in
  opposite directions between two finite dependent products of additive-commutative-monoid
  modules over a commutative semiring, the trace of `g.comp f` is the sum of its
  returning coordinate-path traces. Only the source factors must be finitely generated
  and projective; the intermediate factors need neither property. Scalar, both index
  and both carrier universes are independent.
- **[Duals and Hom](docs/Overview.md#categorical-duals-and-hom-modules):** right categorical
  duals use arbitrary rings. For a finite-projective source over a semiring and
  commuting target actions, Hom is independently projective or finite over the outer
  semiring when the target is. Quotient Hom is a restriction kernel for group modules
  over a ring, with commuting outer semiring action; no finite/projective premise.
- **[Local freeness](docs/Overview.md#local-freeness):** every projective right module
  is free over a ring with a proper two-sided ideal and unit complement, with no
  generation bound. The `IsLocalRing` form permits noncommutative rings and independent
  universes; split-range assembly itself requires explicitly free increments.
- **[Categories and restriction](docs/Overview.md#categories-scalar-restriction-and-size):**
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
- **[Stabilization and dimension](docs/Overview.md#stabilization-and-finite-dimension):**
  over arbitrary rings a finite-projective common stabilizer can be replaced by a
  standard finite free one, without hypotheses on the two modules. Finite free
  categorical objects are classified by finite rank over strong-rank-condition rings;
  division rings supply freeness, not rank classification for all projectives.
- **[Right classes and K₀](docs/Overview.md#right-module-classes-and-k₀):** over any ring,
  including zero rings, ring-sized classes use arbitrary-carrier finite projectives;
  K₀ is their group completion, with finite-projective/finite-free common stabilization
  and additive scalar-extension maps. Division-ring classes and K₀ are ℕ and ℤ;
  division-ring extension maps are bijective, and maps from a division-ring source
  to any ring are independent of the scalar homomorphism. Zero-ring objects collapse.
- **[Morita invariance](docs/Overview.md#right-module-classes-and-k₀):** ordinary
  equivalences of right-module categories over arbitrary rings induce additive
  equivalences of finite-projective classes and K₀, with four independent universe
  parameters and category carriers at their scalar/carrier maxima; no functor linearity
  or additivity premise.
- **[Matrix rings](docs/Overview.md#right-module-classes-and-k₀):** over arbitrary
  rings, finite nonempty indices with `Fintype` and `DecidableEq` give canonical
  additive equivalences on finite-projective right-module classes and K₀.
  Forward generators are right rows; the inverse regular matrix generator is
  `[ι → R]`, not generally `[R]`.
- **[Stable categories and rank](docs/Overview.md#stable-categories-and-stalk-rank):**
  the ring-module stable quotient is preadditive; Ext¹ detection needs `Small.{uM} R`.
  For commutative rings, finite projectives realize locally constant natural stalk
  ranks and decompose by rank fibers; classification is only for componentwise-free models.
- **[Free modules and summands](docs/Overview.md#free-modules-and-finite-summands):** Hom from finite free
  semiring sources to targets with commuting actions is free/finite when the target is, independently.
  Countably free modules absorb summands and cancel finite coordinates; semisimple
  freeness needs finite stably-free modules, and Laurent freeness is one-variable
  over a field. Finite-summand cancellation needs Dedekind/stable finiteness;
  finite-free rank bounds need rank condition, not arbitrary cancellation.
- **[Right inverses and coordinates](docs/Overview.md#right-inverses-and-infinite-coordinates):**
  over any ring, `x * y = 1` splits the right regular module by the `1 - y * x`
  defect; the defect vanishes iff `y * x = 1`. Over nontrivial semirings, infinite
  basis index cardinals agree across universes without IBN or rank condition;
  infinite coordinate equivalence excludes finite targets, not finite-rank uniqueness.
- **[Simple multiplicities](docs/Overview.md#simple-multiplicities-and-matrix-rows):**
  arbitrary-ring semisimple modules isotypic of a fixed simple type have Hom-dimension
  multiplicity, invariant under compatible chosen-ring semilinear equivalences.
  Right matrix rows over division rings with finite nonempty indices are simple
  and decompose every right module. Scalar-rank formulas require compatible actions,
  strong rank condition and a simple type free over the scalar semiring; no generation bound.
- **[Stable presentations and kernels](docs/Overview.md#stable-presentations-and-split-kernels):**
  over rings, finite stable presentations mean finite and stably free; IBN semirings
  give cross-sum/integer-difference invariance. Split kernels over semirings require
  an additive-group source, additive-monoid target and a specified section; finite
  generation and projectivity follow independently from the corresponding source
  property. A surjection from a stably free source to a finite stably free target has stably free kernel.
- **[Right-free transport](docs/Overview.md#right-free-coefficient-transport):** arbitrary
  semiring homomorphisms transport supplied right-linear coordinate maps with finite
  source and arbitrary target index; supplied equivalences require both indices finite.
  Coefficients multiply on the left and scalars on the right, with independent universes;
  Ring tensor bridges require both indices finite, not IBN or equal prescribed ranks.
- **[Right extension comparisons](docs/Overview.md#right-scalar-extension-comparisons):**
  arbitrary ring maps admit identity, composition and unit-semiconjugacy comparisons
  for all right modules, with independent universes and no finiteness. Ordered unit
  and associativity laws are pointwise, not categorical coherence. Tensor comparison
  needs a commutative source ring; the scalar-first form also needs a commutative target.
- **[Rank conditions and free words](docs/Overview.md#rank-conditions-free-words-and-cyclic-traces):**
  rank condition and IBN pull back separately along any semiring homomorphism.
  Arbitrary semiring free words have left-linear independent letters with right
  suffixes; two distinct letters give a strong-rank obstruction. The augmentation-kernel
  range description includes trivial coefficients and empty/infinite alphabets. A cyclic additive map
  with injective natural multiples of its unit value gives semiring IBN.

## Use

Add the public library to your `lakefile.toml`:

```toml
[[require]]
name = "projective-modules"
git = "https://github.com/FormalFrontier/projective-modules.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves it when first added or
updated; `lake-manifest.json` locks that commit. To pin a release, use a full
commit from that history. Combining libraries requires compatible releases,
one Mathlib revision, the matching toolchain and dependency lock file.

Use `import ProjectiveModules` for the production aggregate, or a focused
module from the [module map](#module-map); no source-research repository is needed.

For the Noetherian theorem use `import ProjectiveModules.Module.CountablyGenerated.Noetherian`;
its [guide](docs/NoetherianSubmodule.md) gives exact hypotheses and an integer-finsupp example.
For matrix-ring classes and K₀ use `import ProjectiveModules.KTheory.Matrix`;
the [matrix guide](docs/MatrixK0Design.md) explains the right-row action and inverse corner.
Examples and regression clients build in the separate default test target.

## Module map

The aggregate exports the production modules; the paths below link directly
to representative interfaces. The dual is reached through the contraction
aggregate import.

| Area | Interfaces and scope |
| --- | --- |
| [Dual](ProjectiveModules/Dual/BaseChange.lean), [Contraction](ProjectiveModules/Contraction/BaseChange.lean), [Invertible](ProjectiveModules/Invertible/OfRankOne.lean) | Dual/evaluation base change, rank-one iff, scalar endomorphisms and finite-summand cancellation |
| [Bidual evaluation](ProjectiveModules/Module/Bidual.lean) | Ordinary-coefficient bidual equivalence for finite projective semiring modules; forward/inverse evaluation, naturality and coefficient-preserving commutative comparison |
| [Exterior algebra](ProjectiveModules/ExteriorAlgebra/BaseChange.lean), [exterior powers](ProjectiveModules/ExteriorPower/DirectSum.lean) | Full algebra base change; projective powers, determinants/top powers and binary fixed-degree Sum Formula |
| [Free modules](ProjectiveModules/Free/CountableCancellation.lean), [infinite coordinates](ProjectiveModules/Free/InfiniteCoordinates.lean), [rank conditions](ProjectiveModules/Free/InvariantBasisNumber.lean) | Countable cancellation/absorption; finite stably-free semisimple endpoint; infinite basis cardinality and free-coordinate classification without IBN; semiring-homomorphism pullbacks of rank condition and IBN |
| [Linear-map modules](ProjectiveModules/Free/LinearMap.lean) | Finite free semiring source and commuting target actions; independent freeness and finiteness conclusions for Hom over the outer semiring, with independent universes and chosen-basis inverse factorization |
| [Free-word semirings](ProjectiveModules/Free/FreeWordAlgebra.lean) | Rank-two to rank-one left-linear injection by distinct right suffixes and strong-rank obstruction; arbitrary semiring coefficients and alphabet |
| [Free-word augmentation](ProjectiveModules/Free/FreeWordAugmentation.lean), [augmentation kernel](ProjectiveModules/Free/FreeWordAugmentationKernel.lean) | Zero-generator homomorphism returns the empty-word coefficient; full-letter left-linear combination has range equal to its canonical semilinear kernel, for arbitrary semiring coefficients and independent alphabet universe |
| [Fixed-simple multiplicity](ProjectiveModules/Module/IsotypicMultiplicity.lean) | Hom-dimension cardinal of a semisimple isotypic module, direct-sum cardinal statements and invariance under compatible linear or chosen-ring semilinear equivalences, with universe lifts |
| [Right matrix rows](ProjectiveModules/Module/MatrixRow.lean) | Canonical opposite-matrix row simplicity, fixed-row isotypy and arbitrary direct-sum decompositions |
| [Scalar rank](ProjectiveModules/Module/ScalarRank.lean) | Compatible-scalar rank times fixed-simple multiplicity; canonical noncommutative right matrix-row dimension |
| [Finite stable presentations](ProjectiveModules/Free/StablePresentation.lean) | Arbitrary-ring finite/stably-free existence equivalence; IBN-only cross-sum and integer-difference invariance for semirings |
| [Balanced tensor](ProjectiveModules/Module/BalancedTensorProduct.lean), [right extension](ProjectiveModules/Module/RightExtension.lean) | Right-module scalar extension over arbitrary ring homomorphisms, quotients, finite free coordinates |
| [Right coefficient products](ProjectiveModules/Module/RightProduct.lean) | Named Pi/binary opposite-scalar actions; finite arbitrary-projective closure; canonical finite-projective bundles; coordinate recovery and finite reconstruction along projection scalar extension, with independent universes |
| [Right coefficient-product maps](ProjectiveModules/Module/RightProduct/Hom.lean) | `Module.piRightHomAddEquiv`: additive component correspondence for maps linear under the canonical right coefficient-product action on arbitrary-index families over semirings with additive-commutative-monoid fibers; supported-input components, coordinatewise inverse, identity and composition laws. `Module.piRightEndEquiv`: semiring equivalence with the family of factor endomorphism semirings, using the same additive data and `f * g = f.comp g`; independent index, coefficient and carrier universes, without finiteness, finite generation, projectivity, presentation or commutativity assumptions |
| [Product classes and K₀](ProjectiveModules/KTheory/Product.lean) | Finite Pi/binary additive equivalences along projection right extensions; module generators, group-completion and signed inverse laws; independent scalar/carrier universes, without commutativity or cancellation |
| [Principal right ideals](ProjectiveModules/Module/RightExtensionIdeal.lean) | Arbitrary-ring image-one extension equivalence without idempotence and image-zero annihilation with idempotence; idempotent right ideals and their extensions as finite projectives over arbitrary rings |
| [Right-extension comparisons](ProjectiveModules/Module/RightExtensionComparison.lean), [comparison coherence](ProjectiveModules/Module/RightExtensionComparisonCoherence.lean) | `ModuleCat.RightExtension.idLinearEquiv` and `compLinearEquiv`: identity/composition linear equivalences and both-direction pure-tensor API; `compLinearEquiv_id_left`, `compLinearEquiv_id_right` and `compLinearEquiv_assoc`: pointwise unit and triple-composition laws over arbitrary rings/right modules with independent universes |
| [Inner-conjugate extensions](ProjectiveModules/Module/RightExtensionConjugacy.lean) | Fixed-right-target linear equivalence for unit-semiconjugate ring homomorphisms; ordered forward/inverse tensors, one-generator uniqueness and independent scalar/carrier universes |
| [Commutative-base tensor comparison](ProjectiveModules/Module/RightExtensionTensorProduct.lean) | `tensorProductObj` and `tensorProductTmul` specify both scalar views; `tensorProductLinearEquiv` is module-first for `CommRing R` and arbitrary `Ring S`; `extendScalarsLinearEquiv` is scalar-first for `CommRing S`; both-direction pure tensors, tensor commutation and map naturality with independent universes |
| [Right endomorphism matrices and coefficient transport](ProjectiveModules/Module/RightEndomorphismMatrix.lean) | Semiring coefficient transport with finite source and arbitrary target; supplied equivalences with both indices finite; column convention for square endomorphism matrices, finite-coordinate Ring tensor bridges and quasi-regular quotient unit reflection |
| [Local projectives](ProjectiveModules/Module/LocalProjective.lean), [arbitrary local freeness](ProjectiveModules/Module/ArbitraryLocalProjectiveFree.lean), [local scalar interface](ProjectiveModules/Module/LocalRing.lean) | Finite, countable and arbitrary-rank right-module routes under proper-ideal/unit-complement hypotheses; `IsLocalRing` scalar formulation |
| [Countably generated](ProjectiveModules/Module/CountablyGenerated.lean), [Noetherian submodules](ProjectiveModules/Module/CountablyGenerated/Noetherian.lean), [filtration](ProjectiveModules/Module/TransfiniteRangeBasis.lean) | Sequence-span predicate, submodule theorem, invariant countable supports and split-range assembly |
| [Split kernels](ProjectiveModules/Module/ProjectiveKernel.lean) | Over a semiring `R`, with additive-group source `M` and additive-monoid target `A`, the imported `LinearMap.kerProdEquivOfRightInverse` gives `(ker f × A) ≃ₗ[R] M` for a specified linear section of `f : M →ₗ[R] A`; kernel projection/application and inclusion-retraction laws; independent finite-source and projective-source closure, without target finiteness or projectivity and with independent universes |
| [Complements](ProjectiveModules/Module/ProjectiveComplement.lean) | Over a ring `R`, with additive-group modules `F`, `P` and projective target `P`, `Module.Projective.prodKerEquivOfSurjective` chooses a section of a surjection `f : F →ₗ[R] P` and gives `(P × ker f) ≃ₗ[R] F`; finite projective modules have finite complements in finite standard free modules |
| [Right inverse defects](ProjectiveModules/Module/RightRegularDefect.lean), [Hom exactness](ProjectiveModules/Module/HomExact.lean) | Specified right regular decomposition and defect kernel over rings; additive Hom exactness over semirings |
| [Finite dependent products](ProjectiveModules/Module/ProjectivePi.lean) | Canonical pointwise products of projective modules over any semiring are projective for a finite index, without finite generation of the factors and with independent universes |
| [Finite dependent-product trace](ProjectiveModules/Module/Trace/Pi.lean) | Over a commutative semiring, arbitrary endomorphisms of finite dependent products of finite projective additive-commutative-monoid modules have the sum of their diagonal coordinate traces; `Finite` indices and independent scalar, index and carrier universes. For rectangular composites through another finite dependent product, sum the returning source-factor path traces; no finite generation or projectivity is required of the intermediate factors |
| [Trace under scalar restriction](ProjectiveModules/Module/Trace/ScalarRestriction.lean) | Trace of an arbitrary endomorphism restricted through a finite-projective commutative-semiring tower; multiplication-map comparison with `Algebra.trace_trace` on successive finite free commutative-ring extensions |
| [Trace and scalar extension](ProjectiveModules/Module/Trace/BaseChange.lean) | `traceOfFiniteProjective_baseChange`: contraction trace on the canonical tensor-product scalar extension is the image of the source trace for finite projective additive-commutative-monoid modules over commutative semirings; independent scalar and carrier universes, without freeness, flatness or finiteness of the scalar extension. `traceOfFiniteProjective_baseChange_iff_trace` identifies the formula with Mathlib's finite-free trace identity over commutative rings |
| [Finite-projective category](ProjectiveModules/Category/FiniteProjective.lean), [stable category](ProjectiveModules/Category/Stable.lean) | Finite biproducts, preadditive stable quotient and small-ring Ext¹ detection |
| [Projective scalar towers](ProjectiveModules/Module/ScalarRestriction.lean), [finite-projective restriction](ProjectiveModules/Category/FiniteProjectiveRestriction.lean) | Projectivity through semiring towers with projective coefficients; finite-projective ring-homomorphism restriction under its canonical coefficient hypothesis, with carrier, stored-action and map-application laws, both directions of the underlying-functor comparison, and identity/composition functor laws |
| [Module-category equivalences](ProjectiveModules/Category/ModuleEquivalence.lean) | Finite-generation preservation and reflection at independent universes; canonical finite-presentation preservation with unrestricted source and target at the scalar/carrier maximum, and preservation and reflection with both carriers at their maxima; the same bounds for finite projectivity |
| [Compact elements](ProjectiveModules/Order/CompactlyGenerated.lean) | Order isomorphisms preserve and reflect compact elements of arbitrary partial orders; no completeness or top element required |
| [Finite-projective representatives](ProjectiveModules/Category/FiniteProjectiveSmallness.lean) | Derived ring-universe essential smallness at independent carrier universes; ring-sized representatives, linear equivalences and class equality in one reference skeleton |
| [Finite dimension](ProjectiveModules/Category/FiniteModuleDimension.lean) | Finite-rank representative transport; finite-free categorical isomorphism criteria over strong-rank-condition rings |
| [Finite stabilization](ProjectiveModules/Module/FiniteStabilization.lean) | Replace a finite projective common stabilizer by a common standard finite free one; no hypotheses on the two ambient modules |
| [Right regular module](ProjectiveModules/Module/RightRegular.lean) | Canonical opposite-scalar free and finite instances on the ordinary semiring carrier, including zero semirings |
| [Right-module K₀](ProjectiveModules/KTheory/K0.lean), [stabilization](ProjectiveModules/KTheory/Stabilization.lean) | Ring-sized projective class monoid and group completion; arbitrary-universe module generators, descent/universal properties, difference representatives and common finite-projective or finite-free stabilization |
| [Right-module Morita invariance](ProjectiveModules/KTheory/ModuleEquivalence.lean) | Additive equivalences of projective classes and K₀ along ordinary right-module category equivalences; independent scalar/carrier universes, arbitrary-carrier representative/lift evaluation, inverse, completion and coherence laws |
| [Matrix classes and K₀](ProjectiveModules/KTheory/Matrix.lean) | Canonical additive equivalences for arbitrary rings and finite nonempty decidable indices; arbitrary-carrier right-row generators, supported inverse corners, index/height independence and completion compatibility |
| [K₀ scalar extension](ProjectiveModules/KTheory/ScalarExtension.lean) | Additive change-of-rings maps with arbitrary-carrier evaluation and whole-map identity/composition laws; independence of the homomorphism for division-ring sources and arbitrary ring targets |
| [K₀ dimension](ProjectiveModules/KTheory/Rank.lean), [zero rings](ProjectiveModules/KTheory/ZeroRing.lean) | Dimension classifications of projective classes by ℕ and K₀ by ℤ over division rings, and bijectivity of division-ring scalar-extension maps; entire class/group collapse over subsingleton rings |
| [Rank realization](ProjectiveModules/Module/LocallyConstantRank.lean), [fibers](ProjectiveModules/Module/RankFiberDecomposition.lean), [component models](ProjectiveModules/Module/ComponentwiseFree.lean) | Locally constant ranks and conditional componentwise-free classification |
| [PID](ProjectiveModules/Module/PID.lean), [Laurent](ProjectiveModules/Module/LaurentPolynomial.lean) | Arbitrary-rank commutative PID freeness; one-variable Laurent finite-projective freeness |

`ProjectiveModules/Module/ComponentwiseFreeExamples.lean` and
`tests/PublicAPIClient.lean` and
`tests/ProjectiveModulesTests/InfiniteCoordinatesClient.lean` are regression
clients, not modules of the
production aggregate. The project’s [documentation index](docs/README.md)
links the selected mathematical [API guide](docs/API.md) and
[focused Noetherian guide](docs/NoetherianSubmodule.md).

## Mathematical scope

The [overview](docs/Overview.md#mathematical-scope) retains detailed hypotheses,
construction order, examples and limitations. Rank does not classify all finite
projectives; cancellation is bounded, the stable category is not abelian, and
full exterior-algebra base change is not fixed-degree scalar extension.
These are library declarations reusing pinned dependencies, not whole-book coverage.

## Build

The project pins Lean `v4.34.0-rc2`; `lakefile.toml` and
`lake-manifest.json` fix the dependency graph. Install the pinned toolchain and
fetch the matching mathlib cache **before** building. Both existing default
roots are built by:

```sh
lake exe cache get
lake build
```

The default targets are `ProjectiveModules` and `ProjectiveModulesTests`;
the latter compiles example and ordinary-import regression modules. A focused
check after the cache fetch is `lake build ProjectiveModules` or
`lake build ProjectiveModulesTests`. The test target includes intentionally
private importing clients for finite-projective modules and right-extension
comparison coherence, which can report a `privateModule` warning. These
ordinary commands do not make warnings fatal. The root resolves
mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`, GLG
`2683f75e2c5774ddd1295c46062035cb6afabb8a` and Stable Range
[`c283b01ed9ebc33c7eefcdb4f3d2ca45141f469e`](https://github.com/FormalFrontier/stable-range/commit/c283b01ed9ebc33c7eefcdb4f3d2ca45141f469e).
Both latter libraries declare
the same mathlib revision and Lean `4.34.0-rc2` toolchain as this root.
Dependencies are not vendored.

## Documentation limits

The [index](docs/README.md), selected [API guide](docs/API.md) and focused
[Noetherian guide](docs/NoetherianSubmodule.md) are not exhaustive name catalogues,
machine-generated accounts of the whole current API, or proof/source-coverage
certificates. Use the [current sources](ProjectiveModules/) for exact types,
including namespace, universe and instance context; see the
[overview's further limits](docs/Overview.md#further-limits) for bounded nonclaims.

## References

- I. Kaplansky, *Projective modules*, Annals of Mathematics **68** (1958),
  372–377.
- C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  author-hosted complete-book build dated 2013-08-29; Remark I.2.2.1 cites
  Kaplansky's theorem.

Focused modules list mathematical references and prior formalization APIs;
[credits](docs/CREDITS.md) describe contributions and Mathlib reuse.

## License and credit

Original Formal Frontier contributions are released under
[Apache-2.0](LICENSE), with `Authors: Formal Frontier Agents` in Lean headers.
AI agents developed and documented the library: Prism contributed the
foundational mathematics and retained source-expression adaptations; other
agents contributed the stable category, exterior Sum Formula, rank and
componentwise-free constructions, semisimple endpoint, and the original
Noetherian proof and clients; a separate agent contributed the Noetherian
theorem’s library adaptation, public imports and adapted documentation.
See [credits](docs/CREDITS.md)
for truthful roles and provenance. These credits do not assign copyright
ownership, assert human mathematical review or source-author endorsement,
or relicense dependency code or Weibel’s book; no book text or PDF is shipped.
The balanced-tensor and right-extension interfaces follow Prism's foundational
formalization and its maintenance by Prism and Lens; Lens contributed the
identity/composition comparisons and their pointwise unit and associativity
laws, using Mathlib's ring-homomorphism and linear-map interfaces.
The commutative-base comparisons additionally reuse Mathlib's tensor
universal property, commutation, tensor maps and module transport; their
scalar-first target follows Jujian Zhang's Mathlib change-of-rings
formalization. These tensor comparison interfaces were contributed by Lens.
