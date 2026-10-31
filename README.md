# Projective Modules

A reusable Lean library for projective and free modules, scalar extension,
exterior algebra, cancellation, local freeness, stable categories, right-module
K₀ and rank. Hypotheses vary by result; see the linked guides and declarations.
Maintained by the Formal Frontier source-maintainer team.

## Headline results

- **[Kernels with a common section](ProjectiveModules/Topology/KernelComparison.lean).**
  Over a semiring, continuous linear maps `r, s : A →L[K] H` sharing a right inverse
  `Γ : H →L[K] A` have canonically continuously linearly equivalent kernels, via
  `a ↦ a - Γ (s a)`. Here `H` is an additive commutative monoid with a module
  structure and a given topology, and `A` is an additive commutative group with a
  module structure and a given topological additive group topology. The comparison
  uses the induced kernel topologies and satisfies identity, inverse and composition
  laws; no topology on the scalar semiring or separation axiom is required.

Tensoring over a commutative semiring with a projective factor preserves joint pair
injectivity of arbitrary dependent families. The canonical comparison
`P ⊗[R] (∀ i, B i) → ∀ i, P ⊗[R] B i` is injective, but is not generally surjective;
see [tensor products and products](ProjectiveModules/TensorProduct/Pi.lean).

- **[Symmetric powers](ProjectiveModules/Module/SymmetricPower.lean).**
  Finitely indexed symmetric powers over a commutative semiring preserve
  finite generation, freeness and projectivity separately. An arbitrary
  supplied basis gives a monomial basis indexed by multiplicity vectors
  of total slot count. Projectivity requires no finite generation.
  For arbitrary label types,
  [concatenation](ProjectiveModules/Module/SymmetricPower/Tensor.lean) is a
  surjective linear map from the tensor product of the two symmetric powers
  to the symmetric power on the disjoint union. It is characterized on all
  labelled generator tensors and is natural under linear maps.
- **[Finite-projective Hom](ProjectiveModules/Module/FiniteProjectiveHom.lean).**
  For arbitrary semirings `R`, `S`, `T`, a finite projective `R`-module `M`
  and `σ : R →+* S`, let `N` be both an `S`-module and a `T`-module.
  Semilinear maps carry the
  [canonical pointwise `T`-module structure](ProjectiveModules/LinearMap/ChangeOfScalars.lean)
  when the `T`-action on `N` commutes with the image of `σ`. They are
  projective over `T` if `N` is projective over `T`, and finitely generated
  over `T` if `N` is finitely generated over `T`, independently. No `T`-action
  on `M` or commutation with all of `S` is required.
- **[Finite generation from rank-one residue fibers](ProjectiveModules/Module/FiniteOfFiberRank.lean).**
  An arbitrary projective module over a commutative ring is finitely generated when
  every maximal residue tensor fiber has cardinal rank one. No finite generation,
  finite presentation or Noetherian hypothesis is assumed, and scalar and carrier
  universes are independent. The supporting results separate nonzero-fiber saturation
  of dual evaluations from functional proportionality under the weaker rank-at-most-one
  condition, which also allows zero fibers. The rank is a cardinal, not natural-number
  `finrank`; the zero ring is allowed.

- **[Finite generation from constant finite residue rank](ProjectiveModules/Module/FiniteOfFiberRank.lean).**
  A projective module over a commutative ring whose maximal residue tensor fibers all
  have cardinal rank `r : ℕ` is finitely generated, without assuming finite generation
  or presentation.
  The result includes rank zero and the zero ring, and preserves independent scalar
  and carrier universes. In rank zero the module is
  [subsingleton](ProjectiveModules/Module/ZeroOfFiberRank.lean). Degreewise exterior
  base change and finite support reduce the argument to rank-one finiteness and
  surjectivity over maximal localizations.

- **[Finite generation from locally constant finite residue rank](ProjectiveModules/Module/FiniteOfLocallyConstantRank.lean).**
  A projective module over a commutative ring is finitely generated exactly when
  its residue-field tensor ranks are finite cardinals and their Cardinal-valued
  function on the prime spectrum is locally constant. The finite ranks may vary
  between components; no common rank value, finite-generation premise or
  nontrivial-ring hypothesis is needed for the finiteness implication.
  [Residue rank base change](ProjectiveModules/Module/ResidueRank.lean) identifies
  the Cardinal ranks of `κ(q) ⊗[S] (S ⊗[R] M)` and `κ(f⁻¹(q)) ⊗[R] M`
  for every homomorphism `f : R →+* S` of commutative rings, arbitrary `R`-module
  `M`, and prime `q` of `S`, with cardinal lifts for independent universes.
  This includes infinite-dimensional fibers, without finite-generation, flatness
  or projectivity hypotheses. The maximal-ideal quotient comparison for an algebra
  also allows the contracted prime to be nonmaximal.

- **[Residue ranks of cyclic quotients](ProjectiveModules/Module/QuotientResidueRankLocus.lean).**
  For a commutative ring `R` and any ideal `I`, the Cardinal-valued residue-field
  tensor rank of `R/I` is one at primes containing `I` and zero elsewhere.
  This function is locally constant exactly when `V(I)` is clopen, without a
  finite-generation assumption on `I`. A nonzero proper ideal in a domain
  gives non-local constancy; in particular, `ℤ/(2)` is not projective as a
  `ℤ`-module. The ranks are also [compatible with pullback along ring
  homomorphisms](ProjectiveModules/Module/QuotientResidueRankMap.lean), with
  cardinal lifts accommodating independent universes.

- **[Tensor and direct-sum residue ranks](ProjectiveModules/Module/ResidueRankOperations.lean).**
  For arbitrary modules over a commutative ring, the cardinal residue-field rank of
  a tensor product is the product of the ranks of its two fibres, with lifts for
  independent universes. The rank of an arbitrary algebraic direct sum is the
  cardinal sum of the fibre ranks. No finite generation, flatness or projectivity
  hypothesis is required, and the index and module universes are independent.

- **[Quotients by an intersection and a sum](ProjectiveModules/Module/QuotientIntersection.lean).**
  For submodules `U,V` of a module `M` over any ring `S`, `diagonal` maps
  `M ⧸ (U ⊓ V)` to `(M ⧸ U) × (M ⧸ V)` by the two quotient factor maps, and
  `difference` maps a pair represented by `(x,y)` to `[x-y]` modulo `U ⊔ V`.
  The diagonal–difference sequence is short exact. If the sum quotient is projective,
  the [splitting criteria](ProjectiveModules/Module/QuotientIntersectionSplitting.lean)
  `finite_iff` and `projective_iff` characterize finite generation and projectivity of
  the intersection quotient by the corresponding property of both individual quotients.
  The [right-module K₀ theorem](ProjectiveModules/KTheory/QuotientIntersection.lean)
  `KTheory.K0.of_quotientInf_add_quotientSup` derives finite generation and projectivity
  of the intersection quotient, finite generation of the sum quotient, and the equality
  `[M ⧸ (U ⊓ V)] + [M ⧸ (U ⊔ V)] = [M ⧸ U] + [M ⧸ V]` in `KTheory.K0 R`.
  Its only property premises are finite generation and projectivity of each individual
  quotient and projectivity of the sum quotient over `Rᵐᵒᵖ`.
  No finiteness or projectivity of `M` is required. Scalar and module
  universes are independent, with noncommutative and zero rings allowed.

- **[Diagonal quotients of module products](ProjectiveModules/Module/DiagonalQuotient.lean).**
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
  [projective splitting](ProjectiveModules/Module/DiagonalQuotientSplitting.lean) gives
  `exists_section` and `exists_equiv_prod`: the diagonal quotient splits as the product
  of `X ⧸ (ker f ⊔ ker g)` and the two range quotients, with both the projection and
  canonical kernel inclusion respected. The same hypothesis gives `projective_iff`,
  relating projectivity of the diagonal quotient to that of the source kernel-sum quotient,
  and `finite_iff`, characterizing finite generation by finite generation of both product
  factors.
  For right-linear maps, [K₀ additivity](ProjectiveModules/KTheory/DiagonalQuotient.lean)
  is proved by `KTheory.K0.of_diagonalQuotient`:
  `[D] = ([K] + [M ⧸ range f]) + [N ⧸ range g]`, where
  `D = (M × N) ⧸ range (f.prod g)` and `K = X ⧸ (ker f ⊔ ker g)`. Only the three
  right-hand modules need be finitely generated and projective over `Rᵐᵒᵖ`; no such
  hypothesis on `X`, `M`, `N`, or `D` is required. The ring may be noncommutative or zero,
  and the four carrier universes are independent. The proof uses short-exact additivity
  for the canonical projection and for the product of cokernels.
  All these results are exported by `import ProjectiveModules`.

- **[Kernel row of a lifted coproduct](ProjectiveModules/Module/KernelCoprod.lean).**
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

- **[Schanuel kernel comparison](ProjectiveModules/Module/KernelComparison.lean).**
  Over any semiring, supplied lifts between two linear maps from additive
  commutative groups to a common additive commutative monoid give
  `(ker p × Q) ≃ₗ[R] (ker q × P)`, with formulas retaining both lifts.
  The core needs neither surjectivity nor projectivity. For surjections from
  projective source modules, the
  [projective presentation theorem](ProjectiveModules/Module/ProjectiveKernelComparison.lean)
  obtains such an equivalence from the projective lifting property.
  The common target needs no additive inverses; all universes are independent.

- **[Intrinsic Euler classes](ProjectiveModules/KTheory/Presentation.lean).**
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

- **Continuous kernel-product splitting.**
  [`ContinuousLinearMap.exists_equiv_ker_prod`](ProjectiveModules/Topology/Splitting.lean)
  splits a surjective continuous linear map as `M ≃L[R] (f.ker × N)`, with `f` as
  its second coordinate. The scalar semiring has a given topology; the source is
  an additive commutative group with continuous addition and scalar multiplication.
  The target is an additive commutative monoid, projective with its given module
  topology. No continuity assumptions on the target's operations are needed.

The [mathematical overview](docs/Overview.md) gives detailed results, formulas,
examples and qualifications; links below go to the corresponding result families.

- **[Continuous projective lifting](ProjectiveModules/Topology/Projective.lean):**
  continuous linear maps from a projective module carrying its module topology
  lift through surjective continuous linear maps over a semiring with a scalar
  topology. The target of the lift has continuous addition and scalar
  multiplication; the common codomain needs no continuity of its operations.
  Conversely, testing all such continuous liftings detects algebraic projectivity
  for any fixed source topology; with its given module topology this is an iff.
- **[Coefficient products](docs/Overview.md#coefficient-products):** finite products of
  arbitrary rings reconstruct right modules and split finite-projective classes and K₀.
  For arbitrary families of rings, `ProjectiveClass.piMap` is injective; its image
  consists exactly of families admitting projective-class complements to finite free
  classes with one common number of generators.
  Coordinate recovery also allows infinite indices; binary universes are independent,
  empty families and zero rings are included, and no class cancellation is assumed.
  Finite families of left modules over semirings are finitely generated or projective
  over the coefficient product when the factors are, with the canonical pointwise action.
- **[Finite free K₀ denominators](ProjectiveModules/KTheory/FiniteFree.lean):** over any
  ring `R`, the finite free right-module classes `[Fin n → Rᵐᵒᵖ]` are cofinal under
  addition in `ProjectiveClass R`. Every element of `K0 R` is the class of a finite
  projective right module minus one of these finite free classes. Zero rings are
  included; neither cancellation nor invariant basis number is assumed.
- **[Euler characteristics](ProjectiveModules/KTheory/CochainEulerCharacteristic.lean):**
  finite alternating sums of finite-projective right-module classes in the existing
  `K0 R` are independent of the finite support, and additive on degreewise products.
  For finitely supported acyclic cochain complexes, the even and odd term-class
  sums agree already in `ProjectiveClass R`, giving zero Euler characteristic.
  Supports mean that the original modules vanish outside the chosen finite set;
  arbitrary finite truncations need not be supports. Arbitrary rings, including
  noncommutative rings and zero rings, are allowed; no cancellation is assumed.
- **[Reduced K₀ and stable freeness](ProjectiveModules/KTheory/Reduced.lean):** over any
  ring `R`, the additive quotient of `K0 R` by integer multiples of the regular
  right-module class has the universal property for additive maps killing that class.
  Every reduced class has a finite projective representative. A finite projective
  right module has zero reduced class exactly when it becomes finite free after
  adding a finite free module, with independent carrier universes and no rank or
  invariant basis number assumption. This is an additive quotient, not a quotient ring.
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
- **[Commuting idempotent refinements](ProjectiveModules/Module/ComponentwiseFree.lean):**
  over any semiring, two finite complete orthogonal idempotent families whose entries
  commute across the families have a complete orthogonal Cartesian product family.
  All pairs are retained, including zero products; the two index universes are independent,
  and empty families and zero semirings are allowed.
- **[Commuting idempotent endomorphisms](ProjectiveModules/Module/CommutingIdempotents.lean):**
  over any semiring `R`, two commuting idempotent endomorphisms `p`, `q` of an
  `R`-module `M` whose addition is a commutative group give
  `LinearMap.commutingIdempotentsEquiv`, an `R`-linear equivalence from `M` to
  the product of `p.range ⊓ q.range`, `p.range ⊓ q.ker`, `p.ker ⊓ q.range` and
  `p.ker ⊓ q.ker`, in that order. Scalar and carrier universes are independent.
- **[Inclusion-exclusion for commuting ranges](ProjectiveModules/KTheory/CommutingIdempotents.lean):**
  over an arbitrary ring, commuting idempotents on a finite projective right module
  have finite projective ranges, intersection and sum. Their original `K₀` classes
  satisfy `[range e] + [range f] = [range e ⊓ range f] + [range e ⊔ range f]`.
  The ambient additive monoid and scalar action are retained; no group or extra
  finite-projectivity premise is supplied. The underlying range identities and
  projectivity results hold over semiring scalars, with an additive group required
  for the results about the sum.
- **[Finite intersections of idempotent ranges](ProjectiveModules/Module/FiniteRangeIntersections.lean):**
  over any semiring `R`, a finite pairwise commuting family of idempotent endomorphisms
  of an additive-commutative-monoid `R`-module `M` has a finitely generated intersection
  of ranges when `M` is finitely generated
  (`Module.Finite.iInf_range_of_commuting_idempotents`), and a projective intersection
  when `M` is projective (`Module.Projective.iInf_range_of_commuting_idempotents`).
  Neither conclusion requires the other ambient hypothesis. `LinearMap.range_noncommProd`
  identifies the range of the finite product with the intersection. The original module
  and action are retained, scalar, carrier and index universes are independent, and the
  empty intersection is `⊤`.
- **[Finite simultaneous decomposition](ProjectiveModules/Module/CommutingProjections.lean):**
  for any semiring `R`, additive commutative group `M` with an `R`-module structure,
  finite index type `I`, and supplied pairwise commuting idempotent endomorphisms
  `p : I → Module.End R M`, `LinearMap.commutingIdempotentsPiEquiv` identifies the
  original `M` with the product of all Boolean-selected intersections of the original
  ranges and kernels. Its components are the commuting products of `p i` or `1 - p i`,
  and its inverse sums the block inclusions. Zero blocks and the empty constraint
  family are retained; scalar, module and index universes are independent. No freeness,
  finite generation, finite dimension or commutativity of `R` is assumed.
- **[Exterior constructions](docs/Overview.md#exterior-constructions):** full exterior
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
- **[Exterior contractions](ProjectiveModules/ExteriorPower/Contraction.lean):** over any
  commutative ring, contraction by a linear functional restricts to consecutive exterior
  powers and is natural under every module map, with pullback of the functional.
  The [contraction calculus](ProjectiveModules/ExteriorAlgebra/Contraction.lean) includes
  uniqueness, the product rule twisted by the grade involution, and Cartan's identity.
  A vector and functional pairing to one give a contracting identity.
- **[Unimodular contraction](ProjectiveModules/ExteriorAlgebra/ContractionExactness.lean):**
  for every quadratic form over a commutative ring, contraction by a surjective covector
  has range equal to its kernel. A vector pairing to one gives a
  [linear splitting](ProjectiveModules/ExteriorAlgebra/ContractionSplitting.lean) into two
  copies of that kernel, with explicit forward and inverse formulas. Left multiplication
  squares to the quadratic value, not necessarily to zero; no invertibility of two,
  finiteness or freeness is required.
- **[Naturality of cycle splittings](ProjectiveModules/ExteriorAlgebra/ContractionNaturality.lean):**
  a quadratic-form-preserving linear map restricts to contraction kernels. Pulling back
  the covector and mapping the unit-pairing vector makes the splitting commute with
  the Clifford map, using the same induced cycle map on both product factors.
  No injectivity is needed; for zero quadratic forms every linear map qualifies.
- **[Right modules over contraction cycles](ProjectiveModules/ExteriorAlgebra/ContractionRightModule.lean):**
  for any covector the contraction kernel is a unital subalgebra `B`.
  A vector paired to one upgrades the same cycle-product splitting to `Bᵐᵒᵖ`-linearity
  for right multiplication, preserving the coordinates, inverse and base-ring action.
- **[Determinant lines](docs/Overview.md#determinant-lines):** for finite projective
  modules over arbitrary commutative rings, the dependent product of top exterior
  powers over attained stalk-rank fibers is invertible. Rank zero, zero rings and
  independent universes are included. Isomorphism invariance, rank-fiber recovery,
  zero-module and invertible-module normalizations assert existence of linear
  isomorphisms, not a chosen coherent family of maps. For any commutative
  `R`-algebra `S` supported on a rank fiber, the scalar-extended line is isomorphic
  to the homogeneous exterior power of `S ⊗[R] P` in that fiber's rank.
  The tensor product of the determinant lines of two finite projective modules
  is isomorphic to the determinant line of their product.
- **[Determinant classes under scalar extension](ProjectiveModules/ExteriorPower/DeterminantLineBaseChange.lean):**
  for arbitrary commutative rings `R`, `S`, a homomorphism `f : R →+* S` and a
  finite projective right `R`-module `P`,
  `ModuleCat.RightExtension.determinantLine_mk` identifies the Picard class over
  `Sᵐᵒᵖ` of the determinant line of `ModuleCat.RightExtension.Obj f P` with
  `CommRing.Pic.mapRingHom f.op` applied to the determinant class of `P` over
  `Rᵐᵒᵖ`. Coefficient and carrier universes are independent; variable local rank,
  rank zero and zero rings are allowed, with no flatness assumption on `S`.
- **[K₀ determinant](ProjectiveModules/KTheory/Determinant.lean):** for every
  commutative ring `R`, `KTheory.K0.determinantHom R` is the surjective additive
  homomorphism from right-module K₀ to the additively written Picard group.
  Its value on a finite projective module is its determinant-line class,
  transported from `Rᵐᵒᵖ` to `R`. This normalization determines it uniquely;
  carrier universes are independent and the zero ring is included.
- **[K₀ determinant naturality](ProjectiveModules/KTheory/DeterminantNaturality.lean):**
  for every unital homomorphism `f : R →+* S` of commutative rings in independent
  universes, the additive determinant `K₀(R) → Additive (Pic R)` commutes with
  K₀ scalar extension and Picard base change. This includes zero rings and
  nonflat maps, with no constant-rank assumption.
- **[Duality and trace](docs/Overview.md#duality-biduality-and-trace):** finite-projective
  dual/evaluation base change; rank-one invertibles including zero rings; cancellation
  only of common finite free summands. Finite-projective left-module biduality uses ordinary coefficients
  over arbitrary semirings; finite-projective contraction trace, cyclicity, dual,
  product, tensor and finite dependent-product laws use commutative semirings.
  Contraction trace also commutes with arbitrary scalar extension between commutative
  semirings, with no freeness or flatness assumption; on finite free modules over
  commutative rings it agrees with Mathlib's scalar-extension trace formula.
  Biduality and trace allow additive monoids; the commutator corollary needs additive groups.
- **[Topologies on invertible modules](ProjectiveModules/Invertible/Topology.lean):**
  a Hausdorff invertible topological vector space over a nontrivially normed field
  has the module topology on its given space. No completeness of the field or
  norm on the vector space is assumed; scalar and carrier universes are independent.
  Scalar multiplication gives `ContinuousLinearMap.scalarEndEquiv`, a continuous
  linear equivalence from the field to its continuous endomorphisms with bounded
  convergence. Its inverse is the canonical algebraic scalar, with action and
  algebraic-comparison laws; no input vector, frame or inverse is required.
- **[Partial trace](ProjectiveModules/Module/Trace/Partial.lean):** over a commutative
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
- **[Tensor-family zero detection](ProjectiveModules/Dual/TensorProduct.lean):** over a
  commutative semiring, tensoring a jointly zero-detecting family with a projective
  module on either side preserves zero detection. The family's source and dependent
  targets are arbitrary additive commutative monoids. For two jointly zero-detecting
  families `f i : A →ₗ[R] B i` and `g j : C →ₗ[R] D j`, the maps `f i ⊗ g j`
  jointly detect zero when `C` and every `B i` are projective; no projectivity of
  `A` or `D j` is required. Universes are independent, index types may be empty,
  and no finite-generation assumption is needed. This is zero detection, not
  separation of arbitrary pairs.
- **[Tensor dual separation](ProjectiveModules/Dual/TensorProduct.lean):** over a
  commutative semiring, products of linear forms detect zero in `M ⊗[R] N` when
  `M` is projective and the canonical dual evaluation on `N` is left-separating
  (detects zero). Additive commutative monoids and independent scalar/carrier
  universes suffice, without finite generation. The two-projective criterion is
  a corollary; any scalar submodule, including any ideal, can be the second factor
  without a projectivity assumption on it.
- **[Tensor equality from linear forms](ProjectiveModules/Dual/TensorProduct.lean):**
  over a commutative semiring `R`, two tensors in `M ⊗[R] N` are equal iff
  every product of linear forms takes equal values on them, when `M` is
  projective and the canonical dual evaluation `Module.Dual.eval R N` is
  injective. In particular, both modules being projective suffices. Additive
  commutative monoids, independent scalar/carrier universes and arbitrary rank
  are allowed; ordinary point injectivity on `N`, not merely zero detection,
  is the hypothesis of the general criterion.
- **[Faithful tensor injectivity reflection](ProjectiveModules/Dual/TensorProduct.lean):**
  over a commutative semiring `R`, tensoring with a module `P` with faithful scalar
  action reflects injectivity of maps `M →ₗ[R] N` when `Module.Dual.eval R M` is
  injective, in particular when `M` is projective. The additive structures may be
  commutative monoids, all scalar/carrier universes are independent, and no module
  needs finite generation. Neither flatness of `P` nor any condition on `N` is
  required. For any indexed family `v : ι → N`, injectivity of the finite-support
  relation map `a ↦ a.sum (fun i p => p ⊗ₜ[R] v i)` with coefficients in such a `P` implies
  `LinearIndependent R v`. This is reflection only, not preservation of injectivity.
- **[Canonical tensor–Hom injectivity](ProjectiveModules/Dual/TensorProduct.lean):** over a
  commutative semiring `R`, the canonical map `Module.Dual R M ⊗[R] N →ₗ[R] M →ₗ[R] N`
  is injective when the output `N` is projective. Both modules are additive commutative
  monoids with independent scalar and carrier universes; neither needs finite generation,
  and no projectivity of `M` is assumed.
- **[Tensoring semilinear Hom](ProjectiveModules/TensorProduct/Hom.lean):** for a
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
- **[Flat tensor–Hom comparison](ProjectiveModules/TensorProduct/Hom.lean):** for
  a flat `R`-module `N`, the canonical map
  `(L →ₗ[R] M) ⊗[R] N →ₗ[R] (L →ₗ[R] M ⊗[R] N)` is injective when `L` is
  finitely generated over a commutative semiring `R`, and bijective when `L` is
  finitely presented over a commutative ring `R`. All three modules are additive
  commutative monoids, with four independent scalar and carrier universes;
  `M` is arbitrary, and neither `L` nor `N` need be projective.
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
- **[Finite projectives and injectivity](ProjectiveModules/Module/Injective.lean):**
  `Module.injective_of_finite_projective` shows that a finitely generated projective
  left module over an arbitrary left self-injective ring is injective, with
  independent scalar and carrier universes.
  [Morita invariance of self-injectivity](ProjectiveModules/Category/ModuleEquivalence.lean)
  states that for rings `R : Type uR`, `S : Type uS` and any given equivalence
  `e : ModuleCat.{max uR vR} R ≌ ModuleCat.{max uS vS} S`,
  `ModuleCat.selfInjective_iff_of_equivalence` gives
  `Module.Injective R R ↔ Module.Injective S S`. The ring and carrier universes
  are independent; no identification of the two regular-module images is assumed.
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
- **Noetherian modules and rings under equivalence:** For rings `R : Type uR`
  and `S : Type uS`, the [Noetherian interface](ProjectiveModules/Category/Noetherian.lean)
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
- **[Submodule lattices and length](ProjectiveModules/Category/Length.lean):**
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
  Isomorphism-invariant functions descend to class functions, and preservation of zero
  and direct sum bundles this descent as an additive map.
- **[Invariant basis number and the regular K₀ class](ProjectiveModules/KTheory/InvariantBasisNumber.lean):**
  for any ring `R`, possibly noncommutative and including zero rings,
  `InvariantBasisNumber R` holds iff the integer orbit
  `z ↦ z • K0.of R Rᵐᵒᵖ` is injective, equivalently the regular class has
  infinite additive order: `addOrderOf (K0.of R Rᵐᵒᵖ) = 0`.
  Here the regular right module has both scalar ring and carrier `Rᵐᵒᵖ`;
  this is a condition on that single class, not torsion-freeness of all of `K0 R`.
- **[Tensor semiring of projective classes](ProjectiveModules/KTheory/TensorProduct.lean):**
  for every commutative ring `R`, `ProjectiveClass R` has a canonical `CommSemiring`
  instance with direct-sum addition and tensor multiplication. On finite projective
  right modules in independent carrier universes, multiplication gives the class of
  `M ⊗[Rᵐᵒᵖ] N`. Right actions are represented by left `Rᵐᵒᵖ`-module structures;
  the unit is the regular right-module class `of R Rᵐᵒᵖ`, and natural-number casts
  use the direct-sum monoid's scaling of that unit. This is the class-semiring
  construction of Weibel, *The K-book*, II §2, extended to include the zero ring.
- **[Tensor-product ring on K₀](ProjectiveModules/KTheory/Ring.lean):** for every
  commutative ring `R`, including the zero ring, the additive Grothendieck group
  `K0 R` has the commutative-ring structure supplied by Group Theory's generic
  completion API. Its additive group and whole `K0.ofClass` map are retained.
  `K0.ofClassRingHom` bundles the class map; the unit is the regular right-module
  generator, and multiplication of module generators computes `M ⊗[Rᵐᵒᵖ] N`,
  with independent module-carrier universes. The generic ring lift and
  extensionality APIs apply to any target ring in an independent universe,
  including noncommutative and zero targets.
- **[Integer-rank ring equivalences](ProjectiveModules/KTheory/Rank.lean):** for
  fields, commutative local rings and commutative principal ideal domains,
  `KTheory.K0.finrankRingEquiv`, `localRingEquivInt` and `pidRingEquivInt` identify
  the tensor-product K₀ ring with `ℤ`. Their entire underlying additive
  equivalences are the existing dimension equivalences. Local dimension uses
  the Jacobson residue field, and PID dimension uses the fraction field and
  agrees with source-module finrank on finite projectives. Each inverse is the
  canonical integer cast, equivalently `z ↦ z • [R]`. These hypotheses exclude
  zero rings; the general K₀ ring construction above remains zero-inclusive.
- **[Scalar extension on tensor semirings](ProjectiveModules/KTheory/RingScalarExtension.lean):**
  for any unital homomorphism of commutative rings, including zero rings,
  `KTheory.ProjectiveClass.mapRingHom` enriches the additive class map to a semiring
  homomorphism, with the same whole underlying additive map. It sends arbitrary-carrier
  finite projective right-module classes to their right extensions and respects identity
  and composition; scalar and carrier universes are independent.
- **[Ring compatibility of the K₀ product comparison](ProjectiveModules/KTheory/ProductRing.lean):**
  for any family of commutative rings, the original additive `KTheory.K0.piMap`
  preserves the tensor unit and multiplication. Index and scalar universes are
  independent; empty families and zero factors are allowed. The regular
  right-module formula holds for arbitrary unital rings. Over `Bool → ℤ`,
  the product of free factor modules of ranks one and zero is not free;
  its K₀ class is idempotent and is the inverse image of the coordinate
  idempotent under `KTheory.K0.piEquiv`.
- **[K₀ trace naturality](ProjectiveModules/KTheory/TraceNaturality.lean):**
  for arbitrary rings `R`, `S` in independent universes and every unital
  `f : R →+* S`, `KTheory.K0.traceModCommutators_map` identifies trace after
  right extension of scalars `K0.map f` with the induced additive map on
  commutator quotients applied to the source trace. No commutativity, flatness,
  injectivity or nontriviality hypothesis is required.
- **[Product comparisons and uniform rank bounds](ProjectiveModules/KTheory/RankBound.lean):**
  the [canonical additive comparison](ProjectiveModules/KTheory/Product.lean) maps
  K₀ of any product of rings to the product of their K₀ groups. For a family of
  possibly noncommutative division rings, it is injective and its image consists
  exactly of families whose integer ranks have one uniform absolute bound.
  More generally, every K₀ element of an arbitrary ring `R` has uniformly bounded
  absolute integer ranks under any indexed family of unital maps `R →+* D i` to
  division rings. For an infinite product of division rings, the comparison is
  not surjective.
- **[Local and PID K₀ calculations](ProjectiveModules/KTheory/Rank.lean):** for a
  possibly noncommutative local ring, `KTheory.K0.localEquivInt` identifies K₀ with ℤ
  by canonical Jacobson-residue dimension. For a commutative PID,
  `KTheory.K0.pidEquivInt` uses fraction-field dimension, agreeing with source-module
  finrank on finite projectives. Both send the regular class to one, with inverse
  `z ↦ z • [R]` for every integer. Any unital map to a division ring also gives an
  explicit integer retraction, without a surjectivity hypothesis.
- **[Scalar-matrix K₀ maps](ProjectiveModules/KTheory/Matrix.lean):** for a finite
  nonempty index of cardinality `n` over a division ring, scalar extension has
  coordinate multiplication by `n` under the Morita/dimension identification. Its
  image is generated by the regular matrix-module class and has index `n`; for
  `n > 1` the scalar-extension map has no additive left inverse. The empty-index
  matrix ring is zero and its regular-class subgroup has index one. These coordinate
  formulas do not assert an identification with intrinsic module length.
- **[Finite matrix families](ProjectiveModules/KTheory/Semisimple.lean):** for a finite
  family of finite nonempty matrix blocks over division rings, finite-projective
  classes have natural-number coordinates and K₀ has integer coordinates.
  The coordinate basis consists of the classes of supported right rows, which
  uniquely classify simple right modules in arbitrary carrier universes. The
  regular module has coordinate `card (κ i)` at each block, not its square.
  Empty outer families are included.
- **[Semisimple rings](ProjectiveModules/KTheory/SemisimpleEquivalence.lean):** for
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
- **[K₀ bijectivity from projective classes](ProjectiveModules/KTheory/ScalarExtension.lean):**
  for arbitrary rings `R` and `S` in independent universes and any `f : R →+* S`,
  bijectivity of the scalar-extension class map `ProjectiveClass.map f` implies
  bijectivity of `K0.map f`, by
  `KTheory.K0.map_bijective_of_projectiveClass_map_bijective`. This conditional
  group-completion result assumes neither cancellation nor nontrivial rings.
- **[Nilpotent-kernel invariance](ProjectiveModules/KTheory/Nilpotent.lean):**
  for a surjective unital homomorphism of arbitrary, possibly noncommutative rings
  with uniformly nilpotent two-sided kernel ideal, the scalar-extension maps on
  finite-projective right-module isomorphism-class monoids and on K₀
  are additive equivalences.
- **[Opposite-ring duality](docs/Overview.md#right-module-classes-and-k₀):** for any
  ring `R`, dualizing finite-projective right modules gives canonical additive
  equivalences of class monoids `ProjectiveClass R ≃+ ProjectiveClass Rᵐᵒᵖ`
  and their group completions `K0 R ≃+ K0 Rᵐᵒᵖ`
  ([duality maps](ProjectiveModules/KTheory/Dual.lean)). The inverse uses canonical
  double-opposite scalar transport; module-carrier universes are independent.
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
- **[Locally constant module rank](ProjectiveModules/Module/RankLocallyConstant.lean):**
  `Module.rankLocallyConstant R M` assigns a locally constant natural-valued
  function on `Spec R` to each finite projective left module over a commutative
  ring. It is invariant under linear isomorphism, sends subsingleton modules to
  zero and the regular module to one, adds under finite dependent products and
  binary products, and multiplies under tensor products. Arbitrary commutative
  algebra base change pulls this function back along the induced map on prime
  spectra. Scalar, module and index universes are independent; empty products
  and zero rings are included. These are module-level laws, not a class or K₀ map.
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
- **[Pointwise right tensor base change](ProjectiveModules/Module/RightExtensionTensorProduct.lean):**
  for homomorphisms of commutative rings, including zero rings,
  `oppositeScalarEquiv` compares right extension with opposite-base scalar extension,
  and `tensorBaseChangeEquiv` distributes it over tensors of arbitrary right modules.
  Both are linear over the target opposite ring and have forward and inverse
  pure-tensor formulas, with independent scalar and module universes.
- **[Surjective right extension](ProjectiveModules/Module/RightExtensionQuotient.lean):**
  for a surjection of arbitrary rings and any right module, the kernel of
  `m ↦ m ⊗ 1` is the submodule generated by the right action of the ring-map kernel.
  The zero and fiber criteria require no commutativity or finiteness assumptions.
- **[Rank conditions and free words](docs/Overview.md#rank-conditions-free-words-and-cyclic-traces):**
  rank condition and IBN pull back separately along any semiring homomorphism.
  Arbitrary semiring free words have left-linear independent letters with right
  suffixes; two distinct letters give a strong-rank obstruction. The augmentation-kernel
  range description includes trivial coefficients and empty/infinite alphabets. A cyclic additive map
  with injective natural multiples of its unit value gives semiring IBN.

- **[Tensor-image membership](ProjectiveModules/TensorProduct/Submodule.lean):** over a
  commutative ring, if `W ≤ V` has projective quotient, any jointly zero-detecting
  family `f i : A →ₗ[R] B i` detects membership in the image of
  `W ⊗[R] A → V ⊗[R] A`. This image equals the infimum of the comaps of the
  corresponding images in `V ⊗[R] B i`. The source and dependent targets are
  arbitrary modules, and the index type may be infinite or empty.
## Trace modulo additive commutators

This is the endomorphism-level Hattori–Stallings trace described in Weibel,
*The K-book*, §II.2, “Hattori–Stallings trace map”. Its finite-dual-family
formula is a coordinate expression of the finite-complement construction.

[The additive trace construction](ProjectiveModules/Module/Trace/CommutatorQuotient.lean)
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

[Identity trace on classes and K₀](ProjectiveModules/KTheory/Trace.lean) descends
the identity endomorphism trace through `ProjectiveClass.lift` and extends it
through `K0.lift`, giving additive maps from `KTheory.ProjectiveClass R` and
`KTheory.K0 R` to the same additive quotient. These types already use the right
`R`-module convention. The ordinary right regular module has value the class
of `1`; no cancellation or injectivity of the completion map is assumed.
[Naturality on K₀](ProjectiveModules/KTheory/TraceNaturality.lean) identifies,
for every unital `f : R →+* S`, the trace after right extension of scalars with
Mathlib's additive quotient map induced by `f`. The rings and their universe
levels are independent.

The construction reuses Mathlib's finite/projective, opposite, linear-map and
additive-quotient APIs; General Linear Groups' additive-commutator and rectangular
trace formalization; and Projective Modules' contraction, complement/retract
and right-matrix formalizations. Their contributors and the motivating Weibel
reference for the existing right-matrix convention are credited in the module.

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
For Noetherian objects and transport under module-category equivalences, use
`import ProjectiveModules.Category.Noetherian`.
For matrix-ring classes and K₀ use `import ProjectiveModules.KTheory.Matrix`;
the [matrix guide](docs/MatrixK0Design.md) explains the right-row action and inverse corner.
For semisimple right-module coordinates and the simple-row K₀ basis, use
`import ProjectiveModules.KTheory.SemisimpleEquivalence`; its module documentation
explains chosen decompositions and the two-block rational example.
Examples and regression clients build in the separate default test target.

For the length theorems use `import ProjectiveModules.Category.Length`; they are
not re-exported by the aggregate. This focused import also re-exports
`ProjectiveModules.Category.SubmoduleEquivalence` for submodule transport.
Given `e` and `X` as above, `ModuleCat.submoduleOrderIsoOfEquivalence e X` has type
`Submodule R X ≃o Submodule S (e.functor.obj X)`; its `OrderIso` API provides
order reflection, inverse transport and top/bottom preservation. The length
and finite-length theorems apply to the same `e` and `X` without finiteness assumptions.

## Module map

The paths below link directly to representative production interfaces. The
Noetherian equivalence interface requires its focused import and is not exported
by the aggregate. The dual is reached through the contraction aggregate import.

| Area | Interfaces and scope |
| --- | --- |
| [Dual](ProjectiveModules/Dual/BaseChange.lean), [Contraction](ProjectiveModules/Contraction/BaseChange.lean), [Invertible](ProjectiveModules/Invertible/OfRankOne.lean), [Tensor–Hom](ProjectiveModules/TensorProduct/Hom.lean) | Dual/evaluation base change, rank-one iff, scalar endomorphisms, finite-summand cancellation and tensoring semilinear Hom: canonical equivalence for a finite projective source or tensor factor, and finite-source surjectivity for a projective tensor factor |
| [Invertible module topologies and continuous endomorphisms](ProjectiveModules/Invertible/Topology.lean) | `Module.Invertible.isModuleTopology` identifies the given module topology; `ContinuousLinearMap.scalarEndEquiv` identifies the scalar field with continuous endomorphisms in bounded convergence. Hausdorff invertible topological vector spaces over nontrivially normed fields, with independent scalar/carrier universes and no completeness, norm or chosen frame |
| [Bidual evaluation](ProjectiveModules/Module/Bidual.lean) | Ordinary-coefficient bidual equivalence for finite projective semiring modules; forward/inverse evaluation, naturality and coefficient-preserving commutative comparison |
| [Exterior algebra](ProjectiveModules/ExteriorAlgebra/BaseChange.lean), [exterior powers](ProjectiveModules/ExteriorPower/DirectSum.lean) | Full algebra base change; projective powers, determinants/top powers and binary fixed-degree Sum Formula |
| [Exterior duality](ProjectiveModules/ExteriorPower/Duality.lean), [alternating forms](ProjectiveModules/ExteriorPower/AlternatingForms.lean) | Canonical determinant-pairing equivalence in every degree for finite projective modules over arbitrary commutative rings; ordinary-map naturality, inverse formulas along retractions and alternating-form representation, with independent universes |
| [Contraction calculus](ProjectiveModules/ExteriorAlgebra/Contraction.lean), [exterior contractions](ProjectiveModules/ExteriorPower/Contraction.lean) | `CliffordAlgebra.contractLeft_mul`, `ExteriorAlgebra.map_contractLeft`, `exteriorPower.contractLeft`: twisted product rule, arbitrary-map naturality and canonical consecutive-degree restrictions, with square-zero and anticommutation in every characteristic |
| [Unimodular contraction](ProjectiveModules/ExteriorAlgebra/ContractionExactness.lean), [cycle splitting](ProjectiveModules/ExteriorAlgebra/ContractionSplitting.lean) | `CliffordAlgebra.range_contractLeft_eq_ker_of_surjective`, `CliffordAlgebra.contractLeftKerProdEquiv`: exactness under surjectivity and a two-kernel linear decomposition from a unit-pairing vector, for arbitrary quadratic forms |
| [Cycle-map naturality](ProjectiveModules/ExteriorAlgebra/ContractionNaturality.lean) | `CliffordAlgebra.contractLeftKerMap`, `CliffordAlgebra.contractLeftKerProdEquiv_map`: functorial maps on contraction kernels and naturality of both splitting coordinates under quadratic-form-preserving linear maps, without injectivity |
| [Cycle subalgebras and right modules](ProjectiveModules/ExteriorAlgebra/ContractionRightModule.lean) | `CliffordAlgebra.contractLeftKerSubalgebra`, `CliffordAlgebra.contractLeftKerProdEquivRight`: cycle subalgebras for arbitrary covectors and right-linear refinements of unimodular contraction splittings, recovering the base-ring splitting by restriction of scalars |
| [Homogeneous exterior base change](ProjectiveModules/ExteriorPower/BaseChange.lean) | `ExteriorAlgebra.equivBaseChange_map_exteriorPower`: image equality with the scalar-extended homogeneous submodule, for arbitrary degree and independent ring/carrier universes |
| [Invertible top exterior powers](ProjectiveModules/ExteriorPower/Invertible.lean) | `exteriorPower.invertible_of_rankAtStalk_eq`: the top exterior power of a finite projective module of constant stalk rank is invertible, without a nontrivial-ring hypothesis |
| [Exterior vanishing](ProjectiveModules/ExteriorPower/StalkRank.lean) | `exteriorPower.subsingleton_of_rankAtStalk_lt`: an exterior power of a finite flat module vanishes above all stalk ranks, for arbitrary commutative rings and independent universes |
| [Determinant lines](ProjectiveModules/ExteriorPower/DeterminantLine.lean) | `Module.DeterminantLine`: invertible for finite projective modules of variable stalk rank; linear-isomorphism invariance, rank-fiber recovery, product compatibility, zero and invertible-module comparisons as `Nonempty` isomorphisms |
| [Determinant scalar extension](ProjectiveModules/ExteriorPower/DeterminantLineBaseChange.lean) | `ModuleCat.RightExtension.determinantLine_mk`: the determinant-line Picard class of a finite projective right module commutes with arbitrary ring-homomorphism scalar extension via the opposite homomorphism; no flatness or constant-rank hypothesis |
| [Free modules](ProjectiveModules/Free/CountableCancellation.lean), [infinite coordinates](ProjectiveModules/Free/InfiniteCoordinates.lean), [rank conditions](ProjectiveModules/Free/InvariantBasisNumber.lean) | Countable cancellation/absorption; finite stably-free semisimple endpoint; infinite basis cardinality and free-coordinate classification without IBN; semiring-homomorphism pullbacks of rank condition and IBN |
| [Semilinear scalar restriction](ProjectiveModules/LinearMap/ChangeOfScalars.lean), [categorical comparison](ProjectiveModules/Category/ChangeOfScalars.lean) | Pointwise auxiliary-linear equivalence between semilinear Hom and Hom into the canonically restricted target, over three arbitrary semirings with commuting target actions; full ring-category additive comparison |
| [Finsupp–Hom comparison](ProjectiveModules/LinearMap/Finsupp.lean) | Coordinatewise comparison from finitely supported families of semilinear maps to semilinear maps with finitely supported values: always injective and bijective for a finitely generated source, over arbitrary semirings with commuting auxiliary scalar actions, arbitrary index type and independent universes |
| [Linear-map modules](ProjectiveModules/Free/LinearMap.lean) | Finite free semiring source and commuting target actions; independent freeness and finiteness conclusions for Hom over the outer semiring, with independent universes and chosen-basis inverse factorization |
| [Free-word semirings](ProjectiveModules/Free/FreeWordAlgebra.lean) | Rank-two to rank-one left-linear injection by distinct right suffixes and strong-rank obstruction; arbitrary semiring coefficients and alphabet |
| [Free-word augmentation](ProjectiveModules/Free/FreeWordAugmentation.lean), [augmentation kernel](ProjectiveModules/Free/FreeWordAugmentationKernel.lean) | Zero-generator homomorphism returns the empty-word coefficient; full-letter left-linear combination has range equal to its canonical semilinear kernel, for arbitrary semiring coefficients and independent alphabet universe |
| [Fixed-simple multiplicity](ProjectiveModules/Module/IsotypicMultiplicity.lean) | Hom-dimension cardinal of a semisimple isotypic module, direct-sum cardinal statements and invariance under compatible linear or chosen-ring semilinear equivalences, with universe lifts |
| [Right matrix rows](ProjectiveModules/Module/MatrixRow.lean) | Canonical opposite-matrix row simplicity, fixed-row isotypy and arbitrary direct-sum decompositions |
| [Scalar rank](ProjectiveModules/Module/ScalarRank.lean) | Compatible-scalar rank times fixed-simple multiplicity; canonical noncommutative right matrix-row dimension |
| [Finite stable presentations](ProjectiveModules/Free/StablePresentation.lean) | Arbitrary-ring finite/stably-free existence equivalence; IBN-only cross-sum and integer-difference invariance for semirings |
| [Balanced tensor](ProjectiveModules/Module/BalancedTensorProduct.lean), [right extension](ProjectiveModules/Module/RightExtension.lean) | Right-module scalar extension over arbitrary ring homomorphisms, quotients, finite free coordinates |
| [Left coefficient products](ProjectiveModules/Module/Product.lean) | `Module.finite_pi` and `Module.projective_pi`: finite-family closure over the coefficient semiring product for the canonical pointwise left action, with independent index, coefficient and carrier universes |
| [Right coefficient products](ProjectiveModules/Module/RightProduct.lean) | Named Pi/binary opposite-scalar actions; finite arbitrary-projective closure; canonical finite-projective bundles; coordinate recovery and finite reconstruction along projection scalar extension, with independent universes |
| [Right coefficient-product maps](ProjectiveModules/Module/RightProduct/Hom.lean) | `Module.piRightHomAddEquiv`: additive component correspondence for maps linear under the canonical right coefficient-product action on arbitrary-index families over semirings with additive-commutative-monoid fibers; supported-input components, coordinatewise inverse, identity and composition laws. `Module.piRightEndEquiv`: semiring equivalence with the family of factor endomorphism semirings, using the same additive data and `f * g = f.comp g`; independent index, coefficient and carrier universes, without finiteness, finite generation, projectivity, presentation or commutativity assumptions |
| [Product classes and K₀](ProjectiveModules/KTheory/Product.lean) | Arbitrary-family `ProjectiveClass.piMap` injectivity; image exactly the families admitting projective-class complements to finite free classes with one common number of generators. Finite Pi/binary additive equivalences for projective classes and K₀ along projection right extensions; module generators, group-completion and signed inverse laws; independent scalar/carrier universes, without commutativity or cancellation |
| [Principal right ideals](ProjectiveModules/Module/RightExtensionIdeal.lean) | Arbitrary-ring image-one extension equivalence without idempotence and image-zero annihilation with idempotence; idempotent right ideals and their extensions as finite projectives over arbitrary rings |
| [Right-extension comparisons](ProjectiveModules/Module/RightExtensionComparison.lean), [comparison coherence](ProjectiveModules/Module/RightExtensionComparisonCoherence.lean) | `ModuleCat.RightExtension.idLinearEquiv` and `compLinearEquiv`: identity/composition linear equivalences and both-direction pure-tensor API; `compLinearEquiv_id_left`, `compLinearEquiv_id_right` and `compLinearEquiv_assoc`: pointwise unit and triple-composition laws over arbitrary rings/right modules with independent universes |
| [Inner-conjugate extensions](ProjectiveModules/Module/RightExtensionConjugacy.lean) | Fixed-right-target linear equivalence for unit-semiconjugate ring homomorphisms; ordered forward/inverse tensors, one-generator uniqueness and independent scalar/carrier universes |
| [Commutative-base tensor comparison](ProjectiveModules/Module/RightExtensionTensorProduct.lean) | `tensorProductObj` and `tensorProductTmul` specify both scalar views; `tensorProductLinearEquiv` is module-first for `CommRing R` and arbitrary `Ring S`; `extendScalarsLinearEquiv` is scalar-first for `CommRing S`; both-direction pure tensors, tensor commutation and map naturality with independent universes. For commutative source and target rings, `oppositeScalarEquiv` compares extension along the opposite homomorphism, and `tensorBaseChangeEquiv` distributes right extension over the original opposite-base tensor product, with forward and inverse pure-tensor formulas |
| [Right endomorphism matrices and coefficient transport](ProjectiveModules/Module/RightEndomorphismMatrix.lean) | Semiring coefficient transport with finite source and arbitrary target; supplied equivalences with both indices finite; column convention for square endomorphism matrices, finite-coordinate Ring tensor bridges and quasi-regular quotient unit reflection |
| [Local projectives](ProjectiveModules/Module/LocalProjective.lean), [arbitrary local freeness](ProjectiveModules/Module/ArbitraryLocalProjectiveFree.lean), [local scalar interface](ProjectiveModules/Module/LocalRing.lean) | Finite, countable and arbitrary-rank right-module routes under proper-ideal/unit-complement hypotheses; `IsLocalRing` scalar formulation |
| [Countably generated](ProjectiveModules/Module/CountablyGenerated.lean), [Noetherian submodules](ProjectiveModules/Module/CountablyGenerated/Noetherian.lean), [filtration](ProjectiveModules/Module/TransfiniteRangeBasis.lean) | Sequence-span predicate, submodule theorem, invariant countable supports and split-range assembly |
| [Split kernels](ProjectiveModules/Module/ProjectiveKernel.lean) | Over a semiring `R`, with additive-group source `M` and additive-monoid target `A`, the imported `LinearMap.kerProdEquivOfRightInverse` gives `(ker f × A) ≃ₗ[R] M` for a specified linear section of `f : M →ₗ[R] A`; kernel projection/application and inclusion-retraction laws; independent finite-source and projective-source closure, without target finiteness or projectivity and with independent universes |
| [Commuting idempotent endomorphisms](ProjectiveModules/Module/CommutingIdempotents.lean) | `LinearMap.commutingIdempotentsEquiv`: four range/kernel intersections for two commuting idempotents on an additive-commutative-group module over any semiring, with independent universes. Four `[simp]` coordinate equations apply `p * q`, `p * (1 - q)`, `(1 - p) * q` and `(1 - p) * (1 - q)`; the inverse `[simp]` equation sums the underlying components as `(a + b) + (c + d)` |
| [Complements](ProjectiveModules/Module/ProjectiveComplement.lean) | Over a ring `R`, with additive-group modules `F`, `P` and projective target `P`, `Module.Projective.prodKerEquivOfSurjective` chooses a section of a surjection `f : F →ₗ[R] P` and gives `(P × ker f) ≃ₗ[R] F`; finite projective modules have finite complements in finite standard free modules |
| [Injectivity](ProjectiveModules/Module/Injective.lean) | Finitely generated projective left modules over an arbitrary left self-injective ring are injective, with independent scalar and carrier universes |
| [Right inverse defects](ProjectiveModules/Module/RightRegularDefect.lean), [Hom exactness](ProjectiveModules/Module/HomExact.lean) | Specified right regular decomposition and defect kernel over rings; additive Hom exactness over semirings |
| [Continuous projective lifting](ProjectiveModules/Topology/Projective.lean) | `ContinuousLinearMap.projective_lifting_property`: continuous linear lifts from projective modules with their module topology over a semiring with a scalar topology; continuous addition and scalar multiplication on the target of the lift, with no operation-continuity assumption on the common codomain |
| [Finite commuting projections](ProjectiveModules/Module/CommutingProjections.lean) | `LinearMap.commutingIdempotentsPiEquiv`: simultaneous decomposition of the original module by a finite pairwise commuting idempotent family over a semiring, for an additive commutative group module; all original range/kernel intersections, Boolean product projectors, component action and inverse inclusion sum, including zero blocks and empty constraints |
| [Finite dependent products](ProjectiveModules/Module/ProjectivePi.lean) | Canonical pointwise products of projective modules over any semiring are projective for a finite index, without finite generation of the factors and with independent universes |
| [Finite dependent-product trace](ProjectiveModules/Module/Trace/Pi.lean) | Over a commutative semiring, arbitrary endomorphisms of finite dependent products of finite projective additive-commutative-monoid modules have the sum of their diagonal coordinate traces; `Finite` indices and independent scalar, index and carrier universes. For rectangular composites through another finite dependent product, sum the returning source-factor path traces; no finite generation or projectivity is required of the intermediate factors |
| [Trace under scalar restriction](ProjectiveModules/Module/Trace/ScalarRestriction.lean) | Trace of an arbitrary endomorphism restricted through a finite-projective commutative-semiring tower; multiplication-map comparison with `Algebra.trace_trace` on successive finite free commutative-ring extensions |
| [Trace and scalar extension](ProjectiveModules/Module/Trace/BaseChange.lean) | `traceOfFiniteProjective_baseChange`: contraction trace on the canonical tensor-product scalar extension is the image of the source trace for finite projective additive-commutative-monoid modules over commutative semirings; independent scalar and carrier universes, without freeness, flatness or finiteness of the scalar extension. `traceOfFiniteProjective_baseChange_iff_trace` identifies the formula with Mathlib's finite-free trace identity over commutative rings |
| [Partial trace](ProjectiveModules/Module/Trace/Partial.lean) | `partialTraceOfFiniteProjective`: linear contraction of arbitrary maps `M ⊗ N →ₗ M ⊗ P` to maps `N →ₗ P` over a commutative semiring, with only the traced factor `M` finite projective and four independent universes. The all-map evaluation formula uses the canonical tensor–Hom inverse; on `TensorProduct.map a b` the result is `traceOfFiniteProjective R M a • b`, without normalization. On `V = Fin 2 → ℕ`, tensor symmetry has partial trace `id` |
| [Finite-projective category](ProjectiveModules/Category/FiniteProjective.lean), [stable category](ProjectiveModules/Category/Stable.lean) | Finite biproducts, preadditive stable quotient and small-ring Ext¹ detection |
| [Projective scalar towers](ProjectiveModules/Module/ScalarRestriction.lean), [finite-projective restriction](ProjectiveModules/Category/FiniteProjectiveRestriction.lean) | Projectivity through semiring towers with projective coefficients; finite-projective ring-homomorphism restriction under its canonical coefficient hypothesis, with carrier, stored-action and map-application laws, both directions of the underlying-functor comparison, and identity/composition functor laws |
| [Module-category equivalences](ProjectiveModules/Category/ModuleEquivalence.lean) | Finite-generation preservation and reflection at independent universes; canonical finite-presentation preservation with unrestricted source and target at the scalar/carrier maximum, and preservation and reflection with both carriers at their maxima; the same bounds for finite projectivity; left self-injectivity of the two rings is equivalent under any given equivalence with both carriers at their scalar/carrier maxima |
| [Noetherian objects, modules and rings](ProjectiveModules/Category/Noetherian.lean) | Canonical subobject/submodule ascending-chain bridge; Noetherian-module preservation and reflection at independent universes; left-Noetherian ring transport with target at the scalar/carrier maximum and unrestricted source, and ring iff at both maxima |
| [Submodule equivalences](ProjectiveModules/Category/SubmoduleEquivalence.lean), [length](ProjectiveModules/Category/Length.lean) | Canonical submodule order isomorphism, numerical length equality in `ℕ∞` for all modules (including `⊤`), and finite-length equivalence; arbitrary rings and independent scalar/carrier universes, without maximum-universe or finiteness hypotheses |
| [Compact elements](ProjectiveModules/Order/CompactlyGenerated.lean) | Order isomorphisms preserve and reflect compact elements of arbitrary partial orders; no completeness or top element required |
| [Finite-projective representatives](ProjectiveModules/Category/FiniteProjectiveSmallness.lean) | Derived ring-universe essential smallness at independent carrier universes; ring-sized representatives, linear equivalences and class equality in one reference skeleton |
| [Finite dimension](ProjectiveModules/Category/FiniteModuleDimension.lean) | Finite-rank representative transport; finite-free categorical isomorphism criteria over strong-rank-condition rings |
| [Finite stabilization](ProjectiveModules/Module/FiniteStabilization.lean) | Replace a finite projective common stabilizer by a common standard finite free one; no hypotheses on the two ambient modules |
| [Dual-evaluation saturation](ProjectiveModules/Module/DualSaturation.lean) | For arbitrary projective modules over commutative rings, nonzero maximal residue tensor fibers force any ideal containing all dual evaluations to be the unit ideal; no finite generation or rank-one premise |
| [Small residue rank](ProjectiveModules/Module/SmallFiberRank.lean) | Cardinal maximal-fiber rank at most one forces functional proportionality, with zero fibers allowed and no finite-generation premise |
| [Rank-one finiteness](ProjectiveModules/Module/FiniteOfFiberRank.lean) | An arbitrary projective module with cardinal rank one at every maximal residue tensor fiber is finitely generated; independent scalar and carrier universes, including zero rings |
| [Constant finite residue rank](ProjectiveModules/Module/FiniteOfFiberRank.lean), [vanishing](ProjectiveModules/Module/ZeroOfFiberRank.lean) | `finite_of_residue_rank_eq_nat` gives finite generation from constant finite cardinal maximal-fiber rank; cardinal rank zero forces the original module to be subsingleton |
| [Locally constant finite residue rank](ProjectiveModules/Module/FiniteOfLocallyConstantRank.lean), [continuity](ProjectiveModules/Module/LocallyConstantResidueRank.lean) | A projective module is finitely generated exactly when its genuine cardinal residue ranks are finite and locally constant; no uniform rank is assumed |
| [Residue rank base change](ProjectiveModules/Module/ResidueRank.lean) | For any homomorphism of commutative rings and any module over its source, scalar extension preserves Cardinal-valued residue rank at every target prime, with independent universes and no finite-generation, flatness or projectivity hypotheses; maximal-quotient fiber ranks also agree with residue ranks at the contracted prime |
| [Cyclic quotient residue ranks](ProjectiveModules/Module/QuotientResidueRankLocus.lean) | The cardinal residue rank of `R/I` is one on `V(I)` and zero off it; local constancy is equivalent to clopen `V(I)`, nonzero proper ideals in domains give non-local constancy, and ranks are compatible with pullback along ring homomorphisms |
| [Tensor and direct-sum residue ranks](ProjectiveModules/Module/ResidueRankOperations.lean) | Cardinal fibre ranks multiply under tensor products and add under arbitrary algebraic direct sums, without finite generation, flatness or projectivity |
| [Exterior base change](ProjectiveModules/ExteriorPower/TensorProduct.lean), [top exterior rank](ProjectiveModules/ExteriorPower/Rank.lean) | Degreewise scalar-extension equivalences with pure-wedge and naturality formulas, without flatness; cardinal rank `r` over a field gives rank one in exterior degree `r` |
| [Exterior surjectivity](ProjectiveModules/ExteriorPower/Surjectivity.lean), [finite support](ProjectiveModules/ExteriorPower/FiniteSupport.lean) | A map to a free module with a `Fin r` basis is surjective exactly when its degree-`r` exterior map is; finitely generated exterior powers admit finite source spans surjecting onto them |
| [Local fiber bases](ProjectiveModules/Module/LocalFiberBasis.lean) | A projective module with maximal residue cardinal rank `r` has a `Fin r` basis after localization at that maximal ideal, without a prior finite-generation hypothesis |
| [Localization and tensor products](ProjectiveModules/Localization/TensorProduct.lean) | The canonical localized-module–tensor equivalence intertwines localized maps and scalar extension, over arbitrary commutative semirings and submonoids |
| [Right regular module](ProjectiveModules/Module/RightRegular.lean) | Canonical opposite-scalar free and finite instances on the ordinary semiring carrier, including zero semirings |
| [Right-module K₀](ProjectiveModules/KTheory/K0.lean), [stabilization](ProjectiveModules/KTheory/Stabilization.lean) | Ring-sized projective class monoid and group completion; arbitrary-universe module generators, descent/universal properties, difference representatives and common finite-projective or finite-free stabilization |
| [Tensor semiring](ProjectiveModules/KTheory/TensorProduct.lean) | Canonical commutative semiring on finite-projective right-module classes over commutative rings, including zero rings; direct-sum addition, tensor multiplication, regular unit and natural casts, with independent module-carrier universes |
| [Product comparison and tensor multiplication](ProjectiveModules/KTheory/ProductRing.lean) | Regular right-module formula for arbitrary unital rings; unit and multiplication for families of commutative rings, allowing empty families and zero factors, with independent index/scalar universes; a nonfree Bool-indexed integer corner with idempotent K₀ class |
| [Tensor-product ring on K₀](ProjectiveModules/KTheory/Ring.lean) | Generic Grothendieck commutative ring on the existing K₀ group; bundled class ring homomorphism with the same whole additive map, regular unit, tensor-generator multiplication and regular-module cast formulas. The generic ring universal property permits arbitrary target rings and independent universes |
| [Tensor-semiring scalar extension](ProjectiveModules/KTheory/RingScalarExtension.lean) | `ProjectiveClass.mapRingHom` for arbitrary unital commutative rings, including zero rings; whole additive-map compatibility, arbitrary-carrier module evaluation, identity and composition |
| [Opposite-ring duality](ProjectiveModules/KTheory/Dual.lean) | Canonical additive equivalences of class monoids and K₀ over arbitrary rings; normalized right duals, inverse double-opposite transport, regular generators, completion squares and universal extension |
| [Right-module Morita invariance](ProjectiveModules/KTheory/ModuleEquivalence.lean) | Additive equivalences of projective classes and K₀ along ordinary right-module category equivalences; independent scalar/carrier universes, arbitrary-carrier representative/lift evaluation, inverse, completion and coherence laws |
| [Matrix classes and K₀](ProjectiveModules/KTheory/Matrix.lean) | Canonical additive equivalences for arbitrary rings and finite nonempty decidable indices; arbitrary-carrier right-row generators, supported inverse corners, index/height independence and completion compatibility |
| [Semisimple coordinates and simple rows](ProjectiveModules/KTheory/SemisimpleEquivalence.lean) | `KTheory.matrixBlockModuleOfRingEquiv` restricts supported right rows along a chosen finite matrix decomposition; simple-module classification at arbitrary carrier universes, coefficient endomorphism rings, natural class coordinates, integer K₀ basis and block-size regular coordinates; `IsSemisimpleRing.matrixDivisionDecomposition_simple_basis` uses a decomposition chosen from Mathlib's Wedderburn–Artin theorem, including the empty outer family |
| [K₀ scalar extension](ProjectiveModules/KTheory/ScalarExtension.lean) | Additive change-of-rings maps with arbitrary-carrier evaluation and whole-map identity/composition laws; independence of the homomorphism for division-ring sources and arbitrary ring targets |
| [Uniform rank bounds](ProjectiveModules/KTheory/RankBound.lean) | One absolute integer-rank bound for each K₀ element along any indexed unital maps from an arbitrary ring to division rings; non-surjectivity of the comparison for infinite products of division rings |
| [K₀ dimension](ProjectiveModules/KTheory/Rank.lean), [zero rings](ProjectiveModules/KTheory/ZeroRing.lean) | Dimension classifications of projective classes by ℕ and K₀ by ℤ over division rings, and bijectivity of division-ring scalar-extension maps; entire class/group collapse over subsingleton rings |
| [Locally constant module rank](ProjectiveModules/Module/RankLocallyConstant.lean) | Characteristic laws for the existing `Module.rankLocallyConstant`: linear-isomorphism invariance, zero and regular-unit normalizations, finite dependent-product and binary-product addition, tensor multiplication and arbitrary-algebra pullback, including zero rings and empty indices |
| [Rank realization](ProjectiveModules/Module/LocallyConstantRank.lean), [fibers](ProjectiveModules/Module/RankFiberDecomposition.lean), [component models](ProjectiveModules/Module/ComponentwiseFree.lean) | Locally constant ranks, commuting complete orthogonal Cartesian refinements over semirings, and conditional componentwise-free classification |
| [PID](ProjectiveModules/Module/PID.lean), [Laurent](ProjectiveModules/Module/LaurentPolynomial.lean) | Arbitrary-rank commutative PID freeness; one-variable Laurent finite-projective freeness |

`tests/ProjectiveModulesTests/ComponentwiseFreeClient.lean` and
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
`c9705889a85f85cc89d92d21372bb9bc360162c8` and Stable Range
[`c283b01ed9ebc33c7eefcdb4f3d2ca45141f469e`](https://github.com/FormalFrontier/stable-range/commit/c283b01ed9ebc33c7eefcdb4f3d2ca45141f469e),
with Group Theory
[`1ac70ea29b47262c6d365a89007bb5b1d5a1651a`](https://github.com/FormalFrontier/group-theory/commit/1ac70ea29b47262c6d365a89007bb5b1d5a1651a).
These three libraries declare the same mathlib revision and Lean `4.34.0-rc2`
toolchain as this root.
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
  Kaplansky's theorem. The paragraph “Hattori–Stallings trace map” in §II.2
  describes the finite-projective endomorphism trace and its independence
  of the chosen finite complement.
- The Stacks Project, [Tag 00NZ](https://stacks.math.columbia.edu/tag/00NZ):
  finite flat modules over local rings are free.

- Andrew Yang and Mathlib contributors, [`Mathlib.RingTheory.Idempotents`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/RingTheory/Idempotents.lean),
  for complete orthogonal idempotent families and their orthogonality-and-sum criterion.

Focused modules list mathematical references and prior formalization APIs;
[credits](docs/CREDITS.md) describe contributions and Mathlib reuse.

## License and credit

Original Formal Frontier contributions are released under
[Apache-2.0](LICENSE), with `Authors: Formal Frontier Agents` in Lean headers.
Formal Frontier AI agents developed and documented the library, including the
foundational mathematics and retained source-expression adaptations, the
stable category, exterior Sum Formula, rank and componentwise-free
constructions, semisimple endpoint, and the original Noetherian proof and
clients. Separate contributions include the Noetherian theorem’s library
adaptation, public imports and adapted documentation.
See [credits](docs/CREDITS.md)
for truthful roles and provenance. These credits do not assign copyright
ownership, assert human mathematical review or source-author endorsement,
or relicense dependency code or Weibel’s book; no book text or PDF is shipped.
The balanced-tensor and right-extension interfaces follow Formal Frontier's
foundational formalization and its maintenance; Formal Frontier contributed the
identity/composition comparisons and their pointwise unit and associativity
laws, using Mathlib's ring-homomorphism and linear-map interfaces.
The commutative-base comparisons additionally reuse Mathlib's tensor
universal property, commutation, tensor maps and module transport; their
scalar-first target follows Jujian Zhang's Mathlib change-of-rings
formalization. These tensor comparison interfaces were contributed by Formal Frontier.
The commuting-idempotent refinement follows Andrew Yang's Mathlib idempotent-family
interfaces and orthogonality-and-sum criterion.
The tensor-product K₀ ring reuses this library's projective-class tensor semiring,
Formal Frontier Group Theory's additive Grothendieck ring and universal property,
and Alex J. Best and Yaël Dillies' Mathlib completion formalization.
Scalar extension on the tensor semiring of projective classes descends these
comparisons through the existing additive class maps, following Weibel's
change-of-rings construction and Mathlib's bundled homomorphism interfaces.
