# Projective Modules

A reusable Lean library for projective and free modules, scalar extension,
exterior algebra, cancellation, local freeness, stable categories, right-module
K₀ and rank. Hypotheses vary by result; see the linked guides and declarations.
Maintained by the Formal Frontier source-maintainer team.

## Headline results

- **[Scalar determinants and functorial rank-dependent powers](ProjectiveModules/ExteriorPower/DeterminantLine/Scalar.lean).**
  Over a commutative ring, scaling any endomorphism of a finite projective module
  multiplies its canonical determinant by `Module.rankPower R P r`. This
  multiplicative scalar power is characterized on every rank fiber by the usual
  power with that fiber's rank. No constant-rank or invertibility assumption is
  needed. Canonical determinants and rank-dependent powers commute with arbitrary
  scalar extension, without flatness. The power homomorphism is invariant under
  linear equivalence and multiplies pointwise under binary module products.
  For a zero module it is one, including at the scalar zero.

- **[Schur determinants](ProjectiveModules/ExteriorPower/DeterminantLine/Endomorphism/Schur.lean).**
  For finite projective modules over a commutative ring, a block endomorphism
  whose upper-left block is a linear equivalence `e` has determinant
  `det(e) * det(d - c ∘ e⁻¹ ∘ b)`. Neither the complement nor the full block
  needs to be invertible. Varying rank and nonfaithful modules are allowed;
  finite bases identify the scalar determinant with the block matrix determinant.

- **[Determinants in short exact sequences](ProjectiveModules/ExteriorPower/DeterminantLine/Endomorphism/ShortExact.lean).**
  For a short exact sequence `0 → P → M → Q → 0` of finite projective modules
  over a commutative ring and compatible endomorphisms, the determinant on `M`
  is the product of the determinants on `P` and `Q`. No equivariant splitting
  or invertibility assumption is needed. An invariant finite projective submodule
  with finite projective quotient gives the restriction/quotient formula.

- **[Tensor determinants](ProjectiveModules/ExteriorPower/DeterminantLine/Tensor.lean).**
  For finite projective modules over a commutative ring, the determinant of a
  tensor product of arbitrary endomorphisms is the product of the cross
  rank-dependent powers of their determinants. Tensor products compose the
  multiplicative scalar powers. Neither constant rank nor invertibility is needed.

- **[Exterior-power coproduct](ProjectiveModules/ExteriorPower/Coproduct.lean).**
  Over an arbitrary commutative ring and arbitrary modules, the homogeneous
  coproduct maps have coefficient-one signed coshuffle formulas, commute with
  linear maps, and satisfy graded symmetry and associativity. The degree-zero
  and exterior-square formulas include the zero ring and characteristic two.

- **Finite consistency of row-finite linear systems.** For a ring `R` and any
  left `R`-module `M` satisfying `Module.Baer R M`, a system with finitely
  supported coefficient rows has a full solution whenever every finite set of
  rows has a solution (`Module.Baer.exists_solution_of_finite`). Over a semisimple
  ring, this is equivalent to finite consistency for every left module
  (`Finsupp.exists_solution_iff_finite`), hence applies to division rings and
  real vector spaces. The scalar, target, row and coordinate types have
  independent universes; no countability or dimension bound is required.
  Solutions are arbitrary coordinate functions, not finitely supported
  functions, and the assignments for finite subsystems need not be compatible.
  See [`Module.FiniteConsistency`](ProjectiveModules/Module/FiniteConsistency.lean)
  for the extension argument and its Mathlib formalization credits.

- **Finite orthogonal idempotent endomorphisms.** Over a possibly noncommutative
  semiring `R`, a finite orthogonal idempotent family `e` on an additive
  commutative `R`-module `M`, whose sum is the identity, gives the canonical
  equivalence `CompleteOrthogonalIdempotents.linearEquivPiRange`:
  `M ≃ₗ[R] (Π i, LinearMap.range (e i))`. Its coordinates are `e i m` and its
  inverse sums the ambient values. The API includes extensionality and
  naturality for arbitrary linear intertwiners, with no projectivity, topology,
  rank or nontriviality premise. An empty index type forces `M`, not `R`, to be
  zero. See [`Module.OrthogonalIdempotentRanges`](ProjectiveModules/Module/OrthogonalIdempotentRanges.lean).

- **[Endomorphism range ideals](ProjectiveModules/Module/EndomorphismIdeals.lean).**
  For any semiring `R` and additive commutative `R`-module `M`,
  `Module.End.rangeIdeal U` is the right ideal of endomorphisms with range
  in `U`, expressed as an ideal of `(Module.End R M)ᵐᵒᵖ`.
  `Module.End.idealRange I` is the supremum of their ranges, or equivalently
  the `R`-span of all evaluations. These form a Galois connection:
  `idealRange I ≤ U ↔ I ≤ rangeIdeal U`. The principal right ideal generated
  by any endomorphism evaluates to its range. Scalar and module universes
  are independent; neither additive inverses nor finiteness, projectivity,
  commutativity or full invariance of `U` is assumed. This is not an
  unrestricted lattice equivalence.

- **[Simultaneous idempotent conjugation](ProjectiveModules/RingTheory/IdempotentConjugation.lean).**
  Let `R` be any ring, `ι` a finite index type, and `a b : ι → R` two
  orthogonal idempotent families with `b i - a i ∈ I` for a two-sided ideal
  `I ≤ Ring.jacobson R`. The unit
  `u = OrthogonalIdempotents.conjugatingUnit ha I hI hab` has value
  `(∑ i, b i * a i) + (1 - ∑ i, b i) * (1 - ∑ i, a i)`, satisfies
  `(u : R) - 1 ∈ I`, and simultaneously conjugates `a i` to `b i`:
  `u * a i * u⁻¹ = b i`. Neither family must sum to one; noncommutative
  and zero rings are allowed, and an empty family gives the identity unit.
  The coefficient needs no orthogonality, and its unit construction needs
  only orthogonality of `a`; both families' orthogonality enters conjugacy.
  For any ring homomorphism `f`, equal-image orthogonal families admit this
  conjugating unit with `f u = 1` if `ker f ≤ Ring.jacobson R`, or if every
  element of the whole kernel is nilpotent. No surjectivity or uniform
  nilpotence exponent is required; source, target and index universes are
  independent.
  The [construction naturality API](ProjectiveModules/RingTheory/IdempotentConjugationNaturality.lean)
  sends the coefficient of arbitrary `a b : ι → R` to that of `f ∘ a, f ∘ b`
  under any unital `f : R →+* S`, without orthogonality or ideal hypotheses.
  For orthogonal `a`, `Units.map f.toMonoidHom u` equals the target constructed
  unit in `Sˣ` when the source uses a two-sided `I ≤ Ring.jacobson R` with
  `b i - a i ∈ I` for every `i`, and the target uses its own two-sided
  `J ≤ Ring.jacobson S` with `f (b i) - f (a i) ∈ J` for every `i`.
  No ideal-image containment, radical-preservation, injectivity or surjectivity
  assumption is imposed. Joint reindexing of both families by `e : κ ≃ ι`
  between finite types leaves the coefficient and unit unchanged. Only `a`
  must be orthogonal for the unit identities; `b` may be nonidempotent, so these
  are construction-transport laws, not conjugacy in that generality. Neither
  family must sum to one; noncommutative and zero rings, empty finite indices,
  and independent source, target and index universes are included.

- **Total symmetric-power series on `K0`.** For every commutative ring `R`,
  `KTheory.K0.totalSymmetricSeries` sends addition in `K0 R` to multiplication
  of units of `PowerSeries (K0 R)`. On a finite projective right module, its
  coefficients are the classes of the symmetric powers. The linear coefficient
  recovers every virtual class, and the negative regular-module class has series
  `1 - X`. This is a fixed-ring additive construction, not an identification with
  the exterior-power λ-series.

- **[Exterior–symmetric series identity](ProjectiveModules/KTheory/ExteriorSymmetricPowerSeries.lean).**
  Over every commutative ring `R` and for every virtual class `x : K0 R`,
  the exterior- and symmetric-power series satisfy
  `λₓ(-t) σₓ(t) = 1` and `λₓ(t) σₓ(-t) = 1`.
  Their coefficients on finite projective right modules are the respective
  power classes. The proof uses the homogeneous Koszul complex and its
  integer-signed Euler identity, with no freeness, constant-rank or
  characteristic assumptions.

- **[Idempotent-matrix classification](docs/HeadlineResults.md#idempotent-matrix-classification).**
  Over any semiring `R`, a right semimodule `P` is finitely generated and projective
  iff it is `Rᵐᵒᵖ`-linearly equivalent to the range of an idempotent finite
  `R`-matrix acting on `R`-valued columns by `x ↦ e *ᵥ x`, with pointwise
  right action `(MulOpposite.op a • x) i = x i * a`. No finiteness or projectivity
  is assumed in advance; scalar and carrier universes are independent, and size
  zero, zero semirings and the zero semimodule are included.

- **[Quadratic tensor exactness](docs/HeadlineResults.md#quadratic-tensor-exactness).**
  The exterior-square image is the kernel of the symmetric-square quotient over a
  commutative ring; projective modules admit a quotient section.

- **[Kernel families](ProjectiveModules/Topology/KernelComparison.lean).**
  Over an arbitrary semiring, two supplied split linear
  retractions with a common section into a fixed module with a topological
  additive-group structure have homeomorphic total kernel spaces whenever their
  ambient projection difference is jointly continuous. The section-domain modules
  may vary and need no topology. Both total spaces retain their subspace topologies
  in the parameter–ambient product. Writing `Δ = Γr - Γq`, transport is
  `(t,a) ↦ (t,a + Δ(t,a))`, with inverse `(t,a) ↦ (t,a - Δ(t,a))`.

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

- **[Finite generation and residue rank](ProjectiveModules/Module/FiniteOfLocallyConstantRank.lean).**
  An arbitrary projective module over a commutative ring is finitely generated iff
  its prime residue-field tensor ranks are finite cardinals and their
  Cardinal-valued function is locally constant. No uniform rank, finite-generation,
  finite-presentation, Noetherian or nontrivial-ring premise is needed; scalar and
  carrier universes remain independent. The rank is a cardinal, not `finrank`.
  [Rank one or any fixed natural rank at all maximal fibers](ProjectiveModules/Module/FiniteOfFiberRank.lean)
  also suffices, including rank zero and the zero ring; in rank zero the module is
  [subsingleton](ProjectiveModules/Module/ZeroOfFiberRank.lean).
  For arbitrary modules over commutative rings, the
  [residue-rank calculus](docs/HeadlineResults.md#finite-generation-from-locally-constant-finite-residue-rank)
  covers base change, cyclic quotients, tensor products and arbitrary algebraic direct
  sums, without finite generation, flatness or projectivity, with cardinal lifts for
  independent universes.

- **[Schanuel kernel comparison](ProjectiveModules/Module/KernelComparison.lean).**
  Over any semiring, supplied lifts between two linear maps from additive
  commutative groups to a common additive commutative monoid give
  `(ker p × Q) ≃ₗ[R] (ker q × P)`, with formulas retaining both lifts.
  The core needs neither surjectivity nor projectivity. For surjections from
  projective source modules, the
  [projective presentation theorem](ProjectiveModules/Module/ProjectiveKernelComparison.lean)
  obtains such an equivalence from the projective lifting property.
  The common target needs no additive inverses; all universes are independent.

- **[Noetherian and PID freeness](docs/Overview.md#noetherian-submodules-and-pid-freeness):**
  over a left-Noetherian, possibly noncommutative ring, submodules of sequence-spanned
  modules are sequence-spanned, with independent universes and no ambient Noetherian,
  free, projective or finite premise. Commutative PID freeness covers arbitrary-rank projectives
  and submodules of arbitrary-rank free modules, not general Noetherian submodules.

[Noetherian submodules](ProjectiveModules/Module/CountablyGenerated/Noetherian.lean) · [PID](ProjectiveModules/Module/PID.lean)

- **[Finite simultaneous decomposition](ProjectiveModules/Module/CommutingProjections.lean):**
  for any semiring `R`, additive commutative group `M` with an `R`-module structure,
  finite index type `I`, and supplied pairwise commuting idempotent endomorphisms
  `p : I → Module.End R M`, `LinearMap.commutingIdempotentsPiEquiv` identifies the
  original `M` with the product of all Boolean-selected intersections of the original
  ranges and kernels. Its components are the commuting products of `p i` or `1 - p i`,
  and its inverse sums the block inclusions. Zero blocks and the empty constraint
  family are retained; scalar, module and index universes are independent. No freeness,
  finite generation, finite dimension or commutativity of `R` is assumed.

- **[Unimodular contraction](ProjectiveModules/ExteriorAlgebra/ContractionExactness.lean):**
  for every quadratic form over a commutative ring, contraction by a surjective covector
  has range equal to its kernel. A vector pairing to one gives a
  [linear splitting](ProjectiveModules/ExteriorAlgebra/ContractionSplitting.lean) into two
  copies of that kernel, with explicit forward and inverse formulas. Left multiplication
  squares to the quadratic value, not necessarily to zero; no invertibility of two,
  finiteness or freeness is required.

- **[Symmetric powers](ProjectiveModules/Module/SymmetricPower.lean).**
  For arbitrary semimodules over commutative semirings,
  [concatenation](ProjectiveModules/Module/SymmetricPower/Tensor.lean) on arbitrary
  labels is natural and surjective, not generally an equivalence.
  The [binomial decomposition](ProjectiveModules/Module/SymmetricPower/Prod.lean)
  identifies every finite degree of `M × N` with the finite direct sum of tensors
  of complementary symmetric degrees, with coefficient one per labelled subset
  and naturality in both modules. Degree zero preserves the scalar unit;
  the degree-one target is ordered `N × M`.
  [Plethysm](ProjectiveModules/Module/SymmetricPower/Plethysm.lean) flattens finite
  outer and arbitrary inner labels; `Sym^p (Sym^q M) → Sym^(p*q) M` is natural
  and surjective for all natural degrees, with coefficient one on labelled grids.
  Projectivity of `M` gives a linear section, not a canonical or natural choice.
  [Base change](ProjectiveModules/Module/SymmetricPower/BaseChange.lean) along any
  commutative-semiring algebra `R → S` commutes with every finite degree, without
  flatness or projectivity; both directions have natural labelled pure-tensor
  formulas. See the [full statements and unit comparisons](docs/HeadlineResults.md#symmetric-powers).

- **[Exterior series under invertible twists](ProjectiveModules/KTheory/ExteriorPowerSeriesInvertible.lean):**
  For an invertible right module L over a commutative ring R,
  λⁿ([L]x) = [L]ⁿ λⁿ(x) for every virtual class x ∈ K₀(R) and every degree n.
  Equivalently, λ_([L]x)(t) = λ_x([L]t).

- **[Exterior twists by invertible lines](ProjectiveModules/ExteriorPower/InvertibleTwist.lean):**
  over a commutative ring `R`, an invertible module `L` and an arbitrary module `P`
  have the canonical equivalence
  `TensorPower R n L ⊗[R] exteriorPower R n P ≃ₗ[R] exteriorPower R n (L ⊗[R] P)`
  in every degree, including zero. It sends `tprod(l) ⊗ ιMulti(p)` to
  `ιMulti(fun i => l i ⊗ p i)` and is natural for arbitrary linear maps of the
  invertible lines and the other modules. Independent universes and zero rings
  are included; `P` need not be flat, finite, free or projective.

- **[Determinant lines](docs/Overview.md#determinant-lines):** for finite projective
  modules over arbitrary commutative rings, the dependent product of top exterior
  powers over attained stalk-rank fibers is invertible. Rank zero, zero rings and
  independent universes are included. `Module.DeterminantLine.congr` is the
  canonical equivalence induced by a linear equivalence, acting on each attained
  fiber in its top exterior degree. It respects identity, composition and inverses,
  and respects intertwining of arbitrary endomorphisms. Rank-fiber recovery,
  zero-module and invertible-module normalizations assert existence of linear
  isomorphisms. For any commutative `R`-algebra `S` supported on a rank fiber,
  the scalar-extended line is isomorphic to the homogeneous exterior power of
  `S ⊗[R] P` in that fiber's rank.
  The tensor product of the determinant lines of two finite projective modules
  is isomorphic to the determinant line of their product.
  The [scalar determinant](ProjectiveModules/ExteriorPower/DeterminantLine/Endomorphism.lean)
  of any endomorphism is the unique scalar inducing its action on the line.
  It is multiplicative under composition and invariant under intertwining linear
  equivalences, hence under conjugation.

- **Scalar determinants.** Over any commutative ring `R`, for a finite projective
  `R`-module `P` of possibly variable stalk rank,
  `Module.determinant R P : Module.End R P →* R` is multiplicative under
  endomorphism composition. `Module.determinant_eq_iff_map_eq_smul` characterizes
  it as the unique scalar giving the induced action on the determinant line.
  For finite free `P`, `Module.determinant_eq_det` identifies it with
  `LinearMap.det`; on the zero module its value is `1`.
  For any finite free ambient module and specified split presentation,
  `Module.determinant_eq_det_stabilization` computes this scalar as the ordinary
  determinant of the endomorphism extended by the identity on the complement.
  The retract need not be free or have constant stalk rank, and
  `LinearMap.det_stabilization_eq_of_retractions` compares different presentations.
  For arbitrary finite projective factors, `Module.determinant_prodMap` gives
  `det(f × g) = det(f) * det(g)`, even when their stalk ranks vary.
  [Linear duality](ProjectiveModules/ExteriorPower/DeterminantLine/Endomorphism/Dual.lean)
  preserves this determinant. Upper and lower block-triangular endomorphisms have
  the product of their diagonal determinants, with no condition on the off-diagonal
  block. The [unit criterion](ProjectiveModules/ExteriorPower/DeterminantLine/Endomorphism/Units.lean)
  says that an endomorphism is a unit exactly when its scalar determinant is a unit.
  None of these formulas requires freeness or constant stalk rank.
  For finite projective `R`-modules `P` and `Q` in independent universes and
  arbitrary `R`-linear maps `f : P →ₗ[R] Q` and `g : Q →ₗ[R] P`, the
  [intrinsic Sylvester identity](ProjectiveModules/ExteriorPower/DeterminantLine/Endomorphism/Sylvester.lean),
  `Module.determinant_one_add_comp_comm`, states
  `det_P(1 + g ∘ f) = det_Q(1 + f ∘ g)`. Neither module need be free or have
  constant rank; their ranks may differ, and neither endomorphism is assumed
  invertible.
  See [determinant-line endomorphisms](ProjectiveModules/ExteriorPower/DeterminantLine/Endomorphism.lean),
  [finite-free stabilization](ProjectiveModules/ExteriorPower/DeterminantLine/Stabilization.lean),
  and [product endomorphisms](ProjectiveModules/ExteriorPower/DeterminantLine/Endomorphism/Product.lean).

[Determinant lines](ProjectiveModules/ExteriorPower/DeterminantLine.lean)

- **[Characteristic polynomials](ProjectiveModules/LinearAlgebra/Charpoly/CayleyHamilton.lean):**
  for an endomorphism `f` of a finite projective module over any commutative ring,
  `Module.charpoly R P f` is the determinant over `R[X]` of the universal scalar
  pencil `X • id - f.baseChange R[X]`. Evaluation in every commutative algebra and
  arbitrary scalar extension are characterized by `Module.eval₂_charpoly` and
  `Module.charpoly_baseChange`; the finite-free construction agrees with Mathlib's.
  `Module.aeval_self_charpoly` gives Cayley–Hamilton in the endomorphism ring,
  without a faithfulness assumption. Varying ranks and zero rings are included:
  the polynomial need not be monic, and on the zero module it is `1`.
  The [unit and spectrum criteria](ProjectiveModules/LinearAlgebra/Charpoly/Spectrum.lean)
  give `IsUnit ((Module.charpoly R P f).eval r) ↔ IsUnit (r • 1 - f)`.
  Thus the algebraic spectrum is the set of scalars with nonunit polynomial value,
  and `f` is invertible exactly when the constant coefficient is a unit.
  [Zero compositions](ProjectiveModules/LinearAlgebra/Charpoly/ZeroComp.lean) satisfy
  `charpoly(f) * charpoly(g) = charpoly(f + g) * charpoly(0)` whenever `f.comp g = 0`;
  no reverse-zero or commutation hypothesis is needed. As a special case,
  [complementary idempotents](ProjectiveModules/LinearAlgebra/Charpoly/Idempotent.lean)
  satisfy `charpoly(f) * charpoly(1 - f) = charpoly(0) * charpoly(1)`, with all four
  polynomials taken on the original module, without a global rank or freeness assumption.

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

- **[Tensor-image membership](ProjectiveModules/TensorProduct/Submodule.lean):** over a
  commutative ring, if `W ≤ V` has projective quotient, any jointly zero-detecting
  family `f i : A →ₗ[R] B i` detects membership in the image of
  `W ⊗[R] A → V ⊗[R] A`. This image equals the infimum of the comaps of the
  corresponding images in `V ⊗[R] B i`. The source and dependent targets are
  arbitrary modules, and the index type may be infinite or empty.

- **[Local freeness](docs/Overview.md#local-freeness):** every projective right module
  is free over a ring with a proper two-sided ideal and unit complement, with no
  generation bound. The `IsLocalRing` form permits noncommutative rings and independent
  universes; split-range assembly itself requires explicitly free increments.

[arbitrary local freeness](ProjectiveModules/Module/ArbitraryLocalProjectiveFree.lean) · [local scalar interface](ProjectiveModules/Module/LocalRing.lean)

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

- **[Product comparisons and uniform rank bounds](ProjectiveModules/KTheory/RankBound.lean):**
  the [canonical additive comparison](ProjectiveModules/KTheory/Product.lean) maps
  K₀ of any product of rings to the product of their K₀ groups. For a family of
  possibly noncommutative division rings, it is injective and its image consists
  exactly of families whose integer ranks have one uniform absolute bound.
  More generally, every K₀ element of an arbitrary ring `R` has uniformly bounded
  absolute integer ranks under any indexed family of unital maps `R →+* D i` to
  division rings. For an infinite product of division rings, the comparison is
  not surjective.

- **[Nilpotent-kernel invariance](ProjectiveModules/KTheory/Nilpotent.lean):**
  for a surjective unital homomorphism of arbitrary, possibly noncommutative rings
  with uniformly nilpotent two-sided kernel ideal, the scalar-extension maps on
  finite-projective right-module isomorphism-class monoids and on K₀
  are additive equivalences.

- **[Locally constant module rank](ProjectiveModules/Module/RankLocallyConstant.lean):**
  `Module.rankLocallyConstant R M` assigns a locally constant natural-valued
  function on `Spec R` to each finite projective left module over a commutative
  ring. It is invariant under linear isomorphism, sends subsingleton modules to
  zero and the regular module to one, adds under finite dependent products and
  binary products, and multiplies under tensor products. Arbitrary commutative
  algebra base change pulls this function back along the induced map on prime
  spectra. Scalar, module and index universes are independent; empty products
  and zero rings are included. These are module-level laws, not a class or K₀ map.

### Detailed results

[Detailed headline results](docs/HeadlineResults.md)

- [Quotients, kernels and presentations](docs/HeadlineResults.md#quotients-kernels-and-presentations)
- [Freeness, cancellation and free words](docs/HeadlineResults.md#freeness-cancellation-and-free-words)
- [Idempotents and projections](docs/HeadlineResults.md#idempotents-and-projections)
- [Exterior algebra and contraction](docs/HeadlineResults.md#exterior-algebra-and-contraction)
- [Symmetric powers](docs/HeadlineResults.md#symmetric-powers)
- [Determinants](docs/HeadlineResults.md#determinants)
- [Duality, Hom and tensor tests](docs/HeadlineResults.md#duality-hom-and-tensor-tests)
- [Traces](docs/HeadlineResults.md#traces)
- [Topology](docs/HeadlineResults.md#topology)
- [Coefficient products and right extension](docs/HeadlineResults.md#coefficient-products-and-right-extension)
- [Categories, size and length](docs/HeadlineResults.md#categories-size-and-length)
- [Right classes and K0 structures](docs/HeadlineResults.md#right-classes-and-k0-structures)
- [K0 calculations and simple types](docs/HeadlineResults.md#k0-calculations-and-simple-types)
- [Stalk rank and component models](docs/HeadlineResults.md#stalk-rank-and-component-models)
- [Tensor families and finite residue rank](docs/HeadlineResults.md#tensor-families-and-finite-residue-rank)

## Trace modulo additive commutators

[Trace modulo additive commutators](docs/HeadlineResults.md#trace-modulo-additive-commutators)

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
`import ProjectiveModules.Module.SymmetricPower` includes concatenation, the
binomial decomposition, plethysm and base change; each also has a focused module below.

For the Noetherian theorem use `import ProjectiveModules.Module.CountablyGenerated.Noetherian`;
its [guide](docs/NoetherianSubmodule.md) gives exact hypotheses and an integer-finsupp example.
For Noetherian objects and transport under module-category equivalences, use
`import ProjectiveModules.Category.Noetherian`.
This re-exports `ModuleCat.isNoetherianObject_iff` from
`HomologicalAlgebra.ShortComplex.ModuleCatNoetherian` in
[Homological Algebra](https://github.com/FormalFrontier/homological-algebra);
it is not newly proved here. Category-equivalence Noetherian transport remains local.
Prefer its named module argument `(M := ...)`; `(X := ...)` remains a deprecated
alias, while positional and saturated `@` argument order is unchanged.
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
| [Symmetric powers](ProjectiveModules/Module/SymmetricPower.lean), [concatenation](ProjectiveModules/Module/SymmetricPower/Tensor.lean) | Finite-label monomial bases and separate finite-generation, freeness and projectivity closure; natural surjective concatenation on arbitrary labels |
| [Symmetric binomial decomposition](ProjectiveModules/Module/SymmetricPower/Prod.lean) | `SymmetricPower.binomialEquiv`: finite direct sum of complementary-degree tensors for arbitrary semimodules over commutative semirings; coefficient-one subset formula, naturality in both modules and degree-zero/one comparisons |
| [Plethysm](ProjectiveModules/Module/SymmetricPower/Plethysm.lean) | `SymmetricPower.flatten` and `plethysm`: natural surjections for finite outer and arbitrary inner labels, coefficient-one grid formulas and singleton/zero-degree identities; a linear section for projective semimodules, without a canonical choice |
| [Symmetric base change](ProjectiveModules/Module/SymmetricPower/BaseChange.lean) | `SymmetricPower.baseChangeEquiv`: every finite degree commutes with a commutative-semiring algebra extension, with forward/inverse labelled pure-tensor formulas and naturality; no flatness or projectivity |
| [Exterior duality](ProjectiveModules/ExteriorPower/Duality.lean), [alternating forms](ProjectiveModules/ExteriorPower/AlternatingForms.lean) | Canonical determinant-pairing equivalence in every degree for finite projective modules over arbitrary commutative rings; ordinary-map naturality, inverse formulas along retractions and alternating-form representation, with independent universes |
| [Contraction calculus](ProjectiveModules/ExteriorAlgebra/Contraction.lean), [exterior contractions](ProjectiveModules/ExteriorPower/Contraction.lean) | `CliffordAlgebra.contractLeft_mul`, `ExteriorAlgebra.map_contractLeft`, `exteriorPower.contractLeft`: twisted product rule, arbitrary-map naturality and canonical consecutive-degree restrictions, with square-zero and anticommutation in every characteristic |
| [Unimodular contraction](ProjectiveModules/ExteriorAlgebra/ContractionExactness.lean), [cycle splitting](ProjectiveModules/ExteriorAlgebra/ContractionSplitting.lean) | `CliffordAlgebra.range_contractLeft_eq_ker_of_surjective`, `CliffordAlgebra.contractLeftKerProdEquiv`: exactness under surjectivity and a two-kernel linear decomposition from a unit-pairing vector, for arbitrary quadratic forms |
| [Cycle-map naturality](ProjectiveModules/ExteriorAlgebra/ContractionNaturality.lean) | `CliffordAlgebra.contractLeftKerMap`, `CliffordAlgebra.contractLeftKerProdEquiv_map`: functorial maps on contraction kernels and naturality of both splitting coordinates under quadratic-form-preserving linear maps, without injectivity |
| [Cycle subalgebras and right modules](ProjectiveModules/ExteriorAlgebra/ContractionRightModule.lean) | `CliffordAlgebra.contractLeftKerSubalgebra`, `CliffordAlgebra.contractLeftKerProdEquivRight`: cycle subalgebras for arbitrary covectors and right-linear refinements of unimodular contraction splittings, recovering the base-ring splitting by restriction of scalars |
| [Homogeneous exterior base change](ProjectiveModules/ExteriorPower/BaseChange.lean) | `ExteriorAlgebra.equivBaseChange_map_exteriorPower`: image equality with the scalar-extended homogeneous submodule, for arbitrary degree and independent ring/carrier universes |
| [Invertible top exterior powers](ProjectiveModules/ExteriorPower/Invertible.lean) | `exteriorPower.invertible_of_rankAtStalk_eq`: the top exterior power of a finite projective module of constant stalk rank is invertible, without a nontrivial-ring hypothesis |
| [Exterior vanishing](ProjectiveModules/ExteriorPower/StalkRank.lean) | `exteriorPower.subsingleton_of_rankAtStalk_lt`: an exterior power of a finite flat module vanishes above all stalk ranks, for arbitrary commutative rings and independent universes |
| [Determinant lines](ProjectiveModules/ExteriorPower/DeterminantLine.lean) | `Module.DeterminantLine`: invertible for finite projective modules of variable stalk rank; canonical equivalence transport with top-exterior characteristic action, identity/composition/inverse and arbitrary-endomorphism intertwining; rank-fiber recovery, product compatibility, zero and invertible-module comparisons as `Nonempty` isomorphisms |
| [Determinant scalar extension](ProjectiveModules/ExteriorPower/DeterminantLineBaseChange.lean) | `ModuleCat.RightExtension.determinantLine_mk`: the determinant-line Picard class of a finite projective right module commutes with arbitrary ring-homomorphism scalar extension via the opposite homomorphism; no flatness or constant-rank hypothesis |
| [Free modules](ProjectiveModules/Free/CountableCancellation.lean), [infinite coordinates](ProjectiveModules/Free/InfiniteCoordinates.lean), [rank conditions](ProjectiveModules/Free/InvariantBasisNumber.lean) | Countable cancellation/absorption; finite stably-free semisimple endpoint; infinite basis cardinality and free-coordinate classification without IBN; semiring-homomorphism pullbacks of rank condition and IBN |
| [Semilinear tensor–Hom](ProjectiveModules/TensorProduct/SemilinearHomProjective.lean), [coefficient extension](ProjectiveModules/TensorProduct/SemilinearHomCoefficient.lean) | Arbitrary source semiring and commutative base: canonical tensor–Hom bijectivity for finite projective sources; coefficient extension over possibly noncommutative algebras, with explicit right-factor actions |
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
| [Noetherian objects, modules and rings](ProjectiveModules/Category/Noetherian.lean) | Canonical subobject/submodule ascending-chain bridge `ModuleCat.isNoetherianObject_iff` re-exported from `HomologicalAlgebra.ShortComplex.ModuleCatNoetherian`; local Noetherian-module preservation and reflection at independent universes; left-Noetherian ring transport with target at the scalar/carrier maximum and unrestricted source, and ring iff at both maxima |
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
| [Projective tensor powers](ProjectiveModules/TensorPower/Projective.lean) | Tensor powers preserve projectivity over commutative semirings, without a finite-generation hypothesis |
| [Tensor-power classes](ProjectiveModules/KTheory/TensorPower.lean) | The class of a tensor power of a finite projective right module is the corresponding power in K₀ |
| [Exterior series under invertible twists](ProjectiveModules/KTheory/ExteriorPowerSeriesInvertible.lean) | Tensoring any virtual class by an invertible right module rescales its exterior series; all-degree coefficient formula |
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
[`3b3810d5235d21c55ab65664618a4bd2d0df9be9`](https://github.com/FormalFrontier/group-theory/commit/3b3810d5235d21c55ab65664618a4bd2d0df9be9)
and Homological Algebra
[`1ecd25213926138278dbd661bd516de9135d944a`](https://github.com/FormalFrontier/homological-algebra/commit/1ecd25213926138278dbd661bd516de9135d944a).
These four libraries declare the same mathlib revision and Lean `4.34.0-rc2`
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
- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 17,
  for the classical linear tensor–Hom background; see the
  [semilinear comparison](ProjectiveModules/TensorProduct/SemilinearHomProjective.lean)
  for the library’s arbitrary-source-semiring formulation.
- The Stacks Project, [Tag 00NZ](https://stacks.math.columbia.edu/tag/00NZ):
  finite flat modules over local rings are free.
- N. Bourbaki, *Algebra I*, Chapters 1–3, as cited by the
  [symmetric-power base-change module](ProjectiveModules/Module/SymmetricPower/BaseChange.lean).
- Kenny Lau and Mathlib contributors, `Mathlib.LinearAlgebra.TensorPower.Symmetric`,
  for the symmetric tensor powers extended by this library.

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

## Exterior powers and scalar extension

For a homomorphism of commutative rings, extension of scalars commutes with every
exterior power of a right module. The linear equivalence
`exteriorPower.rightExtensionEquiv` preserves alternating generators, with the
extended scalar acting once outside the wedge.

The comparison uses the tensor-product description of scalar extension through
`ModuleCat.extendScalarsTensorEquiv`, which preserves elementary tensors in both
directions. For finite projective right modules,
`KTheory.K0.mapRingHom_exteriorPower` gives the resulting equality of projective
classes in every degree, without freeness, constant rank, or flatness assumptions.

## Scalar translation of characteristic polynomials

For a finite projective module over an arbitrary commutative ring,
[`Module.charpoly_sub_smul`](ProjectiveModules/LinearAlgebra/Charpoly.lean)
expresses subtraction of a scalar multiple of the identity as composition of the intrinsic characteristic polynomial with
`X + C μ`. This generalizes `LinearMap.charpoly_sub_smul` without assuming
freeness, faithfulness, or constant rank. The existing
`Module.charpoly_eq_charpoly` identifies the intrinsic and finite-free
characteristic polynomials.

## Exterior series and scalar extension

[ExteriorPowerSeriesScalarExtension](ProjectiveModules/KTheory/ExteriorPowerSeriesScalarExtension.lean)
proves that extension of scalars commutes with the total exterior series on every
virtual finite-projective class. `KTheory.K0.totalExteriorSeries_naturality` is an
equality of homomorphisms with values in units of power series. Its pointwise and
coefficient formulas use the underlying additive scalar-extension map on K₀,
including on negative virtual classes. The result extends exterior-power base
change from projective-module generators to the whole virtual group.

## Regular characteristic polynomials and stable cancellation

For a finite projective module over an arbitrary commutative ring,
`Module.charpoly_mem_nonZeroDivisors` states that its intrinsic characteristic
polynomial is regular. This permits cancellation even when varying rank prevents
monicity: over `ℤ × ℤ`, the zero endomorphism of the first projection summand has
polynomial `(X, 1)`. The canonical regularity predicate also includes the zero ring.

`Module.charpoly_eq_of_stable_intertwining` cancels the common factor arising from
a shared finite projective endomorphism. An intertwining equivalence between the
stabilized modules need not preserve the displayed summands.

### Affine changes of characteristic polynomials

For an endomorphism `f` of a finite projective module and arbitrary scalars `a`, `b`,
[affine covariance](ProjectiveModules/LinearAlgebra/Charpoly/Affine.lean) gives
`χ_(a • f + b • 1)(a * X + b) = det(a • 1) * χ_f(X)`. The multiplier is the
intrinsic determinant of the scalar endomorphism, not a single power of `a`
chosen from a global rank. Neither invertibility nor regularity of `a` is needed.
The homothety identity is also available separately. In rank zero the scalar
determinant is `1`, even at `a = 0`; on modules of varying rank the multiplier
therefore retains the rank-zero contribution.


## Coefficients of projective characteristic polynomials

For an endomorphism of a finite projective module over a commutative ring,
`Module.charpoly_contentIdeal` says that the coefficient ideal of its intrinsic
characteristic polynomial is the unit ideal. Equivalently,
`Module.span_range_coeff_charpoly` says that all coefficient values generate the
whole ring. This does not assert that an individual coefficient is a unit or
that the polynomial is monic, and allows varying rank and the zero ring.
`Polynomial.contentIdeal_eq_span_range_coeff` identifies polynomial content
ideals with spans of coefficient ranges over any semiring.

`Module.charpoly_dvd_monic` supplies a monic multiple of the intrinsic
characteristic polynomial. Regularity and the unit coefficient ideal share this
argument without a constant-rank hypothesis.
