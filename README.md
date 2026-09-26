# projective-modules

Reusable Lean theory of projective and free modules, duals, scalar extension,
evaluation, invertibility, and module cancellation.

Maintained by Prism on behalf of the Formal Frontier Source-maintainers team.
The status descriptions here and in `formalization.yaml` record the authoring
checkpoint **2026-09-26 19:12 UTC**, before final independent acceptance.
Subsequent review, protected-branch and publication records determine release
status; these historical descriptions do not deny a later accepted release.
The two private GitHub library pins are official upstream revisions.
This documentation accompanies source commit
`1762876bfbae6b8081b61bbd7faafe35311a4d3d` (tree
`fba4133781ebf212991e243a42904bcfe7e9d3ed`). Its pinned warning-fatal build
and complete transitive standard-axiom audit, including private declarations,
passed. Independent whole-candidate/release assessment was pending at the
authoring checkpoint; computational success alone is not acceptance.
Compilation and regression clients do not replace semantic review, complete
proof auditing, rights clearance or release promotion. See the
[native API documentation](docs/README.md) and its explicit limitations.

## Use

Use the aggregate public import, or a focused production module from the map below.
Neither use requires a source-metadata repository or private proof imports.
The designated consumer repository URL is
`https://github.com/FormalFrontier/projective-modules.git` (private access required);
At the authoring checkpoint this candidate was not yet a published GitHub release.
Internal source/evidence commits cited below are exact historical identifiers,
not claims that those objects are already present at the consumer URL.

```lean
import ProjectiveModules

example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Invertible R M ↔
      Module.Finite R M ∧ Module.Projective R M ∧
        Module.rankAtStalk (R := R) M = 1 :=
  Module.invertible_iff_finite_projective_rankAtStalk_eq_one

example (R P : Type*) [Ring R] [AddCommGroup P] [Module R P]
    (n : ℕ) (e : (P × (Fin n →₀ R)) ≃ₗ[R] (ℕ →₀ R)) :
    Nonempty (P ≃ₗ[R] (ℕ →₀ R)) :=
  ⟨Module.Free.natFinsuppEquivOfProdFinFinsuppEquiv R n e⟩
```

The two legacy-module migrations keep their definitions public but their private
implementation bodies opaque across ordinary imports. Use the exterior-algebra
generator laws instead of unfolding its private helpers. Cancellation exports the
documented `Module.Free.CountableFree` and `FiniteFree` coordinate abbreviations;
all other helper declarations remain private. This is an explicit visibility
change from the pre-module implementation, awaiting independent compatibility
review at the authoring checkpoint.

The finite-binder repair changes
`Module.componentwiseFreeModel_finite` and
`Module.componentwiseFreeModel_projective` from `[Fintype I]` to `[Finite I]`,
choosing `Fintype.ofFinite I` locally in each proof. Finiteness and, for the
projectivity theorem, idempotence are still required. A `Fintype I` supplies
`Finite I`, but the literal declaration types have changed: external clients
passing instance arguments explicitly may need adjustment. The in-tree default
clients compiled successfully; compatibility with arbitrary external explicitly
supplied instance arguments is not claimed.

## Module map

Paths are relative to `ProjectiveModules/`; the aggregate exports all production
families. `Dual/BaseChange` is reached through `Contraction/BaseChange`.

| Modules | Main interfaces |
| --- | --- |
| `Dual`, `Contraction` | `IsBaseChange.dual_of_projective`, evaluation base-change equivalence and generator laws |
| `Invertible` | Exact rank-one iff, scalar endomorphism equivalence, finite-summand cancellation |
| `ExteriorAlgebra`, `ExteriorPower` | Full algebra scalar extension; projectivity, determinants, top powers and binary direct-sum decomposition |
| `Free` | Countable cancellation/absorption and finite stably-free semisimple endpoint |
| `Module/BalancedTensor*`, `RightExtension*` | Noncommutative balanced tensor and literal-right scalar extension, quotients, free coordinates, finite residues |
| `Module/RightEndomorphismMatrix` | Column matrices and same-order composition; quasi-regular quotient reflection |
| `Module/LocalProjective*`, `ArbitraryLocalProjectiveFree` | Finite, one-element, countable and arbitrary-rank local projective freeness |
| `Module/CountablyGenerated`, `CountableCoordinateClosure`, `InvariantSupportedProjection`, `Transfinite*` | Countable spanning sequences and transfinite split-range assembly |
| `Module/ProjectiveComplement`, `HomExact` | Explicit complements and additive Hom exactness over arbitrary semirings |
| `Category` | Finite-projective full subcategory; preadditive stable category and Ext¹ detection |
| `Module/LocallyConstantRank`, `RankFiberDecomposition`, `ComponentwiseFree` | Rank realization, fiber decomposition and conditional componentwise-free classification |
| `Module/PID`, `LaurentPolynomial` | Arbitrary-rank PID freeness; one-variable Laurent finite-projective freeness over a field |

`Module/ComponentwiseFreeExamples` is internal regression material, not part of
the production aggregate. Its eight private named examples and
`tests/PublicAPIClient.lean` are built by the separate default test target.

## Scope and mathematical boundaries

The initial API proves that the dual of a finite projective module commutes
with arbitrary scalar extension. It also identifies scalar extension of the
domain of the canonical evaluation pairing with the corresponding tensor
product after base change, and proves compatibility of the evaluation maps.
Using this compatibility, the library proves that a finite projective module
of constant stalk rank one is invertible, including over the zero ring, and
packages this result as an exact characterization of invertible modules.
For an invertible module, the library also packages scalar multiplication as
a ring equivalence from the base ring to the module endomorphism ring and
shows that every endomorphism is multiplication by a unique scalar.
Exterior algebras commute with arbitrary scalar extension, without finite,
projective, flat, characteristic, or invertibility-of-two assumptions.
For every natural degree, the exterior power of a binary direct sum is
canonically the finite direct sum of the tensor products of complementary
exterior powers.  Its inverse wedges the first block before the second, and
the equivalence is natural for arbitrary module maps over the fixed base ring.
When an exterior power is invertible, the library packages the scalar by which
an endomorphism acts on it as a determinant monoid homomorphism.
For a basis indexed by `Fin n`, the top exterior power is identified with the
base ring, and this determinant agrees with `LinearMap.det`; on standard
coordinate modules and matrix endomorphisms it agrees with `Matrix.det`.
Every exterior power of a projective module is projective, without a
finiteness or rank hypothesis.
Finally, a common finite free summand can be cancelled from two invertible
modules.
Over any possibly noncommutative ring, a module whose product with a finite
coordinate module is countably free is itself countably free. This cancellation
is also exposed for arbitrary finite and countably infinite coordinate types.
Every finite stably free left module over a semisimple ring is free, including
over noncommutative and zero rings; the result also applies over opposite rings.
The countably free module also absorbs each of its direct summands; consequently,
every complemented right ideal of its endomorphism ring is absorbed by that ring
as a right module. More generally, complementary submodules of any module give
complementary right ideals of endomorphisms with the corresponding ranges, and
complementary right ideals recover complementary submodules by evaluation.
For a homomorphism of arbitrary possibly noncommutative rings, the library also
constructs the balanced tensor product and extension of scalars for right
modules.  The extension satisfies the expected extension/restriction
correspondence and preserves both projectivity and finite generation.  Its
canonical semilinear map is surjective along every surjective ring homomorphism.
For a two-sided ideal, extension along the quotient map is canonically
equivalent to quotienting a right module by the ideal action.  This
identification respects right-linear equivalences and binary products, and
transfers finite generation, freeness, and the expected product-dimension
formula to the quotient modules.
For a finite coordinate type with decidable equality, scalar extension of the
canonical finite free right module along an arbitrary ring homomorphism is
canonically the corresponding finite free right module over the target ring.
For a two-sided ideal, this identifies the module quotient coordinatewise with
the finite free module over the quotient ring.
Finite free right-module endomorphisms are identified with matrices using the
column convention, and invertibility of a specified coefficient matrix modulo
a quasi-regular two-sided ideal reflects to a right-linear self-equivalence.
These results need no commutativity, nontriviality, or centrality assumptions.
If a proper two-sided ideal has only units in its complement, every finitely
generated projective right module is finite free.  The constructed standard
basis reduces to the canonical basis of the quotient module, so its cardinality
is exactly the quotient-module finrank over the resulting division ring.
Without any finite-generation hypothesis, every single element of a projective
right module lies in a finite free direct summand.  This is exposed by a split
injection from a finite standard coordinate module whose range contains the
chosen element.
Under the same proper-two-sided-ideal/unit-complement hypotheses, every
countably generated projective right module has a basis indexed by a countable
disjoint union of finite types and is therefore free.  This result allows
noncommutative rings, rank-zero blocks, and the zero module.
For an endomorphism of an arbitrary standard free module, every countable set
of basis coordinates is contained in a countable coordinate summand preserved
by that endomorphism.  This closure theorem requires no countability of the
ambient basis and no idempotence assumption.
These countable closures also assemble along a chosen well-order into a
continuous coordinate filtration preserved by the endomorphism.  Each stage
adds only countably many coordinates, while the completed stages cover an
arbitrary, possibly uncountable, basis index type.
For an idempotent endomorphism, nested invariant coordinate supports induce a
canonical split inclusion between their supported range pieces.  Its kernel is
projective, and it is countably generated whenever the coordinate difference
is countable.  Thus every increment in the well-ordered filtration has both
properties and comes with an explicit product decomposition.
If every such split increment is free, the increments assemble as an internal
direct sum and the full range of the idempotent is free.  This transfinite
assembly theorem is independent of local-ring, countability, and
finite-generation hypotheses.
Consequently, under the same proper-two-sided-ideal/unit-complement hypotheses,
every projective right module is free, with no rank, generation, countability,
or commutativity assumption added. The proper-ideal/unit-complement hypotheses
already imply a nontrivial coefficient ring; they do not provide a zero-ring case.
The balanced tensor product is functorial in both variables.  Tensoring a short
exact sequence of left modules with a projective right module preserves
injectivity, exactness at the middle term, and surjectivity, over an arbitrary
possibly noncommutative ring.
Every surjection onto a projective module also gives an explicit decomposition
of its domain as the product of the target and the kernel.  In particular, a
projective module has an `n`-element spanning family exactly when it is a direct
summand of the standard free module of rank `n`.
The finitely generated projective modules over an arbitrary ring are packaged
as a full subcategory of the module category.  This category inherits finite
biproducts, and the same construction over the opposite ring gives the category
of finitely generated projective right modules.
Every locally constant natural-valued function on the prime spectrum of a
commutative ring is realized as the full stalk-rank function of a finite
projective module.  The construction also supplies a finite projective
complement and an explicit equivalence of their product with a finite standard
free module.
Conversely, every finite projective module decomposes canonically over the
finitely many nonempty fibers of its stalk-rank function.  The associated
clopen idempotents identify the base ring with the product of the component
rings, each base-changed component has constant stalk rank, and their product
recovers the original module after restriction of scalars.
Finite projective modules which are explicitly finite free on a complete
orthogonal idempotent decomposition are packaged by the isomorphism-invariant
`Module.ComponentwiseFree` predicate.  Such modules are classified up to
linear equivalence by their locally constant stalk-rank functions.  The
threshold-ideal realization of every locally constant rank is proved to have
an explicit component model, and the resulting classification is also exposed
as an equivalence from the skeleton of the componentwise-free full subcategory.
Over an arbitrary semiring, postcomposition on linear Hom spaces preserves an
injective/exact/surjective triple when the fixed domain is projective; the Hom
spaces are treated additively, so no commutativity or finiteness hypothesis is
needed.
Over an arbitrary possibly noncommutative ring, module morphisms modulo those
factoring through projective modules form a preadditive stable category.  Two
morphisms have the same stable image exactly when their difference factors
through a projective; projective direct summands may be added or deleted up to
stable isomorphism.  When the ring is small in the module universe, this same
criterion is detected by precomposition on first `Ext` groups with every
coefficient module.
The one-variable Laurent polynomial ring over a field is a principal ideal
ring.  Hence every finitely generated projective module over it is free, both
in the ordinary commutative presentation and in the literal opposite-ring
presentation of right modules.
Over any commutative principal ideal domain, every submodule of an
arbitrary-rank free module is free.  Consequently every projective module over
such a ring is free, with no finite-generation or cardinality hypothesis.

This repository is organized around source-independent algebra. Interpretation,
provenance, correspondence, and coverage for motivating sources remain in their
source-metadata repositories. Prism is responsible for the initial integration
on behalf of the Source-maintainers team.

Internal development discussion: `#projective-modules` (not a public contact link).

## Build

The exact Lean toolchain is in `lean-toolchain`, and `lake-manifest.json` pins
the complete dependency graph. Run:

```sh
lake exe cache get
lake build
```

The default builds both `ProjectiveModules` and `ProjectiveModulesTests`.
The latter checks ordinary aggregate imports, the existing example module,
independent universes, the no-hidden-instance rank-one iff, characteristic two,
degrees zero/one, empty coordinates, literal-right multiplication order, and the
stated hypotheses on the local/PID/Laurent/semisimple/category endpoints.

```sh
lake --wfail build ProjectiveModules
lake --wfail build ProjectiveModulesTests
lake env lean -DwarningAsError=true tests/PublicAPIClient.lean
```

The pinned graph is Lean `v4.34.0-rc2`, root mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, official private GitHub
general-linear-groups `1f8fd3e39080be39586ea22fa56c157167eefd00`, and
official private GitHub stable-range
`9ac79cf93ac2d7f3e22c660100a65592df5ac976`; see the complete manifest
for all eight unchanged ancillary pins. Both upstream projects **declare**
mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103` while this root
**resolves** `83abb3e776bdefcbc447a1e44d0debe4010039e5`. The upstream
consumers' successful builds do not transfer to this different effective graph;
the checks below directly exercise the actual Projective graph. Do not remove
pins or silently upgrade dependencies to obtain a passing build.

The unaccepted official-dependency source checkpoint
`741139c83f21c72bfac3f9395a13185806781421` and its documentation candidate
`9d8591e6d0d72e3298c89d1b86744512fe65324e` precede the separate source-only
coordinate-stage successor `5d1b1b276d4a11ee6ce9ae238c9511de8dbec1e9`.
At that coordinate-stage source, on 2026-09-26, fresh `lake exe cache get`
succeeded for the unchanged exact manifest, followed by warning-fatal builds
of both default targets (2,803 jobs,
all 43 Lean files). Fresh native doc-gen4 generation covered all **43 modules**;
its **469 displayed names**, **477 SQLite name rows**, and **47 module-documentation
ranges** are bound to that source in [docs/api-manifest.json](docs/api-manifest.json).
The additional eight SQLite names are non-displayed private rows, not discarded
module records. The forty mathematical leaves, aggregate, eight-example module
and private aggregate client are all included. Detailed original command
receipts, raw native SQLite and module records belong to the separate
`worker-a/coordinate-recursor-successor-evidence-20260926` branch. The earlier
native run and its evidence remain historical, not relabeled as new results.
The native manifest and records remain bound only to that historical source.
Compared with it, four Lean files change through `1762876`: two
`ComponentwiseFree` theorem binders and their proof expressions, and proof
expressions in `ExteriorPower/DirectSum`, `RightExtension` and
`TransfiniteRangeBasis`. The current [API](docs/API.md) separately labels its
source-inspected binder and source-link corrections; these are not a new native
run. Native regeneration is optional, not a release prerequisite.

The first warning-fatal build of `f22009d4f35fb5280add0063732c2c6da57ff112`
failed at `RightExtension.lean:266` (semilinear hom application) and reported
`letI` lints at `ComponentwiseFree.lean:110,120`. Prism's `1762876` repairs
those expressions without changing theorem statements or dependency pins.
The repaired source passed `lake --wfail -KwarningAsError=true -v build`
(2,803 jobs) and the explicit root/ComponentwiseFreeExamples/PublicAPIClient
build (2,802 jobs), both with exit zero and no warning/error diagnostics.
The complete direct `Lean.collectAxioms` audit passed all 43 modules and
1,202 logical declarations, including private helpers and tests, with only
`propext`, `Classical.choice` and `Quot.sound`. The 268 runtime code-generation
names contribute no additional kernel constants. Exact eleven pins and source
inputs were unchanged. The compact private evidence is projective-modules
commit `7da46c6ed68d856cf4dfa320d99521bd8af1d509`,
`release-checks/1762876-build-axioms/REPORT.md` (not a library dependency).
Current computational prerequisites are an **actually applicable pinned build**
and a **complete transitive standard-axiom audit including private declarations**.
Historical stored-proof replay, fresh native docgen and repeated consumer builds
are not additional gates. Consolidated independent review, rights assessment
and authorized release remain separate decisions. The two official private GitHub
dependency pins are present, but their effective compatibility, availability to
authorized consumers, rights and final Projective public-lineage suitability
require exact-candidate review; the historical source commits are not substitute
GitHub release refs.

A historical clean-project baseline on the readiness author's Hive runtime
(2026-09-25), after matching cache retrieval and `lake clean projective-modules`,
took **64.27 seconds
wall time** for `LEAN_NUM_THREADS=2 lake --wfail build` (2803 Lake jobs,
43 tracked Lean files: forty mathematical leaves, the aggregate root, the
ComponentwiseFreeExamples client and the default PublicAPIClient). Dependencies
remained precompiled; this is not a cold-toolchain or full dependency rebuild,
nor a hard process/memory bound.
That prior author verification is recorded in the internal readiness issue #83;
draft attempts and inherited compatibility options are disclosed there.
`-T0` disables Lean's declaration timeout; it is not
trust-zero or an independent stored-proof audit. That 2026-09-25 historical
run used **different development dependency revisions** and is not a proof or
compatibility result for this new graph.

The earlier unamended native/private census found **1,206** raw occurrences,
1,184 with stored bodies. Its maintained checker refused at index 1 in
`Module/CountableCoordinateClosure`:
`_private.ProjectiveModules.Module.CountableCoordinateClosure.0.LinearMap.coordinateStage._unsafe_rec`
was a **partial generated runtime definition with a body**. That historical
session remains incomplete. For source `5d1b1b276d4a11ee6ce9ae238c9511de8dbec1e9`,
a fresh unfiltered census found **1,202 raw occurrences, 1,180 stored bodies and
22 non-bodies** across all 43 modules, with no partial, unsafe or quotient class. The unchanged
maintained checker examines each raw declaration's imported-private TYPE+VALUE
transitive allowed-axiom closure, pretarget replay and stored bodies; all 1,180
stored bodies rechecked, and all seven adverse controls refused for their specified
reasons. Five direct `#print axioms` probes, including
`LinearMap.exists_countable_invariant_supported`, report only `propext`,
`Classical.choice` and `Quot.sound`. These are author verification, not independent
whole-candidate review, source coverage, rights/public-history clearance or
first-release acceptance; no checker or visibility waiver was made. They do not
establish a pass for `f22009d4` or `1762876`. This stored-proof replay is
historical evidence, not a required new release check; affected declarations
are covered by the complete applicable transitive axiom audit above.

## Limitations

Full exterior-algebra base change is not a fixed-degree scalar-extension API.
The binary fixed-degree direct-sum theorem is natural over a fixed ring, not a
replacement for that missing bridge. Rank classifies the explicit componentwise-free
predicate, not all finite projectives. The stable category is preadditive, not
asserted abelian; Ext¹ detection retains its universe-smallness hypothesis.
Countable cancellation does not assert arbitrary cancellation. Semisimple freeness
requires both finite and stably free. The Laurent endpoint is one variable over a
field, not multivariable Quillen–Suslin. Each declaration is authoritative about
its hypotheses; source coverage is maintained separately.

## License, provenance and AI involvement

Original Formal Frontier contributions are available under [Apache-2.0](LICENSE)
under the standing project authorization clarified by operator decision #13158
(an internal record, not a public link).
**Authors: Formal Frontier Agents.** Authorization and contributor attribution are
not assertions of a named copyright holder. Unsupported project-generated ownership
labels have been corrected in this candidate with their origin/history preserved;
this does not remove any identified third-party notice. Author checks report the
pinned copyright-format diagnostics on the truthful headers; no ownership claim
is invented to pass that check. The narrow truthful-header convention has an
independent disposition; the literal lint diagnostics remain nonpassing.
Likewise, the 49 private regression theorems in `tests/PublicAPIClient.lean`
have a narrowly accepted private-module convention, not a literal lint pass.
Neither disposition accepts other diagnostics or the whole release.

This library was developed by AI agents. Prism authored the foundational and
noncommutative/local/PID work, reviewed/integrated later contributions, and authored
this readiness unit. Additional worker contributions are attributed by actual
execution, not just pooled service identity:

| Contribution | Author commit | Actual Task / execution UID |
| --- | --- | --- |
| Semisimple endpoint, worker-a | `d45dd1357bacb64b950f2094d7c4212afd0ffb70` | `hive-request-d7224458a14af4b7440bd94d9777e86a0db1b5d0` / `399bbc83-2562-438d-9d01-4dac0bccd94c` |
| Stable category/Ext, worker-b | `a9b8600bcf758ebbd40cd7f90b1357722e10cbaf` | `hive-request-5c07d0c3cd2e227797162d37387f8a03e2d1f3e6` / `6a5605b3-f4b8-4f97-9be0-14f464e17b16` |
| Locally constant rank, worker-b | `c2f6629480970392ccbd8ca9486ae72bfdcacd24` | `hive-request-ad46d1502ddb687df0f8f99137470c1a4c23ac58` / `11940340-c8a1-4ea9-af20-7faea8886859` |
| Rank fibers, worker-a | `09b084714cb7a2baee194e8b5b8a4dd6abc6dc71` | `hive-request-fb505ab2a5fe64f01fbe0ac730ab345706adbd08` / `f96d1f45-b072-4402-98cd-4f1140793488` |
| Componentwise classification/examples, worker-a | `af19441303f2cacda14f9a03eb137488db7843a9` | `hive-request-70aa82000140d686d99ea82d298e809aefcf9683` / `ba211454-5a4c-4bd7-beef-f963adcfb317` |
| Exterior direct sum, worker-b | `db77a4c278a64bbbd0bf97b46c4cb08675618e13` | `hive-request-b0d122b4c4e1959f47e5cd0cefd863380123726d` / `694d0d15-fb65-4c2d-bad1-ae1aab3ee612` |

This README-only origin/credit correction is by worker-b Task
`hive-request-7b3ba4c1b0c704bd9407edac4d9a3e7e15d546c1`, UID
`fd5f19a2-4d9d-403d-a3ad-e6668bc1742c`; it does not attribute earlier
Lean development to that execution. This documentation-only assembly by
worker-b Task `hive-request-9bdf3d9592d72b8f32a93c03aa093f9e3d3d46d7`,
UID `cee7bd20-464d-4fcb-a94e-24a3fdae6f42`, reconciles metadata and prose
without changing the mathematical or client source files; it is not reviewed
or a release.

The coordinate-stage expression-only source amendment at
`5d1b1b276d4a11ee6ce9ae238c9511de8dbec1e9` and its fresh native
documentation/proof-binding successor are by worker-a Task
`hive-request-5039fb5a4edbcc012c1fa476bd82a1f7ff3e6897`, UID
`bea0dd73-0600-46f0-b6d8-9ebb494b6931`. This execution does not claim
Prism's earlier mathematics or the prior worker's native documentation.

The later exterior projection `cdot` syntax repair at
`d3f7d0338e7e58202bb9baa9156a32bf75128c76` is by worker-a Task
`hive-request-6169580853394aa779febb4ea343c4b3c0e8eb06`, UID
`032d8e86-d444-4fd6-83cc-f26b3c258d2e`. The finite-binder and focused proof
repairs at `f22009d4f35fb5280add0063732c2c6da57ff112` are by worker-a Task
`hive-request-9f2456b974744fa66da59ce58144f50db8b4d6b8`, UID
`fec00aa2-2c65-42aa-91df-628c099c9157`. These are source contributions, not
completed candidate checks. Prism authored the subsequent source-only diagnostic
repair `1762876bfbae6b8081b61bbd7faafe35311a4d3d` and documentation draft
`03e494996a84fda2a4988715c6bdb5e526af12f7`. The current lightweight
documentation assembly and source-inspected API corrections are by worker-a Task
`hive-request-cd60aa62dac1faaf3664d5588c99b0c5cc895da8`, UID
`c6b3e41b-9228-4074-b620-68ec2aa67ba3`; no native output is claimed.

Task names, full file history, source-expression predecessors and notice inventory
are in the internal FormalFrontier/projective-modules issue #83 (not a public URL).
Mathematical motivation includes Weibel's *The K-book* (2013), Chapter I on
projective modules, local freeness, rank and exterior powers. The internal
right-endomorphism matrix diagnostic was generalized by Prism to arbitrary finite
index types: `WeibelKBook/Experiments/ExampleI212IdempotentMatrixDiagnostic.lean`
lines 97–102 and 106–109 share expression with
`ProjectiveModules/Module/RightEndomorphismMatrix.lean` lines 64–69 and 73–76
in this unaccepted candidate.

Further internal Lean-expression predecessors are retained at
`FormalFrontier/source-weibel-k-book@4cd8df74596bae9a81bb4515cde0165f3b02eb46`.
The following source/target locators refer to that source revision and to this
unaccepted ordinary candidate; they identify expression, not book coverage:

| Retained diagnostic under `WeibelKBook/Experiments/` | Shipped module under `ProjectiveModules/` | Shared source lines → candidate lines |
| --- | --- | --- |
| `ExerciseI17AbsorptionDiagnostic.lean` | `Free/CountableAbsorption.lean` | 44–64 → 91–111; 252–255 → 335–338 |
| `ExerciseI17SplitDiagnostic.lean` | `Free/CountableAbsorption.lean` | 55–59 → 67–71; 62–66 → 72–76; 77–83 → 85–91 |
| `ExerciseI19Diagnostic.lean` | `Free/CountableCancellation.lean` | 34–39 → 51–56; 123–133 → 140–150; 146–154 → 163–171; 186–191 → 203–208; 206–212 → 223–229 |
| `ChapterI3ExteriorPowerSumBoundaryDiagnostic.lean` | `ExteriorPower/DirectSum.lean` | 64–80 → 53–69; 64–68 → 77–81 (second occurrence) |

Prism retained the three Free diagnostics in Git commit
`51f3446a0bec5761579bad19fac7710fe2dfce4a` and the exterior diagnostic
in `685437ff1d89bef5d5568360dadd8407ce2391b5`, then contributed the
Free-module adaptations in `a538ed70d53bcbe3edb5644d3eef7e1ce4971559`
and `2d3cb57fb141b685cf12a2809cc70565118393a3`. The later exterior
direct-sum development belongs to PR82 worker-b Task
`hive-request-b0d122b4c4e1959f47e5cd0cefd863380123726d`, UID
`694d0d15-fb65-4c2d-bad1-ae1aab3ee612`, at
`db77a4c278a64bbbd0bf97b46c4cb08675618e13`. Retention and accepted Git
order do not establish original pre-Git drafting or a direction of copying.
The accepted mathematical exposition at source revision
`7f5d5cb3bcb9d8e964223e5fb770fe41ecc30e64`,
`expositions/exterior-power-direct-sum.md`, motivates the exterior construction;
it is neither the Lean-expression predecessor nor a checked production proof.
No book text or PDF is shipped, and citation/access is not a redistribution grant.

Formal dependencies are the pinned mathlib, general-linear-groups and stable-range
APIs. Their implementations and notices remain in their owning projects, not
copied into this repository as dependencies' source files. AI generation, builds,
citation and the license file are not independent origin/rights clearance. Any
actual third-party uncertainty must be resolved before release. New Markdown API,
JSON manifests/inventory and adapted binding script are original project
contributions with the explicit delta in [docs/CREDITS.md](docs/CREDITS.md);
no doc-gen HTML/JS/CSS or external source assets are shipped. Applicability and
proposed public history still require independent rights review, not an
automatic consequence of the earlier accepted 50-file rights disposition.
