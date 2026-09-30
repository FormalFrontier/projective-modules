# Projective Modules

A reusable Lean library for projective and free modules, scalar extension,
exterior algebra, cancellation, local freeness, stable categories and rank.
Its results have different commutativity, handedness and finiteness assumptions;
the declarations and focused modules below specify each interface. Maintained by
Prism on behalf of the Formal Frontier source-maintainer team.

## Headline results

- **Noetherian submodules:** Over a possibly noncommutative left-Noetherian
  ring, any submodule of a module spanned by a sequence is itself spanned by a
  sequence, without assuming that the ambient module is Noetherian, free,
  projective or finitely generated. The ring and module may inhabit independent
  universes. See
  [`Module.CountablyGenerated.submodule_of_isNoetherianRing`](ProjectiveModules/Module/CountablyGenerated/Noetherian.lean)
  and the [proof and example guide](docs/NoetherianSubmodule.md).
- **Freeness over a commutative PID:**
  [`Submodule.free_of_pid_of_free` and `Module.Projective.free_of_pid`](ProjectiveModules/Module/PID.lean)
  cover arbitrary-rank free ambient modules and arbitrary-rank projectives,
  respectively. They do not turn the preceding general Noetherian theorem into
  a freeness statement.
- **Exterior constructions:** The [full exterior algebra](ProjectiveModules/ExteriorAlgebra/BaseChange.lean)
  commutes with arbitrary scalar extension; separately, the
  [fixed-degree binary Sum Formula](ProjectiveModules/ExteriorPower/DirectSum.lean)
  decomposes an exterior power of a direct sum into complementary-degree
  tensor products and is natural for module maps over the fixed ring. Neither
  supplies a fixed-degree scalar-extension theorem. The library also proves
  [projectivity of exterior powers](ProjectiveModules/ExteriorPower/Projective.lean)
  and constructs [determinants](ProjectiveModules/ExteriorPower/Determinant.lean).
- **Duality and invertibility:** The [finite-projective dual](ProjectiveModules/Dual/BaseChange.lean)
  and its [evaluation pairing](ProjectiveModules/Contraction/BaseChange.lean)
  commute with base change. The
  [rank-one characterization of invertibles](ProjectiveModules/Invertible/OfRankOne.lean)
  includes zero rings; [endomorphisms](ProjectiveModules/Invertible/Endomorphism.lean)
  are scalars. Only a [common finite free summand](ProjectiveModules/Invertible/StableCancellation.lean)
  is cancelled from two invertibles.
- **Noncommutative local freeness:** For a proper two-sided ideal whose
  complement consists of units, every projective *right* module is free,
  without a rank or generation bound. This
  [arbitrary-rank endpoint](ProjectiveModules/Module/ArbitraryLocalProjectiveFree.lean)
  assembles projective countable-coordinate filtration increments that are
  free under the local hypotheses. The [split-range assembly](ProjectiveModules/Module/TransfiniteRangeBasis.lean)
  itself requires explicitly free increments and idempotence, not just an
  arbitrary idempotent range. Properness excludes the zero ring.
- **Stable categories and rank:** [Stable module morphisms](ProjectiveModules/Category/Stable.lean)
  modulo maps through projectives form a *preadditive* category over a ring;
  the Ext¹ criterion additionally requires `Small.{uM} R`. For commutative
  rings, [locally constant stalk ranks](ProjectiveModules/Module/LocallyConstantRank.lean)
  are realized by finite projectives, and
  [rank fibers](ProjectiveModules/Module/RankFiberDecomposition.lean) decompose
  them. Classification by rank concerns the explicit
  [componentwise-free finite-projective class](ProjectiveModules/Module/ComponentwiseFree.lean),
  not every finite projective.
- **Bounded free-module endpoints:** A finite coordinate summand can be
  cancelled from a [countably free product](ProjectiveModules/Free/CountableCancellation.lean),
  and the countably free module
  [absorbs its direct summands](ProjectiveModules/Free/CountableAbsorption.lean).
  [Semisimple freeness](ProjectiveModules/Free/Semisimple.lean) requires a
  *finite stably-free* module. The
  [Laurent endpoint](ProjectiveModules/Module/LaurentPolynomial.lean)
  proves finite-projective freeness over the one-variable Laurent polynomial
  ring of a field, not multivariable Quillen–Suslin.

These are declarations of this library whose proofs reuse its pinned
[dependencies](#build); they are not presented as imported results or as
complete coverage of a motivating book.

## Use

Use `import ProjectiveModules` for the production aggregate, or import a
focused module from the [module map](#module-map). No source-research
repository is needed to use the library. The official private GitHub repository
is `https://github.com/FormalFrontier/projective-modules.git` (access required).

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

For the Noetherian theorem alone, use
`import ProjectiveModules.Module.CountablyGenerated.Noetherian`; the
[guide](docs/NoetherianSubmodule.md) gives exact hypotheses and an integer
finsupp example. Examples and ordinary aggregate-import regression clients
belong to a separate default build target, not the production aggregate.

## Module map

The aggregate exports the production modules; the paths below link directly
to representative interfaces. The dual is reached through the contraction
aggregate import.

| Area | Interfaces and scope |
| --- | --- |
| [Dual](ProjectiveModules/Dual/BaseChange.lean), [Contraction](ProjectiveModules/Contraction/BaseChange.lean), [Invertible](ProjectiveModules/Invertible/OfRankOne.lean) | Dual/evaluation base change, rank-one iff, scalar endomorphisms and finite-summand cancellation |
| [Exterior algebra](ProjectiveModules/ExteriorAlgebra/BaseChange.lean), [exterior powers](ProjectiveModules/ExteriorPower/DirectSum.lean) | Full algebra base change; projective powers, determinants/top powers and binary fixed-degree Sum Formula |
| [Free modules](ProjectiveModules/Free/CountableCancellation.lean) | Countable cancellation/absorption; finite stably-free semisimple endpoint |
| [Balanced tensor](ProjectiveModules/Module/BalancedTensorProduct.lean), [right extension](ProjectiveModules/Module/RightExtension.lean) | Right-module scalar extension over arbitrary ring homomorphisms, quotients, finite free coordinates |
| [Right endomorphism matrices](ProjectiveModules/Module/RightEndomorphismMatrix.lean) | Column convention and quasi-regular quotient unit reflection |
| [Local projectives](ProjectiveModules/Module/LocalProjective.lean), [arbitrary local freeness](ProjectiveModules/Module/ArbitraryLocalProjectiveFree.lean) | Finite, countable and arbitrary-rank right-module routes under proper-ideal/unit-complement hypotheses |
| [Countably generated](ProjectiveModules/Module/CountablyGenerated.lean), [Noetherian submodules](ProjectiveModules/Module/CountablyGenerated/Noetherian.lean), [filtration](ProjectiveModules/Module/TransfiniteRangeBasis.lean) | Sequence-span predicate, submodule theorem, invariant countable supports and split-range assembly |
| [Complements](ProjectiveModules/Module/ProjectiveComplement.lean), [Hom exactness](ProjectiveModules/Module/HomExact.lean) | Splittings and additive Hom exactness over semirings |
| [Finite-projective category](ProjectiveModules/Category/FiniteProjective.lean), [stable category](ProjectiveModules/Category/Stable.lean) | Finite biproducts, preadditive stable quotient and small-ring Ext¹ detection |
| [Rank realization](ProjectiveModules/Module/LocallyConstantRank.lean), [fibers](ProjectiveModules/Module/RankFiberDecomposition.lean), [component models](ProjectiveModules/Module/ComponentwiseFree.lean) | Locally constant ranks and conditional componentwise-free classification |
| [PID](ProjectiveModules/Module/PID.lean), [Laurent](ProjectiveModules/Module/LaurentPolynomial.lean) | Arbitrary-rank commutative PID freeness; one-variable Laurent finite-projective freeness |

`ProjectiveModules/Module/ComponentwiseFreeExamples.lean` and
`tests/PublicAPIClient.lean` are regression clients, not modules of the
production aggregate. The project’s [documentation index](docs/README.md)
links the historical generated [API](docs/API.md) and
[Noetherian guide](docs/NoetherianSubmodule.md).

## Mathematical scope

Right modules use opposite-ring actions where needed: the
[balanced tensor](ProjectiveModules/Module/BalancedTensorProduct.lean) and
[right extension](ProjectiveModules/Module/RightExtension.lean) preserve
noncommutative multiplication order. Extension/restriction, quotient and
finite free-coordinate equivalences do not assume commutativity. Tensoring
with a projective right module preserves the three steps of a short exact
sequence of left modules; [Hom exactness](ProjectiveModules/Module/HomExact.lean)
over semirings is additive rather than an unwarranted scalar-linear statement.
[Projective complements](ProjectiveModules/Module/ProjectiveComplement.lean)
split surjections and relate finite spanning families to free summands.

Over a proper two-sided ideal with unit complement, the finite and countable
right-module freeness steps reduce to a quotient division ring; the
arbitrary-rank step uses countable invariant supports of an idempotent on an
arbitrarily indexed free module. A supported range increment is projective and,
for a countable coordinate difference, countably generated; the global range
is free when its successive split increments are free. The endpoint retains
the proper-ideal/unit hypotheses, while the filtration theorem alone does
not assert that every idempotent range is free.

For commutative rings, locally constant natural-valued rank functions on the
prime spectrum are realized by finite projectives and complements. A finite
projective decomposes over finitely many nonempty rank fibers via clopen
idempotents. A componentwise-free module has an explicit finite-free model on
a complete orthogonal idempotent decomposition and is classified within that
class by stalk rank. Zero modules and empty index types remain valid where the
individual declarations permit them. `Module.componentwiseFreeModel_finite`
and `Module.componentwiseFreeModel_projective` use `[Finite I]`, with
idempotence still required by the projectivity theorem; explicit external
instance-argument compatibility with their earlier `[Fintype I]` versions is
not asserted.

## Build

The project pins Lean `v4.34.0-rc2`; `lakefile.toml` and
`lake-manifest.json` fix the dependency graph. Install the pinned toolchain and
fetch the matching mathlib cache **before** building. Both existing default
roots are built by:

```sh
lake exe cache get
lake --wfail -KwarningAsError=true build
```

The default targets are `ProjectiveModules` and `ProjectiveModulesTests`;
the latter compiles example and ordinary-import regression modules. A focused
check after the cache fetch is `lake --wfail build ProjectiveModules` or
`lake --wfail build ProjectiveModulesTests`. The root resolves mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, GLG
`1f8fd3e39080be39586ea22fa56c157167eefd00` and Stable Range
`9ac79cf93ac2d7f3e22c660100a65592df5ac976`; both latter libraries
declare an older mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`.
The effective root resolution is the first mathlib revision; do not repin
other projects to infer this graph. Dependencies are not vendored.

## Documentation limits

The [API index](docs/README.md) and [generated API](docs/API.md) describe a
**historical** native output for 43 modules at source `5d1b1b2`: 469 displayed
sites, 477 database names and 47 module-documentation ranges. Later
source-inspected finite-binder and link corrections are not a new native run.
This release includes a 44th Lean module defining the Noetherian theorem,
outside that generated API. Header-only edits likewise change source hashes
without moving declaration line anchors. The historical API is not an
exhaustive current catalogue; use the actual modules and the focused
[Noetherian guide](docs/NoetherianSubmodule.md). No successful current API
regeneration is represented here.

The full exterior-algebra base-change interface is not fixed-degree scalar
extension. Rank classification does not extend to all finite projectives.
The stable category is preadditive, not abelian; its Ext¹ test needs
`Small.{uM} R`. Countable and finite-summand cancellation are bounded, not
arbitrary cancellation. Semisimple freeness still requires finite stably-free
modules. The Laurent result concerns one variable over a field. A source
citation does not assert a source-by-source correspondence or whole-book
formalization; such accounting belongs in source repositories.

## License and credit

Original Formal Frontier contributions are released under
[Apache-2.0](LICENSE), with `Authors: Formal Frontier Agents` in Lean headers.
AI agents developed and documented the library: Prism contributed the
foundational mathematics and retained source-expression adaptations; other
agents contributed the stable category, exterior Sum Formula, rank and
componentwise-free constructions, semisimple endpoint, the original Noetherian
proof and its distinct later transfer/assembly. See [credits](docs/CREDITS.md)
for truthful roles and provenance. These credits do not assign copyright
ownership, assert human mathematical review or source-author endorsement,
or relicense dependency code or Weibel’s book; no book text or PDF is shipped.
