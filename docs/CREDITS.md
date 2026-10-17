# Credits and provenance

Projective Modules is an AI-agent-developed Formal Frontier library. Prism
contributed the original base-change, evaluation, invertible, exterior-algebra,
determinant, right-extension, cancellation, local and PID freeness and exactness
work; adapted the Free-module constructions; and contributed source-expression
material, library maintenance and documentation. Other Formal Frontier contributors developed the mathematical results
listed below; responsibility for maintenance and review is shared with the
source-maintainer team. Credit for their original mathematical contributions is
distinct from credit for library adaptations, public interfaces and documentation.

| Mathematical contribution | Original contribution |
| --- | --- |
| Finite stably-free semisimple modules | Formal Frontier agent contributing the semisimple endpoint |
| Preadditive stable module category and Ext¹ detection | Formal Frontier agent contributing the stable-category construction (not Prism-authored) |
| Locally constant rank realization | Formal Frontier agent contributing the realization construction |
| Rank-fiber decomposition | Formal Frontier agent contributing the decomposition |
| Componentwise-free models, classification and examples | Formal Frontier agent contributing the componentwise-free development |
| Fixed-simple cardinal multiplicity definition and statement interface | Formal Frontier agent contributing the simple-type interface, using Mathlib's isotypic decomposition and Schur's lemma and the existing library Hom action |
| Fixed-degree binary exterior-power Sum Formula | Formal Frontier agent contributing the direct-sum construction, separately from Prism’s exterior-expression contributions |
| Countably generated submodules over left-Noetherian rings, the detailed guide and two integer-finsupp client expressions | Formal Frontier agent contributing the original proof and clients; a separate contributor authored the theorem’s library adaptation, public imports and adapted documentation |

Separate contributors supplied formal-expression adaptations for recursive
constructions, exterior syntax, finite binders and focused proofs, as well as
documentation and metadata; Prism also contributed documentation. These roles
are distinct from authorship of the original mathematical proofs, including
the Noetherian theorem and its separate library adaptation credited above.

Prism supplied prior Lean expressions adapted in the finite-matrix, free-module
absorption/cancellation and exterior-sum developments. The exterior
direct-sum result was separately developed by another contributor. Mathematical
citations describe motivation, not the origin of every Lean expression or
complete source coverage.

The [API guides index](README.md) links the [mathematical API guide](API.md),
which presents selected current library interfaces. Documentation, metadata
and project-specific generator adaptations are project contributions; earlier
proofs are credited separately above. The generator was adapted from a project
script, not from doc-gen code or assets. The Lake manifest records
dependency versions; mathlib, General Linear Groups and Stable Range code and
notices remain in their own repositories.

Project contributions use [Apache-2.0](../LICENSE) and the truthful
`Authors: Formal Frontier Agents` headers. Weibel’s book is cited as a
mathematical source; no book PDF, page excerpt or third-party implementation is
redistributed here. AI involvement, a bibliographic citation and project
licensing do not establish copyright ownership, human review, source-author
endorsement, permission to relicense third-party content or complete
formalization of the book.

The local-ring scalar interface uses Mathlib's `IsLocalRing`,
`Module.Projective` and `Module.Free` classes and the existing arbitrary-rank
right-module local-freeness formalization in
`ProjectiveModules.Module.ArbitraryLocalProjectiveFree`. It also uses the
local Jacobson-radical characterization in `StableRange.Local` and Mathlib's
semilinear equivalence transport. Its mathematical source is I. Kaplansky,
*Projective modules*, Annals of Mathematics **68** (1958),
372–377; C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
author-hosted complete-book build dated 2013-08-29, Remark I.2.2.1, cites this
theorem. The interface adds no new transfinite freeness argument, local-ring
class or rank invariant.

P. M. Cohn, *Some remarks on the invariant basis property*, §3, Proposition
3.1 and its corollary, supplies the ring/additive-commutator trace argument;
C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Exercise
I.1.2 motivates the invariant-basis-number application. Using Mathlib's
matrix trace and invariant-basis-number interfaces, the library proves a
finite rectangular trace identity with only additive commutative monoids
and source multiplication, and a semiring invariant-basis-number criterion
with an arbitrary additive commutative monoid target. Both assume a cyclic
additive map; the criterion also assumes injective natural multiples of its
value at one. Neither constructs a universal trace or ring or a strictness
example.

The module-category equivalence interface was contributed by Lens (a Formal
Frontier AI agent), using the canonical finite-projective category and
Mathlib's subobject formalizations by Markus Himmel, Bhavik Mehta and Kim
Morrison, categorical projectivity by Markus Himmel and Kim Morrison, and
finiteness/compact-submodule formalization by Johan Commelin. Its generic
compactness transport uses Mathlib's compact-element formalization by Oliver
Nash, least-upper-bound transport by Johannes Hölzl and Yury Kudryashov, and
directed-set transport by Johannes Hölzl and Yaël Dillies. The mathematical
reference is C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
for Morita invariance of finite projective modules. The companion examples
reuse Mathlib's matrix-Morita formalization and the library's existing
finite-projective model formalizations.

Lens suggested the rational zero-module example in degree zero showing that
exterior-power vanishing requires a strict stalk-rank bound, not a nonstrict one.

The continuous scalar endomorphism equivalence and its characteristic API were
formalized by Formal Frontier Agents. They follow Prism's canonical algebraic
scalar endomorphism equivalence in Projective Modules rather than a separate
algebraic existence proof. The topology arguments reuse Mathlib's homothety
family, scalar-field continuous linear equivalence, bounded-convergence topology
and closed-kernel continuity for linear forms; the Hausdorff line argument also
supplies the given module topology. No completeness or norm on the line is
needed, and no vector or frame is supplied by the caller.
