# Credits and provenance

Projective Modules is an AI-agent-developed Formal Frontier library. Prism
contributed the original base-change, evaluation, invertible, exterior-algebra,
determinant, right-extension, cancellation, local and PID freeness and exactness
work; maintained the shared library; retained mathematical diagnostics; adapted
the Free-module constructions; and made subsequent diagnostic and documentation
repairs. Other Formal Frontier contributors developed the mathematical results
listed below; responsibility for maintenance and review is shared with the
source-maintainer team. Their original mathematical contributions are distinct
from later transfer, adaptation, integration and documentation work.

| Mathematical contribution | Original contribution |
| --- | --- |
| Finite stably-free semisimple modules | Formal Frontier agent contributing the semisimple endpoint |
| Preadditive stable module category and Ext¹ detection | Formal Frontier agent contributing the stable-category construction (not Prism-authored) |
| Locally constant rank realization | Formal Frontier agent contributing the realization construction |
| Rank-fiber decomposition | Formal Frontier agent contributing the decomposition |
| Componentwise-free models, classification and examples | Formal Frontier agent contributing the componentwise-free development |
| Fixed-degree binary exterior-power Sum Formula | Formal Frontier agent contributing the direct-sum construction, separately from Prism’s retained exterior diagnostic |
| Countably generated submodules over left-Noetherian rings, the detailed guide and two private integer-finsupp client expressions | Formal Frontier agent contributing the original proof and clients; a separate contribution later transferred the theorem into this library, wired public imports and adapted documentation |

The documentation and metadata were assembled and corrected in subsequent
contributions. One contributor adapted the historical native API generator and
its database/range bindings from a Stable Range project script; another made
an expression-only recursion repair and bound native documentation to that
particular source. Separate contributions repaired exterior syntax, finite
binders and focused proof expressions; Prism repaired the later diagnostic
source and drafted updated documentation; a subsequent contributor assembled
that documentation and made source-inspected historical API corrections.
These are not claims that documentation authors produced the earlier proofs,
or that the Noetherian destination assembler wrote the original theorem.

Prism retained finite matrix, free-module absorption/cancellation and exterior
sum diagnostics in the Weibel K-book source-research repository. Identifiable
Lean expression from these diagnostics was adapted into the corresponding
projective-modules developments; the exterior direct-sum result was separately
developed by another agent. The source citation describes mathematical
motivation, not the origin of every Lean expression. Retained expressions and
Git order do not resolve pre-Git drafting chronology or an undocumented
copying direction. See the original repository histories and the owning source
research record for exact internal correspondences; these credits do not
establish source coverage.

The historical [API index](README.md) links generated Markdown and a JSON
manifest whose native source predates the Noetherian module. Documentation,
manifest and project-specific generator adaptations are project contributions;
the generator was adapted from a project script, not from doc-gen code or
assets. The Lake manifest records
dependency versions; mathlib, General Linear Groups and Stable Range code and
notices remain in their own repositories.

Project contributions use [Apache-2.0](../LICENSE) and the truthful
`Authors: Formal Frontier Agents` headers. Weibel’s book is cited as a
mathematical source; no book PDF, page excerpt or third-party implementation is
redistributed here. AI involvement, a bibliographic citation and project
licensing do not establish copyright ownership, human review, source-author
endorsement, permission to relicense third-party content or complete
formalization of the book.
