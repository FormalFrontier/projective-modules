# Native API documentation

This documentation draft on source `1762876bfbae6b8081b61bbd7faafe35311a4d3d`
inherits **historical** native output for `5d1b1b2`. The two changed finite
binders and affected source links in [API.md](API.md) are labeled
**source-inspected amendments**, not new native records. No fresh docgen run is
claimed or required as a computational release prerequisite.

The [countably generated submodule guide](NoetherianSubmodule.md) is new
source-authored documentation for the 2026-09-29 transfer candidate. Its
theorem and ordinary client are **outside** the historical 43-module,
469-display, 477-database-row native output described here. This addition
does not regenerate or rebind the historical API inventory.

[API.md](API.md) contains native doc-gen4 display signatures, attached Lean
docstrings, and checkout-relative source links for the frozen source/dependency
checkpoint `5d1b1b276d4a11ee6ce9ae238c9511de8dbec1e9`. The pinned native run
examines **all 43 tracked Lean modules** (forty mathematical leaves, aggregate
root, eight-example module, and private aggregate client). It yields **469
display sites**, **477 database name rows** (including eight non-displayed
private rows), and **47 module-documentation ranges**. In particular,
`ProjectiveModules.Free.CountableCancellation` has five distinct module-documentation
positions; a one-range-per-module assumption is false for this source.

The exact database/record/position/start/end/source joins and full source and
pin hashes are recorded in the **historical** [api-manifest.json](api-manifest.json)
and the fixed native [inventory](../scripts/api_inventory.json). The manifest's
`analyzed_source_revision`, `api_sha256`, `documentation_inputs` and native
record/range hashes still describe the old output; they do **not** hash or
certify this amended Markdown or documentation prose. The 469 Markdown links
target checkout-relative paths; links in the two affected modules have been
checked against `1762876`, while parenthetical native database ranges remain
historical `5d1b1b2` positions. The native analysis uses neutral
`source-snapshot/<commit>/<path>` identifiers. The source checkpoint is an
unaccepted internal Forgejo commit, **not** an already published public
Projective revision or website. Original SQLite, native records, generation
commands and streams belong to the separately published issue #83 evidence
branch `worker-a/coordinate-recursor-successor-evidence-20260926`; the JSON
inventory alone does not authenticate native generation. The predecessor run
for `741139c83f21c72bfac3f9395a13185806781421` remains separate historical
evidence and is not relabeled with the new source hash.

## Reproduction

The following is **optional historical reproduction**, on a `5d1b1b2`
checkout with its matching original documentation. It is not a current-release
gate or successful regeneration claim for `1762876`. The `--check` command
intentionally will not match this source-inspected, amended checkout.

Use Lean `leanprover/lean4:v4.34.0-rc2`, tool commit
`leanprover/doc-gen4@97d4ecdfc8e09e7f511724c25e303d448de6a3db`
(tree `ebf77f3e174c145c9ca2db0df1c18a78ae87c93b`) with its committed
manifest, and the complete Projective root manifest. Fetch the matching
mathlib cache **before** building, then build both default targets:

```sh
lake exe cache get
lake --wfail -KwarningAsError=true build
```

Build the unchanged `doc-gen4` executable in its separate pinned checkout;
it does not depend on mathlib. In the Projective checkout, for **each of the
43 `module_paths` in `scripts/api_inventory.json`**, run
`lake env /absolute/doc-gen4 single --build /absolute/analysis MODULE api.db
source-snapshot/5d1b1b276d4a11ee6ce9ae238c9511de8dbec1e9/PATH`.
Create the analysis directory first, then run `lake env /absolute/doc-gen4
bibPrepass --build /absolute/rendered --none` and `lake env /absolute/doc-gen4
fromDb --build /absolute/rendered --manifest /absolute/rendered/manifest.json
/absolute/analysis/api.db`. The original 43 invocation receipts and real
`analysis/api.db` are in the evidence branch. Check the exact generated
Markdown and source-binding manifest with:

```sh
python3 -B scripts/generate_api.py --native-data /absolute/rendered/doc-data \
  --native-db /absolute/analysis/api.db \
  --source-revision 5d1b1b276d4a11ee6ce9ae238c9511de8dbec1e9 --check
python3 -B scripts/test_generate_api.py
```

Without the SQLite database, the data-only mode checks the fixed committed
range/source/native-record hashes but cannot reperform the live database joins.
The portable synthetic controls described here apply to that historical native
output; they do not authenticate the original native executable or establish
proof integrity for this amended checkout.
Source docstrings are distinguished from **missing source docstrings**; no
new authored API notes are presented as native source. Header displays are
not proof bodies or complete mathematical declarations. The native generator
loads dependencies and is not an independent kernel proof checker.

## Boundaries

All root outputs are under unchanged root mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`;
the upstream official projects declare a different mathlib revision. The
earlier unamended raw/private proof census **refused** a generated partial
runtime declaration in `Module/CountableCoordinateClosure`; that session
remains incomplete. On source `5d1b1b2`, the unchanged full raw/private
TYPE+VALUE checker rechecked 1,180 stored bodies among 1,202 occurrences in
43 modules with allowed axioms and seven applicable refusal controls.
This separate author proof evidence is not native documentation evidence or
independent candidate acceptance or a pass for `f22009d4` or `1762876`. The
first warning-fatal `f22009d4` build reported semilinear application and `letI`
lint failures. The repaired `1762876` subsequently passed the pinned warning-fatal
default/client builds and a complete43-module/1,202-declaration transitive
standard-axiom audit including private declarations; see the dated verification
checkpoint in the [README](../README.md). No new native output is claimed.
Only an applicable
pinned build and complete transitive standard-axiom audit including private
declarations are computational prerequisites; the earlier stored-body replay
is historical evidence, not an additional gate. Semantic, rights,
source-coverage and whole-candidate review were open at the authoring checkpoint;
subsequent acceptance is recorded separately. The generated
Markdown and JSON, adapted Apache-2.0 project script and authored pages are
new project contributions; dependency implementations, doc-gen executable,
rendered HTML/assets and Weibel's book are **not shipped**. See
[credits](CREDITS.md) and the issue #83 rights delta before any release.
