# Native API documentation

This release contains **44 Lean files**. [API.md](API.md) records an older,
selected **43-module** native doc-gen4 run on original source
`5d1b1b276d4a11ee6ce9ae238c9511de8dbec1e9`: forty mathematical leaves,
the aggregate import root, an example module and a private regression client.
It displays 469 declaration sites and has 477 database name rows (eight of them
non-displayed private names) and 47 module-documentation positions. In
particular, `ProjectiveModules.Free.CountableCancellation` has five separate
module-documentation positions. These counts describe the historical selection,
**not** a complete inventory of the released Lean files or exported declarations.
The later `ProjectiveModules/Module/CountablyGenerated/Noetherian.lean` is the
44th file; its mathematics is described in the
[countably generated submodule guide](NoetherianSubmodule.md), not in new native
rows of this older API reference.

The historical headers and source docstrings in [API.md](API.md) retain that
run's attribution and provenance. Two `ComponentwiseFree` entries explicitly
mark source-inspected `[Finite I]` amendments to the older native `[Fintype I]`
headers; they are **not** new native records. Links point into the files in this
checkout, including corrected ranges in `ComponentwiseFree` and
`RightExtension`; printed parenthetical native database ranges remain at the
old source positions. The manifest's historical `analyzed_source_revision`,
`api_sha256`, source/native hashes and `documentation_inputs` bind the old
generation, **not** the amended Markdown or this release's current file bytes.
The fixed [inventory](../scripts/api_inventory.json) records the underlying
names, modules and ranges; its `public_display_names` field describes historical
*displayed* sites, including local-instance displays, not an exported-API census.

The original source, genuine native records, SQLite database and invocation
receipts needed to reproduce the historic binding are preserved privately with
the issue #83 evidence. They are **not shipped**, and official public release
history alone does not provide those inputs. The neutral
`source-snapshot/<commit>/<path>` identifiers are not public website links.
The distinct predecessor run for `741139c83f21c72bfac3f9395a13185806781421`
is not interchangeable with this historical source binding.

## Reproduction

This is **optional private historical reproduction**, requiring the original
`5d1b1b2` source checkout, matching documentation, genuine native records,
SQLite database and invocation receipts. None comes from the public release
alone. `--check` is not expected to match this source-amended release.

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
/absolute/analysis/api.db`. Original invocation receipts and SQLite are
preserved privately with issue #83, not shipped. Check the exact generated
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

This historical display is neither an exhaustive present-day public API nor a
proof or source-coverage certificate. Its header pretty-printer can omit
inferable types; inspect the linked Lean source for full context. The native
generator loads dependencies and is not an independent kernel proof checker.
The repaired Python controls use **synthetic** records reconstructed from this
API to test adapter behavior and refusals; they do not supply original native
data, regenerate the released API, or establish Lean evidence. Original native
and proof provenance is retained privately with issue #83 rather than repeated
as a changing acceptance ledger here.

The released root manifest pins mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`; official upstream dependency
projects may declare other mathlib revisions. Generated Markdown/JSON, the
adapted Apache-2.0 project script and authored pages are project contributions;
dependency implementations, the doc-gen4 executable, rendered HTML/assets and
Weibel's book are **not shipped**. See [credits](CREDITS.md) and the
repository [license](../LICENSE) for attribution and rights.
