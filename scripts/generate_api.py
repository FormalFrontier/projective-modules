#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Build the Projective Modules Markdown API from pinned native doc-gen4 data.

This fixed-library adapter checks source bytes, display identities, signatures,
docstring contents, and module records. Native generation and proof checks remain
separate evidence; a matching data file alone does not authenticate its producer.
Adapted from accepted Stable Range native/range binding, with actual module docs.
"""

import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import sqlite3
import subprocess
from urllib.parse import quote


SOURCE = "5d1b1b276d4a11ee6ce9ae238c9511de8dbec1e9"
SOURCE_TREE = "632df62dd1cd298cb08e40e2899fdca557471c32"
TOOL = "97d4ecdfc8e09e7f511724c25e303d448de6a3db"
TOOL_TREE = "ebf77f3e174c145c9ca2db0df1c18a78ae87c93b"
TOOL_MANIFEST_SHA256 = "f9a9113729ee2ccab2ac4e5f8a20420315aab7ee085a98a7c0dc8e83649e1c9b"
TOOL_EXECUTABLE_SHA256 = "d9ce1c0365c19ca90a974c5f707e1d43524f6c6b4fcf4441d2857d9164054ae9"
HERE = Path(__file__).resolve().parent
INVENTORY = json.loads((HERE / "api_inventory.json").read_bytes())
MODULE_PATHS = INVENTORY["module_paths"]
MODULES = tuple(MODULE_PATHS)
INPUTS = tuple(MODULE_PATHS.values()) + (
    "lean-toolchain", "lakefile.toml", "lake-manifest.json")
EXPECTED = INVENTORY["declarations"]
EXPECTED_MODULES = INVENTORY["modules"]
EXPECTED_MODULE_DOCS = INVENTORY["module_docs"]
DATABASE_ONLY = INVENTORY["database_only"]
SOURCE_SNAPSHOT = "source-snapshot/"
NATIVE_DATABASE_SHA256 = "efc7e92333387a5eaa2671bdf0fb79302bb6a2ed65239a5ae646f538079a08ce"
NATIVE_DATABASE_BYTES = 1589248
RANGE_MAP_SHA256 = "03f3c830a413a29a261aaf004e7011214e2249abf2ce8ec26a4ce476ecf31c9a"
DOCUMENTATION_INPUTS = (
    "README.md", "docs/README.md", "docs/CREDITS.md", "scripts/generate_api.py",
    "scripts/api_inventory.json", "scripts/test_generate_api.py", "formalization.yaml")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def canonical_record(record):
    return digest(json.dumps(record, sort_keys=True, ensure_ascii=False).encode())


def range_map():
    require(len(EXPECTED) == 469 and len(DATABASE_ONLY) == 8 and len(MODULES) == 43 and
            all(set(entry) ==
            {"display_kind", "doc_sha256", "end_line", "header_sha256",
             "kind", "line", "module", "position", "render"}
                for entry in EXPECTED.values()),
            "native range inventory structure differs")
    rows = {name: {"module": entry["module"], "position": entry["position"],
                   "start_line": entry["line"], "end_line": entry["end_line"]}
            for name, entry in {**EXPECTED, **DATABASE_ONLY}.items()}
    require(len(rows) == 477 and all(set(entry) == {"module", "position", "line",
            "end_line", "kind", "render", "sorried"} for entry in DATABASE_ONLY.values()),
            "database-only inventory differs")
    require(digest(json.dumps(rows, sort_keys=True, ensure_ascii=False).encode()) ==
            RANGE_MAP_SHA256, "native range inventory differs from DB-bound map")
    return rows


def range_binding(records, sources):
    return dict(format=1, source_revision=SOURCE, source_tree=SOURCE_TREE,
                native_database_sha256=NATIVE_DATABASE_SHA256,
                native_database_bytes=NATIVE_DATABASE_BYTES,
                range_map_sha256=RANGE_MAP_SHA256,
                displayed_ranges=len(EXPECTED), database_name_ranges=len(range_map()),
                module_doc_ranges=sum(map(len, EXPECTED_MODULE_DOCS.values())),
                source_inputs={path: digest(sources[path]) for path in sorted(INPUTS)},
                native_record_canonical_sha256={module: canonical_record(records[module])
                                                for module in MODULES})


def source_range(info, revision, path, sources):
    line_count = len(sources[path].splitlines())
    require(type(info["line"]) is int and 0 < info["line"] <= line_count,
            "invalid native source line")
    expected = SOURCE_SNAPSHOT + revision + "/" + path
    require(info["sourceLink"] == expected, "native source snapshot differs")
    require(info["line"] == EXPECTED[info["name"]]["line"],
            "native source start line differs")
    position = EXPECTED[info["name"]]["position"]
    end_line = EXPECTED[info["name"]]["end_line"]
    require(type(position) is int and position >= 0 and type(end_line) is int and
            info["line"] <= end_line <= line_count, "native source end range differs")


def verify_native_database(database, records, revision, sources):
    require(database.is_file() and not database.is_symlink(), "native database absent or linked")
    pending_wal = database.with_name(database.name + "-wal")
    require(not pending_wal.is_symlink() and
            (not pending_wal.exists() or pending_wal.stat().st_size == 0),
            "native database has unbound WAL content")
    with sqlite3.connect("file:" + quote(str(database.resolve())) + "?mode=ro&immutable=1",
                         uri=True) as connection:
        connection.execute("PRAGMA query_only=ON")
        require(connection.execute("PRAGMA integrity_check").fetchone() == ("ok",),
                "native database integrity check failed")
        modules = dict(connection.execute("SELECT name, source_url FROM modules"))
        require(len(modules) == len(MODULES) and modules ==
                {module: SOURCE_SNAPSHOT + revision + "/" + MODULE_PATHS[module]
                 for module in MODULES}, "native database module source selection differs")
        native_ranges = {(module, position): (start, end) for module, position, start, end in
                         connection.execute("SELECT module_name, position, start_line, end_line "
                                            "FROM declaration_ranges")}
        displayed = list(connection.execute("SELECT module_name, position, name, render, sorried "
                                            "FROM name_info"))
        module_docs = list(connection.execute("SELECT module_name, position, text "
                                              "FROM module_docs_markdown"))
    displayed_keys = {(module, position) for module, position, _, _, _ in displayed}
    document_keys = {(module, position) for module, position, _ in module_docs}
    require(len(displayed) == len(displayed_keys) == len({row[2] for row in displayed}) ==
            len(EXPECTED) + len(DATABASE_ONLY),
            "native database name rows missing or duplicated")
    require(len(module_docs) == len(document_keys) == 47 and
            {module for module, _, _ in module_docs} == set(MODULES) and
            all(bool(text) for _, _, text in module_docs),
            "native database module documentation ranges differ")
    require(not displayed_keys & document_keys and
            set(native_ranges) == displayed_keys | document_keys and
            len(native_ranges) == len(EXPECTED) + len(DATABASE_ONLY) + len(document_keys),
            "native database range census missing, duplicated or unclassified")
    for module, position, name, render, sorried in displayed:
        entry = {**EXPECTED, **DATABASE_ONLY}.get(name)
        require(entry is not None and module == entry["module"] and
                position == entry["position"] and render == entry["render"] and sorried == 0,
                "native database displayed name, position or kind differs")
        start, end = native_ranges[module, position]
        require(type(start) is int and start == entry["line"],
                "native database source start differs")
        require(type(end) is int and end == entry["end_line"] and
                0 < start <= end <= len(sources[MODULE_PATHS[module]].splitlines()),
                "native database source end differs")
        matching = [row["info"] for row in records[module]["declarations"]
                    if row["info"]["name"] == name]
        require((len(matching) == 1 and matching[0]["line"] == start)
                if name in EXPECTED else not matching,
                "native database display-to-record range join differs")
    require({module: sorted([row[1] for row in module_docs if row[0] == module])
             for module in MODULES} ==
            {module: sorted(int(position) for position in rows)
             for module, rows in EXPECTED_MODULE_DOCS.items()},
            "native database module documentation positions differ")
    for module, position, text in module_docs:
        start, end = native_ranges[module, position]
        require(type(start) is int and type(end) is int and
                0 < start <= end <= len(sources[MODULE_PATHS[module]].splitlines()) and
                EXPECTED_MODULE_DOCS[module][str(position)] ==
                {"start_line": start, "end_line": end, "text_sha256": digest(text.encode())},
                "native database module documentation range differs")
    raw = database.read_bytes()
    require(len(raw) == NATIVE_DATABASE_BYTES and digest(raw) == NATIVE_DATABASE_SHA256,
            "native database bytes differ from committed range provenance")


def manifest_source_binding(manifest, revision, sources, records):
    require(type(manifest.get("format")) is int and manifest["format"] == 1
            and manifest.get("docgen_revision") == TOOL
            and manifest.get("docgen_tree") == TOOL_TREE
            and manifest.get("docgen_manifest_sha256") == TOOL_MANIFEST_SHA256
            and manifest.get("docgen_executable_sha256") == TOOL_EXECUTABLE_SHA256
            and manifest.get("generator") == "scripts/generate_api.py"
            and manifest.get("analyzed_source_tree") == SOURCE_TREE,
            "unsupported provenance manifest")
    require(manifest.get("analyzed_source_revision") == revision
            and manifest.get("modules") == list(MODULES)
            and manifest.get("module_paths") == MODULE_PATHS,
            "manifest source selection differs")
    require(manifest.get("inputs") == {path: digest(sources[path]) for path in sorted(INPUTS)},
            "source/pin drift from recorded manifest")
    require(manifest.get("documentation_inputs") ==
            {path: digest((HERE.parent / path).read_bytes()) for path in DOCUMENTATION_INPUTS},
            "documentation/adapter drift from recorded manifest")
    require(manifest.get("native_range_binding") == range_binding(records, sources) and
            manifest.get("native_record_canonical_sha256") ==
            range_binding(records, sources)["native_record_canonical_sha256"],
            "portable database/range/source/native record binding differs")
    require(manifest.get("generation_commands") ==
            ["single --build", "bibPrepass --build --none", "fromDb --build --manifest"]
            and manifest.get("generation_environment") ==
            {"LEAN_NUM_THREADS": "2", "project_lake_env": True},
            "native generation options differ")


def git_source_available(root, revision):
    marker = root / ".git"
    if not marker.exists() and not marker.is_symlink():
        return False
    probe = subprocess.run(["git", "--no-replace-objects", "cat-file", "--batch-check"],
                           input=(revision + "\n").encode(), cwd=root,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(probe.returncode == 0, "cannot inspect selected Git object; refusing fallback")
    line = probe.stdout.decode().strip()
    if line == revision + " missing":
        return False
    require(re.fullmatch(re.escape(revision) + r" commit [0-9]+", line) is not None,
            "selected Git object is not a commit")
    return True


class Header(HTMLParser):
    """Retain every native visible token, including implicit parameters."""

    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.text = []
        self.kinds = []
        self.names = []
        self.feed(value)
        self.close()
        require(not self.stack, "unclosed native header")

    def handle_starttag(self, tag, attrs):
        require(tag in {"div", "span", "a"}, "unexpected native header tag")
        attrs = dict(attrs)
        require(not any(key.startswith("on") for key in attrs), "active header attribute")
        if tag == "div" and "decl_type" in attrs.get("class", "").split():
            self.text.append(" ")
        self.stack.append((tag, set(attrs.get("class", "").split())))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag,
                "unbalanced native header")
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), "text outside native header")
        self.text.append(value)
        if any("decl_kind" in classes for _, classes in self.stack):
            self.kinds.append(value)
        if any("decl_name" in classes for _, classes in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError("unexpected header comment")

    def handle_decl(self, _):
        raise ValueError("unexpected header declaration")

    def rendered(self):
        return " ".join("".join(self.text).split())


def render(records, revision, sources):
    require(revision == SOURCE, "full analyzed source revision differs")
    require(set(records) == set(MODULES) and set(EXPECTED_MODULES) == set(MODULES),
            "native module selection differs")
    require(set(sources) == set(INPUTS), "source/pin inventory differs")
    require(len(EXPECTED) == 469 and len(DATABASE_ONLY) == 8 and len(MODULES) == 43 and
            set(EXPECTED_MODULE_DOCS) == set(MODULES),
            "bounded documentation inventory differs")
    range_map()
    rows = []
    found = {}
    for module in MODULES:
        record = records[module]
        require(record["name"] == module and set(record) ==
                {"name", "imports", "instances", "declarations"},
                "native module structure differs")
        expected_module = EXPECTED_MODULES[module]
        require(record["imports"] == expected_module["imports"]
                and record["instances"] == expected_module["instances"]
                and len(record["declarations"]) == expected_module["display_sites"],
                "native module imports/instances/display-site count differs")
        for row in record["declarations"]:
            require(set(row) == {"header", "info"} and set(row["info"]) ==
                    {"name", "kind", "doc", "docLink", "sourceLink", "line"},
                    "native declaration field shape differs")
            info = row["info"]
            name, kind = info["name"], info["kind"]
            require(name in EXPECTED and EXPECTED[name]["kind"] == kind
                    and EXPECTED[name]["module"] == module,
                    "unexpected native name/kind/module")
            require(name not in found, "duplicate native declaration")
            path = MODULE_PATHS[module]
            source_range(info, revision, path, sources)
            require(info["docLink"] == "./" + module.replace(".", "/") + ".html#" + name,
                    "native self link differs")
            header = Header(row["header"])
            require("".join(header.names) == name
                    and "".join(header.kinds) == EXPECTED[name]["display_kind"],
                    "native header identity differs")
            text = header.rendered()
            require(digest(text.encode()) == EXPECTED[name]["header_sha256"],
                    "native display signature differs, including implicit parameters")
            doc = info["doc"].strip()
            require(digest(doc.encode()) == EXPECTED[name]["doc_sha256"],
                    "native source docstring differs")
            require("```" not in text and "```" not in doc,
                    "unsupported Markdown fence")
            found[name] = EXPECTED[name]
            rows.append(dict(name=name, kind=kind, header=text, module=module,
                             doc=doc, path=path, line=info["line"],
                             end_line=EXPECTED[name]["end_line"]))
    require(found == EXPECTED, "missing native declaration")
    rows.sort(key=lambda row: (MODULES.index(row["module"]), row["line"], row["name"]))
    lines = ["# Generated API reference", "",
             "Native doc-gen4 displays 469 named sites across 43 selected modules.",
             "The native database additionally retains eight non-displayed private name rows.",
             "These sites are not a raw/private/generated declaration census or proof audit.",
             "The example and private regression clients do not export their private declarations.", "",
             "Headers below are complete native *display* signatures, including implicit",
             "parameters and visible modifiers. They are not proof bodies. Pretty-printing",
             "can suppress inferable types; consult the linked source for elaboration context.",
             "Links resolve relative to this checkout, not to an unpublished GitHub commit.",
             "[Generation and limits](README.md) · [Credits](CREDITS.md) ·",
             "[source and tool manifest](api-manifest.json).", "",
             "Missing source docstrings are explicitly marked; no authored notes are passed off as native docs.", ""]
    by_module = {module: [] for module in MODULES}
    for row in rows:
        by_module[row["module"]].append(row)
    for module in MODULES:
        scope = ("aggregate public-import root" if module == "ProjectiveModules" else
                 "private regression client (not exported by the library)" if module ==
                 "PublicAPIClient" else "eight private example checks" if module.endswith(
                     ".ComponentwiseFreeExamples") else "mathematical library leaf")
        lines += ["## " + module, "", "Scope: " + scope + ".", ""]
        if not by_module[module]:
            lines += ["No native public display sites in this module.", ""]
        for row in by_module[module]:
            lines += ["### " + row["name"], "", "```lean", row["header"], "```", ""]
            if row["doc"]:
                lines += [row["doc"], ""]
            else:
                lines += ["*No source docstring is attached to this native display.*", ""]
            lines += [f"[Source](../{row['path']}#L{row['line']}-L{row['end_line']}) "
                      f"(native database range lines {row['line']}–{row['end_line']}).", ""]
    markdown = "\n".join(lines).encode()
    root = HERE.parent
    manifest = dict(
        format=1, generator="scripts/generate_api.py", docgen_revision=TOOL,
        docgen_tree=TOOL_TREE, docgen_manifest_sha256=TOOL_MANIFEST_SHA256,
        docgen_executable_sha256=TOOL_EXECUTABLE_SHA256,
        compiler="leanprover/lean4:v4.34.0-rc2 (6a10ac8c22beadecabdbb0919c2b50214762f91d)",
        analyzed_source_revision=revision, analyzed_source_tree=SOURCE_TREE,
        modules=list(MODULES), module_paths=MODULE_PATHS,
        generation_commands=["single --build", "bibPrepass --build --none",
                             "fromDb --build --manifest"],
        generation_environment={"LEAN_NUM_THREADS": "2", "project_lake_env": True},
        library_display_sites=len(rows), database_name_rows=len(EXPECTED) + len(DATABASE_ONLY),
        boundary_client_display_sites=0,
        documentation_inputs={path: digest((root / path).read_bytes())
                              for path in DOCUMENTATION_INPUTS},
        inputs={path: digest(sources[path]) for path in sorted(sources)},
        public_display_names=[row["name"] for row in rows],
        native_record_canonical_sha256={module: canonical_record(records[module])
                                        for module in MODULES},
        native_range_binding=range_binding(records, sources),
        api_sha256=digest(markdown), proof_certification=False,
        release_acceptance=False)
    return markdown, (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-data", type=Path, required=True)
    parser.add_argument("--native-db", type=Path,
                        help="genuine native SQLite source for active end-range checking")
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--check", action="store_true", help="compare, never write")
    args = parser.parse_args()
    require(re.fullmatch(r"[0-9a-f]{40}", args.source_revision) is not None,
            "full source revision required")
    root = HERE.parent
    sources = {path: (root / path).read_bytes() for path in INPUTS}
    committed_source = git_source_available(root, args.source_revision)
    if committed_source:
        tree = subprocess.check_output(["git", "--no-replace-objects", "rev-parse",
                                        args.source_revision + "^{tree}"], cwd=root).decode().strip()
        require(tree == SOURCE_TREE, "analyzed source tree differs")
        for path, raw in sources.items():
            old = subprocess.check_output(["git", "--no-replace-objects", "show",
                                           args.source_revision + ":" + path], cwd=root)
            require(old == raw, "source/pin drift from analyzed revision: " + path)
        binding = "git-object"
    records = {}
    for module in MODULES:
        path = args.native_data / ("declaration-data-" + module + ".bmp")
        records[module] = json.loads(path.read_bytes())
    if args.native_db is not None:
        verify_native_database(args.native_db, records, args.source_revision, sources)
    else:
        require(not committed_source, "native database required with committed source")
    if committed_source:
        binding = "git-object"
    else:
        manifest_source_binding(json.loads((root / "docs/api-manifest.json").read_bytes()),
                                args.source_revision, sources, records)
        binding = "committed-source-hashes"
    api, manifest = render(records, args.source_revision, sources)
    if args.check:
        previous = json.loads((root / "docs/api-manifest.json").read_bytes())
        require(previous["native_record_canonical_sha256"] ==
                json.loads(manifest)["native_record_canonical_sha256"],
                "native records differ from shipped manifest")
    for name, raw in (("API.md", api), ("api-manifest.json", manifest)):
        target = root / "docs" / name
        if args.check:
            require(target.read_bytes() == raw, "generated file differs: " + name)
        else:
            target.write_bytes(raw)
    print(json.dumps(dict(status="matched" if args.check else "generated",
                          declarations=len(EXPECTED), modules=len(MODULES),
                          api_sha256=digest(api), source_binding=binding,
                          native_database_verified=args.native_db is not None,
                          release_acceptance=False)))


if __name__ == "__main__":
    main()
