#!/usr/bin/env python3
"""Check scoped curriculum inputs and optional proof audits with actual Lake.

Only generated, isolated packages are built or edited. Their sources, caches,
logs, and receipt are retained on both success and failure.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib


PROJECT = Path(__file__).resolve().parents[1]
QUOTE = "Mettapedia.Languages.MeTTa.PrimeCandidates.Native.CandidateMotivationProgramPackages"
IMPORTER = "Mettapedia.CurriculumConsumer"
UNRELATED = "Mettapedia.Languages.Metamath.CacheProbe"
CORE = "Mettapedia.Languages.Metamath.MM2AssembledNormalExecutionCore"
AUDIT = "Mettapedia.Languages.Metamath.MM2AssembledNormalExecution"
CANARY = "Mettapedia.Languages.Metamath.MM2TransformationCanary"
VALIDATION = "Mettapedia.Languages.Metamath.SourceInferenceProjectionValidation"
AUDIT_TARGET = "MetamathProofRegression"
REPLAY_NAMES = {
    "hypothesisReplay", "severedHypothesisReplay", "assertionReplay",
    "severedAssertionReplay", "orderedJoinReplay", "unpreparedOrderedJoinReplay",
    "invalidThenReferenceReplay",
}
INITIAL = "(= (lesson $x) (+ $x 1))\n"
CHANGED = "(= (lesson $x) (+ $x 2))\n"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_stanza(source: str, kind: str, name: str) -> str:
    lines = source.splitlines(keepends=True)
    pattern = re.compile(rf"^(?:@\[default_target\]\s+)?{kind}\s+{name}(?:\s+where)?\s*$")
    indices = [index for index, line in enumerate(lines) if pattern.fullmatch(line.rstrip())]
    require(len(indices) == 1, f"Expected exactly one {kind} {name} declaration")
    start = indices[0]
    end = start + 1
    while end < len(lines) and (not lines[end].strip() or lines[end][0].isspace()):
        end += 1
    return "".join(lines[start:end]).rstrip() + "\n"


def toml_stanza(source: str, kind: str, name: str) -> str:
    matches = list(re.finditer(r"(?m)^\[\[[^\]\n]+\]\]\s*$", source))
    selected = []
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(source)
        stanza = source[match.start():end]
        if match.group(0).strip() == f"[[{kind}]]":
            if tomllib.loads(stanza)[kind][0].get("name") == name:
                selected.append(stanza.rstrip() + "\n")
    require(len(selected) == 1, f"Expected exactly one TOML {kind} {name} declaration")
    return selected[0]


def actual_configurations(project: Path) -> tuple[dict[str, str], dict[str, str]]:
    lean_file, toml_file = project / "lakefile.lean", project / "lakefile.toml"
    lean, toml = lean_file.read_text(), toml_file.read_text()
    lean_package = lean_stanza(lean, "package", "Mettapedia")
    lean_input = lean_stanza(lean, "input_dir", "primeMotivationSources")
    lean_main = lean_stanza(lean, "lean_lib", "Mettapedia")
    lean_quote = lean_stanza(lean, "lean_lib", "PrimeMotivationQuotation")
    lean_audit = lean_stanza(lean, "lean_lib", AUDIT_TARGET)
    require("@[default_target]" in lean_main, "Mettapedia must remain the default Lean target")
    require(not re.search(r"\b(needs|extraDepTargets)\b", lean_main),
            "The default library must not carry global extra dependencies")
    require(re.search(rf"roots\s*:=\s*#\[`{re.escape(QUOTE)}\]", lean_quote) is not None,
            "The quotation library must own exactly the real quoting module")
    require(re.search(r"needs\s*:=\s*#\[`@/primeMotivationSources\]", lean_quote) is not None,
            "The quotation library must retain the real text dependency")
    require(lean.index(lean_main.rstrip()) < lean.index(lean_quote.rstrip()),
            "The quotation library must be declared after the default library")
    require("@[default_target]" not in lean_audit,
            "The expensive proof audit must remain a nondefault target")
    require(re.search(rf"roots\s*:=\s*#\[`{re.escape(AUDIT)}\]", lean_audit) is not None,
            "The explicit audit must retain the complete production regression module")
    require(lean.index(lean_quote.rstrip()) < lean.index(lean_audit.rstrip()),
            "The audit library must be declared after the quotation library")

    data = tomllib.loads(toml)
    main = next(item for item in data["lean_lib"] if item["name"] == "Mettapedia")
    quote = next(item for item in data["lean_lib"] if item["name"] == "PrimeMotivationQuotation")
    audit = next(item for item in data["lean_lib"] if item["name"] == AUDIT_TARGET)
    source_input = next(item for item in data["input_dir"] if item["name"] == "primeMotivationSources")
    require(data["defaultTargets"] == ["Mettapedia"], "Unexpected TOML default targets")
    require(not main.get("needs") and not main.get("extraDepTargets"), "TOML still has global dependencies")
    require(quote.get("roots") == [QUOTE] and quote.get("needs") == ["@/primeMotivationSources"],
            "Lean and TOML quotation configurations disagree")
    require(data["lean_lib"].index(main) < data["lean_lib"].index(quote), "TOML library order differs")
    require(audit.get("roots") == [AUDIT] and not audit.get("defaultTarget"),
            "Lean and TOML nondefault audit configurations disagree")
    require(data["lean_lib"].index(quote) < data["lean_lib"].index(audit),
            "TOML audit library order differs")
    require(source_input == {"name": "primeMotivationSources",
                            "path": "../../MettaKernel/Curriculum/PrimeMotivation",
                            "text": True, "filter": {"extension": ["metta"]}},
            "The actual text input contract changed; update this regression explicitly")
    require('path := "../../MettaKernel/Curriculum/PrimeMotivation"' in lean_input
            and "text := true" in lean_input and 'filter := .extension "metta"' in lean_input,
            "Lean and TOML source-input contracts disagree")
    first_table = re.search(r"(?m)^\[", toml)
    require(first_table is not None, "TOML configuration has no tables")
    header = toml[:first_table.start()].rstrip() + "\n"
    lean_header = "import Lake\nopen System Lake DSL\n" + lean_package + "\n"
    configurations = {
        "lean": lean_header + lean_input + "\n" + lean_main + "\n" + lean_quote + "\n" + lean_audit,
        "toml": header + "\n" + toml_stanza(toml, "lean_lib", "Mettapedia")
                + "\n" + toml_stanza(toml, "lean_lib", "PrimeMotivationQuotation")
                + "\n" + toml_stanza(toml, "lean_lib", AUDIT_TARGET)
                + "\n" + toml_stanza(toml, "input_dir", "primeMotivationSources"),
    }
    missing = re.sub(r"(?m)^\s+needs\s*:=\s*#\[`@/primeMotivationSources\]\s*\n", "", lean_quote)
    require(missing != lean_quote, "Failed to construct the missing-dependency negative control")
    prefix = lean_header + lean_input + "\n"
    configurations["missing-needs"] = prefix + lean_main + "\n" + missing + "\n" + lean_audit
    global_main = lean_main.rstrip() + " where\n  needs := #[`@/primeMotivationSources]\n"
    require(not lean_main.rstrip().endswith("where"), "Unexpected default library body")
    configurations["global-needs"] = prefix + global_main + "\n" + lean_quote + "\n" + lean_audit
    return configurations, {"lakefile.lean": digest(lean_file), "lakefile.toml": digest(toml_file)}


def lean_code(source: str) -> str:
    """Mask strings and nested/line comments, retaining newlines and positions."""
    result = list(source)
    index, depth, quoted = 0, 0, False
    character = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\n])'")
    while index < len(source):
        if depth:
            if source.startswith("/-", index):
                depth += 1
                result[index:index + 2] = "  "
                index += 2
            elif source.startswith("-/", index):
                depth -= 1
                result[index:index + 2] = "  "
                index += 2
            else:
                if source[index] != "\n":
                    result[index] = " "
                index += 1
        elif quoted:
            if source[index] == "\\" and index + 1 < len(source):
                result[index] = " "
                if source[index + 1] != "\n":
                    result[index + 1] = " "
                index += 2
            else:
                quoted = source[index] != '"'
                if source[index] != "\n":
                    result[index] = " "
                index += 1
        elif source.startswith("/-", index):
            depth = 1
            result[index:index + 2] = "  "
            index += 2
        elif source.startswith("--", index):
            end = source.find("\n", index)
            end = len(source) if end < 0 else end
            result[index:end] = " " * (end - index)
            index = end
        elif source[index] == '"':
            quoted = True
            result[index] = " "
            index += 1
        elif source[index] == "'" and (literal := character.match(source, index)):
            result[index:literal.end()] = " " * (literal.end() - index)
            index = literal.end()
        else:
            index += 1
    require(not depth and not quoted, "Unterminated Lean block comment or string in import scan")
    return "".join(result)


def source_import_boundary(project: Path) -> tuple[dict, dict[Path, str]]:
    """Inspect project-local import closures without elaborating their proofs."""
    require("import Fake" not in lean_code('/- /- nested -/ import Fake -/\n-- import Fake\n'),
            "Nested-comment import exclusion failed")
    parsed, hashes = {}, {}

    def read_module(name: str) -> tuple[list[str], list[str]]:
        if name not in parsed:
            path = project / Path(*name.split(".")).with_suffix(".lean")
            require(path.is_file(), f"Missing project-local import: {name}")
            code = lean_code(path.read_text())
            hashes[path] = digest(path)
            imports = []
            for match in re.finditer(
                    r"(?m)^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?([^\n]+)", code):
                imports.extend(match.group(1).split())
            replays = re.findall(r"(?m)^[ \t]*kernel_atom_(?:replay|run)[ \t]+([^\s]+)", code)
            parsed[name] = imports, replays
        return parsed[name]

    def closure(root: str) -> dict:
        pending, seen, external, replays = [root], set(), set(), {}
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            imports, commands = read_module(name)
            if commands:
                replays[name] = commands
            for imported in imports:
                if imported == "Mettapedia" or imported.startswith("Mettapedia."):
                    pending.append(imported)
                else:
                    external.add(imported)
        return {"module_count": len(seen), "modules": sorted(seen),
                "external_imports": sorted(external), "replay_commands": replays}

    result = {}
    for root in ("Mettapedia", "Mettapedia.Languages", "Mettapedia.Languages.Metamath", CORE):
        inspected = closure(root)
        require(not inspected["replay_commands"], f"Routine closure reaches replay commands: {root}")
        require(AUDIT not in inspected["modules"], f"Routine closure reaches the expensive audit: {root}")
        require(CANARY not in inspected["modules"], f"Routine closure reaches concrete canary programs: {root}")
        if root != "Mettapedia":
            require(CORE in inspected["modules"], f"Language interface lost reusable MM2 theory: {root}")
        if root in ("Mettapedia.Languages", "Mettapedia.Languages.Metamath"):
            require(VALIDATION in inspected["modules"],
                    f"Language interface lost source projection validation: {root}")
        result[root] = inspected
    explicit = closure(AUDIT)
    require(explicit["replay_commands"] == {AUDIT: list(read_module(AUDIT)[1])}
            and len(read_module(AUDIT)[1]) == 7 and set(read_module(AUDIT)[1]) == REPLAY_NAMES,
            "The explicit audit must retain exactly all seven concrete replay commands")
    require(CORE in explicit["modules"], "The explicit audit must use the independent MM2 core")
    require(CANARY in explicit["modules"], "The explicit audit must retain its concrete canary programs")
    result[AUDIT] = explicit
    return result, hashes


def write(path: Path, source: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8")


class Fixture:
    def __init__(self, root: Path, lake: str, format_name: str, config: str, toolchain: str):
        self.root, self.lake = root, lake
        self.project = root / "lean" / "mettapedia"
        self.config_name = "lakefile.toml" if format_name == "toml" else "lakefile.lean"
        self.curriculum = root / "MettaKernel" / "Curriculum" / "PrimeMotivation"
        self.lesson = self.curriculum / "01_dfa_petta.metta"
        self.logs = root / "logs"
        self.index = 0
        write(self.project / self.config_name, config)
        write(self.project / "lean-toolchain", toolchain)
        write(self.lesson, INITIAL)
        self.module(QUOTE, '''import Lean
open Lean Elab Term
elab "fixture_file_snapshot%" : term => do
  let text ← IO.FS.readFile "../../MettaKernel/Curriculum/PrimeMotivation/01_dfa_petta.metta"
  return mkStrLit text
def fixtureQuotedText : String := fixture_file_snapshot%
''')
        self.module(IMPORTER, f'''import {QUOTE}
open Lean Elab Term
elab "fixture_import_snapshot%" : term => do
  let declaration ← getConstInfoDefn ``fixtureQuotedText
  return declaration.value
def fixtureImportedText : String := fixture_import_snapshot%
''')
        self.module(UNRELATED, "def fixtureUnrelatedValue : Nat := 17\n")
        self.module(CORE, "def fixtureCoreValue : Nat := 23\n"
                    "theorem fixtureCoreReflexive : fixtureCoreValue = 23 := rfl\n")
        self.module("Mettapedia.Languages.Metamath", f"import {CORE}\nimport {UNRELATED}\n")
        self.module("Mettapedia.Languages", "import Mettapedia.Languages.Metamath\n")
        self.module("Mettapedia", f"import {IMPORTER}\nimport Mettapedia.Languages\n")
        self.audit_source = f'''import {CORE}
import Lean
run_cmd IO.FS.writeFile "AuditElaboration.marker" "explicit-audit\n"
theorem fixtureExplicitAudit : fixtureCoreValue = 23 := fixtureCoreReflexive
'''
        self.module(AUDIT, self.audit_source)
        write(self.project / "SnapshotProbe.lean", f"import {IMPORTER}\n#eval fixtureImportedText\n")
        write(self.project / "CoreProbe.lean", f"import {CORE}\n#check fixtureCoreReflexive\n")
        write(self.project / "AuditProbe.lean", f"import {AUDIT}\n#check fixtureExplicitAudit\n")

    def module(self, name: str, source: str) -> None:
        write(self.project / Path(*name.split(".")).with_suffix(".lean"), source)

    def run(self, *arguments: str, success: bool = True) -> subprocess.CompletedProcess:
        self.index += 1
        command = [self.lake, "--no-cache", "--no-ansi", "-f", self.config_name, *arguments]
        reply = subprocess.run(command, cwd=self.project, capture_output=True, text=True, timeout=120)
        write(self.logs / f"{self.index:02d}.stdout", reply.stdout)
        write(self.logs / f"{self.index:02d}.stderr", reply.stderr)
        write(self.logs / f"{self.index:02d}.command.json", json.dumps(command) + "\n")
        if success:
            require(reply.returncode == 0, f"Lake failed in {self.root.name}: {' '.join(arguments)}\n{reply.stdout}{reply.stderr}")
        return reply

    def cache(self, modules: tuple[str, ...] = (QUOTE, IMPORTER, UNRELATED)) -> dict:
        result = {}
        for module in modules:
            paths = {}
            stem = self.project / ".lake/build/lib/lean" / Path(*module.split("."))
            for suffix in (".olean", ".trace"):
                path = stem.with_suffix(suffix)
                require(path.is_file(), f"Missing test artifact: {path}")
                paths[suffix] = {"sha256": digest(path), "mtime_ns": path.stat().st_mtime_ns}
            result[module] = paths
        return result

    def audit_absent(self) -> None:
        path = self.project / ".lake/build/lib/lean" / Path(*AUDIT.split(".")).with_suffix(".olean")
        require(not path.exists() and not (self.project / "AuditElaboration.marker").exists(),
                "Routine build elaborated the optional audit")

    def observed(self) -> str:
        reply = self.run("env", "lean", "SnapshotProbe.lean")
        return json.loads(reply.stdout.strip())

    def initial(self) -> dict:
        self.run("build")
        require(self.observed() == INITIAL, "Initial importer did not snapshot the authored text")
        return self.cache()


def positive(fixture: Fixture) -> dict:
    initial = fixture.initial()
    fixture.audit_absent()
    fixture.run("build")
    require(fixture.cache() == initial, "A no-op build changed the cache")
    write(fixture.curriculum / "ignored.txt", "Not an authored MeTTa input\n")
    fixture.run("build")
    require(fixture.cache() == initial, "A non-MeTTa file invalidated the cache")
    write(fixture.lesson, CHANGED)
    fixture.run("--no-build", "build", UNRELATED)
    require(fixture.cache()[UNRELATED] == initial[UNRELATED], "Unrelated cache changed before quotation build")
    fixture.run("build")
    changed = fixture.cache()
    require(changed[UNRELATED] == initial[UNRELATED], "Curriculum edit rebuilt unrelated Metamath")
    for module in (QUOTE, IMPORTER):
        for suffix in (".olean", ".trace"):
            require(changed[module][suffix]["sha256"] != initial[module][suffix]["sha256"],
                    f"Changed curriculum did not change {module}{suffix}")
            require(changed[module][suffix]["mtime_ns"] != initial[module][suffix]["mtime_ns"],
                    f"Changed curriculum did not rebuild {module}{suffix}")
    require(fixture.observed() == CHANGED, "Importer retained stale compiled constructor data")
    fixture.run("build")
    require(fixture.cache() == changed, "The refreshed cache is not reusable")
    write(fixture.lesson, INITIAL)
    fixture.run("build")
    restored = fixture.cache()
    require(fixture.observed() == INITIAL, "Restored authored source stayed stale")
    require(restored[UNRELATED] == initial[UNRELATED], "Restoring source invalidated unrelated Metamath")
    fixture.audit_absent()
    audit = optional_audit(fixture)
    return {"outcome": "passed", "initial": initial, "changed": changed, "restored": restored,
            "optional_audit": audit}


def optional_audit(fixture: Fixture) -> dict:
    core = fixture.cache((CORE,))
    fixture.run("build", CORE)
    fixture.run("env", "lean", "CoreProbe.lean")
    fixture.audit_absent()
    fixture.run("build", AUDIT_TARGET)
    explicit = fixture.cache((AUDIT,))
    marker = fixture.project / "AuditElaboration.marker"
    require(marker.read_text() == "explicit-audit\n", "Explicit audit target did not elaborate its module")
    fixture.run("env", "lean", "AuditProbe.lean")
    require(fixture.cache((CORE,)) == core, "Explicit audit rebuilt independent core theory")
    fixture.module(AUDIT, fixture.audit_source.replace("explicit-audit", "updated-audit")
                   + "theorem fixtureExtraAudit : 1 + 1 = 2 := by decide\n")
    fixture.run("--no-build", "build")
    fixture.run("build")
    require(fixture.cache((AUDIT,)) == explicit and marker.read_text() == "explicit-audit\n",
            "Routine build re-elaborated the optional audit after an audit-only edit")
    stale = fixture.run("--no-build", "build", AUDIT_TARGET, success=False)
    require(stale.returncode != 0, "Explicit audit failed to detect its own source change")
    fixture.run("build", AUDIT_TARGET)
    refreshed = fixture.cache((AUDIT,))
    require(refreshed != explicit and marker.read_text() == "updated-audit\n",
            "Explicit audit did not refresh its changed source")
    fixture.run("env", "lean", "AuditProbe.lean")
    require(fixture.cache((CORE,)) == core, "Audit-only source edit invalidated reusable core theory")
    return {"outcome": "passed", "explicit": explicit, "refreshed": refreshed, "core": core}


def negative(fixture: Fixture, name: str) -> dict:
    initial = fixture.initial()
    write(fixture.lesson, CHANGED)
    if name == "missing-needs":
        fixture.run("build")
        current = fixture.cache()
        require(current == initial and fixture.observed() == INITIAL,
                "Missing-needs negative control did not reproduce stale quotation")
        return {"outcome": "detected-stale-quotation", "initial": initial, "changed": current}
    no_build = fixture.run("--no-build", "build", UNRELATED, success=False)
    require(no_build.returncode != 0, "Global-needs negative control did not invalidate unrelated module")
    fixture.run("build")
    current = fixture.cache()
    require(current[UNRELATED][".olean"]["mtime_ns"] != initial[UNRELATED][".olean"]["mtime_ns"],
            "Global dependency did not reproduce the unrelated rebuild")
    require(fixture.observed() == CHANGED, "Global-needs control unexpectedly lost freshness")
    return {"outcome": "detected-unrelated-invalidation", "initial": initial, "changed": current}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=PROJECT, help="Read the real configuration and toolchain here")
    parser.add_argument("--work-dir", type=Path, default=PROJECT / ".scratch_lake_build_scoping",
                        help="Retained generated test packages; the production cache is never used")
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args(argv)
    started = time.monotonic()
    run_directory = None
    try:
        configs, hashes = actual_configurations(args.project)
        import_boundary, source_hashes = source_import_boundary(args.project)
        lake = shutil.which(args.lake)
        require(lake is not None, "Lake executable not found")
        args.work_dir.mkdir(parents=True, exist_ok=True)
        run_directory = Path(tempfile.mkdtemp(prefix="scope-", dir=args.work_dir))
        toolchain = (args.project / "lean-toolchain").read_text()
        results = {}
        for name, config in configs.items():
            fixture = Fixture(run_directory / name, lake, name, config, toolchain)
            results[name] = positive(fixture) if name in ("lean", "toml") else negative(fixture, name)
            print(f"PASS: {name}: {results[name]['outcome']}", flush=True)
        receipt = {"schema": "mettapedia-lake-scoping-regression-v1", "source_configs": hashes,
                   "toolchain": toolchain.strip(), "controls": results,
                   "production_import_boundary": import_boundary,
                   "inspected_sources": {str(path.relative_to(args.project)): sha
                                         for path, sha in source_hashes.items()},
                   "elapsed_seconds": time.monotonic() - started}
        require(hashes == {name: digest(args.project / name) for name in hashes},
                "Real configuration changed while the isolated regression ran")
        require(all(digest(path) == sha for path, sha in source_hashes.items()),
                "Real import graph changed while the isolated regression ran")
        write(run_directory / "receipt.json", json.dumps(receipt, indent=2) + "\n")
        print(f"PASS: actual Lean/TOML scoping and both negative controls "
              f"({receipt['elapsed_seconds']:.3f}s); artifacts retained: {run_directory}")
        return 0
    except (AssertionError, OSError, ValueError, KeyError, StopIteration, subprocess.TimeoutExpired) as error:
        print(f"Build scoping regression failed: {error}", file=sys.stderr)
        if run_directory is not None:
            print(f"Test artifacts retained: {run_directory}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
