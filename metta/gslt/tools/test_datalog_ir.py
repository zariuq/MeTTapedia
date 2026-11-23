#!/usr/bin/env python3
"""Check compact Datalog IR operations on the shared MeTTa execution path."""

from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import time


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--cetta", type=Path)
    parser.add_argument("--petta-runner", type=Path)
    parser.add_argument("--closure", action="store_true", help="check full recursive closure and retained keys")
    parser.add_argument("--acceptance", action="store_true", help="also execute the two larger structured acceptance programs")
    args = parser.parse_args()
    gslt = Path(__file__).resolve().parent.parent
    repo = gslt.parent.parent
    lean = repo / "lean/mettapedia"
    generator = gslt / ("tools/generate_datalog_closure_controls.lean" if args.closure else "tools/generate_datalog_ir_controls.lean")
    cetta = (args.cetta or Path(os.environ.get("CETTA_BIN",
        repo.parent / "hyperon/cetta-prime-2.0-draft-20260910/cetta"))).resolve()
    petta = (args.petta_runner or Path(os.environ.get("PETTA_RUNNER",
        repo.parent / "hyperon/PeTTa/run.sh"))).resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise SystemExit("output directory must be empty")

    timings = []

    def run(label, command, env=None):
        started = time.monotonic()
        with (output / f"{label}.out").open("w") as stdout, (output / f"{label}.err").open("w") as stderr:
            result = subprocess.run(command, cwd=lean, env=env, stdout=stdout, stderr=stderr)
        timings.append({"operation": label, "seconds": time.monotonic() - started,
                        "exit_code": result.returncode})
        (output / "timings.json").write_text(json.dumps(timings, indent=2) + "\n")
        if result.returncode:
            raise SystemExit(f"{label} failed; inspect its output")

    targets = re.findall(r"^import (Mettapedia\.[A-Za-z0-9_.]+)$", generator.read_text(), re.M)
    targets += ["Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRTyping",
                "Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRProgram",
                "Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRProgramOrigins",
                "Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRQueryAgreement",
                "Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRQuerySnapshotTransport",
                "Mettapedia.Languages.Datalog.IRCodecControls"]
    if args.closure:
        targets += ["Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureAdvanceExecution",
                    "Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureCommitLaws",
                    "Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSourceReadingControls",
                    "Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPrefixReading",
                    "Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSearchCoverage",
                    "Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureProgress",
                    "Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRBindingTypingControls",
                    "Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureSourceExact",
                    "Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SouffleDatalogSourceExecution",
                    "Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SouffleDatalogSourceCoverage",
                    "Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSymbolControls"]
    run("proof-build", ["lake", "--wfail", "build", *dict.fromkeys(targets)])

    files = {generator, Path(__file__).resolve(), cetta, petta,
             lean / "lakefile.lean", lean / "lake-manifest.json", lean / "lean-toolchain"}
    for module in targets:
        relative = Path(*module.split("."))
        setup = lean / ".lake/build/ir" / relative.with_suffix(".setup.json")
        files.add(setup)
        modules = {module}
        for name, groups in json.loads(setup.read_text())["importArts"].items():
            if name.startswith("Mettapedia."):
                modules.add(name)
                files.update(Path(path) for group in groups for path in group)
        for name in modules:
            relative = Path(*name.split("."))
            source = lean / relative.with_suffix(".lean")
            files.add(source)
            files.add(lean / ".lake/build/lib/lean" / relative.with_suffix(".olean"))
            for quoted in re.findall(r'^\s*#module_file "([^"]+)"', source.read_text(), re.M):
                files.add((source.parent / quoted).resolve())
    files.update((gslt / "lib").glob("*.metta"))
    files.update((petta.parent / "src").rglob("*.pl"))
    before = {str(path): digest(path) for path in sorted(files)}
    (output / "input-pins.json").write_text(json.dumps(before, indent=2) + "\n")

    generation = ["lake", "env", "lean", "-DwarningAsError=true", "--run", str(generator), str(output)]
    if args.acceptance:
        if not args.closure:
            raise SystemExit("--acceptance requires --closure")
        generation.append("--acceptance")
    run("generation", generation)
    required = json.loads((output / "runtime-digests.json").read_text())
    live = {digest(path) for path in (gslt / "lib").glob("*.metta")}
    if not set(required) <= live:
        raise SystemExit("compiled runtime quotation differs from the current shared libraries")
    workload = output / "complete.metta"
    workload.write_text("\n".join((output / name).read_text()
        for name in ("runtime.metta", "ir-profiles.metta", "controls.metta")))
    environment = dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1")
    run("cetta", [str(cetta), "--lang", "petta", "--quiet", str(workload)], environment)
    run("petta", ["bash", str(petta), "--silent", str(workload)], environment)

    outputs = [(output / f"{engine}.out").read_text() for engine in ("cetta", "petta")]
    if outputs[0] != outputs[1]:
        raise SystemExit("native outputs disagree")
    measurements = json.loads((output / "measurements.json").read_text())
    expected = {row["label"] for row in measurements}
    if args.closure:
        expected |= {row["label"] + "/pending" for row in measurements if row.get("kind", "closure") == "closure"}
        providers = {row["label"]: row["accepted"] for row in measurements if row.get("kind") == "provider"}
        if providers != {"provider/empty": True, "provider/valid": True, "provider/duplicates": True,
                         "provider/unknown-free": False, "provider/wrong-sort": False,
                         "provider/wrong-constructor": False}:
            raise SystemExit("replacement snapshot controls disagree with their required admission outcomes")
    tag = "DatalogClosureControl" if args.closure else "DatalogIRControl"
    found = re.findall(r'^\(' + tag + r' "([^"]+)" (true|false) (true|false) (true|false) (true|false)\)$', outputs[0], re.M)
    if len(found) != len(expected) or {row[0] for row in found} != expected:
        raise SystemExit("missing, duplicated or unexpected controls")
    if any(answer != "true" for row in found for answer in row[1:]):
        raise SystemExit("a native comparison failed")
    for line in outputs[0].splitlines():
        if line != "true" and not line.startswith("(" + tag + " "):
            raise SystemExit("unexpected native output")
    if any(digest(Path(path)) != sha for path, sha in before.items()):
        raise SystemExit("an input changed during qualification")
    record = {"controls": len(found), "checks_per_engine": 4 * len(found),
              "identical_native_output": True, "source_and_objects_stable": True,
              "workload_sha256": digest(workload), "output_sha256": digest(output / "cetta.out"),
              "cetta_sha256": digest(cetta), "petta_runner_sha256": digest(petta),
              "scope": ("Compiled positive programs, complete snapshot closure, logical key readback, exact native resumption and separating replacement-provider checks. The proof build derives actual language validation, snapshot admission and selected-environment scope from successful preparation. It proves source-authorized firing coverage, canonical reachable snapshots, total key readback, absence of internal faults, finite completion for every positive quantum and retained MeTTa-loop fact equality with independent Datalog derivability. Selected ordinary-source packets preserve and reflect authored projection with independent literal/name meaning, which composes with the retained loop without supplied admission or scope hypotheses. Complete supported-profile preparation coverage, lexer/parser/ambiguity/binding adequacy, source/IR/printer round trips and final core qualification remain separate obligations."
                        if args.closure else "Compact IR lookup, compiled positive joins and finite snapshot queries; ordinary-source and whole-program execution are checked separately.")}
    (output / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
