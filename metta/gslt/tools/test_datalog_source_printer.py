#!/usr/bin/env python3
"""Round-trip independent program payloads through the shared source grammar."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time
from packed_source_reader import retained_reader_files, retained_reader_arguments
from source_io import SOURCE_BINARY, source_command


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--reader", required=True, type=Path, help="an existing compile_datalog reader build directory")
    parser.add_argument("--souffle", type=Path)
    args = parser.parse_args()
    tools = Path(__file__).resolve().parent
    repo = tools.parents[2]
    lean = repo / "lean/mettapedia"
    output, reader = args.output.resolve(), args.reader.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise SystemExit("output directory must be empty")
    timings = []

    def run(label, command, failure=None):
        started = time.monotonic()
        with (output / f"{label}.out").open("w") as stdout, (output / f"{label}.err").open("w") as stderr:
            result = subprocess.run([str(x) for x in command], cwd=lean, stdout=stdout, stderr=stderr)
        timings.append({"step": label, "seconds": time.monotonic() - started, "exit_code": result.returncode})
        (output / "timings.json").write_text(json.dumps(timings, indent=2) + "\n")
        text = (output / f"{label}.out").read_text()
        if failure is not None:
            if not result.returncode or failure not in text + (output / f"{label}.err").read_text():
                raise SystemExit(f"{label}: expected the declared diagnostic")
        elif result.returncode:
            raise SystemExit(f"{label} failed; inspect its retained logs")
        return text

    targets = ["Mettapedia.Languages.Datalog.FactInputControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterAdmissionControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrintedSelectionControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxQualification",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterSourceControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontendSource",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourcePrinterControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterSymbolLaws",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterProgramControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogReferenceReaderControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRExecutable",
               "Mettapedia.Languages.Datalog.Closure"]
    run("proof-build", ["lake", "--wfail", "build", "sourceSyntax", *targets])
    files = {SOURCE_BINARY, Path(__file__), tools / "packed_source_reader.py", tools / "source_io.py", tools / "print_datalog.lean", tools / "emit_datalog.lean",
             tools / "generate_datalog_source_printer_controls.lean",
             *retained_reader_files(reader)}
    for target in targets:
        setup = lean / ".lake/build/ir" / Path(*target.split(".")).with_suffix(".setup.json")
        files.add(setup)
        modules = {target}
        for name, groups in json.loads(setup.read_text())["importArts"].items():
            if name.startswith("Mettapedia."):
                modules.add(name)
                files.update(Path(path) for group in groups for path in group)
        for name in modules:
            path = Path(*name.split("."))
            source = lean / path.with_suffix(".lean")
            files.update((source, lean / ".lake/build/lib/lean" / path.with_suffix(".olean")))
            for quoted in re.findall(r'^\s*#module_file "([^"]+)"', source.read_text(), re.M):
                files.add((source.parent / quoted).resolve())
    if args.souffle:
        files.add(args.souffle.resolve())
    digest = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
    pins = {str(path): digest(path) for path in sorted(files)}
    (output / "input-pins.json").write_text(json.dumps(pins, indent=2) + "\n")
    run("generate", ["lake", "env", "lean", "-DwarningAsError=true", "--run",
        tools / "generate_datalog_source_printer_controls.lean", output])
    programs = json.loads((output / "programs.json").read_text())
    expectations = dict(json.loads((output / "expected-outputs.json").read_text()))
    records = []
    source_prefix = source_command(repo / "metta/gslt/module/gold/SouffleDatalog/Syntax.module")
    for name in programs:
        payload, source = output / f"{name}.program.metta", output / f"{name}.dl"
        run(name + "-print", ["lake", "env", "lean", "-DwarningAsError=true", "--run", tools / "print_datalog.lean", payload, source])
        lines = run(name + "-parse", retained_reader_arguments(reader, source, output / f"{name}.cnf")).splitlines()
        status = json.loads(lines[0])
        if status["outcome"] != 0 or not status["accepted"] or status["semanticResults"] != 1:
            raise SystemExit(f"{name}: generated source did not produce one completed parser result")
        packet = output / f"{name}-selected.metta"
        packet.write_text("\n".join(lines[1:]) + "\n")
        rounds = 32 * (status["inputScalars"] + 1) + 256
        run(name + "-coverage", [*source_prefix,
            "coverage", source, output / f"{name}.cnf", output / f"{name}.cnf.pni", rounds])
        run(name + "-catalogue", [*source_prefix,
            "catalogue", source, output / f"{name}.cnf", output / f"{name}.cnf.pni", packet, rounds])
        compiled = output / f"{name}.metta"
        run(name + "-read", ["lake", "env", "lean", "-DwarningAsError=true", "--run", tools / "emit_datalog.lean",
            source, packet, output, compiled, "printed"])
        if payload.read_bytes() != Path(str(compiled) + ".program.metta").read_bytes():
            raise SystemExit(f"{name}: generated-source round trip changed program data")
        if source.read_bytes() != Path(str(compiled) + ".source.dl").read_bytes():
            raise SystemExit(f"{name}: canonical printing changed on the second pass")
        record = {"control": name, "independent_ir_roundtrip": True, "canonical_printing_stable": True,
                  "complete_native_forest": True, "complete_selected_catalogue": True}
        if args.souffle:
            reference = output / (name + "-souffle")
            reference.mkdir()
            run(name + "-souffle", [args.souffle.resolve(), "-F", output, "-D", reference, source])
            record["souffle_accepts_printed_source"] = True
            for relation, rows in expectations[name]:
                actual = (reference / (relation + ".csv")).read_text()
                if any("\n" in row or "\r" in row for row in rows):
                    if len(rows) != 1 or actual != rows[0] + "\n":
                        raise SystemExit(f"{name}: multiline literal output differs from the independent model")
                elif set(actual.splitlines()) != set(rows):
                    raise SystemExit(f"{name}: reference output differs from the independent model")
            record["souffle_outputs_match_independent_model"] = True
        records.append(record)
    protected = output / f"{programs[0]}.dl"
    old = protected.read_bytes()
    run("preserve-source", ["lake", "env", "lean", "-DwarningAsError=true", "--run", tools / "print_datalog.lean",
        output / f"{programs[0]}.program.metta", protected], failure="already exists")
    if protected.read_bytes() != old:
        raise SystemExit("existing source artifact was overwritten")
    if any(digest(path) != expected for path, expected in pins.items()):
        raise SystemExit("an input changed during qualification")
    result = {"controls": records, "source_and_objects_stable": True, "preserved_existing_output": True,
              "scope": "Admitted independent IR to ordinary source, complete checked native forest and selected catalogue, and exact IR readback. Total printing is proved from lexical/IR admission. Souffle source acceptance and outputs are compared with a separately settled Lean reference closure. Universal C implementation verification is not asserted."}
    (output / "qualification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
