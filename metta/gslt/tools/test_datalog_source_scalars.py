#!/usr/bin/env python3
"""Qualify ordinary-source scalar guards and spellings on both MeTTa engines."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time
from packed_source_reader import retained_reader_files, retained_reader_arguments
from source_io import SOURCE_BINARY, source_command


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--reader", type=Path, required=True)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--petta-runner", type=Path, required=True)
    parser.add_argument("--souffle", type=Path, required=True)
    args = parser.parse_args()
    tools = Path(__file__).resolve().parent
    repo = tools.parents[2]
    lean = repo / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    reader = args.reader.resolve()
    cetta, petta, souffle = (path.resolve() for path in (args.cetta, args.petta_runner, args.souffle))
    timings = []

    def run(label, command, failure=None):
        started = time.monotonic()
        with (output / (label + ".out")).open("w") as stdout, (output / (label + ".err")).open("w") as stderr:
            result = subprocess.run(list(map(str, command)), cwd=lean,
                env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"), stdout=stdout, stderr=stderr)
        timings.append(dict(label=label, seconds=time.monotonic() - started, exit_code=result.returncode))
        (output / "timings.json").write_text(json.dumps(timings, indent=2) + "\n")
        if failure is not None:
            if result.returncode == 0 or failure not in (output / (label + ".out")).read_text() + (output / (label + ".err")).read_text():
                raise SystemExit(f"{label}: missing expected rejection")
        elif result.returncode:
            raise SystemExit(f"{label}: failed; inspect retained output")
        return (output / (label + ".out")).read_text()

    targets = ["Mettapedia.Languages.Datalog.FactInputControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxCommand",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontendSource",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourcePrinterControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontendMeaning",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSymbolControls",
               "Mettapedia.Languages.Datalog.NumericPrinting",
               "Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution"]
    run("build", ["lake", "--wfail", "build", "sourceSyntax", *targets])
    current_reader = output / "current-reader"
    reader_files = retained_reader_files(reader)
    if len(reader_files) == 5:
        run("reader-export", [*source_command(repo / "metta/gslt/module/gold/SouffleDatalog/Syntax.module"), "export", current_reader])
        for path in reader_files[1:]:
            if (current_reader / path.name).read_bytes() != path.read_bytes():
                raise SystemExit("the supplied reader was built from a different grammar or selection policy")
    else:
        run("reader-export", ["lake", "env", "lean", "-DwarningAsError=true", "--run",
            tools / "export_datalog_reader.lean", current_reader])
        for name in ("source-structural.metta", "source-classes.metta", "source-start.term"):
            if (current_reader / name).read_bytes() != (reader / "reader" / name).read_bytes():
                raise SystemExit("the supplied reader was built from a different grammar")
    files = {SOURCE_BINARY, Path(__file__).resolve(), tools / "packed_source_reader.py", tools / "source_io.py", cetta, petta, souffle,
             *reader_files,
             *(tools / name for name in ("emit_datalog.lean", "check_datalog_source_result.lean",
                                        "export_datalog_reader.lean"))}
    for target in targets:
        setup = lean / ".lake/build/ir" / Path(*target.split(".")).with_suffix(".setup.json")
        files.add(setup)
        modules = {target}
        for name, groups in json.loads(setup.read_text())["importArts"].items():
            if name.startswith("Mettapedia."):
                modules.add(name)
                files.update(Path(path) for group in groups for path in group)
        for name in modules:
            relative = Path(*name.split("."))
            files.update((lean / relative.with_suffix(".lean"),
                          lean / ".lake/build/lib/lean" / relative.with_suffix(".olean")))
    files.update((repo / "metta/gslt/module/gold/SouffleDatalog").glob("*.module"))
    files.update((repo / "metta/gslt/lib").glob("*.metta"))
    files.update((petta.parent / "src").rglob("*.pl"))
    digest = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
    pins = {str(path): digest(path) for path in sorted(files)}
    (output / "input-pins.json").write_text(json.dumps(pins, indent=2) + "\n")

    words = ["z", "é", "λ", "🙂", "Z", "a", "aa", "", "10", "2"]
    symbols = '.decl word(x:symbol)\n.decl cmp(x:symbol,y:symbol,op:symbol)\n.output cmp\n'
    symbols += ''.join('word(' + json.dumps(word, ensure_ascii=False) + ').\n' for word in words)
    symbols += ''.join(f'cmp(x,y,"{name}") :- word(x),word(y),x {operator} y.\n'
                       for name, operator in (("lt", "<"), ("le", "<="), ("gt", ">"), ("ge", ">=")))
    integers = '.decl n(x:number)\n.output n\n'
    integers += ''.join(f'n({value}).\n' for value in
        ("00012", "-00012", "-0", "0b1010", "-0b1010", "0xAf", "-0xAf",
         "-9223372036854775808", "9223372036854775807"))
    controls = []
    for name, source_text, relation in (("symbols", symbols, "cmp"), ("integers", integers, "n")):
        source = output / (name + ".dl")
        source.write_text(source_text)
        reference = output / (name + "-reference")
        reference.mkdir()
        run(name + "-souffle", [souffle, "-D", reference, source])
        lines = run(name + "-parse", retained_reader_arguments(reader, source, output / (name + ".cnf"))).splitlines()
        status = json.loads(lines[0])
        if status["outcome"] != 0 or not status["accepted"] or status["semanticResults"] != 1:
            raise SystemExit(f"{name}: expected one completed source parse")
        packet = output / (name + "-selected.metta")
        packet.write_text("\n".join(lines[1:]) + "\n")
        compiled = output / (name + ".metta")
        run(name + "-emit", ["lake", "env", "lean", "-DwarningAsError=true", "--run",
            tools / "emit_datalog.lean", source, packet, output, compiled, "scalar"])
        canonical = Path(str(compiled) + ".source.dl")
        canonical_lines = run(name + "-canonical-parse", retained_reader_arguments(reader, canonical, output / (name + "-canonical.cnf"))).splitlines()
        canonical_status = json.loads(canonical_lines[0])
        if canonical_status["outcome"] != 0 or not canonical_status["accepted"] or canonical_status["semanticResults"] != 1:
            raise SystemExit(f"{name}: canonical source did not produce one completed parse")
        canonical_packet = output / (name + "-canonical-selected.metta")
        canonical_packet.write_text("\n".join(canonical_lines[1:]) + "\n")
        recompiled = output / (name + "-canonical.metta")
        run(name + "-canonical-emit", ["lake", "env", "lean", "-DwarningAsError=true", "--run",
            tools / "emit_datalog.lean", canonical, canonical_packet, output, recompiled, "scalar"])
        for suffix in ("", ".program.metta", ".source.dl"):
            if Path(str(compiled) + suffix).read_bytes() != Path(str(recompiled) + suffix).read_bytes():
                raise SystemExit(f"{name}: canonical round trip changed its payload or execution")
        workload = output / (name + "-run.metta")
        workload.write_text(compiled.read_text() + '''
!(let* (($initial (scalar:begin))
        ($direct (scalar:resume $initial 100 5000))
        ($partial (scalar:resume $initial 1 1))
        ($resumed (scalar:resume $partial 100 5000)))
   (let $printed (println! (gslt:snapshot:result $direct))
     (println! (DatalogScalarResume (== $direct $resumed)))))
''')
        engine_outputs = []
        for engine, command in (("cetta", [cetta, "--lang", "petta", "--quiet", workload]),
                                ("petta", ["bash", petta, "--silent", workload])):
            text = run(name + "-" + engine, command)
            results = [line for line in text.splitlines() if line.startswith("(SnapshotResult ")]
            if len(results) != 1 or text.splitlines().count("(DatalogScalarResume true)") != 1:
                raise SystemExit(f"{name}/{engine}: missing closure or exact resumption result")
            result = output / (name + "-" + engine + "-result.metta")
            result.write_text(results[0])
            run(name + "-" + engine + "-check", ["lake", "env", "lean", "-DwarningAsError=true", "--run",
                tools / "check_datalog_source_result.lean", Path(str(compiled) + ".program.metta"),
                result, reference / (relation + ".csv"), relation])
            engine_outputs.append(results[0])
        if engine_outputs[0] != engine_outputs[1]:
            raise SystemExit(f"{name}: completed runtime states differ")
        controls.append(dict(name=name, reference_equal=True, engines_equal=True, exact_resume=True,
                             canonical_roundtrip=True))
    rejections = []
    for name, source_text, diagnostic in (
        ("overflow", '.decl n(x:number)\nn(9223372036854775808).\n', "literal is outside"),
        ("unsafe-guard", '.decl n(x:symbol)\nn(x) :- x < "z".\n', "outside the typed positive core"),
        ("mixed-guard", '.decl n(x:symbol)\n.decl result(x:symbol)\nn("a").\nresult(x) :- n(x), x < 2.\n', "outside the typed positive core")):
        source = output / (name + ".dl")
        source.write_text(source_text)
        lines = run(name + "-parse", retained_reader_arguments(reader, source, output / (name + ".cnf"))).splitlines()
        status = json.loads(lines[0])
        if status["outcome"] != 0 or not status["accepted"] or status["semanticResults"] != 1:
            raise SystemExit(f"{name}: rejection must occur at semantic admission")
        packet = output / (name + "-selected.metta")
        packet.write_text("\n".join(lines[1:]) + "\n")
        run(name + "-refuse", ["lake", "env", "lean", "-DwarningAsError=true", "--run",
            tools / "emit_datalog.lean", source, packet, output, output / (name + ".metta"), "scalar"],
            failure=diagnostic)
        rejections.append(name)
    changed = [path for path, expected in pins.items() if digest(path) != expected]
    if changed:
        raise SystemExit("qualification inputs changed")
    record = dict(controls=controls, rejected=rejections, input_pins_stable=True,
        scope="Ordinary source, completed packed parse, emitted closure, complete fact-set equality with Souffle and exact resumption on both engines.")
    (output / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
