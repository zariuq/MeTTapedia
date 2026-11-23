#!/usr/bin/env python3
"""Qualify default fact-file framing and scalars through emitted MeTTa."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

from packed_source_reader import Commands, LEAN, REPO, TOOLS, retained_reader_arguments, retained_reader_files
from source_io import SOURCE_BINARY, source_command


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reader", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--souffle", type=Path, required=True)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--petta-runner", type=Path, required=True)
    args = parser.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    commands = Commands(work / "commands")
    commands.run("build", ["lake", "--wfail", "build", "sourceSyntax",
        "Mettapedia.Languages.Datalog.FactInputControls",
        "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterAdmissionCheck",
        "Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution"])
    module = REPO / "metta/gslt/module/gold/SouffleDatalog/Syntax.module"
    prefix = source_command(module)
    grammar = work / "grammar"
    commands.run("export", [*prefix, "export", grammar])
    reader_files = retained_reader_files(args.reader.resolve())
    for path in reader_files[1:]:
        if (grammar / path.name).read_bytes() != path.read_bytes():
            raise RuntimeError("retained parser differs from the current declared source profile")
    cases = [
        ("empty-file", "symbol", b"", True),
        ("empty-symbol", "symbol", b"\n", True),
        ("duplicate-empty-symbols", "symbol", b"\n\n", True),
        ("unicode-symbol", "symbol", "λ🙂\n".encode(), True),
        ("nul-symbol", "symbol", b"a\x00b\n", True),
        ("crlf", "symbol", b"alpha\r\nbeta\r\n", True),
        ("unterminated", "symbol", b"alpha", True),
        ("nullary", "", b"\n", True),
        ("extra-field", "symbol", b"alpha\tignored\n", True),
        ("decimal", "number", b"010\n+12\n  -3\n-0\n", True),
        ("signed-bounds", "number", b"-9223372036854775808\n9223372036854775807\n", True),
        ("unsigned", "unsigned", b"0x10\n0b10\n+12\n18446744073709551615\n", True),
        ("unsigned-reference-sign", "unsigned", b" -1\n0b-1\n0b+10\n", True),
        ("signed-hex-refusal", "number", b"0x10\n", False),
        ("blank-number-refusal", "number", b"\n", False),
        ("blank-number-record-refusal", "number", b"1\n\n", False),
        ("signed-overflow", "number", b"9223372036854775808\n", False),
        ("unsigned-overflow", "unsigned", b"18446744073709551616\n", False),
        ("unsigned-negative", "unsigned", b"-1\n", False),
    ]
    parsed_sources = {}
    for kind in dict.fromkeys(kind for _, kind, _, _ in cases):
        source = work / ((kind or "nullary") + ".dl")
        source.write_text(".decl R(" + ("x:" + kind if kind else "") + ")\n.input R\n.output R\n")
        forest = source.with_suffix(".cnf")
        result = commands.run((kind or "nullary") + "-parse",
            retained_reader_arguments(args.reader.resolve(), source, forest)).read_text().splitlines()
        status = json.loads(result[0])
        if status["outcome"] != 0 or status["semanticResults"] != 1:
            raise RuntimeError("fact-file source did not parse uniquely")
        packet = source.with_suffix(".packet")
        packet.write_text("\n".join(result[1:]) + "\n")
        commands.run((kind or "nullary") + "-coverage", [*prefix, "coverage", source, forest, str(forest) + ".pni", 4096])
        commands.run((kind or "nullary") + "-catalogue", [*prefix, "catalogue", source, forest, str(forest) + ".pni", packet, 4096])
        parsed_sources[kind] = source, packet
    rows = []
    for name, kind, data, accepted in cases:
        directory = work / name
        directory.mkdir()
        (directory / "R.facts").write_bytes(data)
        reference = directory / "reference"
        reference.mkdir()
        source, packet = parsed_sources[kind]
        ref = subprocess.run([str(args.souffle.resolve()), "-F", str(directory), "-D", str(reference), str(source)],
                             capture_output=True, text=True)
        (directory / "reference.log").write_text(ref.stdout + ref.stderr)
        emitted = directory / "program.metta"
        result = subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", str(TOOLS / "emit_datalog.lean"),
            str(source), str(packet), str(directory), str(emitted), "fact-input"], cwd=LEAN, capture_output=True, text=True)
        (directory / "emission.log").write_text(result.stdout + result.stderr)
        if (ref.returncode == 0) != accepted or (result.returncode == 0) != accepted:
            raise RuntimeError(name + ": source input admission differs from the reference")
        if not accepted:
            if "invalid input record or scalar" not in result.stdout + result.stderr:
                raise RuntimeError(name + ": refused at an unexpected boundary")
            rows.append(dict(case=name, refused=True, reference_agrees=True))
            continue
        run = directory / "run.metta"
        run.write_text(emitted.read_text() + '\n!(let* (($initial (fact-input:begin)) '
            '($done (fact-input:resume $initial 20 1000)) ($part (fact-input:resume $initial 1 1000)) '
            '($again (fact-input:resume $part 19 1000))) '
            '(let $printed (println! (OrdinaryDatalog (gslt:snapshot:result $done))) '
            '(println! (InputResume (== $done $again)))))\n')
        outputs = []
        for engine, command in (("cetta", [args.cetta.resolve(), "--lang", "petta", "--quiet", run]),
                                ("petta", ["bash", args.petta_runner.resolve(), "--silent", run])):
            output = commands.run(name + "-" + engine, command,
                env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1")).read_text()
            if not output.endswith("true\n") or "(SnapshotResult SnapshotComplete " not in output or \
                    not any(marker in output for marker in ("(InputResume true)", "(InputResume True)")):
                raise RuntimeError(name + ": execution or exact resumption did not complete")
            outputs.append(output)
            commands.run(name + "-" + engine + "-decode", ["lake", "env", "lean", "-DwarningAsError=true", "--run",
                TOOLS / "check_datalog_output.lean", str(emitted) + ".dictionary.metta",
                commands.work / (name + "-" + engine + ".out"), directory / (engine + "-facts")])
            actual = (directory / (engine + "-facts/R.csv")).read_bytes()
            expected = (reference / "R.csv").read_bytes()
            if set(actual.splitlines()) != set(expected.splitlines()):
                raise RuntimeError(name + ": completed facts differ from the reference")
        if outputs[0] != outputs[1]:
            raise RuntimeError(name + ": engine outputs differ")
        rows.append(dict(case=name, both_engines_complete=True, reference_agrees=True, exact_resume=True))
    digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    record = dict(controls=rows, cetta_sha256=digest(args.cetta.resolve()),
                  source_checker_sha256=digest(SOURCE_BINARY), souffle_sha256=digest(args.souffle.resolve()))
    (work / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"controls": len(rows), "reference_agrees": True}))


if __name__ == "__main__":
    main()
