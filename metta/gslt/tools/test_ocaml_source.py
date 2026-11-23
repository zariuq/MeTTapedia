#!/usr/bin/env python3
"""Check ordinary OCaml source through the authored grammar and compact IR.

This gate retains packed forests, checks selected-tree readback, and executes
the independent reference machine. Emitted MeTTa and universal frontend
correspondence are separate qualification obligations.
Some refusal controls are valid OCaml outside the current admission profile;
their refusal is not a claim that OCaml rejects them.
"""

import argparse
import hashlib
import json
from pathlib import Path

from packed_source_reader import Commands, REPO, TOOLS, build_native_reader, compile_pack, parse_source
from test_core_syntax import OCAML_RESULTS


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--cetta-source", type=Path, required=True)
    parser.add_argument("--ocaml", type=Path, required=True)
    args = parser.parse_args()
    work = args.work.resolve()
    require(not work.exists(), "use a new work directory")
    work.mkdir(parents=True)
    commands = Commands(work)
    module = REPO / "lean/mettapedia/Mettapedia/GSLT/LanguageDef/ModuleFormat"
    inputs = [Path(__file__), TOOLS / "packed_source_reader.py", TOOLS / "test_core_syntax.py",
              TOOLS / "export_core_reader.lean", TOOLS / "check_ocaml_source.lean",
              TOOLS / "parse_gslt_source.c", TOOLS / "source_family_selection.h",
              module / "GoldCoreSyntax.lean", module / "SourcePacket.lean", module / "SourcePacketView.lean",
              module / "OCamlSourceLowering.lean", module / "SourceSyntaxExport.lean",
              REPO / "metta/gslt/module/gold/SourceLexical.module",
              REPO / "metta/gslt/module/gold/OCaml/Syntax.module", args.ocaml.resolve()]
    sources = REPO / "metta/gslt/module/gold/OCaml/examples"
    cases = [(name, sources / (name + ".ml"), expected) for name, expected in OCAML_RESULTS.items()]
    extra = [
        ("simultaneous_binding", "let x = 10;; let x = 1 and y = x;; (x, y);;", "(1, 10)"),
        ("constructor_fields", "type t = Pair of (int * int) | Many of int * int;; "
         "let f x = match x with Pair (a,b) -> a - b | Many (a,b) -> b - a;; "
         "(f (Pair (8,3)), f (Many (8,3)));;", "(5, -5)"),
        ("constructor_capture", "type t = A | B;; let x = A;; "
         "let f x = match x with A -> 1 | B -> 2;; type u = A | C;; f x;;", "1"),
        ("minimum_integer", "-4611686018427387904;;", "-4611686018427387904"),
        ("minimum_negation", "let x = -4611686018427387904;; (x, -x);;",
         "(-4611686018427387904, -4611686018427387904)"),
        ("recursive_lambda_value", "let rec id = fun x -> x;; id 5;;", "5"),
    ]
    for name, text, expected in extra:
        source = work / (name + ".ml")
        source.write_text(text)
        cases.append((name, source, expected))
    for name, text in [
        ("unbound", "missing;;"),
        ("duplicate_pattern", "fun (x, x) -> x;;"),
        ("constructor_arity", "type t = C of int * int;; C 1;;"),
        ("unknown_constructor", "Missing;;"),
        ("constructor_overloading", "type t = A | B;; "
         "let f x = match x with A -> 1 | B -> 2;; type u = A | C;; f A;;"),
        ("recursive_nonfunction", "let rec x = 1;; x;;"),
        ("recursive_cyclic_value", "let rec ones = 1 :: ones;; ones;;"),
        ("nonrecursive_self_reference", "let f x = f x;; f 1;;"),
        ("integer_range", "4611686018427387904;;"),
        ("negative_integer_range", "-4611686018427387905;;"),
    ]:
        source = work / (name + ".ml")
        source.write_text(text)
        cases.append((name, source, None))
    inputs += [source for _, source, _ in cases]
    initial = {str(path): sha(path) for path in inputs}
    commands.run("build", ["lake", "--wfail", "build",
        "Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering",
        "Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketControls",
        "Mettapedia.Languages.OCaml.Examples"])
    binary, native = build_native_reader(args.cetta_source, work / "native", commands, selections=True)
    inputs += native
    exported = work / "grammar"
    commands.run("export", ["lake", "env", "lean", "-DwarningAsError=true", "--run",
                             TOOLS / "export_core_reader.lean", "ocaml", exported])
    abi, start, support = compile_pack(args.cetta_source, exported, commands, "pack")
    inputs += support
    results = []
    for name, source, expected in cases:
        forest = work / (name + ".forest")
        row = parse_source(binary, abi, start, source, forest, commands, "parse-" + name,
                           selection=exported / "selection.term", result_limit=256)
        require(row["outcome"] == 0 and row["semanticResults"] == 1,
                name + ": expected one complete explicitly selected parser result")
        packet = work / (name + ".packet")
        packet.write_text("\n".join((work / ("parse-" + name + ".out")).read_text().splitlines()[1:]) + "\n")
        checked = commands.run("lower-" + name, ["lake", "env", "lean", "-DwarningAsError=true",
            "--run", TOOLS / "check_ocaml_source.lean", source, packet,
            name if expected is not None else "--refuse"])
        require(not checked.with_suffix(".err").read_bytes(), name + ": frontend diagnostic")
        if expected is not None:
            output = commands.run("reference-" + name,
                [args.ocaml, "-noinit", "-noprompt", "-no-version"], input=source.read_bytes())
            text = output.read_text()
            require("- :" in text and not output.with_suffix(".err").read_bytes(), name + ": OCaml diagnostic")
            value = " ".join(text.rsplit("- :", 1)[1].split("=", 1)[1].split())
            require(value == expected, name + ": OCaml observation differs")
        results.append({"name": name, "accepted": expected is not None,
                        "expected": expected, "parser": row, "control": checked.read_text().strip(),
                        "source_sha256": sha(source), "forest_sha256": sha(forest),
                        "packet_sha256": sha(packet)})
        (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    require(all(sha(path) == value for path, value in initial.items()), "inputs changed during checking")
    record = {"scope": "authored source grammar, selected packets, compact IR and reference-machine observations",
              "passed": True, "source_cases": len(results), "positive": sum(row["accepted"] for row in results),
              "input_pins": {str(path): sha(path) for path in sorted(set(inputs))},
              "emitted_metta_qualified": False, "universal_frontend_correspondence": False,
              "full_O0_qualified": False}
    (work / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"{len(results)} source admission/model controls passed; accepted observations agree with OCaml")


if __name__ == "__main__":
    main()
