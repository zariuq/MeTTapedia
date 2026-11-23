#!/usr/bin/env python3
"""Compile ordinary positive Datalog through its authored grammar and GSLT IR."""

import argparse
import hashlib
import json
from pathlib import Path
import re
from packed_source_reader import Commands, LEAN, REPO, TOOLS
from source_io import read_source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--facts", required=True, type=Path)
    parser.add_argument("--name", default="datalog")
    parser.add_argument("--parser-host", type=Path, default=REPO.parent / "hyperon/cetta-pre-main-20261023")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9:-]*", args.name):
        raise SystemExit("entry name must be an ordinary MeTTa function prefix")
    tools, lean = TOOLS, LEAN
    source, output = args.source.resolve(), args.output.resolve()
    build = output.with_suffix(output.suffix + ".build")
    destinations = [output, build, *(Path(str(output) + suffix)
        for suffix in (".dictionary.metta", ".source.dl", ".program.metta"))]
    if any(path.exists() for path in destinations):
        raise SystemExit("output or build directory already exists")
    build.mkdir(parents=True)
    commands = Commands(build)
    run = commands.run

    run("proof-build", ["lake", "--wfail", "build",
        "sourceSyntax",
        "Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxCommand",
        "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontend",
        "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontendSource",
        "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSelectedSource",
        "Mettapedia.Languages.Datalog.FactInputCorrespondence",
        "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourcePrinter",
        "Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence",
        "Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution"])
    syntax_module = REPO / "metta/gslt/module/gold/SouffleDatalog/Syntax.module"
    parsed = read_source(syntax_module, source, build / "reader", args.parser_host, commands)
    if not parsed["alternatives"]:
        raise SystemExit("complete checked source catalogue contains no selected program")
    if len(parsed["alternatives"]) != 1:
        raise SystemExit("Datalog requires exactly one selected source alternative; all alternatives are retained")
    packet, source_core = parsed["alternatives"][0]
    run("emit", ["lake", "env", "lean", "-DwarningAsError=true", "--run", tools / "emit_datalog.lean",
                  source, packet, args.facts.resolve(), output, args.name])
    sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    inputs = parsed["native_sources"] + [source, parsed["checker"], tools / "compile_datalog.py", tools / "source_io.py",
        tools / "packed_source_reader.py", tools / "source_plan_identity.h", tools / "source_family_selection.h",
        tools / "emit_datalog.lean", syntax_module]
    grammar = parsed["grammar"]
    record = {"source_sha256": sha(source), "output_sha256": sha(output),
              "canonical_source_sha256": sha(Path(str(output) + ".source.dl")),
              "program_payload_sha256": sha(Path(str(output) + ".program.metta")),
              "source_core_sha256": sha(source_core),
              "parser_binary_sha256": sha(parsed["binary"]),
              "source_checker_sha256": sha(parsed["checker"]),
              "direct_parser_plan": {path.name: sha(path) for path in grammar.iterdir() if path.is_file()},
              "source_inputs": {str(path): sha(path) for path in inputs},
              "packed_forest_retained": True, "native_action_result_count": len(parsed["alternatives"]),
              "exported_forest_representation_checked": True,
              "native_forest_complete_for_input": parsed["whole_input_coverage_checked"],
              "native_selected_catalogue_complete_for_input": parsed["selected_catalogue_checked"],
              "coverage_rounds": parsed["coverage_rounds"],
              "native_parser_implementation_verified": False,
              "semantic_replay_completed": True,
              "selection": "exactly one result after completed declared selection; independent source replay checked",
              "inference_on_host": False,
              "scope": "Positive, range-restricted function-free Datalog with symbols and decimal, binary or hexadecimal signed and unsigned literals; unsupported scalar profiles receive admission diagnostics."}
    (build / "manifest.json").write_text(json.dumps(record, indent=2) + "\n")
    print((build / "emit.out").read_text().strip())


if __name__ == "__main__":
    main()
