#!/usr/bin/env python3
"""Read and print source syntax using an imported syntaxGSLT .module."""

import argparse
import json
from pathlib import Path

from packed_source_reader import Commands, LEAN, build_native_reader, parse_direct_source

SOURCE_BINARY = LEAN / ".lake/build/bin/sourceSyntax"


def source_command(module):
    """Run the shared checker compiled, using the normal imported-module loader."""
    return ["lake", "env", SOURCE_BINARY, Path(module).resolve()]


def write_driver(module, destination):
    """Use the existing module loader, including its import and collision checks."""
    destination = Path(destination)
    destination.write_text(
        "import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxCommand\n"
        "set_option maxRecDepth 32768\nset_option maxHeartbeats 8000000\n"
        "open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Loader\n"
        "namespace SourceInput\n"
        f"#module_tree {json.dumps(str(Path(module).resolve()), ensure_ascii=False)} as Loaded\n"
        "end SourceInput\n"
        "def main (arguments : List String) : IO Unit :=\n"
        "  Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxCommand.run\n"
        "    _root_.SourceInput.Loaded.library _root_.SourceInput.Loaded.module arguments\n")
    return destination


def read_source(module, source, destination, host, commands, *, result_limit=256, coverage_rounds=None):
    """Retain every completed selected alternative, its forest and checked core.

    Selection comes from the module. A result limit is a pending computation,
    never a claim that the source is unambiguous or invalid.
    """
    source, destination = Path(source).resolve(), Path(destination).resolve()
    destination.mkdir(parents=True, exist_ok=False)
    prefix = source_command(module)
    grammar = destination / "grammar"
    commands.run("source-export", [*prefix, "export", grammar])
    binary, native_sources = build_native_reader(host, destination / "native", commands, selections=True)
    forest = destination / "source.cnf"
    status = parse_direct_source(binary, grammar, source, forest, commands, "source-parse",
                                 selected=True, result_limit=result_limit)
    (destination / "parse-status.json").write_text(json.dumps(status, indent=2) + "\n")
    if status["outcome"] != 0:
        raise RuntimeError("source parsing remains unfinished; its forest and outcome are retained")
    rounds = coverage_rounds if coverage_rounds is not None else 32 * (status["inputScalars"] + 1) + 256
    if rounds < 0:
        raise ValueError("coverage rounds must be nonnegative")
    commands.run("source-coverage", [*prefix, "coverage", source, forest, str(forest) + ".pni", rounds])
    packets = (commands.work / "source-parse.out").read_text().splitlines()[1:]
    if len(packets) != status["semanticResults"] or any(not line.startswith("(result ") for line in packets):
        raise RuntimeError("native result packet count disagrees with its completion receipt")
    catalogue = destination / "selected-results.packets"
    catalogue.write_text("".join(text + "\n" for text in packets))
    commands.run("source-catalogue", [*prefix, "catalogue", source, forest, str(forest) + ".pni", catalogue, rounds])
    alternatives = []
    for index, text in enumerate(packets):
        packet = destination / f"alternative-{index}.packet"
        core = destination / f"alternative-{index}.core"
        packet.write_text(text + "\n")
        commands.run(f"source-read-{index}", [*prefix, "read", source, packet, core])
        alternatives.append((packet, core))
    return dict(alternatives=alternatives, status=status, binary=binary,
                native_sources=native_sources, grammar=grammar, checker=SOURCE_BINARY, forest=forest,
                coverage_rounds=rounds, whole_input_coverage_checked=True, selected_catalogue_checked=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=("export", "parse", "read", "print", "forest", "coverage", "catalogue"))
    parser.add_argument("module", type=Path)
    parser.add_argument("paths", nargs="+", type=Path)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--host", type=Path, help="CeTTa source checkout supplying the native parser")
    parser.add_argument("--result-limit", type=int, default=256)
    parser.add_argument("--coverage-rounds", type=int)
    args = parser.parse_args()
    arity = {"export": 1, "parse": 2, "read": 3, "print": 2, "forest": 3, "coverage": 3, "catalogue": 4}[args.operation]
    if len(args.paths) != arity:
        parser.error(f"{args.operation} expects {arity} paths")
    if args.coverage_rounds is not None and args.coverage_rounds < 0:
        parser.error("coverage rounds must be nonnegative")
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    commands = Commands(work)
    commands.run("build", ["lake", "--wfail", "build", "sourceSyntax"])
    if args.operation == "parse":
        if args.host is None or not 0 < args.result_limit <= 4294967295:
            parser.error("parse needs --host and a positive uint32 result limit")
        result = read_source(args.module, args.paths[0], args.paths[1], args.host, commands,
                             result_limit=args.result_limit, coverage_rounds=args.coverage_rounds)
        print(json.dumps(dict(alternatives=len(result["alternatives"]),
                              completed=True, forest_representation_checked=True, whole_input_coverage_checked=True,
                              selected_catalogue_checked=True)))
        return
    output = commands.run("source-io", [*source_command(args.module),
        args.operation, *(path.resolve() for path in args.paths),
        *([str(args.coverage_rounds if args.coverage_rounds is not None else 4096)]
          if args.operation in ("coverage", "catalogue") else [])], LEAN)
    print(output.read_text(), end="")


if __name__ == "__main__":
    main()
