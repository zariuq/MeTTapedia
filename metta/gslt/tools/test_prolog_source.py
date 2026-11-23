#!/usr/bin/env python3
"""Qualify declared ISO/SWI sentence profiles through the shared source pipeline.

The grammar's admitted surface is tested here; this is not a claim of complete
ISO or SWI source coverage. All native alternatives are retained and checked.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from packed_source_reader import Commands, REPO, TOOLS, build_native_reader, parse_direct_source
from source_io import write_driver


CASES = [
    ("fact", "edge(a,b).", True, True),
    ("rule", "path(X,Y) :- edge(X,Y).", True, True),
    ("quotes", '"ab".', True, True),
    ("zero", "f().", False, True),
    ("quoted-op", "a '+' b.", True, False),
    ("list", "[a,b|T].", True, True),
    ("integer", "0x10.", True, True),
    ("negative", "-7.", True, True),
    ("digits", "12_345.", False, True),
    ("backticks", "`ab`.", False, True),
    ("priority", "a+b*c.", True, True),
    ("clash", "a=b=c.", False, False),
    ("sharing", "f(X,X,_,_).", True, True),
    ("comment", "/* note */ edge(a,b). % tail", True, True),
    ("character-code", "0'_.", True, True),
    ("left-associative", "a-b-c.", True, True),
    ("unknown-operator", "a likes b.", False, False),
    ("unclosed", "f(a.", False, False),
    ("quoted-semicolon", "a ';' b.", True, False),
    ("spaced-dot", "a . b.", False, False),
    ("dot-operator", "a.b.", False, True),
    ("nil", "[].", True, True),
    ("quoted-nil", "'[]'.", True, True),
    ("explicit-cons", "'.'(a,[]).", True, True),
    ("space-escape", "'a\\sb'.", False, True),
]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--cetta-source", type=Path)
    parser.add_argument("--reader", type=Path, help="use and hash an existing native packed reader")
    parser.add_argument("--lean", type=Path, help="use a selected Lean executable and its inherited import path")
    parser.add_argument("--existing-build", action="store_true")
    args = parser.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    commands = Commands(work / "commands")
    lean = [args.lean] if args.lean else ["lake", "env", "lean"]
    if not args.existing_build:
        commands.run("build", ["lake", "--wfail", "build",
            "Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSyntaxControls",
            "Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologDatalogControls",
            "Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSourceFrontend"])
    if args.reader:
        binary = args.reader.resolve()
    else:
        require(args.cetta_source is not None, "supply --reader or --cetta-source")
        binary, _ = build_native_reader(args.cetta_source, work / "native", commands, selections=True)
    results, drivers, grammars = [], {}, {}
    for dialect in ("iso", "swi"):
        directory = work / dialect
        directory.mkdir()
        module = REPO / "metta/gslt/module/prolog" / (dialect.upper() + "Syntax.module")
        driver = write_driver(module, directory / "source_driver.lean")
        grammar = directory / "grammar"
        commands.run(dialect + "-export", [*lean, "--run", driver, "export", grammar])
        drivers[dialect], grammars[dialect] = driver, grammar

    def parse(dialect, label, source, directory):
        forest = directory / (label + ".forest")
        tag = dialect + "-" + label
        status = parse_direct_source(binary, grammars[dialect], source, forest, commands,
                                     tag, selected=True, result_limit=256)
        require(status["outcome"] == 0, tag + ": native parsing remains pending")
        packets = (commands.work / (tag + ".out")).read_text().splitlines()[1:]
        require(len(packets) == status["semanticResults"], tag + ": result count differs")
        catalogue = directory / (label + ".packet")
        catalogue.write_text("".join(packet + "\n" for packet in packets))
        return status, packets, forest, catalogue

    for label, text, iso, swi in CASES:
        source = work / (label + ".pl")
        source.write_text(text)
        for dialect, expected in (("iso", iso), ("swi", swi)):
            tag = dialect + "-" + label
            status, packets, forest, catalogue = parse(dialect, label, source, work / dialect)
            require(bool(packets) == expected, tag + ": unexpected syntax admission")
            if packets:
                commands.run(tag + "-interpret", [*lean, "--run", TOOLS / "check_prolog_source.lean",
                                                  dialect, source, catalogue])
            # Independent positive, ambiguous and complete-empty coverage.
            coverage = label in ("fact", "negative", "clash")
            if coverage:
                rounds = 32 * (status["inputScalars"] + 1) + 256
                commands.run(tag + "-coverage", [*lean, "--run", drivers[dialect], "coverage",
                    source, forest, str(forest) + ".pni", rounds])
                commands.run(tag + "-catalogue", [*lean, "--run", drivers[dialect], "catalogue",
                    source, forest, str(forest) + ".pni", catalogue, rounds])
            results.append(dict(case=tag, alternatives=len(packets), coverage_checked=coverage,
                                source_sha256=hashlib.sha256(source.read_bytes()).hexdigest()))
            (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")

    clauses = ["edge(a,b).", "edge(b,c).", "path(X,Y) :- edge(X,Y).",
               "path(X,Z) :- edge(X,Y),path(Y,Z)."]
    for dialect in ("iso", "swi"):
        directory = work / (dialect + "-datalog")
        directory.mkdir()
        for index, text in enumerate(clauses):
            source = directory / (str(index) + ".pl")
            source.write_text(text)
            _, packets, _, catalogue = parse(dialect, "clause-" + str(index), source, directory)
            require(len(packets) == 1, "common Datalog clause has unexpected ambiguity")
            (directory / (str(index) + ".packet")).write_bytes(catalogue.read_bytes())
        commands.run(dialect + "-datalog", [*lean, "--run", TOOLS / "check_prolog_datalog.lean", dialect, directory])
    require((work / "iso-datalog/common.dl").read_bytes() == (work / "swi-datalog/common.dl").read_bytes(),
            "the two source profiles produced different Datalog source")

    # Re-enter the ordinary Datalog source frontend through its actual grammar.
    directory = work / "iso-datalog"
    module = REPO / "metta/gslt/module/gold/SouffleDatalog/Syntax.module"
    driver = write_driver(module, directory / "datalog_driver.lean")
    grammar = directory / "datalog-grammar"
    commands.run("datalog-export", [*lean, "--run", driver, "export", grammar])
    status = parse_direct_source(binary, grammar, directory / "common.dl", directory / "common.forest",
                                 commands, "datalog-read", selected=True, result_limit=256)
    packets = (commands.work / "datalog-read.out").read_text().splitlines()[1:]
    require(status["outcome"] == 0 and len(packets) == 1, "Datalog source parsing did not finish uniquely")
    (directory / "common.dl.packet").write_text(packets[0] + "\n")
    commands.run("datalog-agreement", [*lean, "--run", TOOLS / "check_prolog_datalog.lean", "datalog", directory])

    whole = work / "operator-updates.pl"
    whole.write_text(':- op(600,xfy,likes).\na likes b.\n'
                     ':- set_prolog_flag(double_quotes,codes).\n"ab".\n:- op(0,xfy,likes).\n')
    planned = work / "stateful"
    commands.run("stateful-plan", [*lean, "--run", TOOLS / "plan_prolog_source.lean", "swi", whole, planned])
    units = json.loads((planned / "sentences.json").read_text())
    for unit in units:
        directory = planned / str(unit["unit"])
        driver = write_driver(directory / unit["module"], directory / "source_driver.lean")
        grammar = directory / "grammar"
        tag = "stateful-" + str(unit["unit"])
        commands.run(tag + "-export", [*lean, "--run", driver, "export", grammar])
        status = parse_direct_source(binary, grammar, directory / "sentence.pl", directory / "source.forest",
                                     commands, tag, selected=True, result_limit=256)
        packets = (commands.work / (tag + ".out")).read_text().splitlines()[1:]
        require(status["outcome"] == 0 and packets, tag + ": sentence parsing did not complete")
        catalogue = directory / "source.packet"
        catalogue.write_text("".join(packet + "\n" for packet in packets))
        commands.run(tag + "-interpret", [*lean, "--run", TOOLS / "check_prolog_source.lean",
            "state", "swi", whole, str(unit["unit"]), directory / "sentence.pl", catalogue])
    directory = planned / "final"
    driver = write_driver(directory / "SWISyntax.module", directory / "source_driver.lean")
    commands.run("removed-export", [*lean, "--run", driver, "export", directory / "grammar"])
    status = parse_direct_source(binary, directory / "grammar", work / "unknown-operator.pl",
        directory / "removed.forest", commands, "removed-operator", selected=True, result_limit=256)
    require(status["outcome"] == 0 and not status["semanticResults"], "removed operator still parses")

    corrupted = work / "invalid.packet"
    corrupted.write_text('(result (node Missing nil) nil)\n')
    failed = subprocess.run([*map(str, lean), "--run", str(TOOLS / "check_prolog_source.lean"),
        "iso", str(work / "fact.pl"), str(corrupted)], cwd=REPO / "lean/mettapedia", capture_output=True, text=True)
    (work / "invalid.log").write_text(failed.stdout + failed.stderr)
    require(failed.returncode != 0 and "source packet failed independent certificate replay" in failed.stdout + failed.stderr,
            "invalid source packet was not rejected by replay")
    summary = dict(cases=len(results), independent_coverage_cases=6, datalog_profiles=2,
                   ordinary_datalog_agreement=True, corrupt_packet_rejected=True,
                   stateful_sentences=len(units), removed_operator_refused=True,
                   reader_sha256=hashlib.sha256(binary.read_bytes()).hexdigest())
    (work / "qualification.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
