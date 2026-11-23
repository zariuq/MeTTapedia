#!/usr/bin/env python3
"""Check three authored source grammars, retained forests and native examples.

This is a syntax/selection gate. It does not execute OCaml, Maude or Erlang IR
through MeTTa, certify their operational semantics, or seal a language core.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re

from packed_source_reader import Commands, REPO, TOOLS, build_native_reader, compile_pack, parse_source


OCAML_RESULTS = {
    "core_recursion": "(720, 55)",
    "core_lists": "([2; 3; 4], 6, [1; 2; 3; 4], [3; 2; 1])",
    "core_mutual": "(true, true, false)",
    "core_variants": "(42, 9)",
    "core_closures": "(7, 7, 13)",
    "core_sort": "[1; 1; 2; 3]",
}
MAUDE_RESULTS = {
    "core_peano": [("Nat", "s(s(s(s(s(s(0))))))")],
    "core_bags": [("Nat", "s(s(s(0)))"), ("Bag", "a b")],
    "core_conditional": [("Nat", "s(s(0))")],
    "compound_unit": [("Element", "zero")],
}
ERLANG_RESULTS = {
    "core_sequential": "{120,[3,2,1],[1,2,3],[2,3]}",
    "core_pingpong": "done",
    "core_counter": "2",
    "core_selective": "{a,b}",
    "core_parallel_map": "[9,1,4]",
}
BAD = {
    "ocaml": [
        ("unclosed-parenthesis", "(1 + 2;;"),
        ("unclosed-comment", "(* missing end"),
        ("unclosed-string", '"missing end'),
        ("missing-else", "if true then 1;;"),
        ("reserved-binder", "let if = 1;;"),
    ],
    "maude": [
        ("missing-module-end", "fmod M is sort S ."),
        ("unclosed-attributes", "fmod M is sort S . op a : -> S [ctor . endfm"),
        ("missing-equation-rhs", "fmod M is sort S . op a : -> S . eq a = . endfm"),
        ("unclosed-term", "red f(a ."),
    ],
    "erlang": [
        ("missing-module-end", "module 'm' [] attributes []"),
        ("unclosed-atom", "module 'm [] attributes [] end"),
        ("missing-function-arrow", "module 'm' ['f'/0] attributes [] 'f'/0 = fun () 1 end"),
        ("unclosed-case", "module 'm' ['f'/0] attributes [] 'f'/0 = fun () -> case 1 of <1> when 'true' -> 2 end"),
    ],
}


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
    parser.add_argument("--maude", type=Path, required=True)
    parser.add_argument("--erlang-bin", type=Path, required=True)
    parser.add_argument("--replay-results", type=int, default=256)
    args = parser.parse_args()
    work = args.work.resolve()
    require(not work.exists(), "use a new work directory")
    require(args.replay_results > 0, "the selected-replay budget must be positive")
    work.mkdir(parents=True)
    commands = Commands(work)
    host = args.cetta_source.resolve()
    gold = REPO / "metta/gslt/module/gold"
    inputs = [TOOLS / name for name in ["test_core_syntax.py", "packed_source_reader.py",
        "parse_gslt_source.c", "source_family_selection.h", "export_core_reader.lean"]]
    inputs += [REPO / "lean/mettapedia/Mettapedia/GSLT/LanguageDef/ModuleFormat" / name
               for name in ["SourceSyntax.lean", "SourceSyntaxExport.lean", "GoldCoreSyntax.lean"]]
    inputs += [gold / "SourceLexical.module"] + [gold / language / "Syntax.module"
                                                for language in ["OCaml", "Maude", "Erlang"]]
    inputs += [source for language, extension in [("OCaml", "ml"), ("Maude", "maude"), ("Erlang", "erl")]
               for source in sorted((gold / language / "examples").glob(f"core_*.{extension}"))]
    inputs += sorted((gold / "Maude/controls").glob("*.maude"))
    initial = {str(path): sha(path) for path in inputs}
    commands.run("proof-build", ["lake", "--wfail", "build",
        "Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntax",
        "Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxExport"])
    binary, native_sources = build_native_reader(host, work / "native", commands, selections=True)
    inputs += native_sources
    inputs += sorted((host / "experiments/gslt2parse_foundation/native").glob("*.h"))
    references = []
    examples = {"ocaml": [], "maude": [], "erlang": []}

    for name, expected in OCAML_RESULTS.items():
        source = gold / "OCaml/examples" / (name + ".ml")
        output = commands.run("reference-" + name,
            [args.ocaml, "-noinit", "-noprompt", "-no-version"], input=source.read_bytes())
        text = output.read_text()
        require("- :" in text, name + ": OCaml did not report a final value")
        value = " ".join(text.rsplit("- :", 1)[1].split("=", 1)[1].split())
        require(value == expected, name + ": unexpected OCaml value")
        require(not output.with_suffix(".err").read_bytes(), name + ": OCaml diagnostic")
        references.append({"language": "ocaml", "case": name, "value": value})
        examples["ocaml"].append(source)

    maude_env = dict(os.environ, MAUDE_LIB=str(args.maude.resolve().parent))
    maude_sources = sorted((gold / "Maude/examples").glob("core_*.maude")) + sorted((gold / "Maude/controls").glob("*.maude"))
    for source in maude_sources:
        output = commands.run("reference-" + source.stem,
            [args.maude, "-no-banner", "-no-advise", "-no-wrap"],
            cwd=args.maude.resolve().parent, input=source.read_bytes() + b"\nquit\n", env=maude_env)
        text = output.read_text()
        require(not output.with_suffix(".err").read_bytes(), source.stem + ": Maude diagnostic")
        results = re.findall(r"^result ([^:]+): (.+)$", text, re.M)
        if source.stem in MAUDE_RESULTS:
            require(results == MAUDE_RESULTS[source.stem], source.stem + ": unexpected Maude value")
        elif source.stem == "core_mutex":
            require("No solution." in text and "Solution 1" not in text, "mutex search did not settle negatively")
        elif source.stem == "core_vending":
            solutions = sorted(tuple(sorted(value.split()))
                               for value in re.findall(r"^M --> (.+)$", text, re.M))
            expected = sorted([( "q", "q", "q", "q"), ("$",), ("c",), ("a", "q")])
            require(solutions == expected and "No more solutions." in text, "vending solutions differ")
        else:
            raise RuntimeError("no native observation declared for " + source.stem)
        references.append({"language": "maude", "case": source.stem, "values": results})
        examples["maude"].append(source)

    erlang_sources = sorted((gold / "Erlang/examples").glob("core_*.erl"))
    for mode, flags in [("core", ["+to_core"]), ("beam", [])]:
        destination = work / mode
        destination.mkdir()
        output = commands.run("erlang-" + mode,
            [args.erlang_bin / "erlc", "-Werror", *flags, "-o", destination, *erlang_sources])
        require(not output.read_bytes() and not output.with_suffix(".err").read_bytes(),
                "Erlang compilation produced diagnostics")
    for source in erlang_sources:
        examples["erlang"].append(work / "core" / (source.stem + ".core"))
        if source.stem == "core_blocked":
            references.append({"language": "erlang", "case": source.stem,
                               "compiled": True, "runtime_observation": "not run"})
            continue
        expression = f'io:format("~tp~n", [{source.stem}:run()]), halt().'
        output = commands.run("reference-" + source.stem,
            [args.erlang_bin / "erl", "-noshell", "-pa", work / "beam", "-eval", expression])
        value = output.read_text().strip()
        require(not output.with_suffix(".err").read_bytes(), source.stem + ": Erlang diagnostic")
        if source.stem == "core_sender_order":
            require(value in ["[a1,a2,b]", "[a1,b,a2]", "[b,a1,a2]"], "sender-order witness violates per-sender ordering")
        else:
            require(value == ERLANG_RESULTS[source.stem], source.stem + ": unexpected Erlang value")
        references.append({"language": "erlang", "case": source.stem, "witness": value})
    (work / "references.json").write_text(json.dumps(references, indent=2) + "\n")

    rows = []
    for language in examples:
        exported = work / (language + "-pack")
        commands.run(language + "-export", ["lake", "env", "lean", "-DwarningAsError=true",
            "--run", TOOLS / "export_core_reader.lean", language, exported])
        abi, start, support = compile_pack(host, exported, commands, language + "-compile")
        inputs += support
        cases = [(source.stem, source, True) for source in examples[language]]
        for label, text in BAD[language]:
            source = work / (language + "-" + label + ".source")
            source.write_text(text)
            cases.append((label, source, False))
        if language == "ocaml":
            source = work / "keyword-prefix.ml"
            source.write_text("let ifx = 1;; ifx;;")
            cases.append(("keyword-prefix", source, True))
        for label, source, expected in cases:
            key = language + "-" + label
            raw_forest, selected_forest = work / (key + ".raw.cnf"), work / (key + ".selected.cnf")
            raw = parse_source(binary, abi, start, source, raw_forest, commands, key + "-raw",
                               recognize_only=True)
            selected = parse_source(binary, abi, start, source, selected_forest, commands, key + "-selected",
                selection=exported / "selection.term", result_limit=args.replay_results)
            require(raw["outcome"] == 0 and selected["outcome"] == 0,
                    key + ": recognition or selected replay remains pending")
            require((selected["semanticResults"] > 0) == expected, key + ": wrong selected-source decision")
            require(sha(raw_forest) == sha(selected_forest), key + ": selection changed the original forest")
            require(raw["semanticResults"] == 0 and raw["recognitionOnly"], key + ": eager tree expansion")
            for outcome in [raw, selected]:
                require(outcome["inputBytes"] == source.stat().st_size and
                        outcome["inputScalars"] == len(source.read_text()) and outcome["sourcePasses"] == 1,
                        key + ": source accounting mismatch")
            rows.append({"language": language, "case": label, "expected": expected,
                "raw": raw, "selected": selected, "forest_sha256": sha(raw_forest),
                "source_sha256": sha(source), "recognition_and_replay_complete": True})
            (work / "syntax-results.json").write_text(json.dumps(rows, indent=2) + "\n")

    require(all(sha(path) == value for path, value in initial.items()), "source inputs changed during the gate")
    inputs = sorted(set(inputs))
    manifest = {"scope": "authored syntax, explicit local selection and retained packed forests",
        "cases": len(rows), "positive_cases": sum(row["expected"] for row in rows),
        "negative_cases": sum(not row["expected"] for row in rows),
        "native_examples": len(references), "core_execution_through_metta": False,
        "qualified_cores": 0, "native_reader_sha256": sha(binary),
        "inputs": {str(path): sha(path) for path in inputs},
        "references": {str(path): sha(path) for path in [args.ocaml.resolve(), args.maude.resolve(),
            (args.erlang_bin / "erlc").resolve(), (args.erlang_bin / "erl").resolve()]}}
    (work / "qualification.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"{len(rows)} syntax/selection controls; {len(references)} native example records; all forests retained")


if __name__ == "__main__":
    main()
