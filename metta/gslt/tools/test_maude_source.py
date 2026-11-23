#!/usr/bin/env python3
"""Check current Maude source syntax and signature-directed elaboration.

Every retained structural alternative is elaborated. Successful results must
agree; operator ambiguity is refused. Signature interfaces for imports do not
admit imported equation theories. Native reduction/search records are separate
reference evidence, not execution of the elaborated theory in MeTTa.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re

from packed_source_reader import Commands, REPO, TOOLS, build_native_reader, compile_pack, parse_source
from test_core_syntax import MAUDE_RESULTS


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--cetta-source", type=Path, required=True)
    parser.add_argument("--maude", type=Path, required=True)
    parser.add_argument("--existing-build", action="store_true")
    args = parser.parse_args()
    work = args.work.resolve()
    require(not work.exists(), "use a new work directory")
    work.mkdir(parents=True)
    commands = Commands(work)
    gold = REPO / "metta/gslt/module/gold"
    sources = sorted((gold / "Maude/examples").glob("core_*.maude")) + sorted((gold / "Maude/controls").glob("*.maude"))
    module = REPO / "lean/mettapedia/Mettapedia/GSLT/LanguageDef/ModuleFormat"
    inputs = [Path(__file__), TOOLS / "packed_source_reader.py", TOOLS / "test_core_syntax.py",
              TOOLS / "parse_gslt_source.c", TOOLS / "source_family_selection.h",
              TOOLS / "export_core_reader.lean", TOOLS / "check_maude_source.lean",
              module / "SourcePacket.lean", module / "SourcePacketView.lean", module / "GoldCoreSyntax.lean",
              module / "MaudeSourceResolution.lean", module / "MaudeSourceLowering.lean",
              gold / "SourceLexical.module", gold / "Maude/Syntax.module", args.maude.resolve(), *sources]
    inputs += [args.maude.resolve().parent / "prelude.maude"]
    model = REPO / "lean/mettapedia/Mettapedia/Languages/Maude"
    inputs += [model / name for name in ["Syntax.lean", "DecidableEquality.lean", "Semantics.lean", "Examples.lean", "PeanoNormalization.lean"]]
    for name in ["MaudeSourceResolution", "MaudeSourceLowering", "GoldCoreSyntax"]:
        inputs.append(REPO / "lean/mettapedia/.lake/build/lib/lean/Mettapedia/GSLT/LanguageDef/ModuleFormat" / (name + ".olean"))
    initial = {str(path): sha(path) for path in inputs}
    if not args.existing_build:
        commands.run("build", ["lake", "--wfail", "build",
            "Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeSourceLowering",
            "Mettapedia.Languages.Maude.PeanoNormalization"])
    binary, native = build_native_reader(args.cetta_source, work / "native", commands, selections=True)
    inputs += native
    exported = work / "grammar"
    commands.run("export", ["lake", "env", "lean", "-DwarningAsError=true", "--run",
                            TOOLS / "export_core_reader.lean", "maude", exported])
    abi, start, support = compile_pack(args.cetta_source, exported, commands, "pack")
    inputs += support
    cases = [(source.stem, source, False) for source in sources]
    heterogeneous = work / "heterogeneous_comm.maude"
    heterogeneous.write_text("fmod HETERO is sorts S T . ops a b : -> S [ctor] . "
                             "op f : S S -> T [comm] . endfm red f(b,a) .")
    cases.append(("heterogeneous_comm", heterogeneous, False))
    for name, text in [
        ("unknown_operator", "fmod GOLD-PEANO is sort Nat . op 0 : -> Nat . endfm red missing ."),
        ("unknown_sort", "fmod M is op a : -> Missing . endfm red a ."),
        ("wrong_arity", "fmod M is sort S . op a : -> S . op f : S -> S . endfm red f(a,a) ."),
        ("ambiguous_operator", "fmod M is sort S . op a : -> S . op _+_ : S S -> S . endfm red a + a + a ."),
        ("unknown_import", "fmod M is protecting MISSING . sort S . op a : -> S . endfm red a ."),
        ("functional_rule", "fmod M is sort S . ops a b : -> S . rl a => b . endfm red a ."),
        ("wrong_unit_sort", "fmod M is sorts S T . op a : -> S . op t : -> T . op __ : S S -> S [assoc id: t] . endfm red a ."),
        ("rewrite_condition", "mod M is sort S . ops a b : -> S . crl a => b if a => b . endm rew a ."),
    ]:
        source = work / (name + ".maude")
        source.write_text(text)
        cases.append((name, source, True))
    env = dict(os.environ, MAUDE_LIB=str(args.maude.resolve().parent))
    results = []
    for name, source, refuse in cases:
        forest = work / (name + ".forest")
        parsed = parse_source(binary, abi, start, source, forest, commands, "parse-" + name,
            selection=exported / "selection.term", result_limit=256)
        require(parsed["outcome"] == 0 and parsed["semanticResults"] > 0,
                name + ": source replay did not produce a complete finite result")
        packet = work / (name + ".packet")
        packet.write_text("\n".join((work / ("parse-" + name + ".out")).read_text().splitlines()[1:]) + "\n")
        checked = commands.run("lower-" + name, ["lake", "env", "lean", "-DwarningAsError=true",
            "--run", TOOLS / "check_maude_source.lean", source, packet,
            "--ambiguous" if name == "ambiguous_operator" else "--refuse" if refuse else name])
        require(not checked.with_suffix(".err").read_bytes(), name + ": elaboration diagnostic")
        reference = None
        if not refuse:
            output = commands.run("reference-" + name, [args.maude, "-no-banner", "-no-advise", "-no-wrap"],
                cwd=args.maude.resolve().parent, input=source.read_bytes() + b"\nquit\n", env=env)
            require(not output.with_suffix(".err").read_bytes(), name + ": native Maude diagnostic")
            text = output.read_text()
            reference = re.findall(r"^result ([^:]+): (.+)$", text, re.M)
            if name in MAUDE_RESULTS:
                require(reference == MAUDE_RESULTS[name], name + ": native result differs")
            elif name == "heterogeneous_comm":
                require(reference == [("T", "f(a, b)")], "commutativity changed the result sort")
            elif name == "core_mutex":
                require("No solution." in text and "Solution 1" not in text, "mutex safety search differs")
            elif name == "core_vending":
                solutions = sorted(tuple(sorted(value.split())) for value in re.findall(r"^M --> (.+)$", text, re.M))
                require(solutions == sorted([("q", "q", "q", "q"), ("$",), ("c",), ("a", "q")]) and
                        "No more solutions." in text, "vending solutions differ")
            else:
                raise RuntimeError("unknown native fixture " + name)
        results.append({"name": name, "refused": refuse, "parser": parsed, "native": reference,
                        "elaboration": checked.read_text().strip(), "source_sha256": sha(source),
                        "packet_sha256": sha(packet), "forest_sha256": sha(forest)})
        (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    require(all(sha(path) == digest for path, digest in initial.items()), "inputs changed during checking")
    record = {"passed": True, "cases": len(results), "scope": "Current grammar, signature-directed IR and native reference records",
              "input_pins": {str(path): sha(path) for path in sorted(set(inputs))},
              "fresh_dependency_build": not args.existing_build, "import_signature_is_execution_certificate": False,
              "universal_frontend_correspondence": False, "emitted_metta_qualified": False, "full_M0_qualified": False}
    (work / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"{len(results)} Maude source/elaboration controls passed; native reference records agree")


if __name__ == "__main__":
    main()
