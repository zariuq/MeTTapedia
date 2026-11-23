#!/usr/bin/env python3
"""Check textual Core Erlang through its authored grammar and independent IR.

The native compiler supplies Core text and BEAM supplies reference observations.
Packed forests are retained. Actor comparisons witness one fair model schedule;
schedule-sensitive outputs check membership in the declared permitted set.
This gate does not certify every source program or the emitted MeTTa backend.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path

from packed_source_reader import Commands, REPO, TOOLS, build_native_reader, compile_pack, parse_source


RESULTS = {
    "core_sequential": "{120,[3,2,1],[1,2,3],[2,3]}",
    "core_pingpong": "done",
    "core_counter": "2",
    "core_selective": "{a,b}",
    "core_parallel_map": "[9,1,4]",
    "core_function_message": "42",
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
    parser.add_argument("--erlang-bin", type=Path, required=True)
    parser.add_argument("--existing-build", action="store_true",
                        help="use existing Lean objects and record that no dependency build was run")
    args = parser.parse_args()
    work = args.work.resolve()
    require(not work.exists(), "use a new work directory")
    work.mkdir(parents=True)
    commands = Commands(work)
    erlang = args.erlang_bin.resolve()
    version = erlang.parent / "lib/erlang/releases/29/OTP_VERSION"
    require(version.read_text().strip() == "29.1.2", "expected Erlang/OTP 29.1.2")
    examples = REPO / "metta/gslt/module/gold/Erlang/examples"
    ordinary = sorted(examples.glob("core_*.erl"))
    module = REPO / "lean/mettapedia/Mettapedia/GSLT/LanguageDef/ModuleFormat"
    inputs = [Path(__file__), TOOLS / "packed_source_reader.py", TOOLS / "check_erlang_source.lean",
              TOOLS / "export_core_reader.lean", TOOLS / "parse_gslt_source.c",
              TOOLS / "source_family_selection.h", module / "SourcePacket.lean", module / "SourcePacketView.lean",
              module / "GoldCoreSyntax.lean", module / "SourceSyntaxExport.lean",
              module / "ErlangSourceLowering.lean", REPO / "metta/gslt/module/gold/SourceLexical.module",
              REPO / "metta/gslt/module/gold/Erlang/Syntax.module", version,
              erlang / "erl", erlang / "erlc", *ordinary]
    inputs += sorted((erlang.parent / "lib/erlang").glob("erts-*/bin/beam.smp"))
    initial = {str(path): sha(path) for path in inputs}
    if not args.existing_build:
        commands.run("build", ["lake", "--wfail", "build",
            "Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangSourceLowering",
            "Mettapedia.Languages.Erlang.ActorExamples"])
    core, beam = work / "core", work / "beam"
    core.mkdir()
    beam.mkdir()
    commands.run("compile-core", [erlang / "erlc", "-Werror", "+to_core", "-o", core, *ordinary])
    commands.run("compile-beam", [erlang / "erlc", "-Werror", "-o", beam, *ordinary])
    binary, native = build_native_reader(args.cetta_source, work / "native", commands, selections=True)
    inputs += native
    exported = work / "grammar"
    commands.run("export", ["lake", "env", "lean", "-DwarningAsError=true", "--run",
                            TOOLS / "export_core_reader.lean", "erlang", exported])
    abi, start, support = compile_pack(args.cetta_source, exported, commands, "pack")
    inputs += support
    cases = [(path.stem, core / (path.stem + ".core"), False) for path in ordinary]
    cases.append(("core_multiple_values", examples / "core_multiple_values.core", False))
    extra = {
        "core_shadow": ("module 'core_shadow' ['run'/0] attributes [] "
            "'run'/0 = fun () -> let <X> = 1 in case 2 of <X> when 'true' -> X end end", False),
        "core_local_shadow": ("module 'core_local_shadow' ['run'/0,'g'/0] attributes [] "
            "'g'/0 = fun () -> call 'erlang':'get_module_info'('core_local_shadow') "
            "'run'/0 = fun () -> letrec 'g'/0 = fun () -> 7 in apply 'g'/0() end", False),
        "undefined_export": ("module 'm' ['run'/0,'missing'/0] attributes [] 'run'/0 = fun () -> 1 end", True),
        "duplicate_definition": ("module 'm' ['run'/0] attributes [] 'run'/0 = fun () -> 1 'run'/0 = fun () -> 2 end", True),
        "header_arity": ("module 'm' ['run'/0] attributes [] 'run'/0 = fun () -> 1 'g'/1 = fun () -> 2 end", True),
        "unbound_variable": ("module 'm' ['run'/0] attributes [] 'run'/0 = fun () -> X end", True),
        "reachable_metadata": ("module 'm' ['run'/0] attributes [] 'run'/0 = fun () -> call 'erlang':'get_module_info'('m') end", True),
        "external_call": ("module 'm' ['run'/0] attributes [] 'run'/0 = fun () -> call 'other':'f'() end", True),
        "finite_wait": ("module 'm' ['run'/0] attributes [] 'run'/0 = fun () -> primop 'recv_wait_timeout'(0) end", True),
        "unknown_primop": ("module 'm' ['run'/0] attributes [] 'run'/0 = fun () -> primop 'unknown'() end", True),
    }
    for name, (text, refuse) in extra.items():
        source = work / (name + ".core")
        source.write_text(text)
        cases.append((name, source, refuse))
    rows = []
    env = dict(os.environ, ERL_FLAGS="+S 1:1 +A 1")
    for name, source, refuse in cases:
        forest = work / (name + ".forest")
        parsed = parse_source(binary, abi, start, source, forest, commands, "parse-" + name,
            selection=exported / "selection.term", result_limit=256)
        require(parsed["outcome"] == 0 and parsed["semanticResults"] == 1,
                name + ": expected one complete explicitly selected parser result")
        packet = work / (name + ".packet")
        packet.write_text("\n".join((work / ("parse-" + name + ".out")).read_text().splitlines()[1:]) + "\n")
        commands.run("lower-" + name, ["lake", "env", "lean", "-DwarningAsError=true", "--run",
            TOOLS / "check_erlang_source.lean", source, packet, "--refuse" if refuse else name])
        reference = None
        if name in RESULTS or name == "core_sender_order":
            output = commands.run("reference-" + name,
                [erlang / "erl", "-noshell", "-pa", beam, "-eval",
                 f'io:format("GSLT_RESULT=~w~n",[{name}:run()]),halt().'], env=env)
            values = [line.split("=", 1)[1] for line in output.read_text().splitlines()
                      if line.startswith("GSLT_RESULT=")]
            require(len(values) == 1, name + ": missing BEAM observation")
            reference = values[0]
            if name == "core_sender_order":
                require(reference in ["[a1,a2,b]", "[a1,b,a2]", "[b,a1,a2]"], name + ": sender ordering violated")
            else:
                require(reference == RESULTS[name], name + ": BEAM observation differs")
        rows.append({"name": name, "refused": refuse, "parser": parsed, "beam": reference,
                     "model_control": (work / ("lower-" + name + ".out")).read_text().strip(),
                     "source_sha256": sha(source), "packet_sha256": sha(packet), "forest_sha256": sha(forest)})
        (work / "results.json").write_text(json.dumps(rows, indent=2) + "\n")
    commands.run("factorial-entry", ["lake", "env", "lean", "-DwarningAsError=true", "--run",
        TOOLS / "check_erlang_source.lean", core / "core_sequential.core",
        work / "core_sequential.packet", "core_factorial_entry"])
    require(all(sha(path) == digest for path, digest in initial.items()), "inputs changed during checking")
    record = {"scope": "Selected textual Core Erlang entry -> compact IR -> independent actor model",
              "passed": True, "cases": len(rows) + 1, "fresh_dependency_build": not args.existing_build,
              "input_pins": {str(path): sha(path) for path in sorted(set(inputs))},
              "emitted_metta_qualified": False, "universal_source_or_DCE_correspondence": False,
              "complete_schedule_exploration_qualified": False, "full_E0_qualified": False}
    (work / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"{len(rows) + 1} source/model controls passed; native reference observations agree")


if __name__ == "__main__":
    main()
