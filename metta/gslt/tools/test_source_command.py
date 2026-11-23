#!/usr/bin/env python3
"""Compare compiled and interpreted execution of the shared source checker."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

from packed_source_reader import Commands, LEAN, REPO, build_native_reader, parse_direct_source
from source_io import SOURCE_BINARY, source_command, write_driver


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--host", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    args = parser.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    commands = Commands(work / "commands")
    commands.run("build", ["lake", "--wfail", "build", "sourceSyntax"])
    module = REPO / "metta/gslt/tests/source_io/SourceIOPolicy.module"
    driver = write_driver(module, work / "Interpreted.lean")
    prefixes = {"compiled": source_command(module),
                "interpreted": ["lake", "env", "lean", "-DwarningAsError=true", "--run", driver]}
    rows = []

    def run(label, operation, arguments, diagnostic=None):
        outputs = []
        for engine, prefix in prefixes.items():
            started = time.monotonic()
            result = subprocess.run([str(x) for x in [*prefix, operation, *arguments]],
                                    cwd=LEAN, capture_output=True, text=True)
            (work / f"{label}-{engine}.log").write_text(result.stdout + result.stderr)
            if diagnostic is None:
                if result.returncode:
                    raise RuntimeError(f"{label}/{engine}: source command failed")
                outputs.append(result.stdout)
            elif result.returncode == 0 or diagnostic not in result.stdout + result.stderr:
                raise RuntimeError(f"{label}/{engine}: expected refusal or pending diagnostic")
            rows.append(dict(control=label, engine=engine, seconds=time.monotonic() - started,
                             exit_code=result.returncode))
        if outputs and outputs[0] != outputs[1]:
            raise RuntimeError(label + ": checker output differs")

    for engine, prefix in prefixes.items():
        commands.run(engine + "-export", [*prefix, "export", work / (engine + "-grammar")])
    compiled = work / "compiled-grammar"
    interpreted = work / "interpreted-grammar"
    if {p.name: p.read_bytes() for p in compiled.iterdir()} != {p.name: p.read_bytes() for p in interpreted.iterdir()}:
        raise RuntimeError("compiled grammar export differs")
    native, native_sources = build_native_reader(args.host, work / "native", commands, selections=True)
    for word, label, selected in (("y", "Other", True), ("x", "First", False)):
        source = work / (word + ".source")
        source.write_text(word)
        packet = work / (word + ".packet")
        packet.write_text(f"(result (node {label} nil) nil)\n")
        forest = work / (word + ".cnf")
        status = parse_direct_source(native, compiled, source, forest, commands, word + "-parse",
                                     selected=True, result_limit=16)
        if status["outcome"] != 0 or (status["semanticResults"] > 0) != selected:
            raise RuntimeError("native selection differs")
        catalogue = work / (word + ".packets")
        catalogue.write_text(packet.read_text() if selected else "")
        run(word + "-forest", "forest", [source, forest, str(forest) + ".pni"])
        run(word + "-coverage", "coverage", [source, forest, str(forest) + ".pni", 64])
        run(word + "-catalogue", "catalogue", [source, forest, str(forest) + ".pni", catalogue, 64])
        run(word + "-pending", "catalogue", [source, forest, str(forest) + ".pni", catalogue, 0],
            "selected catalogue construction remains pending")
        if not selected:
            run("policy-refusal", "read", [source, packet, work / "refused.core"],
                "violates the declared selection policy")
        else:
            for engine, prefix in prefixes.items():
                core, printed = work / (engine + ".core"), work / (engine + ".printed")
                commands.run(engine + "-read", [*prefix, "read", source, packet, core])
                commands.run(engine + "-print", [*prefix, "print", core, printed])
                if printed.read_bytes() != source.read_bytes():
                    raise RuntimeError("source text changed")
            if (work / "compiled.core").read_bytes() != (work / "interpreted.core").read_bytes():
                raise RuntimeError("source core changed")
            omitted = work / "omitted.packets"
            omitted.write_text("")
            run("omitted-result", "catalogue", [source, forest, str(forest) + ".pni", omitted, 64],
                "differ from the complete selected catalogue")
    run("wrong-operation", "missing-operation", [], "expected export DIRECTORY")
    digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    record = dict(controls=rows, exact_exports=True, exact_cores=True, exact_printed_text=True,
                  compiled_sha256=digest(SOURCE_BINARY), module_sha256=digest(module),
                  native_sources={str(path): digest(path) for path in native_sources})
    (work / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"comparisons": len(rows) // 2, "exports_cores_and_printing_equal": True}))


if __name__ == "__main__":
    main()
