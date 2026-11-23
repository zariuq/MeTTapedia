#!/usr/bin/env python3
"""Compare whole prepared-IR CHR programs on both shared-runtime engines."""

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

from packed_source_reader import Commands, build_native_reader, parse_direct_source
from source_io import source_command

PROGRAMS = ["minimum", "propagation", "gcd", "sieve", "fibonacci", "cyclic_paths", "empty",
            "guard_false", "guard_true", "partner_choice", "partner_choice_wide", "partner_pair", "guarded_partner"]


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--program", action="append", choices=PROGRAMS)
    parser.add_argument("--cetta", type=Path)
    parser.add_argument("--petta-runner", type=Path)
    parser.add_argument("--source", action="store_true", help="read the ordinary CHR source fixtures through syntaxGSLT")
    parser.add_argument("--reader", type=Path, help="reuse an existing native source reader")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    gslt, lean = repo / "metta/gslt", repo / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    programs = args.program or PROGRAMS
    cetta = (args.cetta or repo.parent / "hyperon/cetta-prime-2.0-draft-20260910/cetta").resolve()
    petta = (args.petta_runner or repo.parent / "hyperon/PeTTa/run.sh").resolve()
    generator = gslt / "tools/generate_chr_program_controls.lean"
    targets = re.findall(r"^import (Mettapedia\.[A-Za-z0-9_.]+)$", generator.read_text(), re.M)
    with (output / "build.log").open("w") as log:
        subprocess.run(["lake", "--wfail", "build", *targets, *(["sourceSyntax"] if args.source else [])],
                       cwd=lean, stdout=log, stderr=subprocess.STDOUT, check=True)
    common_gate = gslt / "tools/test_gslt_complete.sh"
    match = re.search(r"^libraries=\((.*?)^\)", common_gate.read_text(), re.S | re.M)
    if match is None:
        raise RuntimeError("the common runtime library list is missing")
    libraries = [gslt / f"lib/{name}.metta" for name in match[1].split()]
    libraries += [gslt / "lib/gslt_integer.metta", gslt / "lib/gslt_chr.metta"]
    inputs = {Path(__file__).resolve(), generator, common_gate, *libraries, cetta, petta,
              lean / "lean-toolchain", lean / "lakefile.lean", lean / "lake-manifest.json"}
    inputs.update((petta.parent / "src").rglob("*.pl"))
    swipl = shutil.which("swipl")
    if swipl is None:
        raise RuntimeError("SWI-Prolog is required by the PeTTa runner")
    inputs.add(Path(swipl).resolve())
    mork = petta.parent / "mork_ffi/target/release/libmork_ffi.so"
    if mork.is_file():
        inputs.add(mork.resolve())
    inputs.update(gslt / "module" / (name + ".module") for name in ["CHRIR", "CHRProgram", "CHRMatch", "Radix16"])
    for target in targets:
        relative = Path(*target.split("."))
        setup = lean / ".lake/build/ir" / relative.with_suffix(".setup.json")
        inputs.update([setup, lean / relative.with_suffix(".lean"), lean / ".lake/build/lib/lean" / relative.with_suffix(".olean")])
        for dependency, groups in json.loads(setup.read_text())["importArts"].items():
            if dependency.startswith("Mettapedia."):
                inputs.add(lean / Path(*dependency.split(".")).with_suffix(".lean"))
            inputs.update(Path(path) for group in groups for path in group)
    source_pipeline = None
    if args.source:
        source_module = gslt / "module/gold/CHR/CHRSyntax.module"
        source_commands = Commands(output / "source-commands")
        source_prefix = source_command(source_module)
        grammar = output / "source-grammar"
        source_commands.run("source-export", [*source_prefix, "export", grammar])
        if args.reader:
            reader = args.reader.resolve(strict=True)
        else:
            reader, native_sources = build_native_reader(cetta.parent, output / "source-reader", source_commands, selections=True)
            inputs.update(native_sources)
        inputs.update([reader, source_module, lean / ".lake/build/bin/sourceSyntax",
                       gslt / "module/prolog/PrologCommonSyntax.module"])
        inputs.update(grammar.iterdir())
        inputs.update(gslt / "module/gold/CHR/examples/c0" / (name + ".chr") for name in programs)
        source_pipeline = (source_commands, source_prefix, grammar, reader)
    pins = {str(path): digest(path) for path in inputs if path.is_file()}
    results = []

    def run_engine(label, command, directory):
        started = time.monotonic()
        with (directory / f"{label}.out").open("w") as stdout, (directory / f"{label}.err").open("w") as stderr:
            result = subprocess.run(command, cwd=lean, env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"), stdout=stdout, stderr=stderr)
        rows = (directory / f"{label}.out").read_text().splitlines()
        controls = [row for row in rows if row.startswith("(CHRWholeProgramControl ")]
        parsed = [re.fullmatch(r'\(CHRWholeProgramControl "([^"]+)" (true|false) (true|false) (true|false) ([0-9]+) ([0-9]+)\)', row) for row in controls]
        wires = [row for row in rows if row.startswith("(CHRWireControl ")]
        passed = (result.returncode == 0 and not (directory / f"{label}.err").read_text()
                  and len(parsed) == 1 and parsed[0] is not None and parsed[0].groups()[1:4] == ("true",) * 3
                  and len(wires) == 7 and all(re.findall(r"\b(?:true|false)\b", row) == ["true", "true"] for row in wires))
        return {"engine": label, "exit_code": result.returncode, "seconds": time.monotonic() - started,
                "passed": passed, "whole_program": controls, "wire_controls": wires,
                "stdout_sha256": digest(directory / f"{label}.out"), "stderr_sha256": digest(directory / f"{label}.err")}

    if not args.source:
        with (output / "generation.log").open("w") as log:
            subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", str(generator), str(output),
                            "--batch", *programs], cwd=lean, stdout=log, stderr=subprocess.STDOUT, check=True)
    for name in programs:
        directory = output / name
        if source_pipeline:
            directory.mkdir()
            commands, prefix, grammar, reader = source_pipeline
            source = gslt / "module/gold/CHR/examples/c0" / (name + ".chr")
            forest = directory / "source.forest"
            status = parse_direct_source(reader, grammar, source, forest, commands, name + "-parse", selected=True)
            if not status["accepted"] or status["outcome"] != 0:
                raise RuntimeError(name + ": source recognition rejected or remains unfinished")
            lines = (commands.work / (name + "-parse.out")).read_text().splitlines()[1:]
            if len(lines) != status["semanticResults"]:
                raise RuntimeError(name + ": source result count differs")
            packets = directory / "source.packets"
            packets.write_text("".join(line + "\n" for line in lines))
            rounds = 32 * (status["inputScalars"] + 1) + 256
            commands.run(name + "-coverage", [*prefix, "coverage", source, forest, str(forest) + ".pni", rounds])
            commands.run(name + "-catalogue", [*prefix, "catalogue", source, forest, str(forest) + ".pni", packets, rounds])
            commands.run(name + "-generate", ["lake", "env", "lean", "-DwarningAsError=true", "--run", generator,
                directory, "--source", name, source, packets])
            (directory / "source-status.json").write_text(json.dumps(status, indent=2) + "\n")
        workload = directory / "workload.metta"
        workload.write_text("\n".join(path.read_text() for path in [*libraries, directory / "query.metta", directory / "controls.metta"]))
        for path in [workload, directory / "query.metta", directory / "controls.metta"]:
            pins[str(path)] = digest(path)
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            jobs = [pool.submit(run_engine, "cetta", [str(cetta), "--lang", "petta", "--quiet", str(workload)], directory),
                    pool.submit(run_engine, "petta", ["bash", str(petta), "--silent", str(workload)], directory)]
            engines = [job.result() for job in jobs]
        identical = (engines[0]["whole_program"] == engines[1]["whole_program"] and engines[0]["wire_controls"] == engines[1]["wire_controls"])
        results.append({"program": name, "engines": engines, "outputs_identical": identical,
                        "passed": all(engine["passed"] for engine in engines) and identical})
        print(json.dumps(results[-1]), flush=True)
    changed = [path for path, before in pins.items() if digest(Path(path)) != before]
    record = {"programs": results, "input_pins": pins, "changed_inputs": changed,
              "all_passed": all(result["passed"] for result in results) and not changed,
              "scope": ("Ordinary CHR source fixtures: complete forest/catalogue, source/IR agreement, exact source printing, final multisets and resumption"
                        if args.source else "Whole prepared IR programs, exact final multisets, resumption and shared-wire interoperability controls"),
              "ordinary_source_fixture_controls_qualified": args.source,
              "universal_frontend_correspondence_proved": False, "source_controller_correspondence_proved": False}
    (output / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    if not record["all_passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
