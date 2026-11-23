#!/usr/bin/env python3
"""Check indexed OCaml programs through native GSLT service execution.

With --source-packets, compile the ordinary core-example source files using
the explicitly selected packets produced by test_ocaml_source.py.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--program", action="append", choices=["core_recursion", "core_lists", "core_mutual",
        "core_variants", "core_closures", "core_sort", "pattern_priority", "match_failure",
        "right_to_left_fault", "short_circuit", "literal", "capture", "higher_order",
        "tuple_parameter", "ordered_pattern", "unselected_loop"])
    parser.add_argument("--cetta", type=Path)
    parser.add_argument("--petta-runner", type=Path)
    parser.add_argument("--source-packets", type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    gslt, lean = repo / "metta/gslt", repo / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    standard = ["core_recursion", "core_lists", "core_mutual", "core_variants", "core_closures", "core_sort"]
    programs = args.program or (standard if args.source_packets else standard +
                               ["pattern_priority", "match_failure", "right_to_left_fault", "short_circuit"])
    cetta = (args.cetta or repo.parent / "hyperon/cetta-prime-2.0-draft-20260910/cetta").resolve()
    petta = (args.petta_runner or repo.parent / "hyperon/PeTTa/run.sh").resolve()
    generator = gslt / "tools/generate_ocaml_program_controls.lean"
    targets = ["Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlExecutionData",
               "Mettapedia.Languages.OCaml.Examples",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering"]
    with (output / "build.log").open("w") as log:
        subprocess.run(["lake", "--wfail", "build", *targets], cwd=lean, stdout=log,
                       stderr=subprocess.STDOUT, check=True)
    common = gslt / "tools/test_gslt_complete.sh"
    match = re.search(r"^libraries=\((.*?)^\)", common.read_text(), re.S | re.M)
    if match is None:
        raise RuntimeError("the shared library list is missing")
    libraries = [gslt / "lib" / (name + ".metta") for name in match[1].split()]
    libraries += [gslt / "lib" / name for name in ["gslt_integer.metta", "gslt_word16.metta",
                                                  "gslt_snapshot_closure.metta", "gslt_provider_cache.metta",
                                                  "gslt_ocaml.metta"]]
    inputs = {Path(__file__).resolve(), generator, common, *libraries, cetta, petta,
              lean / "lean-toolchain", lean / "lakefile.lean", lean / "lake-manifest.json"}
    inputs.update((petta.parent / "src").rglob("*.pl"))
    inputs.update(gslt / "module" / (name + ".module") for name in ["OCamlIR", "OCamlMachine", "Radix16"])
    if args.source_packets:
        inputs.update([gslt / "module/gold/OCaml/Syntax.module", gslt / "module/gold/SourceLexical.module"])
        for name in programs:
            inputs.update([gslt / "module/gold/OCaml/examples" / (name + ".ml"),
                           args.source_packets.resolve() / (name + ".packet")])
    for target in targets:
        relative = Path(*target.split("."))
        setup = lean / ".lake/build/ir" / relative.with_suffix(".setup.json")
        inputs.update([setup, lean / relative.with_suffix(".lean"),
                       lean / ".lake/build/lib/lean" / relative.with_suffix(".olean")])
        for dependency, groups in json.loads(setup.read_text())["importArts"].items():
            if dependency.startswith("Mettapedia."):
                inputs.add(lean / Path(*dependency.split(".")).with_suffix(".lean"))
            inputs.update(Path(path) for group in groups for path in group)
    pins = {str(path): sha(path) for path in inputs}
    (output / "input-pins.json").write_text(json.dumps(pins, indent=2) + "\n")
    results = []
    for name in programs:
        directory = output / name
        source_arguments = [] if not args.source_packets else [
            gslt / "module/gold/OCaml/examples" / (name + ".ml"),
            args.source_packets.resolve() / (name + ".packet")]
        with (output / ("generate-" + name + ".log")).open("w") as log:
            subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", generator,
                directory, name, *source_arguments], cwd=lean, stdout=log, stderr=subprocess.STDOUT, check=True)
        workload = directory / "workload.metta"
        workload.write_text("\n".join(path.read_text()
            for path in [*libraries, directory / "machine.metta", directory / "controls.metta"]))
        for path in [workload, directory / "machine.metta", directory / "controls.metta"]:
            pins[str(path)] = sha(path)
        (output / "input-pins.json").write_text(json.dumps(pins, indent=2) + "\n")
        engines = []
        for label, command in [("cetta", [str(cetta), "--lang", "petta", "--quiet", str(workload)]),
                               ("petta", ["bash", str(petta), "--silent", str(workload)])]:
            with (directory / (label + ".out")).open("w") as out, (directory / (label + ".err")).open("w") as err:
                started = time.perf_counter()
                result = subprocess.run(command, cwd=lean, env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"),
                                        stdout=out, stderr=err)
                elapsed = time.perf_counter() - started
            rows = [line for line in (directory / (label + ".out")).read_text().splitlines()
                    if line.startswith("(OCamlProgramControl ")]
            parsed = [re.fullmatch(r'\(OCamlProgramControl "([^"]+)" (true|false) (true|false) (true|false) ([0-9]+)\)', row)
                      for row in rows]
            passed = (result.returncode == 0 and not (directory / (label + ".err")).read_bytes()
                      and len(parsed) == 1 and parsed[0] is not None and parsed[0].groups()[1:4] == ("true",) * 3)
            engines.append({"engine": label, "passed": passed, "exit_code": result.returncode,
                            "controls": rows, "seconds": elapsed,
                            "stdout_sha256": sha(directory / (label + ".out"))})
        identical = engines[0]["controls"] == engines[1]["controls"]
        results.append({"program": name, "engines": engines, "outputs_identical": identical,
                        "passed": identical and all(engine["passed"] for engine in engines)})
        (output / "program-results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(results[-1]), flush=True)
        if not results[-1]["passed"]:
            raise RuntimeError(name + ": native program controls failed")
    changed = [path for path, expected in pins.items() if sha(path) != expected]
    record = {"programs": results, "input_pins": pins, "changed_inputs": changed,
              "all_passed": not changed and all(row["passed"] for row in results),
              "scope": ("Ordinary source and selected packets" if args.source_packets else "Prepared IR") +
                       ", native services, retained provider epochs and exact resumption",
              "source_lowering_executed": bool(args.source_packets),
              "source_lowering_qualified": False, "controller_correspondence_proved": False,
              "full_ocaml_core_qualified": False}
    (output / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    if not record["all_passed"]:
        raise RuntimeError("qualification inputs changed")


if __name__ == "__main__":
    main()
