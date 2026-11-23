#!/usr/bin/env python3
"""Compare emitted indexed-OCaml structural programs on CeTTa and SWI PeTTa."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--cetta", type=Path)
    parser.add_argument("--petta-runner", type=Path)
    parser.add_argument("--program", action="append", choices=[
        "literal", "capture", "higher_order", "tuple_parameter", "ordered_pattern", "unselected_loop"])
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    gslt, lean = repo / "metta/gslt", repo / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    programs = args.program or ["literal", "capture", "higher_order", "tuple_parameter", "ordered_pattern", "unselected_loop"]
    cetta = (args.cetta or repo.parent / "hyperon/cetta-prime-2.0-draft-20260910/cetta").resolve()
    petta = (args.petta_runner or repo.parent / "hyperon/PeTTa/run.sh").resolve()
    generator = gslt / "tools/generate_ocaml_kernel_controls.lean"
    target = "Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilationControls"
    with (output / "build.log").open("w") as log:
        subprocess.run(["lake", "--wfail", "build", target], cwd=lean, stdout=log,
                       stderr=subprocess.STDOUT, check=True)
    common = gslt / "tools/test_gslt_complete.sh"
    match = re.search(r"^libraries=\((.*?)^\)", common.read_text(), re.S | re.M)
    if match is None:
        raise RuntimeError("the common runtime library list is missing")
    libraries = [gslt / f"lib/{name}.metta" for name in match[1].split()]
    inputs = {Path(__file__).resolve(), generator, common, *libraries, cetta, petta,
              lean / "lean-toolchain", lean / "lakefile.lean", lean / "lake-manifest.json"}
    inputs.update((petta.parent / "src").rglob("*.pl"))
    inputs.update(gslt / "module" / (name + ".module") for name in ["OCamlIR", "OCamlMachine", "Radix16"])
    relative = Path(*target.split("."))
    setup = lean / ".lake/build/ir" / relative.with_suffix(".setup.json")
    inputs.update([setup, lean / relative.with_suffix(".lean"),
                   lean / ".lake/build/lib/lean" / relative.with_suffix(".olean")])
    for dependency, groups in json.loads(setup.read_text())["importArts"].items():
        if dependency.startswith("Mettapedia."):
            inputs.add(lean / Path(*dependency.split(".")).with_suffix(".lean"))
        inputs.update(Path(path) for group in groups for path in group)
    pins = {str(path): sha(path) for path in inputs}
    results = []
    for name in programs:
        directory = output / name
        with (output / f"generate-{name}.log").open("w") as log:
            subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", generator,
                directory, name], cwd=lean, stdout=log, stderr=subprocess.STDOUT, check=True)
        workload = directory / "workload.metta"
        workload.write_text("\n".join(path.read_text()
            for path in [*libraries, directory / "machine.metta", directory / "controls.metta"]))
        for path in [workload, directory / "machine.metta", directory / "controls.metta"]:
            pins[str(path)] = sha(path)
        engines = []
        for label, command in [
            ("cetta", [str(cetta), "--lang", "petta", "--quiet", str(workload)]),
            ("petta", ["bash", str(petta), "--silent", str(workload)])]:
            with (directory / (label + ".out")).open("w") as out, (directory / (label + ".err")).open("w") as err:
                result = subprocess.run(command, cwd=lean, env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"),
                                        stdout=out, stderr=err)
            rows = [line for line in (directory / (label + ".out")).read_text().splitlines()
                    if line.startswith("(OCamlKernelControl ")]
            parsed = [re.fullmatch(r'\(OCamlKernelControl "([^"]+)" (true|false) (true|false) (true|false) (true|false) (true|false) (true|false) ([0-9]+) ([0-9]+)\)', row)
                      for row in rows]
            passed = (result.returncode == 0 and not (directory / (label + ".err")).read_bytes()
                      and len(parsed) == 1 and parsed[0] is not None and
                      parsed[0].groups()[1:7] == ("true",) * 6)
            engines.append({"engine": label, "passed": passed, "exit_code": result.returncode,
                            "controls": rows, "stdout_sha256": sha(directory / (label + ".out"))})
        identical = engines[0]["controls"] == engines[1]["controls"]
        results.append({"program": name, "engines": engines, "outputs_identical": identical,
                        "passed": identical and all(engine["passed"] for engine in engines)})
        (output / "program-results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(results[-1]), flush=True)
        if not results[-1]["passed"]:
            raise RuntimeError(name + ": native kernel controls failed")
    changed = [path for path, expected in pins.items() if sha(path) != expected]
    record = {"programs": results, "input_pins": pins, "changed_inputs": changed,
              "all_passed": not changed and all(row["passed"] for row in results),
              "scope": "Prepared structural indexed code; final values, continuation order and exact resumption",
              "full_ocaml_execution_qualified": False, "source_lowering_qualified": False,
              "primitive_service_qualified": False, "pattern_failure_control_qualified": False}
    (output / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    if not record["all_passed"]:
        raise RuntimeError("qualification inputs changed")


if __name__ == "__main__":
    main()
