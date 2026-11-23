#!/usr/bin/env python3
"""Execute the compiled indexed Erlang machine on both pinned MeTTa engines.

The arena, primitive service and exact resumption are compared with the
independent reference model. Source lowering, universal source/controller
correspondence, the full identity profile and E0 qualification remain open.
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
    parser.add_argument("--program", action="append")
    parser.add_argument("--cetta", type=Path)
    parser.add_argument("--petta-runner", type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    gslt, lean = repo / "metta/gslt", repo / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    targets = ["Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangExecutionData",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangCompilationControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangPrimitiveControls"]
    with (output / "build.log").open("w") as log:
        subprocess.run(["lake", "--wfail", "build", *targets], cwd=lean, stdout=log,
                       stderr=subprocess.STDOUT, check=True)
    generator = gslt / "tools/generate_erlang_kernel_controls.lean"
    cetta = (args.cetta or repo.parent / "hyperon/cetta-prime-2.0-draft-20260910/cetta").resolve()
    petta = (args.petta_runner or repo.parent / "hyperon/PeTTa/run.sh").resolve()
    common = gslt / "tools/test_gslt_complete.sh"
    match = re.search(r"^libraries=\((.*?)^\)", common.read_text(), re.S | re.M)
    if match is None:
        raise RuntimeError("the shared runtime library list is missing")
    libraries = [gslt / "lib" / (name + ".metta") for name in match[1].split()]
    libraries += [gslt / "lib" / name for name in
                  ["gslt_integer.metta", "gslt_word16.metta", "gslt_snapshot_closure.metta", "gslt_erlang.metta"]]
    inputs = {Path(__file__).resolve(), generator, common, *libraries, cetta, petta,
              lean / "lean-toolchain", lean / "lakefile.lean", lean / "lake-manifest.json"}
    inputs.update((petta.parent / "src").rglob("*.pl"))
    inputs.update(gslt / "module" / (name + ".module") for name in
                  ["Radix16", "ErlangData", "ErlangSequentialIR", "ErlangSequentialMachine"])
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

    def save_pins():
        (output / "input-pins.json").write_text(json.dumps(pins, indent=2) + "\n")

    def generate(directory, name):
        with (output / ("generate-" + name + ".log")).open("w") as log:
            subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", generator, directory, name],
                           cwd=lean, stdout=log, stderr=subprocess.STDOUT, check=True)

    save_pins()
    generate(output, "manifest")
    available = json.loads((output / "programs.json").read_text())
    programs = args.program or available
    if not programs or any(name not in available for name in programs):
        raise RuntimeError("unknown or empty program selection")
    results = []
    for name in programs:
        directory = output / name
        generate(directory, name)
        workload = directory / "workload.metta"
        workload.write_text("\n".join(path.read_text() for path in
                                      [*libraries, directory / "machine.metta", directory / "controls.metta"]))
        for path in [workload, directory / "machine.metta", directory / "controls.metta", directory / "preparation.json"]:
            pins[str(path)] = sha(path)
        save_pins()
        engines = []
        for label, command in [("cetta", [str(cetta), "--lang", "petta", "--quiet", str(workload)]),
                               ("petta", ["bash", str(petta), "--silent", str(workload)])]:
            started = time.monotonic()
            with (directory / (label + ".out")).open("w") as out, (directory / (label + ".err")).open("w") as err:
                result = subprocess.run(command, cwd=lean, env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"),
                                        stdout=out, stderr=err)
            rows = [line for line in (directory / (label + ".out")).read_text().splitlines()
                    if line.startswith("(ErlangKernelControl ")]
            parsed = [re.fullmatch(r'\(ErlangKernelControl "([^"]+)"' + r" (true|false)" * 3 + r"\)", row)
                      for row in rows]
            passed = (result.returncode == 0 and not (directory / (label + ".err")).read_bytes()
                      and len(parsed) == 1 and parsed[0] is not None and parsed[0][1] == name
                      and parsed[0].groups()[1:] == ("true",) * 3)
            engines.append({"engine": label, "passed": passed, "exit_code": result.returncode,
                            "controls": rows, "seconds": time.monotonic() - started,
                            "stdout_sha256": sha(directory / (label + ".out"))})
            (directory / "engine-results.json").write_text(json.dumps(engines, indent=2) + "\n")
            print(json.dumps({"program": name, **engines[-1]}), flush=True)
        identical = engines[0]["controls"] == engines[1]["controls"]
        results.append({"program": name, "engines": engines, "outputs_identical": identical,
                        "passed": identical and all(engine["passed"] for engine in engines)})
        (output / "program-results.json").write_text(json.dumps(results, indent=2) + "\n")
        if not results[-1]["passed"]:
            raise RuntimeError(name + ": emitted machine disagrees or remains pending")
    changed = [path for path, digest in pins.items() if not Path(path).is_file() or sha(path) != digest]
    qualification = {"programs": results, "checks_per_engine": 3 * len(results),
                     "inputs_current": not changed, "changed_inputs": changed,
                     "all_passed": not changed and all(row["passed"] for row in results),
                     "source_lowering_qualified": False, "universal_compiler_service_correspondence": False,
                     "full_primitive_identity_profile_qualified": False, "full_E0_qualified": False}
    (output / "qualification.json").write_text(json.dumps(qualification, indent=2) + "\n")
    print(json.dumps(qualification), flush=True)
    if not qualification["all_passed"]:
        raise RuntimeError("qualification inputs changed")


if __name__ == "__main__":
    main()
