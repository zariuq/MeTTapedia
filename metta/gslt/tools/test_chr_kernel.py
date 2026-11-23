#!/usr/bin/env python3
"""Check ground CHR transactions through the shared MeTTa execution path."""

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


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--cetta", type=Path)
    parser.add_argument("--petta-runner", type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    gslt, lean = repo / "metta/gslt", repo / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    cetta = (args.cetta or repo.parent / "hyperon/cetta-prime-2.0-draft-20260910/cetta").resolve()
    petta = (args.petta_runner or repo.parent / "hyperon/PeTTa/run.sh").resolve()
    generator = gslt / "tools/generate_chr_kernel_controls.lean"
    targets = re.findall(r"^import (Mettapedia\.[A-Za-z0-9_.]+)$", generator.read_text(), re.M)
    for label, command in (
        ("build", ["lake", "--wfail", "build", *targets]),
        ("generate", ["lake", "env", "lean", "-DwarningAsError=true", "--run", str(generator), str(output)]),
    ):
        with (output / f"{label}.log").open("w") as log:
            result = subprocess.run(command, cwd=lean, stdout=log, stderr=subprocess.STDOUT)
        result.check_returncode()
    common_gate = gslt / "tools/test_gslt_complete.sh"
    match = re.search(r"^libraries=\((.*?)^\)", common_gate.read_text(), re.S | re.M)
    if match is None:
        raise RuntimeError("the common runtime library list is missing")
    libraries = [gslt / f"lib/{name}.metta" for name in match[1].split()]
    workload = output / "workload.metta"
    workload.write_text("\n".join(path.read_text() for path in [*libraries, output / "query.metta", output / "controls.metta"]))
    inputs = {Path(__file__).resolve(), generator, common_gate, *libraries, workload, cetta, petta,
              output / "query.metta", output / "controls.metta", gslt / "module/CHRIR.module",
              gslt / "module/CHRGroundKernel.module", lean / "lean-toolchain", lean / "lakefile.lean",
              lean / "lake-manifest.json"}
    inputs.update((petta.parent / "src").rglob("*.pl"))
    swipl = shutil.which("swipl")
    if swipl is None:
        raise RuntimeError("SWI-Prolog is required by the PeTTa runner")
    inputs.add(Path(swipl).resolve())
    mork = petta.parent / "mork_ffi/target/release/libmork_ffi.so"
    if mork.is_file():
        inputs.add(mork.resolve())
    for target in targets:
        relative = Path(*target.split("."))
        setup = lean / ".lake/build/ir" / relative.with_suffix(".setup.json")
        inputs.update([setup, lean / relative.with_suffix(".lean"),
                       lean / ".lake/build/lib/lean" / relative.with_suffix(".olean")])
        for dependency, groups in json.loads(setup.read_text())["importArts"].items():
            if dependency.startswith("Mettapedia."):
                inputs.add(lean / Path(*dependency.split(".")).with_suffix(".lean"))
            inputs.update(Path(path) for group in groups for path in group)
    pins = {str(path): digest(path) for path in inputs}
    labels = ["simplification", "simpagation-equal-values", "propagation-keeps", "two-occurrences",
              "same-occurrence-twice", "missing-occurrence", "wrong-value", "body-order"]

    def run(label, command):
        started = time.monotonic()
        environment = dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1")
        with (output / f"{label}.out").open("w") as stdout, (output / f"{label}.err").open("w") as stderr:
            result = subprocess.run(command, cwd=lean, env=environment, stdout=stdout, stderr=stderr)
        rows = [line for line in (output / f"{label}.out").read_text().splitlines()
                if line.startswith("(CHRKernelModelControl ")]
        parsed = [re.fullmatch(r'\(CHRKernelModelControl "([^"\n]+)" (true|false) (true|false) (true|false) (true|false)\)', row)
                  for row in rows]
        passed = result.returncode == 0 and len(parsed) == len(labels) and all(parsed)
        if passed:
            passed = [match[1] for match in parsed] == labels and all(match.groups()[1:] == ("true",) * 4 for match in parsed)
        return {"engine": label, "exit_code": result.returncode, "seconds": time.monotonic() - started,
                "passed": passed, "controls": rows, "checks": len(parsed) * 4,
                "stdout_sha256": digest(output / f"{label}.out"), "stderr_sha256": digest(output / f"{label}.err")}

    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        jobs = [pool.submit(run, "cetta", [str(cetta), "--lang", "petta", "--quiet", str(workload)]),
                pool.submit(run, "petta", ["bash", str(petta), "--silent", str(workload)])]
        results = [job.result() for job in jobs]
    changed = [path for path, before in pins.items() if digest(Path(path)) != before]
    identical = results[0]["controls"] == results[1]["controls"]
    passed = all(result["passed"] for result in results) and identical and not changed
    record = {"results": results, "input_pins": pins, "changed_inputs": changed, "all_passed": passed,
              "control_outputs_identical": identical, "controls": len(labels), "checks_per_engine": len(labels) * 4,
              "scope": "Ground transactions, complete receipt edges, run/explore and retained resumption",
              "full_refined_chr_controller_qualified": False, "ordinary_chr_source_qualified": False}
    (output / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({key: value for key, value in record.items() if key != "input_pins"}, indent=2))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
