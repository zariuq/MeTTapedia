#!/usr/bin/env python3
"""Check the emitted Datalog ground kernel on CeTTa PeTTa mode and SWI PeTTa."""

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
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", required=True, type=Path)
    parser.add_argument("--petta-runner", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--cetta-sha256")
    parser.add_argument("--petta-runner-sha256")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    lean = root.parents[1] / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    cetta, petta = args.cetta.resolve(), args.petta_runner.resolve()
    for binary, expected in ((cetta, args.cetta_sha256), (petta, args.petta_runner_sha256)):
        if expected and digest(binary) != expected:
            raise RuntimeError(f"selected reference identity differs: {binary.name}")
    generator = root / "tools/generate_datalog_kernel_controls.lean"
    modules = re.findall(r"^import (Mettapedia\.[A-Za-z0-9_.]+)$", generator.read_text(), re.M)
    for label, command in (
            ("build", ["lake", "--wfail", "build", *modules]),
            ("generate", ["lake", "env", "lean", "-DwarningAsError=true", "--run", str(generator), str(output)])):
        result = subprocess.run(command, cwd=lean, text=True, capture_output=True)
        (output / f"{label}.log").write_text(result.stdout + result.stderr)
        result.check_returncode()
    common_gate = root / "tools/test_gslt_complete.sh"
    match = re.search(r"^libraries=\((.*?)^\)", common_gate.read_text(), re.S | re.M)
    if match is None:
        raise RuntimeError("the common runtime library list is missing")
    libraries = [root / f"lib/{name}.metta" for name in match[1].split()]
    workload = output / "workload.metta"
    workload.write_text("\n".join(p.read_text() for p in [*libraries, output / "query.metta", output / "controls.metta"]))
    inputs = [Path(__file__), generator, common_gate, *libraries, workload,
              output / "query.metta", output / "controls.metta", cetta, petta,
              lean / "lean-toolchain", lean / "lake-manifest.json"]
    swipl = shutil.which("swipl")
    if swipl:
        inputs.append(Path(swipl).resolve())
    for module in modules:
        relative = Path(*module.split("."))
        setup = lean / ".lake/build/ir" / relative.with_suffix(".setup.json")
        inputs.extend([setup, lean / relative.with_suffix(".lean"),
                       lean / ".lake/build/lib/lean" / relative.with_suffix(".olean")])
        for dependency, groups in json.loads(setup.read_text())["importArts"].items():
            if dependency.startswith("Mettapedia."):
                inputs.append(lean / Path(*dependency.split(".")).with_suffix(".lean"))
            inputs.extend(Path(path) for group in groups for path in group)
    inputs.extend((root / "module/gold/SouffleDatalog").glob("*.module"))
    pins = {str(path.resolve()): digest(path) for path in inputs}

    def run(label, command):
        environment = dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1")
        started = time.monotonic()
        with (output / f"{label}.stdout").open("w") as stdout, (output / f"{label}.stderr").open("w") as stderr:
            result = subprocess.run(command, cwd=lean, env=environment, stdout=stdout, stderr=stderr)
        rows = [line for line in (output / f"{label}.stdout").read_text().splitlines()
                if line.startswith("(DatalogQueryKernelModelControl ")]
        labels = [re.search(r'"(present|repeated|absent|empty)"', line)[1] for line in rows]
        answers = [re.findall(r"\b(?:true|false)\b", line) for line in rows]
        return {"engine": label, "exit_code": result.returncode, "seconds": time.monotonic() - started,
                "controls": rows, "checks": sum(map(len, answers)),
                "passed": result.returncode == 0 and labels == ["present", "repeated", "absent", "empty"]
                and answers == [["true"] * 4] * 4,
                "stdout_sha256": digest(output / f"{label}.stdout"),
                "stderr_sha256": digest(output / f"{label}.stderr")}

    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        pending = [pool.submit(run, "cetta", [str(cetta), "--lang", "petta", "--quiet", str(workload)]),
                   pool.submit(run, "petta", ["bash", str(petta), "--silent", str(workload)])]
        results = [task.result() for task in pending]
    changed = [path for path, before in pins.items() if digest(Path(path)) != before]
    identical = results[0]["controls"] == results[1]["controls"]
    passed = all(row["passed"] for row in results) and identical and not changed
    record = {"results": results, "inputs": pins, "library_count": len(libraries),
              "input_pins_stable": not changed, "changed_inputs": changed,
              "control_outputs_identical": identical, "all_passed": passed,
              "scope": "Ground application IR: run, explore, edge endpoints and resumed trace",
              "ordinary_source_to_execution_qualified": False,
              "complete_receipt_wire_comparison": False, "full_datalog_core_qualified": False}
    (output / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({key: value for key, value in record.items() if key != "inputs"}, indent=2))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
