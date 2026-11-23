#!/usr/bin/env python3
"""Run the authored GSLT mailbox canary through CeTTa PeTTa and native rho.

The runtime executable and imported library sources are frozen together.
This is a component gate; complete E0 actors and frontend adequacy remain open.
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
    parser.add_argument("--cetta", required=True, type=Path)
    parser.add_argument("--runtime-lib", required=True, type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    gslt, lean = repo / "metta/gslt", repo / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    runtime = output / "runtime"
    (runtime / "lib").mkdir(parents=True)
    binary = runtime / "cetta"
    binary.write_bytes(args.cetta.read_bytes())
    binary.chmod(0o755)
    libraries = []
    for name in ["rho.metta", "rhometta.metta", "lts.metta"]:
        target = runtime / "lib" / name
        target.write_bytes((args.runtime_lib / name).read_bytes())
        libraries.append(target)
    generator = gslt / "tools/generate_erlang_rho_mailbox_controls.lean"
    targets = ["Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox",
               "Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission",
               "Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelEmission"]
    with (output / "build.log").open("w") as log:
        subprocess.run(["lake", "--wfail", "build", *targets], cwd=lean,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    match = re.search(r"^libraries=\((.*?)^\)",
                      (gslt / "tools/test_gslt_complete.sh").read_text(), re.S | re.M)
    if match is None:
        raise RuntimeError("shared runtime library list missing")
    common = [gslt / "lib" / (name + ".metta") for name in match[1].split()]
    adapter = gslt / "lib/gslt_erlang_rho.metta"
    inputs = {Path(__file__).resolve(), generator, adapter, binary, *libraries, *common,
              gslt / "tools/test_gslt_complete.sh", lean / "lean-toolchain",
              lean / "lakefile.lean", lean / "lake-manifest.json"}
    for name in ["Radix16", "ErlangData", "ErlangMailbox"]:
        inputs.add(gslt / "module" / (name + ".module"))
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
    with (output / "generation.log").open("w") as log:
        subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", generator, output],
                       cwd=lean, stdout=log, stderr=subprocess.STDOUT, check=True)
    workload = output / "workload.metta"
    workload.write_text("\n".join(path.read_text() for path in
        [*common, output / "machine.metta", adapter, output / "controls.metta"]))
    for path in [workload, output / "machine.metta", output / "controls.metta"]:
        pins[str(path)] = sha(path)
    (output / "input-pins.json").write_text(json.dumps(pins, indent=2) + "\n")
    started = time.monotonic()
    with (output / "stdout.txt").open("w") as out, (output / "stderr.txt").open("w") as err:
        result = subprocess.run([str(binary), "--lang", "petta", "--quiet", str(workload)],
                                cwd=lean, env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"),
                                stdout=out, stderr=err)
    rows = [line for line in (output / "stdout.txt").read_text().splitlines()
            if line.startswith("(ErlangRhoMailboxControl ")]
    changed = [path for path, digest in pins.items() if not Path(path).is_file() or sha(path) != digest]
    passed = (result.returncode == 0 and not (output / "stderr.txt").read_bytes()
              and rows == ["(ErlangRhoMailboxControl true true true true)"] and not changed)
    qualification = {"all_passed": passed, "checks": 4, "seconds": time.monotonic() - started,
                     "runtime_sha256": sha(binary), "inputs_current": not changed,
                     "changed_inputs": changed, "component": "rho token to authored GSLT mailbox",
                     "full_actor_scheduler_qualified": False, "source_lowering_qualified": False,
                     "universal_actor_correspondence": False, "full_E0_qualified": False}
    (output / "qualification.json").write_text(json.dumps(qualification, indent=2) + "\n")
    print(json.dumps(qualification), flush=True)
    if not passed:
        raise RuntimeError("rho mailbox component gate failed")


if __name__ == "__main__":
    main()
