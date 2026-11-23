#!/usr/bin/env python3
"""Check the experimental E0 actor adapter against its independent IR model.

Uses native rho state transfer, the emitted sequential GSLT evaluator, and
its authored mailbox component. Universal actor and frontend qualification
remain separate obligations.
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
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--runtime-lib", type=Path, required=True)
    programs = ["self", "empty-peek", "spawn", "selective", "blocked", "spawn-send", "self-selective", "ping-pong", "counter",
                "parallel-map", "parallel-map-duplicates", "causal-forward", "causal-reverse", "mailbox-resumption"]
    parser.add_argument("--program", action="append", choices=programs)
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
    native_libraries = []
    for name in ["rho.metta", "rhometta.metta", "lts.metta"]:
        path = runtime / "lib" / name
        path.write_bytes((args.runtime_lib / name).read_bytes())
        native_libraries.append(path)
    targets = ["Mettapedia.Languages.Erlang.ParallelActorExamples", "Mettapedia.Languages.Erlang.ActorControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangExecutionData",
               "Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelEmission"]
    with (output / "build.log").open("w") as log:
        subprocess.run(["lake", "--wfail", "build", *targets], cwd=lean,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    common_script = gslt / "tools/test_gslt_complete.sh"
    match = re.search(r"^libraries=\((.*?)^\)", common_script.read_text(), re.S | re.M)
    if match is None:
        raise RuntimeError("shared library list missing")
    libraries = [gslt / "lib" / (name + ".metta") for name in match[1].split()]
    libraries += [gslt / "lib" / name for name in ["gslt_integer.metta", "gslt_word16.metta", "gslt_snapshot_closure.metta", "gslt_erlang.metta"]]
    adapters = [gslt / "lib/gslt_erlang_rho.metta", gslt / "lib/gslt_erlang_actors.metta"]
    resume_controls = gslt / "tests/petta/gslt_erlang_mailbox_resumption_controls.metta"
    generators = [gslt / "tools/generate_erlang_rho_mailbox_controls.lean", gslt / "tools/generate_erlang_actor_controls.lean"]
    inputs = {Path(__file__).resolve(), binary, *native_libraries, common_script, *libraries, *adapters, *generators,
              resume_controls,
              lean / "lean-toolchain", lean / "lake-manifest.json", lean / "lakefile.lean"}
    inputs.update(gslt / "module" / (name + ".module") for name in ["Radix16", "ErlangData", "ErlangMailbox", "ErlangSequentialIR", "ErlangSequentialMachine"])
    for target in targets:
        relative = Path(*target.split("."))
        setup = lean / ".lake/build/ir" / relative.with_suffix(".setup.json")
        inputs.update([setup, lean / relative.with_suffix(".lean"), lean / ".lake/build/lib/lean" / relative.with_suffix(".olean")])
        for dependency, groups in json.loads(setup.read_text())["importArts"].items():
            if dependency.startswith("Mettapedia."):
                inputs.add(lean / Path(*dependency.split(".")).with_suffix(".lean"))
            inputs.update(Path(path) for group in groups for path in group)
    pins = {str(path): sha(path) for path in inputs}
    def generate(generator, directory, name=None):
        command = ["lake", "env", "lean", "-DwarningAsError=true", "--run", str(generator), str(directory)]
        if name is not None:
            command.append(name)
        with (output / ("generate-" + (name or "mailbox") + ".log")).open("w") as log:
            subprocess.run(command, cwd=lean, stdout=log, stderr=subprocess.STDOUT, check=True)
    generate(generators[0], output / "mailbox")
    results = []
    for name in args.program or programs:
        directory = output / name
        emitted_case = "self" if name == "mailbox-resumption" else name
        generate(generators[1], directory, emitted_case)
        workload = directory / "workload.metta"
        sources = [*libraries, output / "mailbox/machine.metta", *adapters,
                   directory / "machine.metta", directory / "controls.metta"]
        if name == "mailbox-resumption":
            sources.append(resume_controls)
        workload.write_text("\n".join(path.read_text() for path in sources))
        for path in [workload, directory / "machine.metta", directory / "controls.metta"]:
            pins[str(path)] = sha(path)
        (output / "input-pins.json").write_text(json.dumps(pins, indent=2) + "\n")
        started = time.monotonic()
        with (directory / "stdout.txt").open("w") as out, (directory / "stderr.txt").open("w") as err:
            result = subprocess.run([str(binary), "--lang", "petta", "--quiet", str(workload)], cwd=lean,
                                    env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"), stdout=out, stderr=err)
        rows = [line for line in (directory / "stdout.txt").read_text().splitlines() if line.startswith("(ErlangActorControl ")]
        passed = (result.returncode == 0 and not (directory / "stderr.txt").read_bytes() and len(rows) == 1
                  and ('"' + emitted_case + '" true true true true ') in rows[0])
        resume_rows = [line for line in (directory / "stdout.txt").read_text().splitlines()
                       if line.startswith("(ErlangMailboxResumeControl ")]
        if name == "mailbox-resumption":
            passed = passed and resume_rows == ["(ErlangMailboxResumeControl " + " ".join(["true"] * 12) + ")"]
        entry = {"name": name, "passed": passed, "exit_code": result.returncode,
                 "additional_check": "source_network_fresh_pid_and_completed_children",
                 "seconds": time.monotonic() - started, "controls": rows,
                 "resumption_controls": resume_rows, "checks": 16 if name == "mailbox-resumption" else 4}
        results.append(entry)
        (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(entry), flush=True)
        if not passed:
            raise RuntimeError(name + ": actor result, resumption or mailbox control failed")
    changed = [path for path, digest in pins.items() if not Path(path).is_file() or sha(path) != digest]
    qualification = {"passed": not changed and all(row["passed"] for row in results),
                     "cases": len(results), "checks": sum(row["checks"] for row in results), "inputs_current": not changed,
                     "execution_profile": "cetta-petta-rhometta-local-actors",
                     "changed_inputs": changed, "runtime_sha256": sha(binary),
                     "source_lowering_qualified": False, "universal_actor_correspondence": False,
                     "complete_schedule_exploration_qualified": False, "full_E0_qualified": False}
    (output / "qualification.json").write_text(json.dumps(qualification, indent=2) + "\n")
    print(json.dumps(qualification), flush=True)
    if not qualification["passed"]:
        raise RuntimeError("actor gate inputs changed")


if __name__ == "__main__":
    main()
