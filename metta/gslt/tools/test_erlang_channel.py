#!/usr/bin/env python3
"""Compare the channel IR via OSLF, both MeTTa engines and Erlang/OTP.

This is a component gate. It does not qualify the complete actor scheduler,
sequential Core Erlang execution or the source frontend.
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
    parser.add_argument("--erlang-bin", type=Path, required=True)
    parser.add_argument("--cetta", type=Path)
    parser.add_argument("--petta-runner", type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    gslt, lean = repo / "metta/gslt", repo / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    targets = ["Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangChannelControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangChannelExecution",
               "Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission"]
    with (output / "build.log").open("w") as log:
        subprocess.run(["lake", "--wfail", "build", *targets], cwd=lean, stdout=log,
                       stderr=subprocess.STDOUT, check=True)
    cetta = (args.cetta or repo.parent / "hyperon/cetta-prime-2.0-draft-20260910/cetta").resolve()
    petta = (args.petta_runner or repo.parent / "hyperon/PeTTa/run.sh").resolve()
    erlang = args.erlang_bin.resolve(strict=True)
    otp_version = erlang.parent / "lib/erlang/releases/29/OTP_VERSION"
    if otp_version.read_text().strip() != "29.1.2":
        raise RuntimeError("expected the pinned Erlang/OTP 29.1.2 reference")
    generator = gslt / "tools/generate_erlang_channel_controls.lean"
    source = gslt / "module/gold/Erlang/examples/channel_operations.erl"
    common = gslt / "tools/test_gslt_complete.sh"
    match = re.search(r"^libraries=\((.*?)^\)", common.read_text(), re.S | re.M)
    if match is None:
        raise RuntimeError("the shared runtime library list is missing")
    libraries = [gslt / "lib" / (name + ".metta") for name in match[1].split()]
    inputs = {Path(__file__).resolve(), generator, source, common, *libraries, cetta, petta,
              erlang / "erl", erlang / "erlc", otp_version, lean / "lean-toolchain", lean / "lakefile.lean",
              lean / "lake-manifest.json"}
    inputs.update((petta.parent / "src").rglob("*.pl"))
    inputs.update(erlang.parent.glob("lib/erlang/erts-*/bin/beam.smp"))
    inputs.update(gslt / "module" / (name + ".module") for name in
                  ["Radix16", "ErlangData", "ErlangMailbox", "ErlangChannel"])
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

    save_pins()
    with (output / "generation.log").open("w") as log:
        subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", generator, output],
                       cwd=lean, stdout=log, stderr=subprocess.STDOUT, check=True)
    manifest = json.loads((output / "oslf.json").read_text())
    questions = manifest["questions"]
    if len(questions) != 6 or not all(row["expectedReachable"] is True and row["wrongReachable"] is False
                                      for row in questions):
        raise RuntimeError("OSLF failed a positive or separating negative channel question")
    if (manifest["emptyChannelHasStep"] is not False or manifest["fifoViolationReachable"] is not False
            or manifest["zeroBudget"] is not None):
        raise RuntimeError("OSLF confused an empty channel, FIFO order or budget exhaustion")
    workload = output / "workload.metta"
    workload.write_text("\n".join(path.read_text() for path in
                                  [*libraries, output / "machine.metta", output / "controls.metta"]))
    for path in [workload, output / "machine.metta", output / "controls.metta", output / "oslf.json"]:
        pins[str(path)] = sha(path)
    save_pins()
    results = []
    for name, command in [("cetta", [str(cetta), "--lang", "petta", "--quiet", str(workload)]),
                          ("petta", ["bash", str(petta), "--silent", str(workload)])]:
        started = time.monotonic()
        with (output / (name + ".out")).open("w") as out, (output / (name + ".err")).open("w") as err:
            result = subprocess.run(command, cwd=lean, env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"),
                                    stdout=out, stderr=err)
        rows = [line for line in (output / (name + ".out")).read_text().splitlines()
                if line.startswith("(ErlangChannelControl ")]
        parsed = [re.fullmatch(r'\(ErlangChannelControl "([^"]+)"' + r" (true|false)" * 6 + r"\)", row)
                  for row in rows]
        passed = (result.returncode == 0 and not (output / (name + ".err")).read_bytes()
                  and len(parsed) == len(questions) and all(parsed)
                  and [match.group(1) for match in parsed] == [row["name"] for row in questions]
                  and all(match.groups()[1:] == ("true",) * 6 for match in parsed))
        results.append({"engine": name, "passed": passed, "exit_code": result.returncode,
                        "checks": 6 * len(rows), "controls": rows,
                        "stdout_sha256": sha(output / (name + ".out")),
                        "seconds": time.monotonic() - started})
        (output / "engine-results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(results[-1]), flush=True)
    native = output / "erlang"
    native.mkdir()
    for options in [[], ["+to_core"]]:
        with (native / ("compile-core.log" if options else "compile-beam.log")).open("w") as log:
            subprocess.run([str(erlang / "erlc"), "-Werror", *options, "-o", native, source],
                           stdout=log, stderr=subprocess.STDOUT, check=True)
    reference = subprocess.run([str(erlang / "erl"), "-noshell", "-pa", native, "-eval",
                                'io:format("~w~n", [channel_operations:run()]), halt().'],
                               capture_output=True, text=True)
    (native / "reference.out").write_text(reference.stdout)
    (native / "reference.err").write_text(reference.stderr)
    expected = "{[a],[a,b,c],[a,a,a],{a,[b]},{a,[a]},{new,[first,second,old,earlier]}}\n"
    reference_passed = reference.returncode == 0 and reference.stdout == expected and not reference.stderr
    version = subprocess.run([str(erlang / "erl"), "-noshell", "-eval",
                              'io:format("~s", [erlang:system_info(otp_release)]), halt().'],
                             capture_output=True, text=True, check=True)
    if version.stdout != "29" or version.stderr:
        raise RuntimeError("expected the Erlang/OTP 29 reference")
    for path in native.iterdir():
        pins[str(path)] = sha(path)
    save_pins()
    changed = [path for path, pinned in pins.items() if not Path(path).is_file() or sha(path) != pinned]
    same = len(results) == 2 and results[0]["controls"] == results[1]["controls"]
    qualification = {"component": manifest["component"], "oslf_decided_questions": 14,
                     "checks_per_engine": 36, "engines": results, "outputs_identical": same,
                     "reference_controls": 6, "reference_passed": reference_passed,
                     "otp_release": version.stdout, "otp_version": otp_version.read_text().strip(),
                     "inputs_current": not changed, "changed_inputs": changed,
                     "all_passed": same and reference_passed and not changed and all(r["passed"] for r in results),
                     "complete_actor_scheduler": False, "full_E0_qualified": False}
    (output / "qualification.json").write_text(json.dumps(qualification, indent=2) + "\n")
    print(json.dumps(qualification), flush=True)
    if not qualification["all_passed"]:
        raise RuntimeError("channel component qualification failed")


if __name__ == "__main__":
    main()
