#!/usr/bin/env python3
"""Compare the actor fixtures with OTP and a completed emitted actor gate.

The fixtures share declared results and mailbox observations. They do not
establish a universal source-lowering or actor-correspondence theorem.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--erl", type=Path, required=True)
    parser.add_argument("--erlc", type=Path, required=True)
    parser.add_argument("--actor-gate", type=Path, required=True)
    parser.add_argument("--program", action="append",
                        choices=["spawn-send", "self-selective", "ping-pong", "counter",
                                 "parallel-map", "parallel-map-duplicates", "causal-forward", "causal-reverse"])
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    repo = Path(__file__).resolve().parents[3]
    source = repo / "metta/gslt/module/gold/Erlang/examples/actor_operations.erl"
    gate = args.actor_gate.resolve()
    qualified = json.loads((gate / "qualification.json").read_text())
    if (not qualified["passed"] or qualified.get("inputs_current") is False
            or qualified.get("changed_inputs")):
        raise RuntimeError("emitted actor gate is not qualified on its pinned inputs")
    emitted = {row["name"]: row for row in json.loads((gate / "results.json").read_text())}
    gate_pins = json.loads((gate / "input-pins.json").read_text())
    if not gate_pins:
        raise RuntimeError("emitted actor gate has no pinned inputs")
    stale = [name for name, digest in gate_pins.items()
             if not Path(name).is_file() or sha(name) != digest]
    if stale:
        raise RuntimeError("emitted gate inputs changed: " + repr(stale))
    erl, erlc = args.erl.resolve(), args.erlc.resolve()
    probe = subprocess.run([str(erl), "-noshell", "-eval",
        'io:format("~s~n~s~n", [string:trim(erlang:system_info(system_version)), code:root_dir()]), halt().'],
        capture_output=True, text=True, check=True)
    if probe.stderr:
        raise RuntimeError(probe.stderr)
    version, installation = probe.stdout.splitlines()
    (output / "runtime-version.txt").write_text(probe.stdout)
    inputs = [Path(__file__).resolve(), source, erl, erlc,
              gate / "qualification.json", gate / "results.json", gate / "input-pins.json"]
    beam_files = list(Path(installation).glob("erts-*/bin/beam.smp"))
    if not beam_files:
        raise RuntimeError("cannot identify OTP's native VM binary")
    inputs += beam_files
    release_files = list((Path(installation) / "releases").glob("*/OTP_VERSION"))
    inputs += release_files
    pins = {str(path): sha(path) for path in inputs}
    for kind, options in [("beam", []), ("core", ["+to_core"])]:
        with (output / ("compile-" + kind + ".log")).open("w") as log:
            subprocess.run([str(erlc), "-Werror", *options, "-o", str(output), str(source)],
                           stdout=log, stderr=subprocess.STDOUT, check=True)
    results = []
    observation_pins = {}
    fixtures = [
        ("spawn_send", "spawn-send", "42", "[]"),
        ("self_selective", "self-selective", "{a,b}", "[b]"),
        ("ping_pong", "ping-pong", "done", "[]"),
        ("counter", "counter", "2", "[]"),
        ("parallel_map", "parallel-map", "[4,6]", "[]"),
        ("parallel_map_duplicates", "parallel-map-duplicates", "[4,4]", "[]"),
        ("two_senders", "causal-forward", ["{a,b}", "{b,a}"], "[]"),
        ("two_senders", "causal-reverse", ["{a,b}", "{b,a}"], "[]"),
    ]
    selected = args.program or [ir_name for _, ir_name, _, _ in fixtures if ir_name in emitted]
    if not selected:
        raise RuntimeError("no corresponding actor fixtures in the supplied gate")
    for native_name, ir_name, value, mailbox in fixtures:
        if ir_name not in selected:
            continue
        row = emitted[ir_name]
        prefix = '(ErlangActorControl "' + ir_name + '" true true true true '
        if not row["passed"] or len(row["controls"]) != 1 or not row["controls"][0].startswith(prefix):
            raise RuntimeError("emitted actor control failed: " + ir_name)
        expression = ('Observed=actor_operations:run(' + native_name + '), '
            '{messages,Mailbox}=process_info(self(),messages), '
            'io:format("ActorReference ~w ~w~n",[Observed,Mailbox]), halt().')
        started = time.monotonic()
        native = subprocess.run([str(erl), "-noshell", "-pa", str(output), "-eval", expression],
                                capture_output=True, text=True)
        stdout_path = output / (ir_name + ".out")
        stderr_path = output / (ir_name + ".err")
        stdout_path.write_text(native.stdout)
        stderr_path.write_text(native.stderr)
        observation_pins[str(stdout_path)] = hashlib.sha256(native.stdout.encode()).hexdigest()
        observation_pins[str(stderr_path)] = hashlib.sha256(native.stderr.encode()).hexdigest()
        accepted_values = value if isinstance(value, list) else [value]
        expected = {"ActorReference " + result + " " + mailbox + "\n" for result in accepted_values}
        passed = native.returncode == 0 and not native.stderr and native.stdout in expected
        results.append({"case": native_name, "emitted_case": ir_name, "passed": passed,
                        "comparison": "permitted_outcome_membership" if len(accepted_values) > 1
                                      else "exact_result_and_mailbox",
                        "observation": native.stdout, "seconds": time.monotonic() - started})
        print(json.dumps(results[-1]), flush=True)
        if not passed:
            raise RuntimeError("OTP actor fixture failed: " + native_name)
    for path in [*output.glob("*.beam"), *output.glob("*.core")]:
        pins[str(path)] = sha(path)
    changed = [name for name, digest in pins.items() if not Path(name).is_file() or sha(name) != digest]
    changed += [name for name, digest in gate_pins.items()
                if not Path(name).is_file() or sha(name) != digest]
    changed += [name for name, digest in observation_pins.items()
                if not Path(name).is_file() or sha(name) != digest]
    qualification = {"passed": not changed and all(row["passed"] for row in results),
        "runtime_version": version,
        "release_versions": {str(path): path.read_text().strip() for path in release_files},
        "cases": results, "input_pins": pins, "observation_pins": observation_pins,
        "changed_inputs": changed, "emitted_actor_gate_joined": True,
        "emitted_gate_scope": qualified.get("scope", qualified.get("execution_profile")),
        "source_lowering_qualified": False, "universal_actor_correspondence": False}
    (output / "qualification.json").write_text(json.dumps(qualification, indent=2) + "\n")
    if not qualification["passed"]:
        raise RuntimeError("actor comparison inputs changed")


if __name__ == "__main__":
    main()
