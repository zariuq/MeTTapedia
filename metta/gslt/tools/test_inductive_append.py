#!/usr/bin/env python3
"""Qualify the selected authored append specialization on the chosen engines.

Run in lean/mettapedia with `lake env python3` after building
GSLTInductiveAppendQuotation and GSLTInductiveAppendObservation. Supply both
a CeTTa binary and a PeTTa runner.
The qualified native payload profile is natural integers. The Lean checker
compares complete ordered packets, not runtime equality tests. A separate
compound-payload probe records the boundary outside that profile.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--cetta", required=True, type=Path)
    parser.add_argument("--petta", required=True, type=Path)
    parser.add_argument("--library", type=Path,
                        help="Execute this source-checked emission after exact library comparison")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    (output / "qualification.json").write_text(json.dumps(
        {"qualified": False, "status": "running"}, indent=2) + "\n")
    root = Path(__file__).resolve().parents[1]
    repository = root.parents[1]
    lean_root = repository / "lean/mettapedia"
    oracle = root / "tools/qualify_inductive_append.lean"
    observation_oracle = root / "tools/qualify_inductive_append_observations.lean"
    cetta = args.cetta.resolve()
    petta = args.petta.resolve()
    inputs = [Path(__file__).resolve(), oracle, observation_oracle, cetta, petta,
              root / "lib/gslt_inductive_append.metta",
              root / "lib/gslt_native_spatial.metta",
              root / "lib/gslt_inductive_observations.metta",
              root / "module/IndexedNatVecAppend.module"]
    if args.library:
        inputs.append(args.library.resolve())
    inputs += sorted((petta.parent / "src").rglob("*.pl"))
    inputs += [path for path in (petta.parent / "mork_ffi/target/release/libmork_ffi.so",)
               if path.exists()]
    inputs += [lean_root / "Mettapedia/Languages/MeTTa/PeTTa" / name for name in
               ("StdLib.lean", "StdLibCalls.lean", "Eval.lean", "BridgeKit.lean",
                "Bridges/IndexedInductiveAppend.lean", "Bridges/IndexedInductiveAppendControls.lean")]
    inputs += [lean_root / "Mettapedia" / name for name in
               ("OSLF/NativeTypes/Decision/Spatial/BagCardinality.lean",
                "OSLF/NativeTypes/Consumers/IndexedAppend.lean",
                "Languages/MeTTa/PeTTa/Bridges/NativeTypes/IndexedAppend.lean",
                "Languages/MeTTa/PeTTa/Bridges/NativeTypes/IndexedAppendControls.lean",
                "Languages/MeTTa/PeTTa/Bridges/NativeTypes/IndexedAppendSource.lean",
                "Languages/MeTTa/PeTTa/Bridges/NativeTypes/IndexedAppendExecution.lean",
                "Languages/MeTTa/PeTTa/Bridges/NativeTypes/IndexedAppendExecutionControls.lean",
                "Languages/MeTTa/PeTTa/Bridges/NativeTypes/SpatialSource.lean",
                "Languages/MeTTa/PeTTa/Bridges/NativeTypes/SpatialExecution.lean")]
    pins = {str(path): digest(path) for path in inputs}
    records = []
    (output / "qualification.json").write_text(json.dumps(
        {"qualified": False, "status": "running", "source_pins": pins}, indent=2) + "\n")

    def run(label, command, *, expect_success=True, cwd=lean_root):
        start = time.monotonic()
        result = subprocess.run(command, cwd=cwd, env=os.environ.copy(), text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
        (output / (label + ".out")).write_text(result.stdout)
        (output / (label + ".err")).write_text(result.stderr)
        records.append(dict(label=label, returncode=result.returncode,
                            seconds=round(time.monotonic() - start, 6)))
        if (result.returncode == 0) != expect_success:
            raise RuntimeError(f"{label}: unexpected status {result.returncode}; see its logs")
        return result.stdout

    generation = (["emit-library", str(args.library.resolve()), str(output)] if args.library
                  else ["emit", str(output)])
    run("generate", ["lean", "--run", str(oracle), *generation])
    native_input = output / "append-input.metta"
    packets = {}
    for mode in ("prime", "petta"):
        label = "cetta-" + mode
        text = run(label, [str(cetta), "--lang", mode, "--quiet", str(native_input)], cwd=root)
        run(label + "-check", ["lean", "--run", str(oracle), "check", str(output / (label + ".out"))])
        packets[label] = [line.strip() for line in text.splitlines()
                          if line.strip().startswith("(InductiveAppendPacket")]
    text = run("petta", ["bash", str(petta), "--silent", str(native_input)], cwd=root)
    run("petta-check", ["lean", "--run", str(oracle), "check", str(output / "petta.out")])
    packets["petta"] = [line.strip() for line in text.splitlines()
                        if line.strip().startswith("(InductiveAppendPacket")]
    if not packets["cetta-prime"] == packets["cetta-petta"] == packets["petta"]:
        raise RuntimeError("engine packet streams differ")

    run("generate-observations", ["lean", "--run", str(observation_oracle), *generation])
    observation_input = output / "append-observations.metta"
    observations = {}
    for label, command in [
        ("cetta-prime", [str(cetta), "--lang", "prime", "--quiet", str(observation_input)]),
        ("cetta-petta", [str(cetta), "--lang", "petta", "--quiet", str(observation_input)]),
        ("petta", ["bash", str(petta), "--silent", str(observation_input)])]:
        name = label + "-observations"
        text = run(name, command, cwd=root)
        run(name + "-check", ["lean", "--run", str(observation_oracle), "check",
                             str(output / (name + ".out"))])
        observations[label] = [line.strip() for line in text.splitlines()
                               if line.strip().startswith("(InductiveAppendObservation")]
    if not observations["cetta-prime"] == observations["cetta-petta"] == observations["petta"]:
        raise RuntimeError("engine observation packets differ")

    boundary = {}
    boundary_input = output / "append-payload-boundary.metta"
    for label, command in [
        ("cetta-prime", [str(cetta), "--lang", "prime", "--quiet", str(boundary_input)]),
        ("cetta-petta", [str(cetta), "--lang", "petta", "--quiet", str(boundary_input)]),
        ("petta", ["bash", str(petta), "--silent", str(boundary_input)])]:
        boundary[label] = run(label + "-payload-boundary", command, cwd=root).splitlines()

    observed = packets["cetta-prime"]
    mutations = {
        "missing-packet": observed[1:],
        "duplicate-packet": observed + observed[:1],
        "missing-payload": [observed[0].replace("1 2 3 4", "1 3 4")] + observed[1:],
        "extra-payload": [observed[0].replace("1 2 3 4", "1 2 3 4 4")] + observed[1:],
        "reordered-payload": [observed[0].replace("1 2 3 4", "2 1 3 4")] + observed[1:],
    }
    for label, lines in mutations.items():
        if lines == observed:
            raise RuntimeError(f"negative control did not mutate anything: {label}")
        path = output / (label + ".input")
        path.write_text("\n".join(lines) + "\n")
        run(label, ["lean", "--run", str(oracle), "check", str(path)], expect_success=False)
    observation_packets = observations["cetta-prime"]
    observation_mutations = {
        "observation-missing": observation_packets[1:],
        "observation-duplicate": observation_packets + observation_packets[:1],
        "observation-false-refutation": [line.replace("NativeUnknown", "NativeRefuted")
                                         for line in observation_packets],
        "observation-wrong-verdict": [line.replace("NativeProved", "NativeRefuted")
                                      for line in observation_packets],
        "observation-missing-occurrence": [line.replace(
            '(LCons (PApp "Element" LNil) (LCons (PApp "Element" LNil) LNil))',
            '(LCons (PApp "Element" LNil) LNil)', 1) for line in observation_packets],
        "observation-payload-reordered": [line.replace('"two-values" (NativeAppendObservation (1 2)',
                                                       '"two-values" (NativeAppendObservation (2 1)')
                                           for line in observation_packets],
    }
    for label, lines in observation_mutations.items():
        if lines == observation_packets:
            raise RuntimeError(f"observation negative did not mutate anything: {label}")
        path = output / (label + ".input")
        path.write_text("\n".join(lines) + "\n")
        run(label, ["lean", "--run", str(observation_oracle), "check", str(path)], expect_success=False)
    after = {str(path): digest(path) for path in inputs}
    if pins != after:
        changed = {path: {"before": value, "after": after[path]}
                   for path, value in pins.items() if after[path] != value}
        (output / "qualification.json").write_text(json.dumps(
            {"qualified": False, "status": "inputs_changed", "source_pins": pins,
             "changed_inputs": changed, "records": records}, indent=2) + "\n")
        raise RuntimeError("qualification inputs changed during the run")
    result = dict(qualified=True, source_pins=pins, records=records,
                  packet_count=len(observed), engine_modes=list(packets), negative_controls=list(mutations),
                  observation_count=len(observation_packets), observation_negative_controls=list(observation_mutations),
                  artifact_pins={name: digest(output / name) for name in
                                 ("append-library.metta", "append-controls.metta", "append-input.metta",
                                  "append-payload-boundary.metta", "append-observations.metta")},
                  outside_profile_payload_probe=boundary,
                  scope="Selected typed append specialization with natural-integer payloads; pinned native runs, not a proof of linked C/GMP or arbitrary atom payload preservation.")
    (output / "qualification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"Qualified {len(observed)} execution packets and {len(observation_packets)} observation packets "
          f"on three engine modes; {len(mutations) + len(observation_mutations)} refusals.")


if __name__ == "__main__":
    main()
