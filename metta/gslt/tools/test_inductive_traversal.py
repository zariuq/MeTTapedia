#!/usr/bin/env python3
"""Qualify inductive traversal or recursion on a pinned CeTTa PeTTa artifact.

Each control runs in its own process group. A correct observed packet and a
completed native run are recorded separately: timeout after publishing a value
does not qualify exhaustion or the complete-result theorem.
An optional SWI-PeTTa reference run is recorded without deciding qualification.
The runtime owners supply the frozen artifact and its build provenance; this
gate checks the selected workload and artifact identity, not C compilation.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pins_match(paths, expected):
    try:
        return expected == {str(path): digest(path) for path in paths}
    except OSError:
        return False


def run(command, *, cwd, timeout):
    started = time.monotonic()
    process = subprocess.Popen(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, start_new_session=True)
    timed_out = False
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(process.pid, signal.SIGTERM)
        try:
            stdout, stderr = process.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
    return dict(returncode=process.returncode, timed_out=timed_out,
                seconds=time.monotonic() - started, stdout=stdout, stderr=stderr)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--suite", choices=("positions", "fold", "bundle"), default="positions")
    parser.add_argument("--cetta", type=Path, required=True,
                        help="owner-qualified frozen opt artifact")
    parser.add_argument("--cetta-sha256", required=True,
                        help="expected SHA-256 of that artifact")
    parser.add_argument("--cetta-revision",
                        help="owner-supplied source revision; build correspondence is external")
    parser.add_argument("--petta", type=Path,
                        help="optional SWI-PeTTa reference run.sh, without qualification authority")
    parser.add_argument("--timeout", type=float, default=15)
    parser.add_argument("--reference-timeout", type=float, default=2)
    parser.add_argument("--diagnostic", action="store_true",
                        help="probe a pinned candidate without claiming release qualification")
    args = parser.parse_args()
    repository = Path(__file__).resolve().parents[3]
    lean_root = repository / "lean/mettapedia"
    folding = args.suite == "fold"
    bundling = args.suite == "bundle"
    oracle = Path(__file__).with_name(
        "qualify_inductive_fold.lean" if folding or bundling else "qualify_inductive_traversal.lean")
    oracle_options = ["bundle"] if bundling else []
    packet_prefix = "(BundlePacket" if bundling else "(FoldPacket" if folding else "(TraversalPacket"
    generated_name = "bundle.metta" if bundling else "fold.metta" if folding else "traversal.metta"
    runner = args.cetta.resolve()
    expected_hash = args.cetta_sha256.lower()
    if len(expected_hash) != 64 or any(c not in "0123456789abcdef" for c in expected_hash):
        parser.error("--cetta-sha256 must be a complete SHA-256 digest")
    if not runner.is_file() or digest(runner) != expected_hash:
        parser.error("CeTTa artifact differs from --cetta-sha256")
    reference = args.petta.resolve() if args.petta else None
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    source_names = (["gslt_inductive_fold.metta", "gslt_search_tree_fold.metta"] if folding else
                    ["gslt_inductive_traversal.metta"])
    inputs = [Path(__file__).resolve(), oracle, runner,
              *(repository / "metta/gslt/lib" / name for name in source_names),
              lean_root / "Mettapedia/Languages/MeTTa/PeTTa/Bridges/IndexedContainerTraversal.lean",
              lean_root / "Mettapedia/GSLT/LanguageDef/IndexedContainerWire.lean",
              lean_root / "Mettapedia/TypeTheory/IndexedContainer.lean",
              lean_root / "Mettapedia/TypeTheory/IndexedPositiveContainer.lean"]
    if bundling:
        inputs += [lean_root / name for name in [
            "Mettapedia/Languages/MeTTa/Bridges/GSLT/FormationSensitiveBundleTraversal.lean",
            "Mettapedia/TypeTheory/IndexedContainerInduction.lean",
            "Mettapedia/TypeTheory/Calculi/CumulativePiSigmaId/Declarations/FormationSensitiveRegisteredListGuestLift.lean",
            "Mettapedia/TypeTheory/Calculi/CumulativePiSigmaId/Declarations/FormationSensitiveIndexedContainerBundleRealization.lean",
            "Mettapedia/GSLT/LanguageDef/InferenceCettaWireFormat.lean"]]
    pins = {str(path): digest(path) for path in inputs}
    reference_inputs = [] if reference is None else [reference, *sorted(
        (reference.parent / "src").rglob("*.pl"))]
    native_library = None if reference is None else reference.parent / "mork_ffi/target/release/libmork_ffi.so"
    if native_library is not None and native_library.is_file():
        reference_inputs.append(native_library)
    reference_error = None
    try:
        reference_pins = {str(path): digest(path) for path in reference_inputs}
    except OSError as error:
        reference_error = str(error)
        reference_pins = {}
        reference = None
    generation = run(["lean", "--run", str(oracle), "emit", str(output), *oracle_options],
                     cwd=lean_root, timeout=60)
    if generation["returncode"] != 0:
        raise RuntimeError(generation["stdout"] + generation["stderr"])
    text = (output / generated_name).read_text()
    source = text.split("\n!(", 1)[0]
    commands = [line for line in text.splitlines() if line.startswith("!(")]
    records = []
    reference_records = []
    observed = []
    for index, command in enumerate(commands):
        path = output / f"case-{index}.metta"
        path.write_text(source + "\n" + command + "\n")
        record = run([str(runner), "--lang", "petta", "--quiet", str(path)],
                     cwd=repository / "metta/gslt", timeout=args.timeout)
        (output / f"case-{index}.out").write_text(record["stdout"])
        (output / f"case-{index}.err").write_text(record["stderr"])
        records.append(dict(case=index, **record))
        observed.extend(line for line in record["stdout"].splitlines()
                        if line.startswith(packet_prefix))
        if reference is not None:
            diagnostic = run(["bash", str(reference), "--silent", str(path)],
                             cwd=repository / "metta/gslt", timeout=args.reference_timeout)
            (output / f"reference-{index}.out").write_text(diagnostic["stdout"])
            (output / f"reference-{index}.err").write_text(diagnostic["stderr"])
            reference_complete = diagnostic["returncode"] == 0 and not diagnostic["timed_out"]
            reference_records.append(dict(case=index,
                classification=("agrees" if reference_complete and diagnostic["stdout"] == record["stdout"]
                                else "completion-divergence" if not reference_complete
                                else "output-divergence"), **diagnostic))
    packet_file = output / "observed-packets.out"
    packet_file.write_text("\n".join(observed) + "\n")
    complete_output = output / "complete-output.out"
    complete_output.write_text("".join(record["stdout"] for record in records))
    checked = run(["lean", "--run", str(oracle), "check", str(complete_output), *oracle_options],
                  cwd=lean_root, timeout=60)
    expected_packets = output / "expected-packets.out"
    baseline = run(["lean", "--run", str(oracle), "check", str(expected_packets), *oracle_options],
                   cwd=lean_root, timeout=60)
    baseline_valid = baseline["returncode"] == 0 and not baseline["timed_out"]
    mutation_source = expected_packets.read_text().splitlines()
    mutations = {
        "missing": mutation_source[:-1],
        "duplicate": mutation_source + mutation_source[:1],
        "missing-occurrence": [line.replace(
            "(LCons (Visited 4) (LCons (Visited 4) (LCons (Visited 2) LNil)))",
            "(LCons (Visited 4) (LCons (Visited 2) LNil))", 1)
            for line in mutation_source],
        "reordered": [line.replace("(Visited 3) (LCons (Visited 1)",
                                    "(Visited 1) (LCons (Visited 3)", 1)
                      for line in mutation_source],
        "extra-output": mutation_source + ["(UnexpectedTraversalOutput)"],
    }
    if folding:
        mutations["missing-occurrence"] = [line.replace(
            '(FoldPacket "repeated" ((LCons 0 (LCons 0 (LCons 1 LNil)))))',
            '(FoldPacket "repeated" ((LCons 0 (LCons 1 LNil))))', 1) for line in mutation_source]
        mutations["reordered"] = [line.replace(
            '(FoldPacket "ordered" ((LCons 1 (LCons 0 LNil))))',
            '(FoldPacket "ordered" ((LCons 0 (LCons 1 LNil))))', 1) for line in mutation_source]
        mutations["code-evaluated"] = [line.replace(
            '(FoldPacket "method-returns-code" ((+ 1 2)))',
            '(FoldPacket "method-returns-code" (3))', 1) for line in mutation_source]
    if bundling:
        for name in ("missing-occurrence", "reordered", "changed-witness"):
            mutations[name] = (output / f"mutation-{name}.out").read_text().splitlines()
    refusals = {}
    for name, lines in mutations.items():
        if lines == mutation_source or not baseline_valid:
            refusals[name] = False
            continue
        path = output / (name + ".out")
        path.write_text("\n".join(lines) + "\n")
        result = run(["lean", "--run", str(oracle), "check", str(path), *oracle_options],
                     cwd=lean_root, timeout=60)
        refusals[name] = result["returncode"] != 0 and not result["timed_out"]
    stable = pins_match(inputs, pins)
    native_complete = all(record["returncode"] == 0 and not record["timed_out"]
                          for record in records)
    packets_exact = checked["returncode"] == 0 and not checked["timed_out"]
    behavior_passed = stable and native_complete and packets_exact and baseline_valid and all(refusals.values())
    result = dict(suite=args.suite, qualified=behavior_passed and not args.diagnostic,
                  diagnostic=args.diagnostic, behavior_passed=behavior_passed,
                  inputs_stable=stable, observed_packets_exact=packets_exact,
                  oracle_mutation_baseline_valid=baseline_valid,
                  native_runs_complete=native_complete, records=records,
                  negative_controls=refusals, source_pins=pins,
                  runner=dict(kind="cetta-petta", binary=str(runner), sha256=expected_hash,
                              argv=[str(runner), "--lang", "petta", "--quiet"],
                              declared_source_revision=args.cetta_revision,
                              build_correspondence="Supplied by runtime owners; not established by this replay."),
                  reference=dict(records=reference_records, source_pins=reference_pins,
                                 setup_error=reference_error,
                                 inputs_stable=pins_match(reference_inputs, reference_pins)),
                  source_machine_costs=json.loads((output / "source-costs.json").read_text()),
                  scope=("Selected formed List/Vector bundle observations; syntax decoding does not check typing."
                         if bundling else
                         "Source-pinned polynomial fold and admitted SearchTree methods; "
                         "arbitrary source-clause elaboration and native implementation refinement remain open."
                         if folding else
                         "Ordered position traversal; full inductive recursor compilation remains open."))
    (output / "qualification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in
                      ("qualified", "inputs_stable", "observed_packets_exact",
                       "native_runs_complete", "negative_controls")}, indent=2))
    return 0 if behavior_passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
