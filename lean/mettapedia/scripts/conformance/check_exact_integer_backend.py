#!/usr/bin/env python3
"""Qualify a CeTTa exact-integer ABI implementation against Lean expectations.

Example (run from the Lean project):
  python3 scripts/conformance/check_exact_integer_backend.py \
    --provider-root CETTA_TREE --generated-c GENERATED_C --output EVIDENCE_DIR \
    --cetta CETTA_BINARY

The selected generated C and provider are compiled in the evidence directory.
No CeTTa build tree is modified. LEAN_RUNNER may select a qualified Lean overlay.
GMP remains trusted; this is a differential gate, not a C correctness proof.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import uuid


OPS = ("add", "sub", "mul", "tquot", "fquot", "trem", "frem")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command: list[str], *, cwd: Path, data: str | None = None) -> str:
    result = subprocess.run(command, cwd=cwd, input=data, text=True,
                            capture_output=True, timeout=180, check=False)
    if result.returncode:
        raise RuntimeError(f"command failed ({result.returncode}): {shlex.join(command)}\n"
                           f"{result.stdout}\n{result.stderr}")
    if result.stderr:
        raise RuntimeError(f"unexpected stderr: {shlex.join(command)}\n{result.stderr}")
    return result.stdout


def expected(vector: list[str], alias: int, capacity: int, fault: int, mode: int) -> str:
    op, a, b, value, trace = vector
    untouched = a if alias == 1 else b if alias == 2 else "777"
    output = untouched
    events: list[str] = []
    called, complete, recorded_status = 0, False, 3
    if mode == 3:  # Direct provider: no generated guard or receipt.
        status = 2 if value == "declined" else 0
        if status == 0:
            output = value
    elif mode == 1:  # Missing mandatory receipt, before any arithmetic.
        status = 3
    else:
        events = trace.split(",")
        complete = True
        if value == "declined":
            status = 1
        else:
            called = 1
            if fault < 0:
                status, output = 0, value
            else:
                partial = op not in OPS[:3]
                pc = 2 if partial else 0
                events = (["S:0"] if partial else []) + [f"S:{pc}", f"E:{pc}:0:{fault}"]
                if fault in (1, 2, 3):
                    status = fault + 1
                    events.append(f"S:{pc + 1 + fault}")
                else:
                    status, complete = 3, False
        recorded_status = status
    count = len(events)
    complete = complete and mode != 2 and capacity >= count
    retained = events[:capacity] if mode != 2 else []
    after_a = output if alias == 1 else a
    after_b = output if alias == 2 else b
    return "\t".join(map(str, [status, output, count, int(complete), called,
                               ",".join(retained), after_a, after_b, recorded_status]))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--provider-root", type=Path, required=True)
    parser.add_argument("--generated-c", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cetta", type=Path, action="append", default=[])
    parser.add_argument("--lang", choices=("he", "petta", "prime"), action="append",
                        help="repeat to qualify several dialects; default: petta")
    parser.add_argument("--sanitize", action="store_true")
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    lean_root = here.parents[1]
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    run_identity = {"run_id": uuid.uuid4().hex,
                    "started_at": datetime.now(timezone.utc).isoformat()}
    # Invalidate any old pass before reading inputs or invoking a tool. A failed
    # or interrupted attempt remains incomplete, never a stale successful run.
    (out / "qualification.json").write_text(json.dumps(
        {**run_identity, "status": "running", "meaning": "Incomplete until status is passed"},
        indent=2) + "\n")
    provider_root = args.provider_root.resolve()
    provider = provider_root / "native/external_call_gmp_exact_integer_v1.c"
    generated = args.generated_c.resolve()
    oracle = here / "ExactIntegerBackendVectors.lean"
    probe = here / "exact_integer_abi_probe.c"
    cc = shlex.split(os.environ.get("CC", "cc"))
    flags = ["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-I", str(provider_root)]
    if args.sanitize:
        flags += ["-fsanitize=address,undefined", "-fno-omit-frame-pointer"]
    gmp_cflags = shlex.split(run(["pkg-config", "--cflags", "gmp"], cwd=lean_root))
    gmp_libs = shlex.split(run(["pkg-config", "--libs", "gmp"], cwd=lean_root))

    def native_dependencies() -> set[Path]:
        dependencies: set[Path] = set()
        for source in (provider, generated, probe):
            emitted = run(cc + flags + gmp_cflags + ["-MM", "-MT", "probe", str(source)], cwd=lean_root)
            names = shlex.split(emitted.replace("\\\n", " ").split(":", 1)[1])
            dependencies.update((lean_root / name).resolve() for name in names)
        return dependencies

    native_inputs = native_dependencies()
    inputs = [Path(__file__).resolve(), oracle, probe, generated, provider,
              provider.with_suffix(".h"), provider_root / "native/external_call_generated_abi_v1.h",
              lean_root / "Mettapedia/GSLT/LanguageDef/ArithmeticExtension.lean",
              lean_root / "Mettapedia/GSLT/LanguageDef/ExactArithmeticToExternalCall.lean"]
    inputs = sorted(set(inputs) | native_inputs)
    binaries = [path.resolve() for path in args.cetta]
    before = {str(path): digest(path) for path in inputs + binaries}
    runner = shlex.split(os.environ.get("LEAN_RUNNER", "lake env lean"))
    oracle_output = run(runner + ["--run", str(oracle), str(out / "vectors.tsv")], cwd=lean_root)
    (out / "oracle.log").write_text(oracle_output)
    vectors = [line.split("\t") for line in (out / "vectors.tsv").read_text().splitlines()]
    if not vectors or any(len(row) != 5 for row in vectors):
        raise RuntimeError("invalid Lean vector table")
    renames = [f"-Dcetta_external_call_exact_integer_{op}_v1=real_{op}" for op in OPS]
    commands = [cc + flags + renames + gmp_cflags + ["-c", str(provider), "-o", str(out / "provider.o")],
                cc + flags + gmp_cflags + [str(probe), str(generated), str(out / "provider.o")]
                + gmp_libs + ["-o", str(out / "abi-probe")]]
    for command in commands:
        run(command, cwd=lean_root)
    requests: list[str] = []
    answers: list[str] = []
    for vector in vectors:
        # Full arithmetic/alias matrix; receipt loss must not alter the result.
        settings = [(alias, capacity, -1, 0) for alias in range(3) for capacity in (0, 2, 4)]
        settings += [(0, 4, -1, mode) for mode in (1, 2, 3)]
        # All guarded and unguarded status exits; invalid statuses stay incomplete.
        settings += [(0, 4, fault, 0) for fault in (1, 2, 3, 99)]
        for alias, capacity, fault, mode in settings:
            requests.append(" ".join(vector[:3] + list(map(str, [alias, capacity, fault, mode]))))
            answers.append(expected(vector, alias, capacity, fault, mode))
    payload = "\n".join(requests) + "\n"
    wanted = "\n".join(answers) + "\n"
    (out / "abi.requests").write_text(payload)
    (out / "abi.expected").write_text(wanted)
    actual = run([str(out / "abi-probe")], cwd=lean_root, data=payload)
    (out / "abi.actual").write_text(actual)
    if actual != wanted:
        lines = actual.splitlines()
        mismatch = next((i for i, (a, b) in enumerate(zip(lines, answers)) if a != b), None)
        detail = (f"request {requests[mismatch]}\nexpected {answers[mismatch]}\nactual {lines[mismatch]}"
                  if mismatch is not None else f"wrong line count: {len(lines)} / {len(answers)}")
        raise RuntimeError("ABI qualification failed: " + detail)

    # A provider that reports success without computing must fail qualification.
    # This negative case tests the value comparison, not just successful status.
    invented = run([str(out / "abi-probe")], cwd=lean_root, data="add 2 3 0 4 0 0\n")
    correct = expected(["add", "2", "3", "5", "S:0,E:0:0:0,S:1"], 0, 4, -1, 0) + "\n"
    (out / "invented-value.actual").write_text(invented)
    if invented == correct:
        raise RuntimeError("invented-value negative control unexpectedly accepted")

    # Real public runtime arithmetic: only the common exact +,-,* fragment.
    # Division spellings and natural subtraction policy are deliberately not inferred.
    runtime_vectors = [v for v in vectors if v[0] in OPS[:3]]
    symbols = dict(zip(OPS[:3], ("+", "-", "*")))
    program = "".join(f"!({symbols[v[0]]} {v[1]} {v[2]})\n" for v in runtime_vectors)
    (out / "exact-integer.metta").write_text(program)
    runtime_expected = "\n".join(v[3] for v in runtime_vectors) + "\n"
    (out / "runtime.expected").write_text(runtime_expected)
    runtime_results = []
    for index, binary in enumerate(binaries):
        for language in args.lang or ["petta"]:
            # HE/Prime print an answer list; PeTTa prints each occurrence.
            # Require exactly one integer occurrence, including the framing.
            expected_output = runtime_expected if language == "petta" else "".join(
                f"[{v[3]}]\n" for v in runtime_vectors)
            (out / f"runtime-{language}.expected").write_text(expected_output)
            observed = run([str(binary), "--lang", language, "--quiet", str(out / "exact-integer.metta")],
                           cwd=binary.parent)
            name = f"runtime-{index}-{language}.actual"
            (out / name).write_text(observed)
            if observed != expected_output:
                raise RuntimeError(f"runtime qualification failed for {binary} ({language}); see {name}")
            runtime_results.append({"binary": str(binary), "sha256": before[str(binary)],
                                    "language": language, "cases": len(runtime_vectors)})
    after = {str(path): digest(path) for path in inputs + binaries}
    if before != after or native_inputs != native_dependencies():
        raise RuntimeError("qualification input changed during the gate")
    record = {**run_identity, "status": "passed", "finished_at": datetime.now(timezone.utc).isoformat(),
              "lean_vectors": len(vectors), "abi_cases": len(requests),
              "invented_value_rejected": True,
              "runtime_results": runtime_results, "sanitizers": args.sanitize,
              "inputs": before, "commands": commands,
              "compiler": run(cc + ["--version"], cwd=lean_root).splitlines()[0],
              "gmp_version": run(["pkg-config", "--modversion", "gmp"], cwd=lean_root).strip(),
              "boundary": "Differential qualification. GMP, C compilation and execution remain trusted. "
                          "Injected resource status does not establish recoverable GMP allocation failure."}
    (out / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"Exact integer backend: {len(requests)} ABI cases passed; "
          f"{len(runtime_vectors)} cases on each of {len(runtime_results)} binary/dialect selections")


if __name__ == "__main__":
    main()
